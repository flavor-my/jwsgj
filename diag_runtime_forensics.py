from __future__ import annotations

import ast
import atexit
import json
import logging
import operator
import os
import sys
import threading
import time
import traceback
import warnings
from collections import defaultdict
from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import Any, ClassVar

from jwsgj.diag_guard_io import (
    atomic_write_text,
)
from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.diag_shared_ast_nodes import iter_own_nodes
from jwsgj.diag_shared_source_core import parse_py_file
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CAT_DYNAMIC_BINDING,
    FIELD_RECOMMENDATIONS,
    FIELD_TOTAL_FUNCTIONS,
    FMT_DATETIME_ISO,
    LAYER_DEGRADE_EXC_WITH_IMPORT,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import get_temp_base, infer_project_root
from jwsgj.runtime_scope import (
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    PACKAGE_VERSION,
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    is_backup_snapshot_dir,
    is_test_dir_path,
    is_test_file_path,
    skill_root_of,
)

__version__ = PACKAGE_VERSION
logger = logging.getLogger(__name__)
__all__ = [
    "CoverageHook",
    "CoverageStaticCrossValidator",
    "CrossValidationEntry",
    "CrossValidationReport",
    "ExceptionHook",
    "Quadrant",
    "coverage_lib_available",
    "ensure_coverage_hook",
    "install",
    "run_cross_validation_layer",
    "snapshot",
    "status",
]
try:
    import coverage as _coverage_mod
    _HAS_COVERAGE = True
except ImportError as _imp_err:
    logger.debug("[diag_runtime_forensics] coverage 导入失败，覆盖率采集降级不可用: %s", _imp_err)
    _coverage_mod = None
    _HAS_COVERAGE = False
_COVERAGE_EXCS: tuple[type[BaseException], ...] = (
    (_coverage_mod.CoverageException,)
    if _HAS_COVERAGE and hasattr(_coverage_mod, "CoverageException")
    else ()
)
_COVERAGE_OP_EXCS: tuple[type[BaseException], ...] = (
    OSError, RuntimeError, KeyError, ValueError, *_COVERAGE_EXCS)
def coverage_lib_available() -> bool:
    return _HAS_COVERAGE
def _short_name(name: Any) -> str:
    return str(name or "").rsplit(".", 1)[-1]
def _coerce_skill_dir(skill_dir: Any) -> str | None:
    if skill_dir is None:
        return None
    try:
        text = os.fsdecode(os.fspath(skill_dir))
    except (TypeError, ValueError) as _e:
        logger.debug("技能根入参不可解析（按未指定处理）: %r: %s", skill_dir, _e)
        return None
    return text or None
def _graph_functions(call_graph) -> Mapping:
    try:
        functions = getattr(call_graph, "functions", None)
    except Exception as exc:  # noqa: BLE001 — 外部图载体属性可抛任意异常
        log_swallowed(
            __name__, exc, context=f"_graph_functions:{type(exc).__name__}")
        return {}
    return functions if isinstance(functions, Mapping) else {}
def _coerce_limit(value: Any, default: int) -> int:
    if isinstance(value, bool):
        return int(value)
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError):
        logger.debug("条数上限非整数，回退默认值 %s: %r", default, value)
        return default
def _restore_trace(saved_trace) -> None:
    try:
        sys.settrace(saved_trace)
    except (TypeError, RuntimeError) as exc:
        logger.debug("恢复trace函数失败: %s", exc)
def _workspace_coverage_dir(warned: bool,
                            skill_root: str = "") -> tuple[str | None, bool]:
    try:
        return (os.path.join(get_temp_base(_coerce_skill_dir(skill_root) or None),
                             "coverage"), warned)
    except (OSError, RuntimeError, ValueError, TypeError) as _e:
        if not warned:
            logger.warning(
                "CoverageHook: 无可用工作空间，覆盖率采集不启动"
                "（产物落点仅限会话工作空间，无兜底）: %s", _e)
        return None, True
def _coverage_source_dir(path: str) -> str:
    try:
        text = os.fsdecode(os.fspath(path))
    except (TypeError, ValueError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return ""
    if os.path.isfile(text):
        return os.path.dirname(text) or "."
    return text if os.path.isdir(text) else ""
def _coerce_source_paths(paths) -> list:
    if not paths:
        return []
    if isinstance(paths, str):
        return [paths]
    try:
        return list(paths)
    except TypeError:
        return [paths]
class CoverageHook:
    def __init__(self, data_dir: str | None = None,
                 skill_dir: str | None = None):
        self._cov: Any | None = None
        self._started: bool = False
        self._paused: bool = False
        self._lock = threading.Lock()
        self._data_dir_arg: str | None = _coerce_skill_dir(data_dir)
        self._skill_dir: str = _coerce_skill_dir(skill_dir) or ""
        self._data_dir: str | None = None
        self._data_dir_resolved: bool = False
        self._data_dir_warned: bool = False
        self._source_paths: list[str] = []
        self._saved_trace_func = None
        self._uncovered_cache: dict[str, frozenset] = {}
        self._snapshot_count: int = 0
        self._final_data: dict | None = None
    def _ensure_data_dir(self) -> str | None:
        if self._data_dir_resolved:
            return self._data_dir
        if self._data_dir_arg:
            self._data_dir = os.path.abspath(self._data_dir_arg)
            self._data_dir_resolved = True
            return self._data_dir
        self._data_dir, self._data_dir_warned = _workspace_coverage_dir(
            self._data_dir_warned, self._skill_dir)
        self._data_dir_resolved = self._data_dir is not None
        return self._data_dir
    def start(self, source_paths: list[str] | None = None) -> None:
        if not _HAS_COVERAGE:
            warnings.warn(
                "coverage.py 未安装，覆盖率采集不可用。pip install coverage",
                stacklevel=2)
            return
        with self._lock:
            if self._started:
                return
            data_dir = self._ensure_data_dir()
            if not data_dir:
                return
            self._source_paths = _coerce_source_paths(source_paths)
            try:
                os.makedirs(data_dir, exist_ok=True)
            except OSError as exc:
                logger.warning("覆盖率数据目录创建失败（兜底落点不可用）: %s", exc)
            source_dirs = self._collect_source_dirs()
            if self._source_paths and not source_dirs:
                logger.warning(
                    "覆盖率源路径均无效，覆盖率采集不启动；"
                    "禁止回退为全进程采集: %r", self._source_paths)
                return
            self._saved_trace_func = sys.gettrace()
            self._uncovered_cache.clear()
            self._final_data = None
            self._cov = self._build_coverage(data_dir, source_dirs)
            if self._cov is None:
                _restore_trace(self._saved_trace_func)
                return
            self._started = True
    def _build_coverage(self, data_dir: str, source_dirs: list[str]):
        if _coverage_mod is None:
            logger.debug("coverage 库不可用，覆盖率采集降级为未采集")
            return None
        cov = None
        try:
            cov = _coverage_mod.Coverage(
                data_file=os.path.join(data_dir, ".coverage"),
                source=source_dirs if source_dirs else None,
                branch=True,
            )
            cov.start()
            return cov
        except _COVERAGE_OP_EXCS as exc:
            if cov is not None:
                self._stop_partial_start(cov)
                self._release_cov_resources(cov)
            logger.warning("覆盖率采集启动失败（降级为未采集）: %s", exc)
            return None
    @staticmethod
    def _stop_partial_start(cov) -> None:
        try:
            cov.stop()
        except Exception as stop_exc:  # noqa: BLE001 — 降级：继续恢复 trace 并释放资源
            logger.debug("停止部分启动的 coverage 失败: %s", stop_exc)
    def _collect_source_dirs(self) -> list[str]:
        source_dirs: list[str] = []
        for p in self._source_paths:
            dirname = _coverage_source_dir(p)
            if dirname and dirname not in source_dirs:
                source_dirs.append(dirname)
        return source_dirs
    def pause(self) -> None:
        with self._lock:
            if self._started and not self._paused and self._cov:
                try:
                    self._cov.stop()
                except _COVERAGE_OP_EXCS as exc:
                    logger.warning(
                        "覆盖率采集暂停失败（保持采集态）: %s", exc)
                    return
                self._paused = True
                _restore_trace(self._saved_trace_func)
    def resume(self) -> None:
        with self._lock:
            if self._paused and self._cov:
                self._saved_trace_func = sys.gettrace()
                self._uncovered_cache.clear()
                try:
                    self._cov.start()
                except _COVERAGE_OP_EXCS as exc:
                    self._stop_partial_start(self._cov)
                    _restore_trace(self._saved_trace_func)
                    logger.warning(
                        "覆盖率采集恢复失败（保持暂停态，数据定格可收割）: %s",
                        exc)
                    return
                self._paused = False
    def snapshot(self) -> bool:
        with self._lock:
            if not self._started or not self._cov:
                return False
            data_dir = self._ensure_data_dir()
            if not data_dir:
                return False
            next_count = self._snapshot_count + 1
            snapshot_path = os.path.join(
                data_dir,
                f"snapshot_{time.time_ns()}_{next_count:04d}.json")
            try:
                os.makedirs(data_dir, exist_ok=True)
                text = json.dumps(
                    self._extract_data(), ensure_ascii=False, indent=2)
                atomic_write_text(
                    snapshot_path, text, tag="coverage_snapshot")
            except (OSError, TypeError, ValueError, RecursionError) as exc:
                logger.warning("覆盖率快照保存失败: %s", exc)
                return False
            self._snapshot_count = next_count
            return True
    def get_uncovered(self, filepath: str) -> set[int]:
        if not isinstance(filepath, str) or not filepath:
            return set()
        with self._lock:
            if not self._started or not self._cov:
                return set()
            cacheable = self._paused
            if cacheable:
                cached = self._uncovered_cache.get(filepath)
                if cached is not None:
                    return set(cached)
            try:
                _, _, _, missing, _ = self._cov.analysis2(filepath)
                result = frozenset(missing)
            except (*_COVERAGE_OP_EXCS, IndexError) as exc:
                logger.debug("获取未覆盖行失败: %s", exc)
                return set()
            if cacheable:
                self._uncovered_cache[filepath] = result
            return set(result)
    @property
    def data(self) -> dict:
        if not _HAS_COVERAGE:
            return {}
        with self._lock:
            if self._started:
                if not self._cov:
                    return {"files": {}}
                return self._extract_data()
            return self._final_data if self._final_data is not None else {}
    @property
    def source_paths(self) -> list[str]:
        return list(self._source_paths)
    @property
    def skill_dir(self) -> str:
        return self._skill_dir
    def _extract_data(self) -> dict:
        result: dict = {"files": {}}
        try:
            cov_data = self._cov.get_data()
            for filename in cov_data.measured_files():
                executed = cov_data.lines(filename)
                if executed is not None:
                    result["files"][filename] = {
                        "executed_lines": list(executed),
                    }
            return result
        except _COVERAGE_OP_EXCS as exc:
            logger.debug("读取覆盖率数据失败: %s", exc)
            return result
    def status(self) -> dict:
        with self._lock:
            return {
                "started": self._started,
                "paused": self._paused,
                "snapshots": self._snapshot_count,
                "data_dir": self._ensure_data_dir(),
                "has_coverage_lib": _HAS_COVERAGE,
            }
    def stop(self) -> None:
        with self._lock:
            if not self._started:
                return
            if self._cov:
                self._final_data = self._extract_data()
                try:
                    self._cov.stop()
                except Exception as exc:  # noqa: BLE001 — 清理路径不得炸停止主流程
                    logger.warning("停止覆盖率采集失败: %s", exc)
                self._release_cov_resources()
                _restore_trace(self._saved_trace_func)
            self._started = False
            self._paused = False
    def _release_cov_resources(self, cov: Any | None = None) -> None:
        target = self._cov if cov is None else cov
        if not target:
            return
        try:
            _exit_cb = (getattr(target, "_atexit", None)
                        or getattr(target, "_atexit_hook", None))
            if _exit_cb is not None:
                atexit.unregister(_exit_cb)
        except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链（清理路径不得炸停止主流程）
            logger.debug("unregister coverage atexit 钩子失败: %s", exc)
        try:
            target.erase()
        except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链（清理路径不得炸停止主流程）
            logger.debug("清理 .coverage 磁盘残留失败: %s", exc)
class Quadrant:
    ACTIVE = "active"
    DYNAMIC = CAT_DYNAMIC_BINDING
    UNDERTESTED = "undertested"
    DEAD = "dead_code"
    EXTERNAL_API = "external_api"
@dataclass
class CrossValidationEntry:
    func_key: str
    func_name: str
    filepath: str
    line_range: tuple[int, int]
    is_covered: bool
    is_reachable: bool
    quadrant: str
    coverage_pct: float = 0.0
    callers: list[str] = field(default_factory=list)
    confidence: str = "medium"
@dataclass
class CrossValidationReport:
    project_root: str
    total_functions: int = 0
    entries: list[CrossValidationEntry] = field(default_factory=list)
    active_count: int = 0
    dynamic_count: int = 0
    undertested_count: int = 0
    dead_count: int = 0
    external_api_count: int = 0
    false_positive_orphans: int = 0
    false_negative_orphans: int = 0
    confirmed_dead: int = 0
    recommendations: list[str] = field(default_factory=list)
    dynamic_binding_candidates: list[str] = field(default_factory=list)
    def summary(self) -> dict:
        total = max(self.total_functions, 1)
        if self.total_functions <= 0:
            static_precision = 0.0 if self.false_positive_orphans else None
        else:
            static_precision = round(
                max(0.0, min(100.0, (total - self.false_positive_orphans)
                             / total * 100)), 1)
        return {
            FIELD_TOTAL_FUNCTIONS: self.total_functions,
            "quadrant_distribution": {
                "active": self.active_count,
                CAT_DYNAMIC_BINDING: self.dynamic_count,
                "undertested": self.undertested_count,
                "dead_code": self.dead_count,
                "external_api": self.external_api_count,
            },
            "precision_metrics": {
                "false_positive_orphans": self.false_positive_orphans,
                "false_negative_orphans": self.false_negative_orphans,
                "confirmed_dead": self.confirmed_dead,
                "external_api_excluded": self.external_api_count,
                "static_precision": static_precision,
            },
            FIELD_RECOMMENDATIONS: self.recommendations,
            "dynamic_binding_candidates": self.dynamic_binding_candidates,
        }
def _posix_path(path: str) -> str:
    return path.replace("\\", "/")
def _rel_segments(root: str, project_root: str) -> list[str]:
    try:
        rel = os.path.relpath(root, project_root)
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_rel_segments:ValueError')
        return []
    return [seg for seg in _posix_path(rel).split("/")
            if seg not in ("", ".", "..")]
def _skip_walk_dir(root: str, project_root: str, skip_tests: bool = False) -> bool:
    raw_parts = _rel_segments(root, project_root)
    if any(seg.startswith(".") for seg in raw_parts):
        return True
    parts = {seg.lower() for seg in raw_parts}
    ignore_dirs = (SCAN_COLLECT_PRUNE_DIRS_LOWER if skill_root_of(project_root)
                   else GENERIC_SCAN_IGNORE_DIRS_LOWER)
    return bool(
        parts & ignore_dirs
        or any(is_backup_snapshot_dir(p) for p in parts)
        or (skip_tests
            and is_test_dir_path(os.path.join(root, "__probe__.py")))
    )
_CONST_UNRESOLVED = object()
_CONSTANT_FALSE_COMPARATORS = {
    ast.Eq: operator.ne,
    ast.Is: operator.is_not,
    ast.IsNot: operator.is_,
    ast.NotEq: operator.eq,
    ast.Lt: operator.ge,
    ast.LtE: operator.gt,
    ast.Gt: operator.le,
    ast.GtE: operator.lt,
    ast.In: lambda left, right: left not in right,
    ast.NotIn: lambda left, right: left in right,
}
def _project_root(call_graph) -> str:
    if call_graph is None:
        return ""
    return getattr(call_graph, "project_root", "") or ""
def _resolve_source_path(call_graph, filepath: str) -> str:
    if not filepath or os.path.isabs(filepath):
        return filepath
    project_root = _project_root(call_graph)
    if project_root:
        candidate = os.path.join(project_root, filepath)
        if os.path.exists(candidate):
            return candidate
    return filepath
def _cache_key(filepath: str) -> str:
    try:
        return os.path.normcase(os.path.abspath(filepath))
    except (OSError, ValueError):
        return filepath
def _coverage_identity(filepath: str, project_root: str) -> str:
    identity_path = (filepath if os.path.isabs(filepath) or not project_root
                     else os.path.join(project_root, filepath))
    return os.path.normcase(os.path.realpath(os.path.abspath(identity_path)))
def _load_tree(filepath: str, call_graph=None, *, ast_getter=None,
               cache: dict[str, ast.Module | None] | None = None):
    key = _cache_key(filepath)
    if cache is not None and key in cache:
        return cache[key]
    tree = None
    if ast_getter is not None:
        tree = _call_ast_getter(ast_getter, filepath)
    if tree is None:
        _source, tree = parse_py_file(
            _resolve_source_path(call_graph, filepath))
    if cache is not None:
        cache[key] = tree
    return tree
def _call_ast_getter(ast_getter, filepath: str):
    try:
        tree = ast_getter(filepath)
    except Exception as exc:  # noqa: BLE001
        log_swallowed(
            __name__, exc,
            f"_load_tree: ast_getter 回退直读 {os.path.basename(filepath)}")
        return None
    return tree if isinstance(tree, ast.AST) else None
class _ExportHarvester:
    def __init__(self, call_graph) -> None:
        self.call_graph = call_graph
    def build_export_evidence(
            self, ast_getter=None) -> tuple[dict[str, set[str]], set[str]]:
        exports_by_file: dict[str, set[str]] = {}
        dynamic_names: set[str] = set()
        for fpath, skip_tests in self._iter_py_files():
            exported = exports_by_file.setdefault(_cache_key(fpath), set())
            self._harvest_file_exports(
                fpath, exported, dynamic_names, skip_tests,
                ast_getter=ast_getter)
        return exports_by_file, dynamic_names
    def _iter_py_files(self):
        project_root = _project_root(self.call_graph)
        if not project_root:
            return
        def _on_walk_error(exc: OSError) -> None:
            logger.warning(
                "导出收割遍历跳过不可读目录（结果按部分集处理）: %s", exc)
        for root, dirs, names in os.walk(project_root, onerror=_on_walk_error):
            dirs[:] = [d for d in dirs
                       if not _skip_walk_dir(os.path.join(root, d),
                                             project_root, skip_tests=False)]
            skip_tests = _skip_walk_dir(root, project_root, skip_tests=True)
            for fname in names:
                if not fname or fname.startswith('.'):
                    continue
                if fname.lower().endswith('.py'):
                    yield os.path.join(root, fname), skip_tests
    def _harvest_file_exports(self, fpath: str, exported: set,
                              dynamic_names: set, skip_tests: bool,
                              ast_getter=None) -> None:
        skip_tests = skip_tests or is_test_file_path(fpath)
        try:
            tree = _load_tree(fpath, self.call_graph, ast_getter=ast_getter)
            if tree is None:
                return
            for node in iter_own_nodes(tree):
                if not skip_tests:
                    self._harvest_all_list_names(node, exported)
                    self._harvest_import_from_names(node, exported)
            for node in walk_nodes(tree):
                val = self._getattr_export_name(node)
                if val is not None:
                    dynamic_names.add(val)
        except Exception as exc:  # noqa: BLE001
            log_swallowed(
                __name__, exc,
                f"_harvest_file_exports: 单文件收割中断 {os.path.basename(fpath)}")
    @staticmethod
    def _all_assignment_parts(node: ast.AST):
        if isinstance(node, ast.Assign):
            return node.targets, node.value
        if isinstance(node, ast.AugAssign):
            if not isinstance(node.op, ast.Add):
                return None
            return [node.target], node.value
        if isinstance(node, ast.AnnAssign):
            targets = [node.target] if node.target is not None else []
            return targets, node.value
        return None
    @classmethod
    def _all_list_strings(cls, value) -> list[str]:
        if isinstance(value, (ast.List, ast.Tuple)):
            return [elt.value for elt in value.elts
                    if isinstance(elt, ast.Constant)
                    and isinstance(elt.value, str)]
        if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
            return (cls._all_list_strings(value.left)
                    + cls._all_list_strings(value.right))
        return []
    @classmethod
    def _harvest_all_list_names(cls, node: ast.AST, exported: set) -> None:
        parts = cls._all_assignment_parts(node)
        if parts is not None:
            targets, value = parts
            names = cls._all_list_strings(value)
            if not names:
                return
            for target in targets:
                if isinstance(target, ast.Name) and target.id == '__all__':
                    exported.update(names)
            return
        if not isinstance(node, ast.Expr):
            return
        call = node.value
        if not (isinstance(call, ast.Call)
                and isinstance(call.func, ast.Attribute)
                and isinstance(call.func.value, ast.Name)
                and call.func.value.id == '__all__'
                and len(call.args) == 1):
            return
        if call.func.attr == 'append':
            arg = call.args[0]
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                exported.add(arg.value)
        elif call.func.attr == 'extend':
            exported.update(cls._all_list_strings(call.args[0]))
    @staticmethod
    def _harvest_import_from_names(node: ast.AST, exported: set) -> None:
        if not isinstance(node, ast.ImportFrom):
            return
        for alias in node.names:
            name = alias.asname or alias.name
            if name not in (None, '', '*'):
                exported.add(name)
    @staticmethod
    def _is_getattr_call(node) -> bool:
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == 'getattr'
                and len(node.args) >= 2)
    @classmethod
    def _getattr_export_name(cls, node):
        if not cls._is_getattr_call(node):
            return None
        name_arg = node.args[1]
        if not (isinstance(name_arg, ast.Constant)
                and isinstance(name_arg.value, str)):
            return None
        val = name_arg.value
        if not val or val[0].isdigit() or not val.replace('_', '').isalnum():
            return None
        return val
class _PathFeasibilityAnalyzer:
    def __init__(self, call_graph, ast_cache: dict[str, ast.Module | None]) -> None:
        self.call_graph = call_graph
        self._ast_cache = ast_cache
    def check_path_feasibility(self, filepath: str, target_line: int) -> bool:
        tree = _load_tree(filepath, self.call_graph, cache=self._ast_cache)
        if tree is None:
            return False
        return self._protected_block_contains(tree, target_line)
    @staticmethod
    def _protected_block_contains(tree, target_line: int) -> bool:
        for node in walk_nodes(tree):
            if isinstance(node, ast.If) and _PathFeasibilityAnalyzer._is_constant_false_condition(node.test):
                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = (getattr(node.body[-1], 'end_lineno', None)
                            if node.body else None) or node.lineno
                if body_start <= target_line <= body_end:
                    return True
        return False
    @classmethod
    def _is_constant_false_condition(cls, test: ast.AST) -> bool:
        if isinstance(test, ast.BoolOp):
            if isinstance(test.op, ast.And):
                return any(cls._is_constant_false_condition(value)
                           for value in test.values)
            if isinstance(test.op, ast.Or):
                return all(cls._is_constant_false_condition(value)
                           for value in test.values)
        if (cls._is_negated_truthy(test)
                or cls._is_constant_comparison_false(test)):
            return True
        value = cls._get_const_value(test)
        return value is not _CONST_UNRESOLVED and not bool(value)
    @classmethod
    def _is_negated_truthy(cls, test: ast.AST) -> bool:
        if not (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)):
            return False
        operand = test.operand
        val = cls._get_const_value(operand)
        return val is not _CONST_UNRESOLVED and bool(val)
    @classmethod
    def _is_constant_comparison_false(cls, test: ast.AST) -> bool:
        if not (isinstance(test, ast.Compare) and len(test.ops) == 1):
            return False
        compare = _CONSTANT_FALSE_COMPARATORS.get(type(test.ops[0]))
        if compare is None or not test.comparators:
            return False
        left_val = cls._get_const_value(test.left)
        right_val = cls._get_const_value(test.comparators[0])
        if left_val is _CONST_UNRESOLVED or right_val is _CONST_UNRESOLVED:
            return False
        if (isinstance(test.ops[0], (ast.Is, ast.IsNot))
                and not any(value is None or isinstance(value, bool)
                            or value is Ellipsis
                            for value in (left_val, right_val))):
            return False
        try:
            return compare(left_val, right_val)
        except (TypeError, ValueError):
            return False
    @staticmethod
    def _get_const_value(node: ast.AST):
        if isinstance(node, ast.Name) and node.id == "__debug__":
            return sys.flags.optimize == 0
        try:
            return ast.literal_eval(node)
        except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
            return _CONST_UNRESOLVED
class _DynamicDispatchJudge:
    _DYNAMIC_PATTERNS = frozenset({'summary', 'stats', 'get_statistics'})
    def is_dynamic_dispatch(self, func_name: str, filepath: str,
                             class_name: str | None = None) -> bool:
        if not func_name:
            return False
        return (self._is_test_symbol(func_name, filepath)
                or self._is_plugin_protocol_dispatch(func_name, class_name)
                or self._is_ast_visitor(func_name)
                or self._is_serialization_symbol(func_name)
                or self._is_protocol_callback(func_name))
    @staticmethod
    def _is_test_symbol(func_name: str, filepath: str) -> bool:
        simple_name = _short_name(func_name)
        if simple_name.startswith('test_') or simple_name == 'test':
            return True
        if not filepath:
            return False
        return is_test_file_path(filepath)
    _PLUGIN_PROTOCOL_METHODS = frozenset({'fix', 'can_auto_fix'})
    @classmethod
    def _is_plugin_protocol_dispatch(cls, func_name: str,
                                     class_name: str | None) -> bool:
        simple_name = _short_name(func_name)
        if simple_name not in cls._PLUGIN_PROTOCOL_METHODS:
            return False
        return bool(class_name) or '.' in func_name
    @staticmethod
    def _is_ast_visitor(func_name: str) -> bool:
        if '.visit_' in func_name or func_name.startswith('visit_'):
            return True
        return '._visit_' in func_name or func_name.startswith('_visit_')
    @classmethod
    def _is_serialization_symbol(cls, func_name: str) -> bool:
        simple_name = _short_name(func_name)
        if simple_name in cls._DYNAMIC_PATTERNS:
            return True
        return simple_name.startswith(('to_', 'from_'))
    @staticmethod
    def _is_protocol_callback(func_name: str) -> bool:
        simple_name = _short_name(func_name)
        if simple_name.startswith('__') and simple_name.endswith('__'):
            return True
        return '.on_' in func_name or func_name.startswith('on_')
_COVERAGE_BASENAME_PREFIX = "\0basename:"
_COVERAGE_QUADRANT_MATRIX = {
    (True, True): (Quadrant.ACTIVE, "high"),
    (True, False): (Quadrant.DYNAMIC, "medium"),
    (False, True): (Quadrant.UNDERTESTED, "medium"),
}
class CoverageStaticCrossValidator:
    def __init__(self, call_graph=None, coverage_data: dict | None = None,
                 skill_type: str = "unknown", ast_getter=None,
                 include_tests: bool = False) -> None:
        self.call_graph = call_graph
        self.coverage_data = coverage_data or {}
        self.skill_type = skill_type
        self.include_tests = include_tests
        self._is_library = skill_type == "library"
        self._ast_cache: dict[str, ast.Module | None] = {}
        self._ast_getter = ast_getter
        self._export_harvester = _ExportHarvester(call_graph)
        self._feasibility = _PathFeasibilityAnalyzer(call_graph, self._ast_cache)
        self._dispatch_judge = _DynamicDispatchJudge()
    def validate(self) -> CrossValidationReport:
        report = CrossValidationReport(
            project_root=_project_root(self.call_graph),
        )
        if not self.call_graph:
            report.recommendations.append("无调用图数据，跳过交叉验证")
        else:
            self._classify_all(report)
            self._generate_recommendations(report)
        logger.info(
            "coverage_cross_validator validate 完成: total=%d active=%d "
            "dynamic=%d undertested=%d dead=%d external_api=%d entries=%d",
            report.total_functions, report.active_count,
            report.dynamic_count, report.undertested_count,
            report.dead_count, report.external_api_count,
            len(report.entries))
        return report
    def _classify_all(self, report: CrossValidationReport) -> None:
        covered_lines = self._build_coverage_index()
        if not covered_lines:
            report.recommendations.append("无有效运行时覆盖率数据，跳过交叉验证")
            return
        reachable_funcs = self._build_reachability_index()
        exports_by_file, dynamic_names = (
            self._export_harvester.build_export_evidence(self._ast_getter))
        functions = _graph_functions(self.call_graph)
        if not functions:
            report.recommendations.append("调用图函数表为空，交叉验证无可比样本")
        for func_key, fnode in functions.items():
            if not self.include_tests and is_test_file_path(
                    getattr(fnode, "filepath", "")):
                continue
            source_path = _resolve_source_path(
                self.call_graph, getattr(fnode, "filepath", ""))
            exported_names = exports_by_file.get(_cache_key(source_path), set())
            entry = self._classify_function(
                func_key, fnode, covered_lines, reachable_funcs,
                exported_names, dynamic_names)
            report.entries.append(entry)
            report.total_functions += 1
            self._record_quadrant(report, func_key, entry)
    @staticmethod
    def _record_quadrant(report: CrossValidationReport, func_key: str,
                         entry) -> None:
        if entry.quadrant == Quadrant.ACTIVE:
            report.active_count += 1
            return
        if entry.quadrant == Quadrant.DYNAMIC:
            report.dynamic_count += 1
            if entry.is_covered and not entry.is_reachable:
                report.false_positive_orphans += 1
            report.dynamic_binding_candidates.append(func_key)
            return
        if entry.quadrant == Quadrant.UNDERTESTED:
            report.undertested_count += 1
            report.false_negative_orphans += 1
            return
        if entry.quadrant == Quadrant.DEAD:
            report.dead_count += 1
            if entry.confidence == "high":
                report.confirmed_dead += 1
            return
        if entry.quadrant == Quadrant.EXTERNAL_API:
            report.external_api_count += 1
    def _build_coverage_index(self) -> dict[str, set[int] | None]:
        index: dict[str, set[int] | None] = {}
        basename_execs: dict[str, list[tuple[str, set[int]]]] = {}
        pr = _project_root(self.call_graph)
        files = self.coverage_data.get("files", {})
        if not isinstance(files, Mapping):
            logger.warning(
                "覆盖率数据 files 形态非法（按未采集处理）: %r", type(files).__name__)
            return index
        for filepath, data in files.items():
            self._register_file_coverage(
                index, basename_execs, filepath, data, pr)
        self._resolve_basename_keys(index, basename_execs)
        return index
    @staticmethod
    def _register_file_coverage(index: dict[str, set[int] | None],
                                basename_execs: dict[str, list[tuple[str, set[int]]]],
                                filepath, data, pr: str) -> None:
        if not isinstance(filepath, str) or not filepath:
            logger.debug("_build_coverage_index: 非文本文件键跳过 %r", filepath)
            return
        if not isinstance(data, dict):
            logger.debug("_build_coverage_index: 非 dict 行数据跳过 %r", filepath)
            return
        _raw_lines = data.get("executed_lines", [])
        if not isinstance(_raw_lines, (list, tuple, set)):
            logger.debug(
                "_build_coverage_index: executed_lines 非 list/tuple/set 跳过 %r",
                filepath)
            return
        if not all(isinstance(line, int) and not isinstance(line, bool)
                   for line in _raw_lines):
            logger.debug(
                "_build_coverage_index: executed_lines 含非法行号跳过 %r",
                filepath)
            return
        executed = set(_raw_lines)
        index[filepath] = executed
        index[_posix_path(filepath)] = executed
        identity = _coverage_identity(filepath, pr)
        index[identity] = executed
        index[_posix_path(identity)] = executed
        if pr:
            try:
                anchored_path = (filepath if os.path.isabs(filepath)
                                 else os.path.join(pr, filepath))
                index[_posix_path(os.path.relpath(anchored_path, pr))] = executed
            except ValueError:
                logger.debug(
                    "_build_coverage_index: 跨盘符 relpath 失败，跳过相对路径索引",
                    exc_info=True)
        basename_execs.setdefault(os.path.basename(filepath), []).append(
            (identity, executed))
    @staticmethod
    def _resolve_basename_keys(index: dict[str, set[int] | None],
                               basename_execs: dict[str, list[tuple[str, set[int]]]]) -> None:
        for basename, entries in basename_execs.items():
            identities = {identity for identity, _executed in entries}
            execs = [executed for _identity, executed in entries]
            resolved = (execs[0]
                        if len(identities) == 1
                        and all(e == execs[0] for e in execs) else None)
            index[_COVERAGE_BASENAME_PREFIX + basename] = resolved
    def _build_reachability_index(self) -> set[str]:
        if not self.call_graph:
            return set()
        reachability_map = (
            self.call_graph.analyses.breakpoints.reach
            .compute_reachability_from_entries())
        if not isinstance(reachability_map, Mapping):
            raise TypeError(
                "compute_reachability_from_entries 返回非映射，可达性未度量")
        return {key for key, reachable in reachability_map.items() if reachable}
    def _classify_function(
        self,
        func_key: str,
        fnode,
        covered_lines: dict[str, set[int] | None],
        reachable_funcs: set[str],
        exported_names: set[str],
        dynamic_names: set[str],
    ) -> CrossValidationEntry:
        filepath = getattr(fnode, "filepath", "")
        start, end = self._resolve_line_range(fnode)
        is_covered, coverage_pct = self._match_coverage(
            filepath, start, end, covered_lines)
        is_reachable = func_key in reachable_funcs
        func_name = str(getattr(fnode, "name", None) or func_key)
        simple_func_name = _short_name(func_name)
        is_module_level = not (
            getattr(fnode, "is_method", False)
            or getattr(fnode, "class_name", None))
        is_exported = bool(exported_names) and (
            func_name in exported_names or func_key in exported_names
            or (is_module_level and simple_func_name in exported_names))
        is_dynamic_name = bool(dynamic_names) and (
            func_name in dynamic_names or func_key in dynamic_names
            or simple_func_name in dynamic_names)
        is_dynamic_dispatch = is_dynamic_name or (
            self._dispatch_judge.is_dynamic_dispatch(
                func_name, filepath,
                class_name=getattr(fnode, "class_name", None)))
        quadrant, confidence = self._determine_quadrant(
            is_covered, is_reachable, is_exported, is_dynamic_dispatch,
            filepath, start, func_name)
        # 单行函数的定义与函数体共享覆盖行，无法仅凭行覆盖区分导入与调用。
        if quadrant == Quadrant.DEAD and start > 0 and start == end:
            confidence = "low"
        return CrossValidationEntry(
            func_key=func_key,
            func_name=func_name,
            filepath=filepath,
            line_range=(start, end),
            is_covered=is_covered,
            is_reachable=is_reachable,
            quadrant=quadrant,
            coverage_pct=round(coverage_pct, 3),
            callers=self._collect_callers(func_key),
            confidence=confidence,
        )
    @staticmethod
    def _resolve_line_range(fnode) -> tuple[int, int]:
        start = getattr(fnode, "start_line", 0)
        end = getattr(fnode, "end_line", 0)
        if (isinstance(start, bool) or not isinstance(start, int)
                or start <= 0):
            return 0, 0
        if (isinstance(end, bool) or not isinstance(end, int)
                or end <= 0 or end < start):
            return 0, 0
        return start, end
    def _collect_callers(self, func_key: str) -> list[str]:
        callers = getattr(self.call_graph, "callers", None) if self.call_graph else None
        raw_callers = callers.get(func_key, ()) if isinstance(callers, Mapping) else ()
        return sorted(str(c) for c in raw_callers)
    def _resolve_body_start(self, filepath: str, start: int, end: int) -> int:
        if end <= start:
            return start
        fallback = start + 1
        if not filepath or start <= 0:
            return fallback
        tree = _load_tree(
            filepath, self.call_graph, ast_getter=self._ast_getter,
            cache=self._ast_cache)
        if tree is None:
            return fallback
        for node in walk_nodes(tree):
            if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and node.lineno == start
                    and (node.end_lineno or node.lineno) == end
                    and node.body):
                return node.body[0].lineno
        return fallback
    def _match_coverage(
        self,
        filepath: str,
        start: int,
        end: int,
        covered_lines: dict[str, set[int] | None],
    ) -> tuple[bool, float]:
        if start <= 0:
            return False, 0.0
        executed_set = covered_lines.get(filepath)
        if executed_set is None and filepath:
            executed_set = covered_lines.get(_posix_path(filepath))
        project_root = _project_root(self.call_graph)
        identity = ""
        if (executed_set is None and filepath
                and (os.path.isabs(filepath) or project_root)):
            identity = _coverage_identity(filepath, project_root)
            executed_set = covered_lines.get(identity)
            if executed_set is None:
                executed_set = covered_lines.get(_posix_path(identity))
        if executed_set is None:
            basename = os.path.basename(filepath) if filepath else ""
            basename_key = _COVERAGE_BASENAME_PREFIX + basename
            if basename and basename_key in covered_lines:
                executed_set = covered_lines[basename_key]
                if executed_set is None:
                    return False, 0.0
        if executed_set is None:
            return False, 0.0
        if end <= start:
            # 单行函数的 ``def`` 与函数体共享同一覆盖行：直接以定义行作为
            # 函数体行集，否则下方 ``body_start = start + 1`` 会得到空集，
            # 使已执行的单行函数被误判为未覆盖。
            func_lines = {start}
        else:
            body_start = self._resolve_body_start(filepath, start, end)
            if body_start <= start:
                body_start = start + 1
            func_lines = set(range(body_start, end + 1))
        executed = executed_set & func_lines
        if not executed:
            return False, 0.0
        return True, len(executed) / max(len(func_lines), 1)
    def _determine_quadrant(
        self,
        is_covered: bool,
        is_reachable: bool,
        is_exported: bool,
        is_dynamic_dispatch: bool,
        filepath: str,
        start: int,
        func_name: str = "",
    ) -> tuple[str, str]:
        evidence = (is_covered, is_reachable)
        if evidence in _COVERAGE_QUADRANT_MATRIX:
            return _COVERAGE_QUADRANT_MATRIX[evidence]
        simple_func_name = _short_name(func_name)
        if is_exported or (self._is_library
                           and not simple_func_name.startswith("_")):
            return Quadrant.EXTERNAL_API, "low"
        if is_dynamic_dispatch:
            return Quadrant.DYNAMIC, "medium"
        confidence = "high"
        if filepath and start > 0 and self._feasibility.check_path_feasibility(
                filepath, start):
            confidence = "low"
        return Quadrant.DEAD, confidence
    def _generate_recommendations(self, report: CrossValidationReport) -> None:
        if report.false_positive_orphans > 0:
            report.recommendations.append(
                f"发现 {report.false_positive_orphans} 个动态绑定候选：覆盖率已覆盖但静态分析标记为孤立。"
                f"建议运行 RuntimeBindingScanner 进行深度扫描。"
            )
        if report.undertested_count > 0:
            report.recommendations.append(
                f"发现 {report.undertested_count} 个未充分测试函数：入口点 BFS 可达但覆盖率未覆盖。"
                f"建议补充测试用例。"
            )
        if report.confirmed_dead > 0:
            report.recommendations.append(
                f"确认 {report.confirmed_dead} 个高置信度死代码函数："
                "既无覆盖率也无入口点可达路径。建议审查是否需要删除。"
            )
        suspected_dead = report.dead_count - report.confirmed_dead
        if suspected_dead > 0:
            report.recommendations.append(
                f"发现 {suspected_dead} 个低置信度死代码候选："
                "受常量路径等证据影响，需人工复核，不计入确认死代码。"
            )
        if report.external_api_count > 0:
            report.recommendations.append(
                f"排除 {report.external_api_count} 个库型技能公开 API 函数："
                "无内部调用者但等待外部调用，非死代码。"
            )
        if report.false_positive_orphans > 0:
            report.recommendations.append(
                f"静态分析假阳性率: {report.false_positive_orphans}/{report.total_functions} "
                f"函数被误判为孤立（实际有覆盖率覆盖）。"
            )
def _build_cross_validator(coverage_hook, call_graph, project_root, ctx, *, library_probe):
    if coverage_hook is not None:
        coverage_hook.snapshot()
        coverage_data = coverage_hook.data
    else:
        coverage_data = {}
    ctx_get_ast = (getattr(ctx, "get_ast", None)
                   if ctx is not None else None)
    return CoverageStaticCrossValidator(
        call_graph=call_graph, coverage_data=coverage_data,
        skill_type="library" if library_probe(project_root) else "unknown",
        ast_getter=ctx_get_ast if callable(ctx_get_ast) else None,
    )
def run_cross_validation_layer(report, coverage_hook, call_graph,
                               project_root, ctx, *, library_probe) -> None:
    try:
        cv_report = _build_cross_validator(
            coverage_hook, call_graph, project_root, ctx,
            library_probe=library_probe).validate()
        cv_summary = cv_report.summary()
        _precision = cv_summary.get("precision_metrics", {}) or {}
        report.metrics[CAT_CROSS_VALIDATION] = _precision
        report.metrics["cross_validation_full"] = cv_summary
        fp_orphans = _precision.get("false_positive_orphans", 0)
        if isinstance(fp_orphans, (int, float)) and fp_orphans > 0:
            logger.info(f"       交叉验证: {fp_orphans} 静态假阳性（覆盖率已覆盖但标记为孤立）")
    except LAYER_DEGRADE_EXC_WITH_IMPORT as exc:
        logger.debug("交叉验证失败(该层数据缺失): %s", exc)
def _skill_root_from_paths(source_paths) -> str:
    for raw in _coerce_source_paths(source_paths):
        try:
            probe = os.path.abspath(str(raw))
        except (OSError, ValueError) as _e:
            logger.debug("覆盖率源路径归一失败（跳过该候选）: %s: %s", raw, _e)
            continue
        if os.path.isdir(probe):
            probe = os.path.join(probe, "_probe.py")
        try:
            root = infer_project_root(probe)
        except (OSError, ValueError) as _e:
            logger.debug("覆盖率源路径上溯失败（跳过该候选）: %s: %s", probe, _e)
            continue
        if root:
            return root
    return ""
def _log_group_stats(title: str, stats: dict) -> None:
    if not stats:
        return
    logger.info("\n%s:", title)
    for name, count in stats.items():
        logger.info("  %s: %d", name, count)
class ExceptionHook:
    _MAX_RECORDS = 500
    _DEFAULT_RECORD_LIMIT = 50
    _CHAIN: ClassVar[list[ExceptionHook]] = []
    _CHAIN_LOCK = threading.Lock()
    def __init__(self):
        self._original_hook = sys.excepthook
        self._bypass_hook = self._original_hook
        self._handler_state = threading.local()
        self._installed: bool = False
        self._lock = threading.Lock()
        self._records: list[dict] = []
        self._total_recorded: int = 0
        self._truncated: bool = False
        self._by_type: dict[str, list[dict]] = defaultdict(list)
        self._by_file: dict[str, list[dict]] = defaultdict(list)
    @staticmethod
    def _is_handler_of(hook, instance) -> bool:
        return (getattr(hook, "__func__", None) is ExceptionHook._handler
                and getattr(hook, "__self__", None) is instance)
    @classmethod
    def _unlink_from_chain(cls, instance) -> bool:
        if instance not in cls._CHAIN:
            return False
        idx = cls._CHAIN.index(instance)
        was_in_place = cls._is_handler_of(sys.excepthook, instance)
        del cls._CHAIN[idx]
        for succ in cls._CHAIN[idx:]:
            if cls._is_handler_of(succ._original_hook, instance):
                succ._original_hook = instance._original_hook
                break
        return was_in_place
    def install(self) -> None:
        with self._lock:
            if self._installed:
                return
            with ExceptionHook._CHAIN_LOCK:
                if ExceptionHook._is_handler_of(sys.excepthook, self):
                    self._installed = True
                    return
                ExceptionHook._unlink_from_chain(self)
                self._original_hook = sys.excepthook
                sys.excepthook = self._handler
                ExceptionHook._CHAIN.append(self)
            self._installed = True
    def uninstall(self) -> None:
        with self._lock:
            if not self._installed:
                return
            self._installed = False
            with ExceptionHook._CHAIN_LOCK:
                if ExceptionHook._unlink_from_chain(self):
                    sys.excepthook = self._original_hook
    def _handler(self, exc_type, exc_value, exc_tb):
        reentrant = getattr(self._handler_state, "active", False)
        if not reentrant:
            self._handler_state.active = True
        try:
            if self._installed and not reentrant:
                try:
                    self._record(exc_type, exc_value, exc_tb)
                except Exception:  # noqa: BLE001 — 钩子是最后一道防线，不允许自身崩溃
                    try:
                        logger.debug("ExceptionHook._record 自身异常", exc_info=True)
                    except Exception as _e:  # nosec B110  # noqa: BLE001 — 无可观测通道
                        log_swallowed(__name__, _e, context='ExceptionHook._handler:Exc')
            if reentrant:
                _orig = self._bypass_hook
            else:
                with self._lock:
                    _orig = self._original_hook
            if not callable(_orig):
                _orig = getattr(sys, "__excepthook__", None)
            if callable(_orig):
                _orig(exc_type, exc_value, exc_tb)
            else:
                logger.debug("ExceptionHook 无可用原始钩子，跳过透传")
        finally:
            if not reentrant:
                self._handler_state.active = False
    def _index_record(self, record: dict) -> None:
        self._by_type[record["type"]].append(record)
        if record["frames"]:
            self._by_file[record["frames"][-1]["file"]].append(record)
    def _record(self, exc_type, exc_value, exc_tb):
        tb_frames = traceback.extract_tb(exc_tb)
        record = self._build_record(exc_type, exc_value, tb_frames)
        with self._lock:
            self._truncate_if_needed()
            self._records.append(record)
            self._index_record(record)
            self._total_recorded += 1
    def _truncate_if_needed(self) -> None:
        if len(self._records) < self._MAX_RECORDS:
            return
        self._truncated = True
        self._records = self._records[
            len(self._records) - self._MAX_RECORDS // 2:]
        self._by_type = defaultdict(list)
        self._by_file = defaultdict(list)
        for rec in self._records:
            self._index_record(rec)
    @staticmethod
    def _build_record(exc_type, exc_value, tb_frames) -> dict:
        return {
            "type": getattr(exc_type, "__name__", None) or str(exc_type),
            "message": str(exc_value),
            "timestamp": time.time(),
            "iso_time": time.strftime(FMT_DATETIME_ISO),
            "frames": [
                {
                    "file": frame.filename,
                    "line": frame.lineno,
                    "function": frame.name,
                    "code": frame.line,
                }
                for frame in tb_frames
            ],
        }
    @staticmethod
    def _top_counts(index: dict) -> dict:
        return {name: len(recs)
                for name, recs in sorted(
                    index.items(),
                    key=lambda item: (-len(item[1]), item[0]))[:10]}
    def summary(self) -> dict:
        with self._lock:
            return {
                "total": self._total_recorded,
                "retained": len(self._records),
                "dropped": self._total_recorded - len(self._records),
                "max_reached": (len(self._records) >= self._MAX_RECORDS
                                or self._truncated),
                "by_type": self._top_counts(self._by_type),
                "by_file": self._top_counts(self._by_file),
                "recent": self._records[-5:] if self._records else [],
            }
    def print_summary(self) -> None:
        s = self.summary()
        logger.info("\n%s", "=" * 60)
        logger.info("[runtime] 异常摘要: 共捕获 %d 个未处理异常", s["total"])
        if s["max_reached"]:
            logger.info(
                "[runtime] 已达保留上限 %d，旧记录已截断，当前保留 %d 条",
                self._MAX_RECORDS, s["retained"])
        logger.info("%s", "=" * 60)
        _log_group_stats("按类型统计", s["by_type"])
        _log_group_stats("按文件统计", s["by_file"])
        if s["recent"]:
            logger.info("\n最近 5 条:")
            for r in s["recent"]:
                logger.info("  [%s] %s: %.100s",
                             r["iso_time"], r["type"], r["message"])
    def status(self) -> dict:
        with self._lock:
            return {
                "installed": self._installed,
                "total": self._total_recorded,
                "retained": len(self._records),
                "max_records": self._MAX_RECORDS,
            }
    def get_records(
        self, exc_type: str | None = None, limit: int = _DEFAULT_RECORD_LIMIT
    ) -> list[dict]:
        with self._lock:
            limit = _coerce_limit(limit, self._DEFAULT_RECORD_LIMIT)
            if limit <= 0:
                return []
            records = (
                self._by_type.get(exc_type, []) if exc_type else self._records
            )
            return records[-limit:]
_coverage_hook: CoverageHook | None = None
_exception_hook: ExceptionHook | None = None
_installed = False
_installed_at = 0.0
_INSTALL_LOCK = threading.Lock()
_SESSION_HOOKS: list = []
_GUARD_STATE_DIRNAME = "runtime_guard"
def _guard_state_dir(skill_dir: str | None = None) -> str:
    skill_dir = _coerce_skill_dir(skill_dir)
    try:
        path = os.path.join(get_temp_base(skill_dir), _GUARD_STATE_DIRNAME)
        os.makedirs(path, exist_ok=True)
        return path
    except (OSError, RuntimeError, ValueError) as exc:
        log_swallowed(
            __name__, exc, context="_guard_state_dir:OSError,RuntimeError,ValueError")
        return ""
def _guard_state_path(skill_dir: str | None = None) -> str:
    base = _guard_state_dir(skill_dir)
    return os.path.join(base, "state.json") if base else ""
def _write_guard_state(payload: dict, skill_dir: str | None = None) -> bool:
    path = _guard_state_path(_coerce_skill_dir(skill_dir))
    if not path:
        return False
    try:
        write_json_artifact(path, payload, indent=2)
    except (OSError, TypeError, ValueError, RecursionError) as exc:
        log_swallowed(__name__, exc, context='_write_guard_state:write')
        return False
    return True
def _read_guard_state(skill_dir: str | None = None) -> dict:
    path = _guard_state_path(_coerce_skill_dir(skill_dir))
    if not path or not os.path.isfile(path):
        return {}
    try:
        with open(path, encoding="utf-8-sig") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError, RecursionError) as exc:
        logger.debug("守卫状态读取失败: %s", exc)
        return {}
def _persist_live_state() -> bool:
    if not _installed or _coverage_hook is None:
        return False
    skill_dir = _coverage_hook.skill_dir
    payload = {
        "installed": True,
        "live": True,
        "pid": os.getpid(),
        "started_at": _installed_at,
        "version": __version__,
        "skill_dir": skill_dir,
        "source_paths": _coverage_hook.source_paths,
        "coverage": _coverage_hook.status(),
        "exceptions": _exception_hook.status() if _exception_hook else None,
    }
    state_written = _write_guard_state(payload)
    if skill_dir:
        skill_state_written = _write_guard_state(payload, skill_dir=skill_dir)
        return state_written and skill_state_written
    return state_written
def install(source_paths: list[str] | None = None,
            skill_dir: str | None = None) -> CoverageHook | None:
    global _coverage_hook, _exception_hook, _installed, _installed_at
    source_paths = _coerce_source_paths(source_paths)
    with _INSTALL_LOCK:
        if _installed:
            return _coverage_hook
        _installed_at = time.time()
        _coverage_hook = CoverageHook(
            skill_dir=skill_dir or _skill_root_from_paths(source_paths))
        _coverage_hook.start(source_paths)
        _exception_hook = ExceptionHook()
        _exception_hook.install()
        _installed = True
        _persist_live_state()
        atexit.register(_on_exit)
    logger.info(
        "diag_runtime_forensics install 完成: coverage_lib=%s source_paths=%d",
        coverage_lib_available(), len(source_paths or []))
    return _coverage_hook
def snapshot() -> bool:
    coverage_started = bool(
        _coverage_hook and _coverage_hook.status().get("started"))
    coverage_saved = _coverage_hook.snapshot() if _coverage_hook else False
    if _exception_hook:
        _exception_hook.print_summary()
    if not _installed:
        return False
    state_saved = _persist_live_state()
    if not state_saved or (coverage_started and not coverage_saved):
        raise RuntimeError(
            "运行时守卫快照保存失败: "
            f"coverage_snapshot={coverage_saved}, guard_state={state_saved}")
    return True
_PID_PROBE_OS = os.name
_WIN_PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
_WIN_ERROR_ACCESS_DENIED = 5
_WIN_STILL_ACTIVE = 259
def _win32_pid_alive(pid: int) -> bool:
    try:
        import ctypes  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
        from ctypes import (
            wintypes,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
        )
        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)  # nosec — 审计认可：仅 Win32 只读查活，不执行外部代码
        kernel32.OpenProcess.argtypes = [
            wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        kernel32.OpenProcess.restype = wintypes.HANDLE
        kernel32.GetExitCodeProcess.argtypes = [
            wintypes.HANDLE, wintypes.LPDWORD]
        kernel32.GetExitCodeProcess.restype = wintypes.BOOL
        kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
        kernel32.CloseHandle.restype = wintypes.BOOL
        handle = kernel32.OpenProcess(
            _WIN_PROCESS_QUERY_LIMITED_INFORMATION, False, pid)
        if not handle:
            return ctypes.get_last_error() == _WIN_ERROR_ACCESS_DENIED
        try:
            code = wintypes.DWORD()
            if not kernel32.GetExitCodeProcess(handle, ctypes.byref(code)):
                return False
            return code.value == _WIN_STILL_ACTIVE
        finally:
            kernel32.CloseHandle(handle)
    except (AttributeError, OSError, ValueError) as exc:
        log_swallowed(
            __name__, exc,
            context="_win32_pid_alive:AttributeError,OSError,ValueError")
        return False
def _pid_is_alive(pid) -> bool:
    if isinstance(pid, bool) or not isinstance(pid, int) or pid <= 0:
        return False
    if pid == os.getpid():
        return True
    if _PID_PROBE_OS == "nt":
        return _win32_pid_alive(pid)
    try:
        os.kill(pid, 0)
    except ProcessLookupError:  # jwsgj:silent-ok 进程不存在即存活探测的正常否定结果
        return False
    except PermissionError:  # jwsgj:silent-ok 无权限探测说明受保护进程仍存在
        return True
    except (OSError, OverflowError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f"_pid_is_alive:{type(_swallowed_exc).__name__}")
        return False
    return True
def _same_guard_skill(left, right) -> bool:
    if not left or not right:
        return False
    try:
        left_key = os.path.normcase(os.path.realpath(os.path.abspath(
            os.fsdecode(os.fspath(left)))))
        right_key = os.path.normcase(os.path.realpath(os.path.abspath(
            os.fsdecode(os.fspath(right)))))
    except (TypeError, ValueError, OSError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return False
    return left_key == right_key
def status(skill_dir: str | None = None) -> dict:
    skill_dir = _coerce_skill_dir(skill_dir)
    live = {
        "installed": _installed,
        "live": _installed,
        "version": __version__,
        "coverage": _coverage_hook.status() if _coverage_hook else None,
        "exceptions": _exception_hook.status() if _exception_hook else None,
    }
    if _installed and (not skill_dir or _same_guard_skill(
            getattr(_coverage_hook, "skill_dir", ""), skill_dir)):
        return live
    persisted = (_read_guard_state(skill_dir) if skill_dir
                 else _read_guard_state())
    if persisted:
        persisted = dict(persisted)
        persisted["live"] = _pid_is_alive(persisted.get("pid"))
        persisted["installed"] = True
        return persisted
    if skill_dir:
        return {
            "installed": False,
            "live": False,
            "version": __version__,
            "skill_dir": skill_dir,
            "coverage": None,
            "exceptions": None,
        }
    return live
def _coverage_scope(paths) -> set[str]:
    scope: set[str] = set()
    for raw in _coerce_source_paths(paths):
        try:
            text = os.fsdecode(os.fspath(raw))
            if text:
                absolute = os.path.abspath(text)
                source_dir = _coverage_source_dir(absolute) or absolute
                scope.add(os.path.normcase(os.path.realpath(source_dir)))
        except (TypeError, ValueError, OSError) as exc:
            logger.debug("覆盖率范围路径归一失败（跳过）: %r: %s", raw, exc)
    return scope
def _coverage_scope_covers(available_paths, requested_paths) -> bool:
    requested = _coverage_scope(requested_paths)
    available = _coverage_scope(available_paths)
    if not requested or not available:
        return False
    for candidate in requested:
        for source_dir in available:
            try:
                if os.path.commonpath((source_dir, candidate)) == source_dir:
                    break
            except ValueError:
                continue
        else:
            return False
    return True
def _find_session_hook(source_paths) -> Any:
    if not _coverage_scope(source_paths):
        return None
    with _INSTALL_LOCK:
        hooks = list(_SESSION_HOOKS)
    for hook in hooks:
        status_fn = getattr(hook, "status", None)
        if callable(status_fn):
            state = status_fn()
            if not isinstance(state, Mapping) or not state.get("started"):
                continue
        if _coverage_scope_covers(
                getattr(hook, "source_paths", None), source_paths):
            return hook
    return None
def ensure_coverage_hook(
        coverage_hook, source_paths, skill_dir: str | None = None):
    if coverage_hook is not None:
        return coverage_hook
    source_paths = _coerce_source_paths(source_paths)
    try:
        coverage_hook = install(source_paths=source_paths, skill_dir=skill_dir)
        if (coverage_hook is not None and source_paths
                and not _coverage_scope_covers(
                    getattr(coverage_hook, "source_paths", None), source_paths)):
            coverage_hook = None
            reused = _find_session_hook(source_paths)
            if reused is not None:
                return reused
            fresh = CoverageHook(
                skill_dir=skill_dir or _skill_root_from_paths(source_paths))
            fresh.start(source_paths)
            status_fn = getattr(fresh, "status", None)
            if callable(status_fn) and not status_fn().get("started"):
                logger.warning(
                    "会话级覆盖率 hook 未启动；本轮按无覆盖数据降级，"
                    "不复用范围外全局 hook（全局采集保持不变）: %d 文件",
                    len(source_paths))
                return None
            with _INSTALL_LOCK:
                _SESSION_HOOKS.append(fresh)
            coverage_hook = fresh
            logger.info(
                "coverage 单例已按先前技能范围安装，本轮启用会话级"
                "独立 hook 采集（防跨技能数据串扰）: %d 文件",
                len(source_paths))
    except LAYER_DEGRADE_EXC_WITH_IMPORT as exc:
        logger.warning("coverage 安装失败（按无覆盖采集降级）: %s", exc)
    return coverage_hook
def _stop_session_hooks() -> None:
    with _INSTALL_LOCK:
        hooks = list(_SESSION_HOOKS)
        _SESSION_HOOKS.clear()
    for hook in hooks:
        stop = getattr(hook, "stop", None)
        if not callable(stop):
            continue
        try:
            stop()
        except Exception as exc:  # noqa: BLE001 — 降级：收尾路径不得阻断退出
            logger.debug("会话覆盖率钩子停止失败: %s", exc)
def _on_exit() -> None:
    _stop_session_hooks()
    try:
        snapshot()
    except Exception as exc:  # noqa: BLE001 — 退出路径不得阻断解释器收尾
        logger.debug("退出时快照失败: %s", exc)

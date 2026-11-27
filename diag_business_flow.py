from __future__ import annotations

import asyncio
import atexit as _atexit
import importlib.util
import inspect
import io
import math
import os
import re
import shutil
import sys
import threading
import time
from collections import Counter, defaultdict, deque
from collections.abc import Mapping
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
from typing import Any, ClassVar
from unittest.mock import MagicMock

from jwsgj.diag_callgraph_builder import (
    CallGraphBuilder,
    split_methods_by_definition,
)
from jwsgj.diag_callgraph_source import (
    EntryPoint,
    EntryPointDiscoverer,
    same_source_file,
)
from jwsgj.diag_types_normalize import signal_bool
from jwsgj.diag_types_vocab import (
    FIELD_TOTAL_FUNCTIONS,
    FUNCTION_ORPHAN_BLINDSPOT_TYPES,
)
from jwsgj.log_config import get_module_logger, log_swallowed, write_module_run
from jwsgj.runtime_paths import normalize_project_root
from jwsgj.runtime_scope import validate_source_paths
from jwsgj.shared_cache import validated_warmed_root

logger = get_module_logger(__name__, __file__)
DEFAULT_MAX_DEPTH = 8
DEFAULT_MAX_CHAINS = 50
_CHAIN_PREVIEW_LIMIT = DEFAULT_MAX_CHAINS
_BREAKDOWN_COUNT_BUCKETS: tuple[str, ...] = (
    "magic_methods", "instance_methods", "other")
_BREAKDOWN_KEYS: tuple[str, ...] = (
    *_BREAKDOWN_COUNT_BUCKETS, "inferred_methods", "framework_reachable")
def _empty_never_reachable_breakdown() -> dict[str, int]:
    return dict.fromkeys(_BREAKDOWN_KEYS, 0)
def _as_object_list(value: Any) -> list:
    if value is None:
        return []
    if isinstance(value, (str, bytes)):
        return []
    if isinstance(value, list):
        return value
    return list(value)
def _as_entry_list(value: Any) -> list:
    if isinstance(value, dict):
        return [value]
    return _as_object_list(value)
def _materialize_source_paths(source_paths: list[str] | None
                              ) -> list[str] | None:
    if source_paths is None or isinstance(source_paths, list):
        return source_paths
    return list(source_paths)
def _coerce_int_limit(value: Any, default: int, *,
                      allow_none: bool = False) -> int | None:
    if value is None:
        return None if allow_none else default
    if isinstance(value, bool):
        return int(value)
    try:
        coerced = int(value)
    except (TypeError, ValueError, OverflowError):
        logger.warning("业务链上限参数非整数，回退默认值 %s：%r", default, value)
        return default
    if coerced < 0:
        logger.warning("业务链上限参数不能为负数，回退默认值 %s：%r", default, value)
        return default
    return coerced
def _coerce_optional_bool(value: Any) -> bool | None:
    if value is None or isinstance(value, bool):
        return value
    return signal_bool(value)
def _sorted_values(values: Any) -> list:
    return sorted(values or ())
def _graph_functions(call_graph: Any) -> Mapping:
    try:
        functions = getattr(call_graph, "functions", None)
    except Exception as exc:  # noqa: BLE001 — 外部图载体属性可抛任意异常
        log_swallowed(
            __name__, exc, context=f"_graph_functions:{type(exc).__name__}")
        return {}
    return functions if isinstance(functions, Mapping) else {}
def build_business_call_graph(
    project_root: str,
    source_paths: list[str] | None = None,
    ctx: Any = None,
    include_tests: bool | None = None,
) -> Any:
    validate_source_paths(source_paths)
    project_root = validated_warmed_root(project_root)
    source_paths = _materialize_source_paths(source_paths)
    include_tests = _coerce_optional_bool(include_tests)
    try:
        return CallGraphBuilder(
            project_root, ctx=ctx, include_tests=include_tests).build(
                source_paths)
    except Exception as e:  # noqa: BLE001 — 构建异常降级为无图，链追踪跳过
        logger.warning("调用图构建降级（业务链追踪跳过）: %s", e)
        return None
@dataclass
class BusinessChain:
    entry: EntryPoint
    chain: list[str]
    depth: int
    reachable_files: set[str] = field(default_factory=set)
    reachable_functions: set[str] = field(default_factory=set)
    simulation_success: bool = False
    simulation_error: str | None = None
    execution_time: float = 0.0
    def to_dict(self) -> dict:
        return {
            "entry": asdict(self.entry),
            "chain": list(self.chain),
            "depth": self.depth,
            "reachable_files": _sorted_values(self.reachable_files),
            "reachable_functions": _sorted_values(self.reachable_functions),
            "simulation_success": self.simulation_success,
            "simulation_error": self.simulation_error,
            "execution_time": self.execution_time,
        }
@dataclass
class ChainSimResult:
    chain_id: str
    success: bool = False
    error: str | None = None
    reached_functions: set[str] = field(default_factory=set)
    reached_files: set[str] = field(default_factory=set)
    execution_path: list[str] = field(default_factory=list)
    execution_time: float = 0.0
    def to_dict(self) -> dict:
        return {
            "chain_id": self.chain_id,
            "success": self.success,
            "error": self.error,
            "reached_functions": _sorted_values(self.reached_functions),
            "reached_files": _sorted_values(self.reached_files),
            "execution_path": list(self.execution_path),
            "execution_time": self.execution_time,
        }
@dataclass
class BusinessFlowReport:
    entry_points: list[EntryPoint] = field(default_factory=list)
    chains: list[BusinessChain] = field(default_factory=list)
    sim_results: list[ChainSimResult] = field(default_factory=list)
    total_functions_in_project: int = 0
    functions_reachable_in_chains: int = 0
    functions_never_reachable: int = 0
    reachable_functions: set[str] = field(default_factory=set)
    never_reachable_breakdown: dict[str, int] = field(
        default_factory=_empty_never_reachable_breakdown)
    blindspots_rescued: int = 0
    blindspots_confirmed: int = 0
    framework_reachable: int = 0
    call_graph: Any = None
    reachability_measured: bool = False
    @property
    def liveness_rate(self) -> float:
        if self.total_functions_in_project == 0:
            return 0.0
        return round(min(self.functions_reachable_in_chains,
                         self.total_functions_in_project)
                     / self.total_functions_in_project, 3)
    @property
    def measured_liveness_rate(self) -> float | None:
        if not self.reachability_measured or not self.total_functions_in_project:
            return None
        return self.liveness_rate
    def summary(self) -> dict:
        return {
            "entry_points": len(self.entry_points),
            "business_chains": len(self.chains),
            "simulated_chains": _simulated_chain_count(self),
            FIELD_TOTAL_FUNCTIONS: self.total_functions_in_project,
            "reachable_functions": self.functions_reachable_in_chains,
            "never_reachable": self.functions_never_reachable,
            "liveness_rate": self.measured_liveness_rate,
            "reachability_measured": self.reachability_measured,
            "blindspots_rescued": self.blindspots_rescued,
            "blindspots_confirmed": self.blindspots_confirmed,
            "never_reachable_breakdown": dict(self.never_reachable_breakdown),
            "framework_reachable": self.framework_reachable,
        }
    def to_report_data(self) -> dict:
        return {
            "summary": self.summary(),
            "chains": [chain.to_dict() for chain in self.chains],
            "sim_results": [result.to_dict() for result in self.sim_results],
            "reachable_functions": sorted(self.reachable_functions),
        }
def _is_qualified_key(name: str | None) -> bool:
    return bool(name) and "." in name and not name.startswith(".")
def callee_adjacency(call_graph: Any) -> dict[str, list[str]]:
    adjacency: dict[str, list[str]] = {}
    for edge in getattr(call_graph, "calls", None) or []:
        caller = getattr(edge, "caller_func", "")
        callee = getattr(edge, "callee_func", "")
        if caller and callee:
            adjacency.setdefault(caller, []).append(callee)
    return adjacency
class BusinessChainTracer:
    def __init__(self, call_graph) -> None:
        self.call_graph = call_graph
        self._callee_index = callee_adjacency(call_graph)
    def trace(self, entries: list[EntryPoint],
              max_depth: int = DEFAULT_MAX_DEPTH,
              max_chains: int | None = DEFAULT_MAX_CHAINS) -> list[BusinessChain]:
        _t0 = time.monotonic()
        entries = _as_object_list(entries)
        max_depth = _coerce_int_limit(max_depth, DEFAULT_MAX_DEPTH)
        max_chains = _coerce_int_limit(
            max_chains, DEFAULT_MAX_CHAINS, allow_none=True)
        chains = []
        attempted = 0
        for entry in entries:
            if max_chains is not None and len(chains) >= max_chains:
                break
            if not entry.callable_name:
                continue
            attempted += 1
            chain = self._trace_one(entry, max_depth)
            if chain:
                chains.append(chain)
        write_module_run(
            "diag_business_flow", "BusinessChainTracer.trace",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            entries=len(entries), attempted=attempted, chains=len(chains))
        return chains
    @staticmethod
    def _resolve_start_funcs(start_func: str | None, call_graph,
                             entry_filepath: str = "") -> list[str]:
        if not start_func:
            return []
        if call_graph is None:
            return [start_func]
        functions = getattr(call_graph, "functions", {}) or {}
        if not _is_qualified_key(start_func):
            return [start_func]
        start_fnode = functions.get(start_func)
        if start_fnode is not None:
            return [start_func]
        dot_func = "." + _short_name(start_func)
        if dot_func in functions:
            dot_filepath = getattr(functions[dot_func], "filepath", "")
            if (not entry_filepath
                    or same_source_file(dot_filepath, entry_filepath,
                                         call_graph)):
                return [dot_func]
        return _class_entry_seeds(start_func, functions, entry_filepath,
                                  call_graph)
    def _trace_one(self, entry: EntryPoint, max_depth: int) -> BusinessChain | None:
        seeds = self._resolve_start_funcs(entry.callable_name, self.call_graph,
                                         entry.filepath)
        reachable_funcs: set[str] = set()
        reachable_files: set[str] = set()
        chain_depth = 0
        for seed in seeds:
            funcs, files, depth = self._bfs_reachable(seed, max_depth)
            reachable_funcs |= funcs
            reachable_files |= files
            chain_depth = max(chain_depth, depth)
        if not reachable_funcs:
            return None
        return BusinessChain(
            entry=entry,
            chain=sorted(reachable_funcs)[:_CHAIN_PREVIEW_LIMIT],
            depth=chain_depth,
            reachable_files=reachable_files,
            reachable_functions=reachable_funcs,
        )
    def _bfs_reachable(self, start_func: str | None,
                       max_depth: int) -> tuple[set[str], set[str], int]:
        visited: set[str] = set()
        queue = deque([(start_func, 0)])
        reachable_funcs: set[str] = set()
        reachable_files: set[str] = set()
        deepest_level = 0
        while queue:
            func, depth = queue.popleft()
            if func in visited or depth >= max_depth:
                continue
            visited.add(func)
            deepest_level = max(deepest_level, depth + 1)
            self._record_reach(func, reachable_funcs, reachable_files)
            for callee in set(self._callee_index.get(func, [])):
                if callee not in visited:
                    queue.append((callee, depth + 1))
        return reachable_funcs, reachable_files, deepest_level
    def _record_reach(self, func: str, reachable_funcs: set[str],
                      reachable_files: set[str]) -> None:
        fnode = None if self.call_graph is None else _graph_functions(
            self.call_graph).get(func)
        if fnode is None:
            return
        reachable_funcs.add(func)
        if fnode.filepath:
            reachable_files.add(fnode.filepath)
def _trace_chains_phase(call_graph: Any, entries: list[EntryPoint],
                       report: BusinessFlowReport,
                       max_depth: int,
                       max_chains: int | None) -> set[str]:
    tracer = BusinessChainTracer(call_graph)
    traced_chains = tracer.trace(entries, max_depth, max_chains)
    report.chains = (traced_chains if max_chains is None
                     else traced_chains[:max(0, max_chains)])
    active = _active_chain_count(report.chains)
    logger.info(
        "        业务链: %s/%s 条, 活跃=%s, 最大深度=%s",
        len(report.chains), len(traced_chains), active,
        max(c.depth for c in traced_chains) if traced_chains else 0)
    all_reachable_funcs: set[str] = set()
    all_reachable_files: set[str] = set()
    for c in traced_chains:
        all_reachable_funcs.update(c.reachable_functions)
        all_reachable_files.update(c.reachable_files)
    report.total_functions_in_project = len(_graph_functions(call_graph))
    logger.info(
        "        可达函数: %s, 可达文件: %s",
        len(all_reachable_funcs), len(all_reachable_files))
    return all_reachable_funcs
def _collect_class_methods(call_graph: Any) -> dict[str, list[str]]:
    class_methods: dict[str, list[str]] = defaultdict(list)
    for fname, fnode in _graph_functions(call_graph).items():
        class_name = getattr(fnode, "class_name", None)
        if not (getattr(fnode, "is_method", False) and class_name):
            continue
        filepath = getattr(fnode, "filepath", "")
        class_methods[f"{filepath}::{class_name}"].append(fname)
    return class_methods
def _short_name(func_name: str) -> str:
    return func_name.rsplit(".", 1)[-1]
def _is_dunder(func_name: str) -> bool:
    short = _short_name(func_name)
    return short.startswith("__") and short.endswith("__")
def _is_private(func_name: str) -> bool:
    return _short_name(func_name).startswith("_")
def _active_chain_count(chains: list[BusinessChain]) -> int:
    return sum(1 for chain in chains if chain.depth > 1)
def _class_entry_seeds(start_class: str, functions: dict,
                       entry_filepath: str, call_graph: Any) -> list[str]:
    prefix = start_class + "."
    members = sorted(
        key for key, fnode in functions.items()
        if key.startswith(prefix)
        and "." not in key[len(prefix):]
        and same_source_file(getattr(fnode, "filepath", ""), entry_filepath,
                              call_graph))
    init_key = prefix + "__init__"
    if init_key in members:
        return [init_key]
    return [key for key in members if not _is_private(key)]
def _any_reachable(names: list[str], reachable: set[str]) -> bool:
    return any(name in reachable for name in names)
def _unreached_public_methods(names: list[str], reachable: set[str]) -> set[str]:
    return {name for name in names
            if name not in reachable and not _is_private(name)}
def _infer_reachable_from_classes(
        class_methods: dict[str, list[str]],
        all_reachable_funcs: set[str],
        call_graph: Any | None = None) -> set[str]:
    inferred_reachable: set[str] = set()
    span_cache: dict[str, list[tuple[str, int, int]] | None] = {}
    for key, methods in class_methods.items():
        if not _any_reachable(methods, all_reachable_funcs):
            continue
        groups = (split_methods_by_definition(
            key, methods, call_graph, span_cache)
            if call_graph is not None else None)
        for group in groups or [methods]:
            if not _any_reachable(group, all_reachable_funcs):
                continue
            inferred_reachable.update(
                _unreached_public_methods(group, all_reachable_funcs))
    return inferred_reachable
def _split_framework_reachable(call_graph: Any,
                               never_reached: set[str]) -> set[str]:
    is_exempt = call_graph.analyses.exemption.is_exempt_from_orphan
    framework_reachable: set[str] = set()
    functions = _graph_functions(call_graph)
    for fname in list(never_reached):
        fnode = functions.get(fname)
        if fnode and is_exempt(fnode):
            framework_reachable.add(fname)
            never_reached.discard(fname)
    return framework_reachable
def _bucket_unreachable(call_graph: Any, never_reached: set[str],
                        report: BusinessFlowReport) -> None:
    functions = _graph_functions(call_graph)
    for fname in never_reached:
        if _is_dunder(fname):
            report.never_reachable_breakdown["magic_methods"] += 1
            continue
        fnode = functions.get(fname)
        is_instance_method = (getattr(fnode, "is_method", False)
                              and getattr(fnode, "class_name", None))
        key = "instance_methods" if is_instance_method else "other"
        report.never_reachable_breakdown[key] += 1
def _classify_unreachable_phase(call_graph: Any, all_reachable_funcs: set[str],
                               inferred_reachable: set[str],
                               report: BusinessFlowReport) -> None:
    never_reached = set(_graph_functions(call_graph)) - all_reachable_funcs
    framework_reachable = _split_framework_reachable(call_graph, never_reached)
    all_reachable_funcs.update(framework_reachable)
    report.framework_reachable = len(framework_reachable)
    report.functions_reachable_in_chains = len(all_reachable_funcs)
    report.functions_never_reachable = (
        report.total_functions_in_project - report.functions_reachable_in_chains
    )
    for _bucket in _BREAKDOWN_COUNT_BUCKETS:
        report.never_reachable_breakdown[_bucket] = 0
    _bucket_unreachable(call_graph, never_reached, report)
    report.never_reachable_breakdown["inferred_methods"] = len(inferred_reachable)
    report.never_reachable_breakdown["framework_reachable"] = len(framework_reachable)
def trace_and_classify(
    call_graph: Any,
    entries: list[EntryPoint],
    report: BusinessFlowReport,
    max_depth: int,
    max_chains: int,
) -> set[str]:
    if not _graph_functions(call_graph):
        raise ValueError("trace_and_classify 需要已构建且含函数的调用图")
    try:
        calls = getattr(call_graph, "calls", None)
    except Exception as exc:  # noqa: BLE001 — 外部图载体属性可抛任意异常
        log_swallowed(
            __name__, exc, context=f"trace_and_classify:{type(exc).__name__}")
        calls = None
    if calls is None:
        raise ValueError(
            "trace_and_classify 需要含 calls 边的调用图；"
            "无调用边的图不能用于可达性判定")
    max_depth = _coerce_int_limit(max_depth, DEFAULT_MAX_DEPTH)
    max_chains = _coerce_int_limit(max_chains, DEFAULT_MAX_CHAINS)
    _t0 = time.monotonic()
    all_reachable_funcs = _trace_chains_phase(
        call_graph, entries, report, max_depth, max_chains)
    inferred_reachable = _infer_reachable_from_classes(
        _collect_class_methods(call_graph), all_reachable_funcs, call_graph)
    all_reachable_funcs.update(inferred_reachable)
    _classify_unreachable_phase(call_graph, all_reachable_funcs,
                               inferred_reachable, report)
    report.reachable_functions = set(all_reachable_funcs)
    report.reachability_measured = True
    write_module_run(
        "diag_business_flow", "trace_and_classify",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        chains=len(report.chains),
        reachable=len(all_reachable_funcs),
        total=report.total_functions_in_project)
    return all_reachable_funcs
def _reject_as_fd(self) -> int:
    raise TypeError("模拟参数不能用作文件描述符")
def _reject_as_path(self) -> str:
    raise TypeError("模拟参数不能用作文件路径")
def _harden_arg_mock(mock: MagicMock) -> MagicMock:
    cls = type(mock)
    if cls.__dict__.get("_jws_arg_hardened"):
        return mock
    cls.__index__ = _reject_as_fd
    cls.__fspath__ = _reject_as_path
    cls._jws_arg_hardened = True
    return mock
class _SafeArgMock(MagicMock):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        _harden_arg_mock(self)
    def _get_child_mock(self, /, **kwargs) -> MagicMock:  # jwsgj:suppress orphan — unittest.mock 内部钩子：mock 生成子 mock 时由框架 _make_child 链路调用
        return _harden_arg_mock(super()._get_child_mock(**kwargs))
_ANN_DEFAULTS: dict = {
    str: lambda: "test",
    int: lambda: 0,
    float: lambda: 0.0,
    bool: lambda: False,
    list: list,
    dict: dict,
    set: set,
    tuple: tuple,
}
_ANN_ALIASES = {t.__name__: t for t in _ANN_DEFAULTS}
def _failure_reason(e: BaseException) -> str:
    if isinstance(e, SystemExit):
        return f"链加载失败: SystemExit: {e}，回退到静态追踪"
    return f"链加载失败: {type(e).__name__}: {str(e)[:80]}，回退到静态追踪"
def _strip_file_stem(entry_func_name: str, filepath: str) -> str:
    first, sep, rest = entry_func_name.partition(".")
    if sep and first == os.path.splitext(os.path.basename(filepath))[0]:
        return rest
    return entry_func_name
@contextmanager
def _prepended_sys_path(project_root: str):
    original_path = list(sys.path)
    sys.path[:] = [project_root, *(p for p in sys.path if p != project_root)]
    try:
        yield
    finally:
        sys.path[:] = original_path
_STD_FD_NAMES: tuple[tuple[int, str], ...] = ((0, "stdin"), (1, "stdout"), (2, "stderr"))
def _fd_is_open(fd: int) -> bool:
    try:
        os.fstat(fd)
    except OSError as exc:
        log_swallowed(__name__, exc, context=f"_fd_is_open:{type(exc).__name__}")
        return False
    return True
@contextmanager
def _simulation_import_paths(project_root: str):
    with _prepended_sys_path(project_root):
        if os.path.isfile(os.path.join(project_root, "__init__.py")):
            with _prepended_sys_path(os.path.dirname(project_root)):
                yield
        else:
            yield
@contextmanager
def _entry_script_import_path(project_root: str, entry_filepath: str):
    filepath = os.path.abspath(os.path.join(project_root, entry_filepath))
    with _prepended_sys_path(os.path.dirname(filepath)):
        yield
def _dup_std_fds() -> dict[int, int]:
    saved: dict[int, int] = {}
    for fd, _name in _STD_FD_NAMES:
        try:
            saved[fd] = os.dup(fd)
        except OSError as _e:
            logger.debug("std fd %d 备份失败，不隔离该 fd: %s", fd, _e)
    return saved
def _close_saved_fds(saved: dict[int, int]) -> None:
    for _backup in saved.values():
        try:
            os.close(_backup)
        except OSError as exc:
            log_swallowed(
                __name__, exc, context=f"_close_saved_fds:{type(exc).__name__}")
def _redirect_std_fds(saved: dict[int, int]) -> list[int] | None:
    try:
        sink = os.open(os.devnull, os.O_RDWR)
    except OSError as _e:
        _close_saved_fds(saved)
        logger.debug("devnull 不可用，跳过 std fd 隔离: %s", _e)
        return None
    redirected: list[int] = []
    try:
        for _fd in saved:
            try:
                os.dup2(sink, _fd)
            except OSError as _e:
                logger.debug("std fd %d 隔离失败，跳过该 fd: %s", _fd, _e)
                continue
            redirected.append(_fd)
    finally:
        try:
            os.close(sink)
        except OSError as exc:
            log_swallowed(
                __name__, exc, context=f"_redirect_std_fds:{type(exc).__name__}")
    return redirected
def _restore_std_fd(fd: int, backup: int) -> None:
    try:
        os.dup2(backup, fd)
    except OSError as _e:
        logger.warning("std fd %d 还原失败（备份 fd %d 保留未关）: %s",
                       fd, backup, _e)
        return
    try:
        os.close(backup)
    except OSError as exc:
        log_swallowed(
            __name__, exc, context=f"_restore_std_fd:{type(exc).__name__}")
def _restore_std_fds(saved: dict[int, int], redirected: list[int]) -> None:
    for _fd in redirected:
        _restore_std_fd(_fd, saved[_fd])
    for _fd, _backup in saved.items():
        if _fd not in redirected:
            try:
                os.close(_backup)
            except OSError as exc:
                log_swallowed(
                    __name__, exc, context=f"_restore_std_fds:{type(exc).__name__}")
    for _fd, _name in _STD_FD_NAMES:
        if _fd in redirected and not _fd_is_open(_fd):
            logger.warning("std fd %d 还原后仍不可用，宿主输出可能受影响", _fd)
@contextmanager
def _isolated_std_fds():
    saved = _dup_std_fds()
    if not saved:
        yield
        return
    redirected = _redirect_std_fds(saved)
    if redirected is None:
        yield
        return
    try:
        yield
    finally:
        _restore_std_fds(saved, redirected)
@contextmanager
def _isolated_report_root():
    """把 HTML 报告落点隔离到沙箱，避免链模拟副作用污染真实交付目录。

    根因：``ChainSimulator`` 为验证业务链活性会**真实调用**入口函数
    （``run_feedback_fix`` / ``run_deadcode_cleanup`` 等），而这些函数按
    ``runtime_paths.get_html_report_base()`` 落盘阶段报告。该方法返回
    **工作空间级** ``htm/``（与治理目标无关），且链模拟把 ``str`` 形参
    填成字面量 ``"test"``，于是模拟产出的报告会写进真实交付目录
    （历史上已污染 ``htm/诊断F*.html`` / ``htm/审核治疗*.html``）。

    ``_safe_env`` 原先只屏蔽流/atexit/模块与 fd，未隔离落点；
    重入守卫也拦不住——因为外泄入口是治疗/复盘阶段函数，不是管线入口。

    修法：模拟期间把 ``JWSGJ_HTML_OUT`` 指向工作空间内的沙箱目录。
    该环境变量参与 ``runtime_paths`` 的路径缓存键，切换即失效，
    无需手工清缓存；退出时恢复原值并清理沙箱。
    隔离失败时降级（不隔离）并保留可见标记，不阻断模拟。
    """
    from jwsgj import runtime_paths as _rp

    previous = os.environ.get(_rp.HTML_DIR_ENV_VAR)
    sandbox = ""
    try:
        workspace = _rp.resolve_workspace_root()
    except Exception as exc:  # noqa: BLE001 - 无工作空间时降级不隔离
        log_swallowed(__name__, exc,
                      context=("_isolated_report_root:"
                               f"{type(exc).__name__}"))
        workspace = ""
    if workspace:
        # Temp 下不能是 htm 叶子（会被判为旧布局），故用带前缀的叶子名。
        for candidate in (
                os.path.join(workspace, "Temp",
                             f"chain_sim_htm_{os.getpid()}"),
                os.path.join(workspace,
                             f"_chain_sim_htm_{os.getpid()}")):
            try:
                _rp._resolve_html_override(candidate)
            except Exception as exc:  # noqa: BLE001 - 逐个候选降级尝试
                log_swallowed(__name__, exc,
                              context=("_isolated_report_root:"
                                       f"{type(exc).__name__}"))
                continue
            os.environ[_rp.HTML_DIR_ENV_VAR] = candidate
            sandbox = candidate
            break
        if not sandbox:
            logger.warning(
                "[ChainSim] 报告落点隔离不可用，模拟期间可能污染真实 htm/")
    try:
        yield
    finally:
        if sandbox:
            if previous is None:
                os.environ.pop(_rp.HTML_DIR_ENV_VAR, None)
            else:
                os.environ[_rp.HTML_DIR_ENV_VAR] = previous
            shutil.rmtree(sandbox, ignore_errors=True)
@contextmanager
def _safe_env():
    with (_suppressed_streams(), _suppressed_atexit(),
          _isolated_modules(), _isolated_std_fds(),
          _isolated_report_root()):
        yield
@contextmanager
def _suppressed_streams():
    old_stdout, old_stderr, old_stdin = sys.stdout, sys.stderr, sys.stdin
    sys.stdout = io.StringIO()
    sys.stderr = io.StringIO()
    sys.stdin = io.StringIO()
    try:
        yield
    finally:
        sys.stdout, sys.stderr, sys.stdin = old_stdout, old_stderr, old_stdin
@contextmanager
def _suppressed_atexit():
    real_register = _atexit.register
    def _register_without_scheduling(func, *_args, **_kwargs):
        return func
    _atexit.register = _register_without_scheduling
    try:
        yield
    finally:
        _atexit.register = real_register
@contextmanager
def _isolated_modules():
    saved_modules = dict(sys.modules)
    try:
        yield
    finally:
        for key in set(sys.modules) - set(saved_modules):
            sys.modules.pop(key, None)
        for key, module in saved_modules.items():
            if sys.modules.get(key) is not module:
                sys.modules[key] = module
class ChainSimulator:
    def __init__(self, project_root: str, timeout: float = 3.0) -> None:
        try:
            timeout = float(timeout)
        except (TypeError, ValueError) as exc:
            raise ValueError("ChainSimulator.timeout 必须为正数秒") from exc
        if not math.isfinite(timeout) or timeout <= 0:
            raise ValueError("ChainSimulator.timeout 必须为正数秒")
        self.project_root = normalize_project_root(project_root)
        self.timeout = timeout
    def simulate_chains(self, chains: list[BusinessChain]) -> list[ChainSimResult]:
        _t0 = time.monotonic()
        chains = _as_object_list(chains)
        with _simulation_import_paths(self.project_root):
            results = [self._simulate_and_record(chain, f"chain_{i}")
                       for i, chain in enumerate(chains)]
            write_module_run(
                "diag_business_flow", "ChainSimulator.simulate_chains",
                duration_ms=(time.monotonic() - _t0) * 1000.0,
                chains=len(chains),
                simulated=sum(1 for c in chains if c.simulation_success))
        return results
    def _simulate_and_record(self, chain: BusinessChain,
                             chain_id: str) -> ChainSimResult:
        try:
            result = self._simulate_chain(chain, chain_id)
        except Exception as exc:  # noqa: BLE001 — 单条载体非法不得击穿整批模拟
            log_swallowed(
                __name__, exc, context=f"_simulate_and_record:{type(exc).__name__}")
            result = ChainSimResult(
                chain_id=chain_id,
                error=f"链载体不可模拟: {type(exc).__name__}: {str(exc)[:80]}")
        if isinstance(chain, BusinessChain):
            chain.simulation_success = result.success
            chain.simulation_error = result.error
            chain.execution_time = result.execution_time
        return result
    @staticmethod
    def _strip_attr_path(entry_func_name: str, module_path: str | None,
                         filepath: str) -> str:
        mod_path = module_path if isinstance(module_path, str) else ""
        if mod_path and entry_func_name.startswith(mod_path + "."):
            return entry_func_name[len(mod_path) + 1:]
        if not mod_path and entry_func_name.startswith("."):
            return entry_func_name[1:]
        return _strip_file_stem(entry_func_name, filepath)
    def _simulate_chain(self, chain: BusinessChain, chain_id: str) -> ChainSimResult:
        result = ChainSimResult(chain_id=chain_id)
        if not chain.entry.callable_name:
            result.error = "无可调用的入口函数"
            return result
        try:
            with _safe_env(), _entry_script_import_path(
                    self.project_root, chain.entry.filepath):
                func, reason = self._resolve_entry_callable(chain, chain_id)
                if func is None:
                    return self._static_trace_result(chain, result, reason or "")
                fallback_reason = self._execute_entry_function(func, result)
                if fallback_reason is not None:
                    return self._static_trace_result(chain, result, fallback_reason)
                self._mark_reachable(result, chain)
        except (SystemExit, Exception) as e:  # noqa: BLE001 —— 模拟器全兜（SystemExit 非 Exception 子类，同列一兜），回退静态追踪
            logger.debug(
                "suppressed 链加载异常，回退静态追踪: %s: %s",
                type(e).__name__, e)
            return self._static_trace_result(chain, result, _failure_reason(e))
        return result
    def _resolve_entry_callable(
        self, chain: BusinessChain, chain_id: str
    ) -> tuple[Any | None, str | None]:
        entry_func_name = chain.entry.callable_name
        filepath = os.path.join(self.project_root, chain.entry.filepath)
        module = self._load_entry_module(
            filepath, chain_id, chain.entry.module_path)
        if module is None:
            return None, "模块加载失败（库项目预期行为），回退到静态追踪"
        attr_path = self._strip_attr_path(
            entry_func_name, chain.entry.module_path, filepath)
        func = self._resolve_attr(module, attr_path)
        if not callable(func) and "." in attr_path:
            root_attr, _sep, local_attr = attr_path.partition(".")
            if getattr(module, root_attr, None) is None:
                local_func = self._resolve_attr(module, local_attr)
                if callable(local_func):
                    func = local_func
        entry_name = chain.entry.name
        if (not callable(func) and chain.entry.entry_type == "public_api"
                and isinstance(entry_name, str)
                and entry_name.startswith("api:")):
            exported_attr = entry_name[len("api:"):]
            if exported_attr and exported_attr != attr_path:
                exported_func = self._resolve_attr(module, exported_attr)
                if callable(exported_func):
                    func = exported_func
        if not callable(func) and "." in attr_path:
            for candidate in vars(module).values():
                if not callable(candidate):
                    continue
                candidate_module = getattr(candidate, "__module__", "")
                candidate_qualname = getattr(candidate, "__qualname__", "")
                if (candidate_module and candidate_qualname
                        and f"{candidate_module}.{candidate_qualname}" == attr_path):
                    func = candidate
                    break
        if func is None or not callable(func):
            return None, f"入口函数不可调用: {entry_func_name}，回退到静态追踪"
        return func, None
    def _package_context_for(
        self, filepath: str, module_path: str | None
    ) -> tuple[str, str]:
        root = os.path.abspath(self.project_root)
        directory = os.path.dirname(os.path.abspath(filepath))
        try:
            rel_dir = os.path.relpath(directory, root)
        except ValueError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context=f'_package_context_for:{type(_swallowed_exc).__name__}')
            return "", root
        if rel_dir == ".." or rel_dir.startswith(".." + os.sep):
            return "", root
        package_parts: list[str] = []
        import_root = root
        current = directory
        root_key = os.path.normcase(os.path.normpath(root))
        while os.path.isfile(os.path.join(current, "__init__.py")):
            part = os.path.basename(current)
            if not part.isidentifier():
                return "", root
            package_parts.append(part)
            import_root = os.path.dirname(current)
            if os.path.normcase(os.path.normpath(current)) == root_key:
                break
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent
        if not package_parts:
            module_parts = (
                module_path.split(".") if isinstance(module_path, str) else [])
            namespace_parts = module_parts[:-1]
            expected_dir = os.path.join(root, *namespace_parts)
            if (namespace_parts
                    and all(part.isidentifier() for part in namespace_parts)
                    and os.path.normcase(os.path.normpath(expected_dir))
                    == os.path.normcase(os.path.normpath(directory))):
                return ".".join(namespace_parts), root
            return "", root
        return ".".join(reversed(package_parts)), import_root
    def _load_entry_module(
        self, filepath: str, chain_id: str, module_path: str | None
    ):
        filepath = os.path.abspath(filepath)
        package, import_root = self._package_context_for(filepath, module_path)
        synthetic_name = f"__jws_biz_{chain_id}"
        module_name = f"{package}.{synthetic_name}" if package else synthetic_name
        spec = importlib.util.spec_from_file_location(module_name, filepath)
        if spec is None or spec.loader is None:
            return None
        module = importlib.util.module_from_spec(spec)
        module.__package__ = package
        module_dir = os.path.dirname(filepath)
        with _prepended_sys_path(import_root):
            if not package and module_dir != import_root:
                sys.path.insert(0, module_dir)
            sys.modules[spec.name] = module
            spec.loader.exec_module(module)
        return module
    @staticmethod
    def _resolve_attr(obj: Any, attr_path: str) -> Any:
        for part in attr_path.split("."):
            obj = getattr(obj, part, None)
            if obj is None:
                return None
        return obj
    def _execute_entry_function(self, func, result: ChainSimResult) -> str | None:
        start = time.perf_counter()
        try:
            sig = inspect.signature(func)
            args, kwargs = self._lightweight_args(sig)
            timed_out = self._call_with_timeout(func, args, kwargs)
            if timed_out:
                return f"模拟执行超时(>{self.timeout:.1f}s)，回退到静态追踪"
            result.success = True
            return None
        except Exception as e:  # noqa: BLE001 —— 模拟器全兜，回退静态追踪
            logger.debug("suppressed 运行时异常，回退静态追踪: %s: %s", type(e).__name__, e)
            return f"运行时异常: {type(e).__name__}: {str(e)[:80]}，回退到静态追踪"
        finally:
            result.execution_time = round(time.perf_counter() - start, 3)
    @staticmethod
    def _mark_reachable(result: ChainSimResult, chain: BusinessChain) -> None:
        for fname in chain.reachable_functions:
            result.reached_functions.add(fname)
        for fpath in chain.reachable_files:
            result.reached_files.add(fpath)
        result.execution_path = sorted(chain.reachable_functions)[:20]
    def _call_with_timeout(self, func, args, kwargs) -> bool:
        outcome: dict[str, Any] = {"error": None}
        def _run():
            try:
                returned = func(*args, **kwargs)
                if inspect.isawaitable(returned):
                    async def _await_returned():
                        return await returned
                    asyncio.run(_await_returned())
            except BaseException as e:  # noqa: BLE001 - 线程边界传递后由上层分诊
                logger.debug(
                    "模拟入口异常，回退静态追踪: %s: %s",
                    type(e).__name__, e)
                outcome["error"] = e
        worker = threading.Thread(target=_run, daemon=True, name="chain-sim")
        worker.start()
        worker.join(self.timeout)
        if worker.is_alive():
            return True
        if outcome["error"] is not None:
            err = outcome["error"]
            if isinstance(err, SystemExit) and err.code in (None, 0):
                return False
            if not isinstance(err, Exception):
                raise RuntimeError(
                    f"模拟执行被 {type(err).__name__} 中断: {err}") from err
            raise err
        return False
    @staticmethod
    def _value_for(param: inspect.Parameter) -> Any:
        if param.default is not inspect.Parameter.empty:
            return param.default
        ann = param.annotation
        if isinstance(ann, str):
            ann = _ANN_ALIASES.get(ann.strip())
        if ann is not None and ann is not inspect.Parameter.empty:
            factory = _ANN_DEFAULTS.get(ann)
            if factory is not None:
                return factory()
        return _SafeArgMock()
    def _lightweight_args(self, sig: inspect.Signature) -> tuple[list[Any], dict[str, Any]]:
        args: list[Any] = []
        kwargs: dict[str, Any] = {}
        for param in sig.parameters.values():
            kind = param.kind
            if kind in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD):
                continue
            if kind is inspect.Parameter.KEYWORD_ONLY:
                kwargs[param.name] = self._value_for(param)
            else:
                args.append(self._value_for(param))
        return args, kwargs
    def _static_trace_result(self, chain: BusinessChain, result: ChainSimResult,
                              reason: str) -> ChainSimResult:
        result.success = False
        result.error = reason
        self._mark_reachable(result, chain)
        return result
def _fnode_doc(fnode: Any) -> str:
    doc = getattr(fnode, "docstring", None) or getattr(fnode, "doc", None) or ""
    return doc if isinstance(doc, str) else str(doc)
def _fnode_params(fnode: Any) -> list:
    raw = getattr(fnode, "params", None) or getattr(fnode, "arg_names", None) or []
    return list(raw) if isinstance(raw, (list, tuple)) else []
def _non_self_params(params: list) -> list:
    return [name for name in params if name not in ("self", "cls")]
@dataclass(frozen=True)
class _ReachEvidence:
    functions: frozenset[str]
    files: frozenset[str]
    simple_names: frozenset[str]
    @classmethod
    def from_sources(cls, business_chains: list[BusinessChain],
                     sim_results: list[ChainSimResult],
                     extra_reachable: set[str] | None) -> _ReachEvidence:
        functions: set[str] = set()
        files: set[str] = set()
        for chain in _as_object_list(business_chains):
            functions.update(getattr(chain, "reachable_functions", None) or ())
            files.update(getattr(chain, "reachable_files", None) or ())
        for result in _as_object_list(sim_results):
            functions.update(getattr(result, "reached_functions", None) or ())
            files.update(getattr(result, "reached_files", None) or ())
        if extra_reachable:
            functions.update(extra_reachable)
        simple_names = {_short_name(r) for r in functions if r}
        return cls(frozenset(functions), frozenset(files),
                   frozenset(simple_names))
    def hit(self, name: str, filepath: str, *,
            allow_file: bool = False) -> bool:
        if name and name in self.functions:
            if (filepath and _short_name(name) == name and self.files
                    and not any(same_source_file(filepath, reached, None)
                                for reached in self.files)):
                return False
            return True
        name_simple = _short_name(name)
        if (name and name_simple == name and not filepath
                and name_simple in self.simple_names):
            return True
        return bool(allow_file and filepath and filepath in self.files)
_MODULE_LEVEL_BLINDSPOT_TYPES = frozenset({
    "orphan_module", "dead_module", "standalone_unimported",
})
class LivenessValidator:
    _RESCUE_BLINDSPOT_TYPES = (
        FUNCTION_ORPHAN_BLINDSPOT_TYPES | _MODULE_LEVEL_BLINDSPOT_TYPES)
    def _rescue_if_reachable(self, entry: dict,
                             evidence: _ReachEvidence) -> dict | None:
        bt = str(entry.get("blindspot_type") or "")
        name = str(entry.get("name") or "")
        filepath = str(entry.get("filepath") or "")
        module_level = bt in _MODULE_LEVEL_BLINDSPOT_TYPES
        if not (evidence.hit(name, filepath, allow_file=module_level)
                and bt in self._RESCUE_BLINDSPOT_TYPES):
            return None
        rescued = dict(entry)
        rescued["liveness"] = "reachable"
        rescued["liveness_source"] = "business_chain"
        return rescued
    def validate(
        self,
        blindspot_entries: list[dict],
        business_chains: list[BusinessChain],
        sim_results: list[ChainSimResult],
        extra_reachable: set[str] | None = None,
    ) -> tuple[list[dict], list[dict]]:
        _t0 = time.monotonic()
        evidence = _ReachEvidence.from_sources(
            business_chains, sim_results, extra_reachable)
        entries = [entry for entry in _as_entry_list(blindspot_entries)
                   if isinstance(entry, dict)]
        rescued = []
        confirmed = []
        for entry in entries:
            hit = self._rescue_if_reachable(entry, evidence)
            if hit is not None:
                rescued.append(hit)
            else:
                confirmed.append(entry)
        write_module_run(
            "diag_business_flow", "LivenessValidator.validate",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            blindspots=len(entries),
            rescued=len(rescued), confirmed=len(confirmed))
        return rescued, confirmed
def _discover_entries_step(project_root: str, ctx: Any,
                           source_paths: list[str] | None,
                           include_tests: bool | None = None,
                           ) -> list[EntryPoint] | None:
    logger.info("[BizChain] 1/4 发现业务入口点...")
    entries: list[EntryPoint] = []
    try:
        discoverer = EntryPointDiscoverer(
            project_root, ctx=ctx, include_tests=include_tests)
        entries = discoverer.discover(source_paths)
    except Exception as e:  # noqa: BLE001 — 发现失败须与真实空入口集区分，禁止继续生成不可达结论
        logger.warning("        入口点发现失败，链追踪与盲区活性验证跳过: %s", e)
        return None
    by_type = Counter(getattr(entry, "entry_type", "") for entry in entries)
    logger.info(
        "        入口点: %s 个 (CLI=%s, main=%s, api=%s, decorator=%s)",
        len(entries), by_type["cli_command"], by_type["main_block"],
        by_type["public_api"], by_type["decorator_entry"])
    return entries
def _trace_chains_step(call_graph: Any, entries: list[EntryPoint],
                       report: BusinessFlowReport,
                       max_depth: int, max_chains: int) -> set[str] | None:
    logger.info("[BizChain] 2/4 追踪业务调用链...")
    functions = _graph_functions(call_graph)
    if not functions:
        report.total_functions_in_project = 0
        logger.info("        调用图为空，无可达证据；跳过链追踪")
        return None
    try:
        return trace_and_classify(
            call_graph, entries, report, max_depth, max_chains)
    except Exception as e:  # noqa: BLE001 — Step 级降级：追踪意外异常不炸穿编排，返回 None 标记可达证据缺失
        logger.warning(
            "        链追踪失败，可达性未度量（不产出 0%% 存活率结论）: %s", e)
        _reset_reachability_evidence(report)
        return None
def _simulate_chains_step(project_root: str,
                          chains: list[BusinessChain]) -> list[ChainSimResult]:
    logger.info("[BizChain] 3/4 模拟执行业务链...")
    try:
        sim_results = ChainSimulator(project_root).simulate_chains(chains)
        success = sum(1 for r in sim_results if r.success)
        logger.info("        模拟: %s/%s 条链成功执行", success, len(sim_results))
        return sim_results
    except Exception as e:  # noqa: BLE001 — Step 级降级：模拟意外异常跳过，与 Step 4 活性验证同口径
        logger.info("        模拟跳过: %s", e)
        return []
def _validate_blindspots_step(
    blindspot_entries: list[dict], chains: list[BusinessChain],
    sim_results: list[ChainSimResult],
    extra_reachable: set[str]) -> tuple[int, int]:
    logger.info("[BizChain] 4/4 交叉验证盲区活性...")
    try:
        validator = LivenessValidator()
        rescued, confirmed = validator.validate(
            blindspot_entries, chains, sim_results,
            extra_reachable=extra_reachable,
        )
        r_count, c_count = len(rescued), len(confirmed)
        logger.info("        救回: %s 个盲区（业务链中可达）", r_count)
        logger.info("        确认: %s 个盲区（确实不可达）", c_count)
        return r_count, c_count
    except Exception as e:  # noqa: BLE001 — Step 级降级：验证意外异常不炸穿编排，盲区计数保持默认
        logger.warning("        盲区活性验证失败，盲区计数保持默认: %s", e)
        return 0, 0
def _simulated_chain_count(report: BusinessFlowReport) -> int:
    return sum(1 for chain in getattr(report, "chains", None) or ()
               if getattr(chain, "simulation_success", False))
def _reset_reachability_evidence(report: BusinessFlowReport) -> None:
    report.total_functions_in_project = 0
    report.functions_reachable_in_chains = 0
    report.functions_never_reachable = 0
    report.reachable_functions = set()
    report.framework_reachable = 0
    report.never_reachable_breakdown = _empty_never_reachable_breakdown()
    report.reachability_measured = False
def _log_flow_summary(report: BusinessFlowReport) -> None:
    _sim_ok = _simulated_chain_count(report)
    if report.reachability_measured and report.total_functions_in_project:
        _reach_text = (f"{report.functions_reachable_in_chains}/"
                       f"{report.total_functions_in_project}"
                       f"({report.liveness_rate * 100:.0f}%)")
    else:
        _reach_text = (f"{report.functions_reachable_in_chains}/未度量"
                       "（无可达性证据）")
    logger.info(
        "[BizChain] 诊断完成: 入口=%d 链=%d(活跃%d) 模拟=%d/%d "
        "可达=%s 盲区救回=%d/确认=%d",
        len(report.entry_points), len(report.chains),
        _active_chain_count(report.chains),
        _sim_ok, len(report.chains),
        _reach_text,
        report.blindspots_rescued, report.blindspots_confirmed)
def diagnose_business_flows(
    project_root: str,
    call_graph: Any = None,
    blindspot_entries: list[dict] | None = None,
    source_paths: list[str] | None = None,
    max_depth: int = DEFAULT_MAX_DEPTH,
    max_chains: int = DEFAULT_MAX_CHAINS,
    ctx: Any = None,
    include_tests: bool | None = None,
) -> BusinessFlowReport:
    project_root = normalize_project_root(project_root)
    validate_source_paths(source_paths)
    source_paths = _materialize_source_paths(source_paths)
    max_depth = _coerce_int_limit(max_depth, DEFAULT_MAX_DEPTH)
    max_chains = _coerce_int_limit(max_chains, DEFAULT_MAX_CHAINS)
    include_tests = _coerce_optional_bool(include_tests)
    blindspot_entries = _as_entry_list(blindspot_entries)
    report = BusinessFlowReport()
    if call_graph is None:
        call_graph = build_business_call_graph(
            project_root, source_paths, ctx, include_tests=include_tests)
    report.call_graph = call_graph
    discovered_entries = _discover_entries_step(
        project_root, ctx, source_paths, include_tests)
    discovery_failed = discovered_entries is None
    report.entry_points = discovered_entries or []
    all_reachable_funcs: set[str] | None = None if discovery_failed else set()
    if call_graph is not None:
        if discovery_failed:
            report.total_functions_in_project = len(
                _graph_functions(call_graph))
        else:
            all_reachable_funcs = _trace_chains_step(
                call_graph, report.entry_points, report,
                max_depth, max_chains)
    report.sim_results = _simulate_chains_step(project_root, report.chains)
    if blindspot_entries and call_graph is not None:
        if all_reachable_funcs is None:
            logger.warning(
                "        链追踪降级，盲区活性验证跳过"
                "（无可达证据，不计入救回/确认）")
        else:
            rescued, confirmed = _validate_blindspots_step(
                blindspot_entries, report.chains, report.sim_results,
                all_reachable_funcs)
            report.blindspots_rescued = rescued
            report.blindspots_confirmed = confirmed
    elif blindspot_entries:
        logger.warning(
            "        调用图缺失，盲区活性验证跳过"
            "（无可达证据，不计入救回/确认）")
    _log_flow_summary(report)
    return report
_READY_MIN_SCORE = 75
_PARTIAL_MIN_SCORE = 40
_SPHINX_ARGS_RE = re.compile(
    r'(?m)^\s*:(?:param|parameter|arg|argument|key|keyword|type)\b')
_SPHINX_RETURNS_RE = re.compile(r'(?m)^\s*:(?:returns?|yields?|rtype)\b')
def _numeric_or(item: Any, name: str, default: float) -> float:
    try:
        return float(getattr(item, name, default))
    except (TypeError, ValueError):
        return float(default)
def _is_external_api(score: Any) -> bool:
    if not getattr(score, "is_public_api", False):
        return False
    try:
        quality = float(getattr(score, "quality_score", 0.0))
    except (TypeError, ValueError):
        return False
    return quality >= _PARTIAL_MIN_SCORE
@dataclass
class ApiSurfaceScore:
    func_name: str
    filepath: str = ""
    has_docstring: bool = False
    has_args_doc: bool = False
    has_returns_doc: bool = False
    has_type_annotations: bool = False
    params_count: int = 0
    annotated_params: int = 0
    in_all_exports: bool = False
    is_public_api: bool = False
    quality_score: float = 0.0
    readiness: str = "unknown"
class ApiSurfaceAnalyzer:
    _WEIGHTS: ClassVar[dict] = {
        "docstring": 25,
        "args_doc": 20,
        "returns_doc": 15,
        "type_annotations": 25,
        "in_all_exports": 15,
    }
    def analyze(self, call_graph, project_root: str) -> list[ApiSurfaceScore]:
        results = []
        functions = _graph_functions(call_graph)
        if not functions:
            return results
        for fqname, fnode in functions.items():
            simple_name = _short_name(fqname)
            if (not getattr(fnode, 'is_public', False)
                    and not self._is_exported(fnode, fqname, simple_name)):
                continue
            score = self._score_function(fqname, fnode, project_root)
            results.append(score)
        return results
    def _score_function(self, fqname: str, fnode, project_root: str) -> ApiSurfaceScore:
        simple_name = _short_name(fqname)
        score = ApiSurfaceScore(
            func_name=fqname,
            filepath=self._resolved_filepath(fnode, project_root),
        )
        score.has_docstring, score.has_args_doc, score.has_returns_doc = (
            self._doc_annotation_flags(fnode))
        score.params_count, score.annotated_params, score.has_type_annotations = (
            self._param_annotation_metrics(fnode))
        score.in_all_exports = self._is_exported(fnode, fqname, simple_name)
        score.is_public_api = (bool(getattr(fnode, 'is_public', False))
                               or score.in_all_exports)
        score.quality_score = self._quality_points(score)
        score.readiness = self._readiness_of(score)
        return score
    @staticmethod
    def _resolved_filepath(fnode, project_root: str) -> str:
        fp = getattr(fnode, 'filepath', '')
        if fp and not os.path.isabs(fp) and project_root:
            return os.path.abspath(os.path.join(project_root, fp))
        return fp
    @staticmethod
    def _is_exported(fnode, fqname: str, simple_name: str) -> bool:
        raw_exports = getattr(fnode, '_global_exports', None)
        global_exports = (raw_exports
                          if isinstance(raw_exports, (set, frozenset, list,
                                                      tuple, dict))
                          else set())
        if (bool(getattr(fnode, '_in_all_exports', False))
                or fqname in global_exports):
            return True
        if (getattr(fnode, 'is_method', False)
                or getattr(fnode, 'class_name', None)):
            return False
        return simple_name in global_exports
    def _quality_points(self, score: ApiSurfaceScore) -> float:
        qs = 0.0
        if score.has_docstring:
            qs += self._WEIGHTS["docstring"]
        if score.has_args_doc:
            qs += self._WEIGHTS["args_doc"]
        if score.has_returns_doc:
            qs += self._WEIGHTS["returns_doc"]
        if score.has_type_annotations:
            qs += self._WEIGHTS["type_annotations"]
        if score.in_all_exports:
            qs += self._WEIGHTS["in_all_exports"]
        return qs
    def _readiness_of(self, score: ApiSurfaceScore) -> str:
        if not score.is_public_api:
            return "internal"
        if score.quality_score >= _READY_MIN_SCORE:
            return "ready"
        if score.quality_score >= _PARTIAL_MIN_SCORE:
            return "partial"
        return "draft"
    def _doc_annotation_flags(self, fnode) -> tuple:
        doc = _fnode_doc(fnode)
        if not doc:
            return False, False, False
        doc_lower = doc.lower()
        has_args = bool(
            re.search(r'\b(?:args|arguments|parameters|params)\s*:',
                      doc_lower)
            or re.search(r'\b(?:args|arguments|parameters|params)\s*\n\s*-{3,}',
                         doc_lower)
            or _SPHINX_ARGS_RE.search(doc_lower))
        has_returns = bool(
            re.search(r'\b(?:returns|return|yields|yield)\s*:', doc_lower)
            or re.search(r'\b(?:returns|yields)\s*\n\s*-{3,}',
                         doc_lower)
            or _SPHINX_RETURNS_RE.search(doc_lower))
        return True, has_args, has_returns
    @staticmethod
    def _param_annotation_metrics(fnode) -> tuple:
        params = _non_self_params(_fnode_params(fnode))
        returns = getattr(fnode, 'returns', None)
        try:
            annotated = int(getattr(fnode, 'annotated_params', 0) or 0)
        except (TypeError, ValueError):
            annotated = 0
        annotated = max(0, min(annotated, len(params)))
        return len(params), annotated, bool(returns or annotated)
    def summary(self, scores: list[ApiSurfaceScore]) -> dict:
        scores = _as_object_list(scores)
        by_readiness = Counter(
            getattr(item, "readiness", "unknown") for item in scores)
        quality_dist = Counter(
            _numeric_or(item, "quality_score", 0.0) for item in scores)
        total = len(scores)
        avg_q = (sum(_numeric_or(item, "quality_score", 0.0)
                     for item in scores) / total if total else 0.0)
        return {
            "total_apis": total,
            "ready": by_readiness.get("ready", 0),
            "partial": by_readiness.get("partial", 0),
            "draft": by_readiness.get("draft", 0),
            "internal": by_readiness.get("internal", 0),
            "avg_quality": round(avg_q, 1),
            "quality_distribution": dict(quality_dist),
        }
def _expand_frontier(frontier: list, adjacency: dict, project_funcs: set,
                     visited: set, discovered: set) -> list:
    next_frontier: list = []
    for caller in frontier:
        for callee in adjacency.get(caller, []):
            if callee in visited:
                continue
            visited.add(callee)
            if callee in project_funcs:
                discovered.add(callee)
            next_frontier.append(callee)
    return next_frontier
class ConsumerInjectionSimulator:
    def simulate_consumers(
        self,
        call_graph,
        api_scores: list[ApiSurfaceScore],
        max_depth: int = DEFAULT_MAX_DEPTH,
        known_reachable: set[str] | None = None,
    ) -> dict[str, Any]:
        max_depth = _coerce_int_limit(max_depth, DEFAULT_MAX_DEPTH)
        external_apis = [s for s in _as_object_list(api_scores)
                         if _is_external_api(s)]
        result: dict[str, Any] = {
            "simulated_consumers": 0,
            "newly_reachable": 0,
            "newly_reachable_funcs": [],
            "adjusted_liveness": 0.0,
        }
        if call_graph is None:
            return result
        known_reachable, project_funcs, adjacency = (
            self._prepare_simulation_context(call_graph, known_reachable))
        total_funcs = len(project_funcs) or 1
        result["adjusted_liveness"] = round(len(known_reachable) / total_funcs, 3)
        if not external_apis:
            return result
        newly_reachable = self._collect_newly_reachable(
            external_apis, known_reachable, adjacency, project_funcs, max_depth)
        result.update({
            "simulated_consumers": len(external_apis),
            "newly_reachable": len(newly_reachable),
            "newly_reachable_funcs": sorted(newly_reachable),
            "adjusted_liveness": round(
                (len(known_reachable) + len(newly_reachable)) / total_funcs, 3),
        })
        return result
    def _collect_newly_reachable(self, external_apis: list[ApiSurfaceScore],
                                 known_reachable: set, adjacency: dict,
                                 project_funcs: set, max_depth: int) -> set:
        newly_reachable: set = set()
        for api in external_apis:
            api_name = getattr(api, "func_name", "")
            if not api_name:
                continue
            newly_reachable |= self._bfs_reachable_from(
                api_name, known_reachable, adjacency,
                project_funcs, max_depth)
        return newly_reachable
    @staticmethod
    def _prepare_simulation_context(call_graph,
                                    known_reachable: set[str] | None) -> tuple:
        project_funcs = set(_graph_functions(call_graph))
        if isinstance(known_reachable, (str, bytes)):
            known_reachable = None
        known = {name for name in (known_reachable or ())
                 if name in project_funcs}
        return known, project_funcs, callee_adjacency(call_graph)
    @staticmethod
    def _bfs_reachable_from(api_name: str, known_reachable: set,
                            adjacency: dict, project_funcs: set,
                            max_depth: int) -> set:
        visited: set = {api_name}
        discovered: set = set()
        if max_depth <= 0:
            return discovered
        if api_name in project_funcs:
            discovered.add(api_name)
        frontier = [api_name]
        depth = 1
        while frontier and depth < max_depth:
            frontier = _expand_frontier(
                frontier, adjacency, project_funcs, visited, discovered)
            depth += 1
        return discovered - set(known_reachable)
class DocSignatureDrivenInference:
    _API_KEYWORDS = re.compile(
        r'\b(?:public|api|interface|endpoint|entry|handler|callback|'
        r'hook|listener|observer|subscriber|middleware|plugin|'
        r'extension|adapter|wrapper|facade)\b',
        re.IGNORECASE,
    )
    _INTERNAL_KEYWORDS = re.compile(
        r'\b(?:internal|private|helper|utility|deprecated|'
        r'temporary|experimental|debug|dev)\b',
        re.IGNORECASE,
    )
    def infer_intent(self, api_scores: list[ApiSurfaceScore], call_graph) -> list[dict]:
        results = []
        functions = _graph_functions(call_graph)
        if not functions:
            return results
        for score in _as_object_list(api_scores):
            func_name = getattr(score, "func_name", None)
            if not func_name:
                continue
            fnode = functions.get(func_name)
            if not fnode:
                continue
            results.append(self._infer_single_intent(score, fnode))
        return results
    _SIGNAL_REASON_NAMES: tuple = (
        "doc_contains_api_keyword", "doc_contains_internal_keyword",
        "returns_callable", "has_params_and_return")
    def _intent_signals(self, doc: str, params: list, returns) -> tuple[bool, bool, bool, bool]:
        non_self_params = _non_self_params(params)
        return (
            bool(self._API_KEYWORDS.search(doc)),
            bool(self._INTERNAL_KEYWORDS.search(doc)),
            bool(returns and 'Callable' in str(returns)),
            bool(non_self_params and returns),
        )
    def _infer_single_intent(self, score: ApiSurfaceScore, fnode) -> dict:
        doc = _fnode_doc(fnode)
        params = _fnode_params(fnode)
        returns = getattr(fnode, 'returns', None)
        signals = self._intent_signals(doc, params, returns)
        api_kw, internal_kw, returns_callable, params_return = signals
        intent = {
            "func_name": score.func_name,
            "likely_public_api": api_kw or params_return,
            "likely_framework_entry": returns_callable,
            "likely_internal": internal_kw,
            "confidence": "low",
            "reasons": [reason for reason, hit
                        in zip(self._SIGNAL_REASON_NAMES, signals, strict=True) if hit],
        }
        self._finalize_intent_confidence(intent, score)
        return intent
    @staticmethod
    def _finalize_intent_confidence(intent: dict, score: ApiSurfaceScore) -> None:
        quality = _numeric_or(score, "quality_score", 0.0)
        if intent["likely_public_api"] and not intent["likely_internal"]:
            if quality >= _READY_MIN_SCORE:
                intent["confidence"] = "high"
            elif quality >= _PARTIAL_MIN_SCORE:
                intent["confidence"] = "medium"
            else:
                intent["confidence"] = "low"
        elif intent["likely_internal"]:
            intent["confidence"] = "high"
            intent["likely_public_api"] = False
    def summary(self, intents: list[dict]) -> dict:
        intents = [intent for intent in _as_object_list(intents)
                   if isinstance(intent, Mapping)]
        stats = {
            "likely_public": 0, "likely_framework": 0,
            "likely_internal": 0, "high_confidence": 0,
        }
        for intent in intents:
            if intent.get("likely_public_api"):
                stats["likely_public"] += 1
            if intent.get("likely_framework_entry"):
                stats["likely_framework"] += 1
            if intent.get("likely_internal"):
                stats["likely_internal"] += 1
            if intent.get("confidence") == "high":
                stats["high_confidence"] += 1
        stats["total"] = len(intents)
        return stats
class EnhancedBusinessFlowReport:
    def __init__(self, base_report: BusinessFlowReport) -> None:
        self.base = base_report
        self.never_reachable_breakdown = dict(base_report.never_reachable_breakdown)
        self.api_scores: list[ApiSurfaceScore] = []
        self.api_surface_summary: dict = {}
        self.consumer_simulation: dict = {}
        self.adjusted_liveness_rate: float | None = (
            base_report.measured_liveness_rate)
        self.intent_details: list[dict] = []
        self.intent_summary: dict = {}
        self.enhanced_liveness_rate: float | None = (
            base_report.measured_liveness_rate)
    def __getattr__(self, name: str) -> Any:
        try:
            base = object.__getattribute__(self, "base")
        except AttributeError:
            raise AttributeError(name) from None
        return getattr(base, name)
    def summary(self) -> dict:
        s = self.base.summary()
        s["never_reachable_breakdown"] = dict(self.never_reachable_breakdown)
        s["api_surface"] = self.api_surface_summary
        s["consumer_simulation"] = self.consumer_simulation
        s["adjusted_liveness_rate"] = self.adjusted_liveness_rate
        s["intent_summary"] = self.intent_summary
        s["enhanced_liveness_rate"] = self.enhanced_liveness_rate
        return s
    def to_report_data(self) -> dict:
        data = self.base.to_report_data()
        data.update({
            "summary": self.summary(),
            "api_scores": [asdict(score) for score in self.api_scores],
            "intent_details": [dict(intent) for intent in self.intent_details],
        })
        return data
def _run_a4_api_surface_step(report: EnhancedBusinessFlowReport,
                            call_graph: Any,
                            project_root: str) -> list[ApiSurfaceScore]:
    logger.info("[BizChain] A4 API surface quality analysis...")
    try:
        analyzer = ApiSurfaceAnalyzer()
        api_scores = analyzer.analyze(call_graph, project_root)
        report.api_scores = api_scores
        report.api_surface_summary = analyzer.summary(api_scores)
        s = report.api_surface_summary
        logger.info(
            "        API: %s funcs, ready=%s, avg_quality=%s",
            s['total_apis'], s['ready'], s['avg_quality'])
        return api_scores
    except Exception as e:  # noqa: BLE001 — 段级降级全集（冷缓存已在调用图构建入口 fail-fast；分析器异常面无法静态穷尽，与 build_business_call_graph 口径对齐）
        logger.info("        A4 skip: %s", e)
        return []
def _run_b4_consumer_sim_step(report: EnhancedBusinessFlowReport,
                              call_graph: Any,
                              api_scores: list[ApiSurfaceScore],
                              max_depth: int) -> set[str]:
    logger.info("[BizChain] B4 Consumer injection simulation...")
    try:
        if api_scores:
            simulator = ConsumerInjectionSimulator()
            sim_result = simulator.simulate_consumers(
                call_graph, api_scores, max_depth,
                known_reachable=report.reachable_functions)
            report.consumer_simulation = sim_result
            consumer_reachable = set(sim_result["newly_reachable_funcs"])
            if sim_result["simulated_consumers"] > 0:
                report.adjusted_liveness_rate = sim_result["adjusted_liveness"]
                logger.info(
                    "        consumers=%s, new_reachable=%s, adj_liveness=%.1f%%",
                    sim_result['simulated_consumers'], sim_result['newly_reachable'],
                    sim_result['adjusted_liveness'] * 100)
            elif report.adjusted_liveness_rate is None:
                logger.info("        consumers=0, adjusted stays unmeasured")
            else:
                logger.info(
                    "        consumers=0, adjusted stays base %.1f%%",
                    report.adjusted_liveness_rate * 100)
            return consumer_reachable
    except Exception as e:  # noqa: BLE001 — 段级降级全集（同 A4 口径）
        logger.info("        B4 skip: %s", e)
    return set()
def _revalidate_consumer_blindspots(
        report: EnhancedBusinessFlowReport,
        blindspot_entries: list[dict],
        consumer_reachable: set[str],
) -> None:
    if not consumer_reachable or not blindspot_entries:
        return
    rescued, confirmed = LivenessValidator().validate(
        blindspot_entries,
        report.chains,
        report.sim_results,
        extra_reachable=set(report.reachable_functions) | consumer_reachable,
    )
    confirmed_count = (
        len(confirmed) if report.base.reachability_measured else 0)
    report.base.blindspots_rescued = len(rescued)
    report.base.blindspots_confirmed = confirmed_count
    logger.info(
        "        消费者证据复核盲区: 救回=%s, 确认=%s",
        len(rescued), confirmed_count)
def _run_c4_doc_inference_step(report: EnhancedBusinessFlowReport,
                                api_scores: list[ApiSurfaceScore],
                                call_graph: Any) -> None:
    logger.info("[BizChain] C4 Doc-signature inference...")
    try:
        if api_scores:
            inferrer = DocSignatureDrivenInference()
            intents = inferrer.infer_intent(api_scores, call_graph)
            report.intent_details = intents
            report.intent_summary = inferrer.summary(intents)
            s = report.intent_summary
            logger.info(
                "        public=%s, framework=%s",
                s.get('likely_public', 0), s.get('likely_framework', 0))
    except Exception as e:  # noqa: BLE001 — 段级降级全集（同 A4 口径）
        logger.info("        C4 skip: %s", e)
def diagnose_business_flows_enhanced(
    project_root: str,
    call_graph: Any = None,
    blindspot_entries: list[dict] | None = None,
    source_paths: list[str] | None = None,
    max_depth: int = DEFAULT_MAX_DEPTH,
    max_chains: int = DEFAULT_MAX_CHAINS,
    skill_type: str = 'unknown',
    ctx: Any = None,
    include_tests: bool | None = None,
) -> EnhancedBusinessFlowReport:
    project_root = normalize_project_root(project_root)
    validate_source_paths(source_paths)
    source_paths = _materialize_source_paths(source_paths)
    max_depth = _coerce_int_limit(max_depth, DEFAULT_MAX_DEPTH)
    max_chains = _coerce_int_limit(max_chains, DEFAULT_MAX_CHAINS)
    include_tests = _coerce_optional_bool(include_tests)
    blindspot_entries = _as_entry_list(blindspot_entries)
    base_report = diagnose_business_flows(
        project_root=project_root,
        call_graph=call_graph,
        blindspot_entries=blindspot_entries,
        source_paths=source_paths,
        max_depth=max_depth,
        max_chains=max_chains,
        ctx=ctx,
        include_tests=include_tests,
    )
    report = EnhancedBusinessFlowReport(base_report)
    if str(skill_type or "").strip().lower() != "library":
        return report
    call_graph = base_report.call_graph
    api_scores = _run_a4_api_surface_step(report, call_graph, project_root)
    consumer_reachable = _run_b4_consumer_sim_step(
        report, call_graph, api_scores, max_depth)
    _revalidate_consumer_blindspots(
        report, blindspot_entries, consumer_reachable)
    _run_c4_doc_inference_step(report, api_scores, call_graph)
    measured_rates = [
        rate for rate in (
            base_report.measured_liveness_rate,
            report.adjusted_liveness_rate,
        ) if rate is not None
    ]
    report.enhanced_liveness_rate = (
        max(measured_rates) if measured_rates else None)
    if report.enhanced_liveness_rate is None:
        logger.info("        enhanced_liveness: unmeasured")
    else:
        base_rate = base_report.measured_liveness_rate
        base_text = (f"{base_rate * 100:.1f}%"
                     if base_rate is not None else "unmeasured")
        logger.info(
            "        enhanced_liveness: %.1f%% (base=%s)",
            report.enhanced_liveness_rate * 100, base_text)
    return report
__all__ = [
    'DEFAULT_MAX_CHAINS',
    'DEFAULT_MAX_DEPTH',
    'ApiSurfaceAnalyzer',
    'ApiSurfaceScore',
    'BusinessChain',
    'BusinessChainTracer',
    'BusinessFlowReport',
    'ChainSimResult',
    'ChainSimulator',
    'ConsumerInjectionSimulator',
    'DocSignatureDrivenInference',
    'EnhancedBusinessFlowReport',
    'LivenessValidator',
    'build_business_call_graph',
    'callee_adjacency',
    'diagnose_business_flows',
    'diagnose_business_flows_enhanced',
    'trace_and_classify',
]

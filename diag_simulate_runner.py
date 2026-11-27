from __future__ import annotations

import argparse
import ast
import dataclasses
import os
import re
import threading
import time
import tokenize
import traceback
import types as _types_mod
from contextlib import nullcontext
from dataclasses import (
    dataclass,
    field,
)
from typing import Any

from jwsgj.diag_callgraph_builder import start_dynamic_tracer
from jwsgj.diag_shared_ast_bindings import import_bound_names
from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    is_main_check,
    iter_module_scope_nodes,
    main_block_entry_args,
)
from jwsgj.diag_simulate_evidence import (
    prepare_evidence_context,
    run_diagnosis,
    simulate_engine_files,
)
from jwsgj.diag_simulate_sandbox import (
    _DEFAULT_ENTRY_TIMEOUT,
    ExecutionResult,
    SandboxExecutor,
    SimEntryPoint,
    _execution_scope,
    _invoke_callable,
    _mark_entry_skipped,
    _pop_sys_path,
    _project_import_roots,
    _project_trust_roots,
    _push_sys_path,
    _restore_active_project_roots,
    _sandbox_argv,
    _set_active_project_roots,
    _sim_mem_guard_min_bytes,
    _sim_module_registration,
    _system_exit_label,
    _trip_mem_guard,
    infer_module_identity,
    safe_compile,
    safe_exec,
)
from jwsgj.diag_types_normalize import (
    int_or,
    normalize_execute_timeout,
)
from jwsgj.diag_types_vocab import MESSAGE_TRUNCATE_LEN
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
    timed_log,
)
from jwsgj.runtime_paths import (
    is_own_skill_root,
    normalize_project_root,
)
from jwsgj.runtime_scope import (
    is_scan_py_name,
    is_test_file_path,
    prune_scan_dirnames,
    safe_relpath,
    scan_prune_dirs,
)

logger = get_module_logger(__name__, __file__)
_ENGINE_FILES = simulate_engine_files(__file__)
__all__ = [
    'ReuseArtifacts',
    'SimulationReport',
    'project_sandbox_channel',
    'sandbox_env_skip_reason',
    'save_coverage',
    'simulate_and_diagnose',
]
_ERROR_TEXT_LIMIT = MESSAGE_TRUNCATE_LEN
_CMD_TIME_BUDGET_SEC = 30.0
_SIM_PRIORITY_ORDER = {'main': 0, 'run': 1, 'execute': 2, 'cli': 3, 'start': 4}
_MAX_SIM_ENTRIES = 10
def _is_self_diag_root(project_root: str) -> bool:
    try:
        return bool(is_own_skill_root(project_root))
    except (OSError, TypeError, ValueError) as exc:
        log_swallowed(__name__, exc, context="_is_self_diag_root:OSError,TypeError,ValueError")
        return False
@dataclass
class SimulationReport:
    project_root: str
    total_entry_points: int = 0
    executed: int = 0
    succeeded: int = 0
    failed: int = 0
    timed_out: int = 0
    entries_discovered: int = 0
    entries_truncated: int = 0
    results: list[ExecutionResult] = field(default_factory=list)
    trace_summary: dict | None = None
    trace_merge: dict | None = None
    coverage_data: dict | None = None
    fuzzy_execution: dict | None = None
    dead_code_confirmation: dict | None = None
    def summary(self) -> dict:
        return {
            "project": self.project_root,
            "entry_points": self.total_entry_points,
            "executed": self.executed,
            "succeeded": self.succeeded,
            "failed": self.failed,
            "timed_out": self.timed_out,
            "sim_errors_count": sum(len(r.sim_errors) for r in self.results),
            "entries_discovered": self.entries_discovered,
            "entries_truncated": self.entries_truncated,
        }
@dataclass
class ReuseArtifacts:
    call_graph: Any = None
    blindspot_report: Any = None
    skip_blindspot_scan: bool = False
_MAIN_BLOCK_EXIT_WRAPPERS = frozenset({"SystemExit", "exit", "quit"})
def _main_call_info(node, known_names=None) -> tuple[str | None, bool]:
    if not isinstance(node, ast.Call):
        return None, False
    func = node.func
    if isinstance(func, ast.Name):
        name = func.id
    elif isinstance(func, ast.Attribute):
        name = func.attr
    else:
        return None, False
    if name in _MAIN_BLOCK_EXIT_WRAPPERS:
        for arg in node.args:
            inner_name, _inner_exit = _main_call_info(arg, known_names)
            if inner_name is not None:
                return inner_name, True
        return None, False
    if isinstance(func, ast.Attribute):
        return None, False
    if known_names is not None and name not in known_names:
        for arg in node.args:
            inner_name, _inner_exit = _main_call_info(arg, known_names)
            if inner_name in known_names:
                return inner_name, _inner_exit
        return None, False
    return name, False
def _main_block_callee(stmt: ast.stmt,
                       known_names=None) -> tuple[str | None, bool]:
    if isinstance(stmt, ast.Expr):
        return _main_call_info(stmt.value, known_names)
    if (isinstance(stmt, ast.Raise) and isinstance(stmt.exc, ast.Call)
            and isinstance(stmt.exc.func, ast.Name)
            and stmt.exc.func.id in _MAIN_BLOCK_EXIT_WRAPPERS):
        return _main_call_info(stmt.exc, known_names)
    return None, False
_MAIN_BLOCK_ENTRY_NESTED_CONTAINERS = (
    ast.Try, TRY_STAR, ast.With, ast.AsyncWith)
def _iter_main_block_entry_stmts(stmts):
    for stmt in stmts:
        yield stmt
        if isinstance(stmt, _MAIN_BLOCK_ENTRY_NESTED_CONTAINERS):
            yield from _iter_main_block_entry_stmts(stmt.body)
        if isinstance(stmt, (ast.Try, TRY_STAR)):
            for handler in stmt.handlers:
                yield from _iter_main_block_entry_stmts(handler.body)
            yield from _iter_main_block_entry_stmts(stmt.orelse)
            yield from _iter_main_block_entry_stmts(stmt.finalbody)
class _SimEntryPointDiscoverer:
    ENTRY_NAMES = frozenset({
        "main", "run", "start", "cli", "execute", "entry",
        "app", "serve", "worker",
    })
    def __init__(self, project_root: str, exclude_test_files: bool = False, ctx: Any=None) -> None:
        self.project_root = os.path.abspath(project_root)
        self.exclude_test_files = exclude_test_files
        self.ctx = ctx
    def discover(self) -> list[SimEntryPoint]:
        entries: list[SimEntryPoint] = []
        for filepath in self._collect_py_files():
            entries.extend(self._scan_file(filepath))
        return entries
    def _collect_py_files(self) -> list[str]:
        files = []
        _skip = scan_prune_dirs(self.project_root)
        for dirpath, dirnames, filenames in os.walk(self.project_root):
            prune_scan_dirnames(dirnames, _skip)
            dirnames.sort()
            files.extend(
                os.path.join(dirpath, fn) for fn in sorted(filenames)
                if self._is_entry_source(fn, dirpath))
        return files
    def _is_entry_source(self, filename: str, dirpath: str = "") -> bool:
        if not is_scan_py_name(filename):
            return False
        if not self.exclude_test_files:
            return True
        # 排除口径必须与 is_test_file_path 对齐：conftest.py 与 tests/ 等测试
        # 目录下的非 test_ 前缀文件（helpers.py 等）同属测试基础设施，仅按
        # basename 判定会把它们当生产入口加载并驱动。路径先相对 project_root，
        # 避免项目根本身位于名为 tests 的目录时被整体误排除。
        relative = safe_relpath(
            os.path.join(dirpath, filename), self.project_root)
        return not is_test_file_path(relative)
    def _scan_file(self, filepath: str) -> list[SimEntryPoint]:
        entries = []
        if self.ctx is not None:
            try:
                tree = self.ctx.get_ast(filepath)
            except (OSError, SyntaxError, ValueError, RuntimeError,
                    KeyError, TypeError, AttributeError, MemoryError) as e:
                logger.warning("[Simulate] 扫描解析失败,返回已收集: %s (%s)",
                               filepath, e)
                return entries
            if tree is None:
                logger.warning("[Simulate] 扫描解析失败,返回已收集: %s", filepath)
                return entries
        else:
            try:
                with tokenize.open(filepath) as f:
                    # jwsgj:suppress loop_io — 审计认可：目录扫描逐文件读取即其语义
                    source = f.read()
                tree = ast.parse(source, filename=filepath)
            except (OSError, SyntaxError, UnicodeDecodeError, ValueError,
                    RecursionError, MemoryError) as e:
                logger.warning("[Simulate] 扫描解析失败,返回已收集: %s: %s", filepath, e)
                return entries
        seen_names = set()
        candidates = [
            *self._find_main_block_entries(tree, filepath),
            *self._find_named_entries(tree, filepath),
        ]
        for entry in candidates:
            if entry.name in seen_names:
                continue
            seen_names.add(entry.name)
            entries.append(entry)
        return entries
    def _find_main_block_entries(self, tree: ast.AST, filepath: str) -> list[SimEntryPoint]:
        entries = []
        module_defs = {
            node.name: node for node in getattr(tree, "body", ())
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        known_names = (set(module_defs) | self.ENTRY_NAMES
                       | import_bound_names(getattr(tree, "body", ())))
        program_name = (os.path.basename(os.path.normpath(self.project_root))
                        or "program")
        for node in iter_module_scope_nodes(tree):
            if not isinstance(node, ast.If):
                continue
            if not is_main_check(node.test):
                continue
            for stmt in _iter_main_block_entry_stmts(node.body):
                callee, exit_on_return = _main_block_callee(
                    stmt, known_names)
                if callee is not None:
                    args, skip_reason = main_block_entry_args(
                        module_defs.get(callee), program_name=program_name)
                    entries.append(SimEntryPoint(
                        name=callee,
                        filepath=filepath,
                        line=stmt.lineno,
                        kind="cli_main",
                        args=args,
                        skip_reason=skip_reason,
                        exit_on_return=exit_on_return,
                    ))
        return entries
    def _find_named_entries(self, tree: ast.AST, filepath: str) -> list[SimEntryPoint]:
        entries = []
        for node in ast.iter_child_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if node.name.startswith("_"):
                continue
            if node.name in self.ENTRY_NAMES:
                args = node.args
                required = (len(args.posonlyargs) + len(args.args)
                            - len(args.defaults) + args.kw_defaults.count(None))
                if required == 0:
                    entries.append(SimEntryPoint(
                        name=node.name,
                        filepath=filepath,
                        line=node.lineno,
                        kind="public_api",
                    ))
        return entries
def _read_module_source(filepath: str, ctx) -> str:
    if ctx is not None:
        try:
            source = ctx.get_source(filepath)
        except (OSError, KeyError, ValueError, TypeError, AttributeError,
                RuntimeError) as exc:
            log_swallowed(
                __name__, exc,
                context='_read_module_source:OSError,KeyError,ValueError,TypeError,AttributeError,RuntimeError')
            source = None
        if source is not None:
            return source
    with tokenize.open(filepath) as f:
        return f.read()
def _safe_load_module(filepath: str, ctx, project_root: str,
                      import_roots=None, *, on_loaded=None) -> dict:
    source = _read_module_source(filepath, ctx)
    code = safe_compile(source, filepath)
    pkg_name, _sim_module_name = infer_module_identity(filepath, project_root)
    _sim_module = _types_mod.ModuleType(_sim_module_name)
    _sim_module.__file__ = filepath
    _sim_module.__package__ = pkg_name
    exec_globals = _sim_module.__dict__
    exec_globals["__name__"] = _sim_module_name
    exec_globals["__file__"] = filepath
    exec_globals["__package__"] = pkg_name
    exec_globals["__spec__"] = None
    _import_roots = (tuple(import_roots) if import_roots
                     else _project_import_roots(project_root))
    _inserted_roots = []
    _previous_roots = None
    with _sim_module_registration(_sim_module):
        try:
            _inserted_roots = _push_sys_path(_import_roots)
            _trusted_roots = _project_trust_roots(project_root, _import_roots)
            _previous_roots = _set_active_project_roots(_trusted_roots)
            if code is not None:
                _exec_err, _exec_tb = safe_exec(code, exec_globals, filepath)
                if _exec_err:
                    _vexc = ValueError(f"{filepath}: {_exec_err}")
                    _vexc.exec_tb = _exec_tb
                    raise _vexc
            else:
                raise ValueError(
                    f"{filepath}: compile unavailable (non-syntax failure)")
            if on_loaded is not None:
                on_loaded(_sim_module)
        finally:
            _pop_sys_path(_inserted_roots)
            if _previous_roots is not None:
                _restore_active_project_roots(_previous_roots)
    return exec_globals
@dataclass
class _SafeRunState:
    project_root: str
    sim_report: SimulationReport
    ctx: Any
    per_entry_timeout: float
    is_self_diag: bool
    mem_guard: int
    tracer: Any = None
    seen_files: set = field(default_factory=set)
    seen_entry_keys: set = field(default_factory=set)
    failed_entry_keys: set = field(default_factory=set)
    loaded_module_globals: dict = field(default_factory=dict)
    loaded_modules: dict = field(default_factory=dict)
    mem_aborted: bool = False
    abort_reason: str = ""
    import_roots: tuple = ()
def _remember_entry_outcome(state: _SafeRunState, filepath, entry_name, result):
    key = (filepath, entry_name)
    state.seen_entry_keys.add(key)
    if result.success:
        state.failed_entry_keys.discard(key)
    else:
        state.failed_entry_keys.add(key)
def _load_and_drive_entry(state: _SafeRunState, filepath, entry_name, result,
                          args):
    def _drive_loaded(module):
        exec_globals = module.__dict__
        result.success = True
        state.seen_files.add(filepath)
        state.loaded_module_globals[filepath] = exec_globals
        state.loaded_modules[filepath] = module
        _drive_entry(entry_name, exec_globals, state.project_root, result,
                     state.is_self_diag, args=args)
    exec_globals = _safe_load_module(
        filepath, state.ctx, state.project_root,
        import_roots=state.import_roots, on_loaded=_drive_loaded)
    _remember_entry_outcome(state, filepath, entry_name, result)
    return exec_globals
def _drive_duplicate_entry(state: _SafeRunState, filepath, entry_name, result,
                           args) -> None:
    mod_globals = state.loaded_module_globals.get(filepath)
    if mod_globals is None:
        result.success = False
        result.duration_sec = 0.0
        result.error = "module globals unavailable for loaded filepath"
        result.sim_errors.append(
            f"{entry_name}: module globals unavailable (load incomplete)")
        _remember_entry_outcome(state, filepath, entry_name, result)
        return
    key = (filepath, entry_name)
    if key in state.seen_entry_keys:
        result.duration_sec = 0.0
        if key in state.failed_entry_keys:
            result.success = False
            result.error = "duplicate of failed entry (not re-executed)"
            result.sim_errors.append(
                f"{entry_name}: duplicate of failed entry (not re-executed)")
        else:
            result.success = True
            result.sim_errors.append(
                f"{entry_name}: skipped (duplicate filepath already loaded)")
        return
    module = state.loaded_modules.get(filepath)
    registration = (_sim_module_registration(module) if module is not None
                    else nullcontext())
    try:
        result.success = True
        with registration:
            _drive_entry(entry_name, mod_globals, state.project_root, result,
                         state.is_self_diag, args=args)
    except Exception as _dup_e:  # noqa: BLE001
        logger.debug("suppressed duplicate-entry drive error (%s): %s", type(_dup_e).__name__, _dup_e)
        result.success = False
        result.error = str(_dup_e)[:_ERROR_TEXT_LIMIT]
        result.traceback = traceback.format_exc()
    _remember_entry_outcome(state, filepath, entry_name, result)
def _mark_entry_channel_error(exc, result):
    logger.debug("suppressed per-entry channel error (%s): %s", type(exc).__name__, exc)
    result.success = False
    result.error = str(exc)[:_ERROR_TEXT_LIMIT]
    result.traceback = (
        getattr(exc, "exec_tb", None) or traceback.format_exc())
def _apply_mem_guard(state: _SafeRunState) -> None:
    if state.mem_aborted:
        return
    if _trip_mem_guard(state.mem_guard):
        state.mem_aborted = True
        state.abort_reason = "sandbox memory guard"
def _finish_entry(sim_report, result, entry_name: str) -> None:
    sim_report.results.append(result)
    sim_report.executed += 1
    if result.timed_out:
        sim_report.timed_out += 1
    elif result.success:
        sim_report.succeeded += 1
    else:
        sim_report.failed += 1
    if result.timed_out:
        logger.info(f"  ⚠ {entry_name} 超时 ({result.duration_sec}s)")
    elif result.success:
        logger.info(f"  ✓ {entry_name} ({result.duration_sec}s)")
    else:
        logger.info(
            f"  ✗ {entry_name}: {(result.error or '未知')[:_ERROR_TEXT_LIMIT]}")
def _mark_entry_timeout(result, budget: float, elapsed: float) -> None:
    _note = f"timeout ({elapsed}s > {budget}s)"
    result.success = False
    result.timed_out = True
    if result.error:
        result.sim_errors.append(f"{_note}: {result.error}")
        return
    result.error = _note
def _drive_deduped_entry(filepath, entry_name, state, result, args) -> None:
    with _execution_scope(state.project_root, state.import_roots,
                          entry_file=filepath), _sandbox_argv(filepath):
        if filepath not in state.seen_files:
            try:
                _load_and_drive_entry(
                    state, filepath, entry_name, result, args=args)
            except Exception as e:  # noqa: BLE001
                log_swallowed(__name__, e,
                              context='_drive_deduped_entry:Exc')
                _mark_entry_channel_error(e, result)
                state.seen_files.add(filepath)
                _remember_entry_outcome(
                    state, filepath, entry_name, result)
            return
        _drive_duplicate_entry(state, filepath, entry_name, result,
                               args=args)
def _drive_entry_profiled(filepath, entry_name, state, result, args) -> None:
    tracer = state.tracer
    previous = None
    installed = False
    if tracer is not None and hasattr(tracer, "install_for_current_thread"):
        try:
            previous = tracer.install_for_current_thread()
            installed = True
        except Exception as _profile_e:  # noqa: BLE001 — 追踪安装失败降级无追踪
            logger.warning("[Simulate] 工作线程 profiler 安装失败（降级无追踪）: %s",
                           _profile_e)
    try:
        _drive_deduped_entry(filepath, entry_name, state, result, args=args)
    except Exception as _drive_e:  # noqa: BLE001 — 工作线程异常必须回到入口结果
        log_swallowed(__name__, _drive_e, context='_drive_entry_profiled:Exc')
        _mark_entry_channel_error(_drive_e, result)
        _remember_entry_outcome(state, filepath, entry_name, result)
    finally:
        if installed:
            try:
                tracer.restore_current_thread(previous)
            except Exception as _restore_e:  # noqa: BLE001 — 还原失败不阻断主链
                logger.debug("工作线程 profiler 还原失败: %s", _restore_e)
def _drive_entry_within_budget(filepath, entry_name, state, result, args) -> bool:
    budget = state.per_entry_timeout
    if budget <= 0:
        state.mem_aborted = True
        state.abort_reason = "entry timeout"
        return True
    worker = threading.Thread(
        target=_drive_entry_profiled,
        args=(filepath, entry_name, state, result, args),
        daemon=True,
        name=f"jwsgj-sim-{entry_name}",
    )
    try:
        worker.start()
    except RuntimeError as _start_e:
        logger.warning("[Simulate] 入口 %s 工作线程启动失败: %s",
                       entry_name, _start_e)
        result.success = False
        result.error = f"thread start failed: {_start_e}"[:_ERROR_TEXT_LIMIT]
        result.traceback = traceback.format_exc()
        return False
    worker.join(budget)
    if not worker.is_alive():
        return False
    state.mem_aborted = True
    state.abort_reason = "entry timeout"
    logger.warning(
        "[Simulate] 入口 %s 超过 %.1fs 预算，残留线程已隔离"
        "（中止余下入口）", entry_name, budget)
    return True
def _run_safe_entry(entry, state: _SafeRunState) -> None:
    _apply_mem_guard(state)
    entry_name = getattr(entry, 'name', '<unknown>')
    result = ExecutionResult(entry=entry)
    t0 = time.time()
    try:
        filepath = entry.filepath
    except AttributeError as _e:
        log_swallowed(__name__, _e, context='_run_safe_entry:AttributeError')
        _mark_entry_skipped(result,
                            "entry missing filepath attribute",
                            f"{entry_name}: missing filepath")
        _finish_entry(state.sim_report, result, entry_name)
        return
    if state.mem_aborted:
        _abort_reason = state.abort_reason or "sandbox memory guard"
        _mark_entry_skipped(
            result,
            f"skipped ({_abort_reason})",
            f"{entry_name}: skipped ({_abort_reason})")
        _finish_entry(state.sim_report, result, entry_name)
        return
    _args = tuple(getattr(entry, 'args', ()) or ())
    _skip = getattr(entry, 'skip_reason', '') or ''
    if _skip:
        _mark_entry_skipped(result,
                            f"[SIM-SKIP] {_skip}",
                            f"{entry_name}: skipped ({_skip})")
        _finish_entry(state.sim_report, result, entry_name)
        return
    _timed_out = _drive_entry_within_budget(
        filepath, entry_name, state, result, _args)
    _elapsed = round(time.time() - t0, 2)
    result.duration_sec = _elapsed
    if _timed_out or state.per_entry_timeout <= 0:
        result = dataclasses.replace(
            result, sim_errors=list(result.sim_errors))
        _mark_entry_timeout(result, state.per_entry_timeout, _elapsed)
    _finish_entry(state.sim_report, result, entry_name)
def _execute_safe_mode(entries, project_root, timeout, sim_report, tracer, ctx: Any=None):
    trace_edges = []
    try:
        state = _SafeRunState(
            project_root=project_root,
            sim_report=sim_report,
            ctx=ctx,
            per_entry_timeout=normalize_execute_timeout(
                timeout, _DEFAULT_ENTRY_TIMEOUT),
            is_self_diag=_is_self_diag_root(project_root),
            mem_guard=_sim_mem_guard_min_bytes(),
            tracer=tracer,
            import_roots=_project_import_roots(project_root),
        )
        for entry in entries:
            try:
                _run_safe_entry(entry, state)
            except Exception as _entry_e:  # noqa: BLE001 — 单入口契约异常隔离
                _bad_name = getattr(entry, "name", "<unknown>")
                logger.warning(
                    "[Simulate] 入口 %s 驱动异常（单入口隔离，余下继续）: %s",
                    _bad_name, _entry_e)
                _bad_result = ExecutionResult(entry=entry)
                _bad_result.error = (
                    f"{type(_entry_e).__name__}: {_entry_e}"
                )[:_ERROR_TEXT_LIMIT]
                _bad_result.traceback = traceback.format_exc()
                _finish_entry(sim_report, _bad_result, _bad_name)
    finally:
        if tracer is not None:
            try:
                trace_edges.extend(tracer.stop())
                sim_report.trace_summary = tracer.summary()
            except Exception as _trace_e:  # noqa: BLE001 — 追踪是辅助证据，收尾失败降级
                logger.warning(
                    "[Simulate] 追踪收尾失败（降级为无追踪摘要）: %s", _trace_e)
    logger.info(f"  [Trace] 捕获 {len(trace_edges)} 条运行时调用边")
    return trace_edges
class _SandboxCliArgs(argparse.Namespace):
    def __getattr__(self, name: str):
        if name.startswith("__") and name.endswith("__"):
            raise AttributeError(name)
def _build_mock_cli_args(project_root: str) -> argparse.Namespace:
    return _SandboxCliArgs(project=project_root)
def _cmd_skip_reason(is_self_diag: bool, elapsed: float) -> str | None:
    if is_self_diag:
        return "self-diagnosis"
    if elapsed >= _CMD_TIME_BUDGET_SEC:
        return "time budget exceeded"
    return None
def _drive_one_cmd(name: str, func, mock_args, result) -> float:
    _t0 = time.time()
    try:
        _invoke_callable(func, mock_args)
    except SystemExit as _exit:
        _label = _system_exit_label(_exit)
        if _label is not None:
            result.success = False
            result.error = f"{name}: {_label}"[:_ERROR_TEXT_LIMIT]
            result.sim_errors.append(f"{name}: {_label}"[:_ERROR_TEXT_LIMIT])
            result.traceback = traceback.format_exc()
        logger.debug("suppressed SystemExit in _execute_main_commands", exc_info=True)
    except BaseException as _sim_e:  # noqa: BLE001 — 隔离目标 cmd_* 的全部退出异常
        logger.debug("suppressed cmd-function error (%s): %s", type(_sim_e).__name__, _sim_e)
        result.sim_errors.append(
            f"{name}: {str(_sim_e)[:_ERROR_TEXT_LIMIT]}")
        result.success = False
        result.error = (
            f"{name}: {type(_sim_e).__name__}: {_sim_e}"[:_ERROR_TEXT_LIMIT])
        result.traceback = traceback.format_exc()
    return time.time() - _t0
def _execute_main_commands(exec_globals, project_root, result,
                          is_self_diag: bool):
    mock_args = _build_mock_cli_args(project_root)
    cmd_elapsed = 0.0
    cmd_funcs = sorted(
        (n, f) for n, f in exec_globals.items()
        if n.startswith('cmd_') and callable(f))
    if not cmd_funcs:
        if is_self_diag:
            _mark_entry_skipped(
                result,
                "[SIM-SKIP] self-diagnosis",
                "main: skipped (self-diagnosis, no cmd_* functions)")
            return
        message = "main: no cmd_* functions to drive (main body not executed)"
        result.success = False
        result.error = message
        result.sim_errors.append(message)
        return
    result.success = True
    driven = 0
    time_budget_exceeded = False
    for name, func in cmd_funcs:
        reason = _cmd_skip_reason(is_self_diag, cmd_elapsed)
        if reason is not None:
            time_budget_exceeded |= reason == "time budget exceeded"
            result.sim_errors.append(f"{name}: skipped ({reason})")
            continue
        driven += 1
        cmd_elapsed += _drive_one_cmd(name, func, mock_args, result)
    time_budget_exceeded |= cmd_elapsed >= _CMD_TIME_BUDGET_SEC
    if time_budget_exceeded and result.success:
        _mark_entry_timeout(result, _CMD_TIME_BUDGET_SEC, cmd_elapsed)
    elif driven == 0:
        result.success = False
        result.error = "[SIM-SKIP] self-diagnosis"
        result.sim_errors.append(
            f"main: skipped (self-diagnosis, {len(cmd_funcs)} cmd_* functions)")
def _drive_entry(entry_name, exec_globals, project_root, result, is_self_diag,
                 args):
    if entry_name == "main" and (is_self_diag or "main" not in exec_globals):
        _execute_main_commands(exec_globals, project_root, result, is_self_diag)
        return
    if is_self_diag:
        _mark_entry_skipped(
            result,
            "[SIM-SKIP] self-diagnosis",
            f"{entry_name}: skipped (self-diagnosis entry guard)")
        return
    if entry_name not in exec_globals:
        message = f"{entry_name}: not found in module globals"
        result.success = False
        result.error = message[:_ERROR_TEXT_LIMIT]
        result.sim_errors.append(message)
        return
    func = exec_globals[entry_name]
    if not callable(func):
        message = f"{entry_name}: entry value not callable"
        result.success = False
        result.error = message[:_ERROR_TEXT_LIMIT]
        result.sim_errors.append(message)
        return
    result.success = True
    try:
        returned = _invoke_callable(func, *args)
        if getattr(getattr(result, "entry", None), "exit_on_return", False):
            raise SystemExit(returned)
    except SystemExit as _exit:
        _label = _system_exit_label(_exit)
        if _label is not None:
            result.success = False
            result.error = f"{entry_name}: {_label}"[:_ERROR_TEXT_LIMIT]
            result.sim_errors.append(f"{entry_name}: {_label}"[:_ERROR_TEXT_LIMIT])
            result.traceback = traceback.format_exc()
        logger.debug("suppressed SystemExit in entry drive", exc_info=True)
    except BaseException as _func_e:  # noqa: BLE001 — 隔离目标入口的全部退出异常
        logger.debug("suppressed entry-function error (%s): %s", type(_func_e).__name__, _func_e)
        result.sim_errors.append(
            f"{entry_name}: {str(_func_e)[:_ERROR_TEXT_LIMIT]}")
        result.success = False
        result.error = (
            f"{entry_name}: {type(_func_e).__name__}: {_func_e}"
        )[:_ERROR_TEXT_LIMIT]
        result.traceback = traceback.format_exc()
def _execute_sandbox_mode(entries, project_root, timeout, sim_report):
    mem_guard = _sim_mem_guard_min_bytes()
    mem_aborted = False
    timed_out_abort = False
    executor = None
    for i, entry in enumerate(entries):
        _entry_name = getattr(entry, 'name', '<unknown>')
        _entry_kind = getattr(entry, 'kind', '?')
        if not mem_aborted and _trip_mem_guard(mem_guard):
            mem_aborted = True
        if executor is not None and getattr(executor, "closed", False):
            timed_out_abort = True
        if mem_aborted or timed_out_abort:
            _reason, _short = (("sandbox memory guard tripped", "memory guard")
                               if mem_aborted
                               else ("entry timeout", "entry timeout"))
            _skipped = ExecutionResult(entry=entry)
            _mark_entry_skipped(
                _skipped,
                f"skipped ({_reason})",
                f"{_entry_name}: skipped ({_short})")
            _finish_entry(sim_report, _skipped, _entry_name)
            continue
        logger.info(f"[Simulate] {i+1}/{len(entries)} 沙箱执行: {_entry_name} ({_entry_kind})")
        try:
            if executor is None or getattr(executor, "closed", False):
                executor = SandboxExecutor(project_root)
            result = executor.execute(entry, timeout=timeout)
        except Exception as e:  # noqa: BLE001
            logger.warning("[Simulate] 沙箱执行器异常（单入口隔离）: %s: %s", _entry_name, e)
            result = ExecutionResult(entry=entry)
            result.success = False
            result.error = str(e)[:_ERROR_TEXT_LIMIT]
            result.traceback = traceback.format_exc()
        _finish_entry(sim_report, result, _entry_name)
def _select_priority_entries(entries: list) -> tuple[list, int]:
    entries_discovered = len(entries)
    if len(entries) > _MAX_SIM_ENTRIES:
        entries.sort(key=lambda e: (_SIM_PRIORITY_ORDER.get(e.name, 99),
                                    os.path.normcase(str(e.filepath)), e.line))
        entries = entries[:_MAX_SIM_ENTRIES]
        logger.info(f"  [sim] 按优先级截取前 {_MAX_SIM_ENTRIES} 个入口点")
    return entries, entries_discovered
def _discover_entries(project_root: str, ctx) -> tuple[list, int]:
    logger.info("[Simulate] 发现入口点...")
    entries = _SimEntryPointDiscoverer(
        project_root, exclude_test_files=True, ctx=ctx).discover()
    logger.info(f"  发现 {len(entries)} 个入口点")
    entries, discovered = _select_priority_entries(entries)
    if not entries:
        logger.info("  ⚠ 未发现入口点，回退到纯静态分析")
    return entries, discovered
@timed_log()
def simulate_and_diagnose(project_root: str,
                          timeout: float=_DEFAULT_ENTRY_TIMEOUT,
                          coverage_hook: Any=None, safe_mode: bool=True, *,
                          reuse: ReuseArtifacts | None=None,
                          ctx: Any=None) -> tuple[SimulationReport, Any]:
    project_root = normalize_project_root(project_root)
    entries, _entries_discovered = _discover_entries(project_root, ctx)
    reuse = reuse or ReuseArtifacts()
    _cg, coverage_hook = prepare_evidence_context(
        project_root, coverage_hook, reuse)
    sim_report = SimulationReport(project_root=project_root)
    sim_report.total_entry_points = len(entries)
    sim_report.entries_discovered = _entries_discovered
    sim_report.entries_truncated = max(0, _entries_discovered - len(entries))
    trace_edges = []
    if entries:
        if safe_mode:
            logger.info("[Simulate] safe_mode: exec 加载 + 运行时追踪...")
            tracer, _ = start_dynamic_tracer(
                project_root, engine_files=_ENGINE_FILES)
            trace_edges = _execute_safe_mode(
                entries, project_root, timeout, sim_report, tracer, ctx=ctx)
        else:
            _execute_sandbox_mode(entries, project_root, timeout, sim_report)
    save_coverage(coverage_hook, sim_report)
    return run_diagnosis(_cg, trace_edges,
                          sim_report, coverage_hook, reuse, ctx=ctx)
_SIM_ERRORS_SAMPLE_CAP = 10
def _call_or_value(obj, attr, default=None):
    value = getattr(obj, attr, default)
    return value() if callable(value) else value
def _normalize_sim_summary(sim_report) -> tuple[dict, bool]:
    if sim_report is None:
        return {}, False
    try:
        _summary_raw = _call_or_value(sim_report, "summary", {})
    except Exception as _sum_e:  # noqa: BLE001 — 病态 summary() 降级空表，不击穿通道
        logger.warning("[Simulate] sim_report.summary() 抛异常，降级空表: %s", _sum_e)
        return {}, False
    if not isinstance(_summary_raw, dict):
        if _summary_raw:
            logger.debug("sim_report.summary() 契约外形态（%s），降级空表",
                         type(_summary_raw).__name__)
        return {}, False
    return _jsonable(_summary_raw), True
_JSON_MAX_DEPTH = 12
def _record_field_is_plain(value) -> bool:
    if value is None or isinstance(value, (bool, int, float, str)):
        return True
    return isinstance(value, (list, tuple, set, frozenset, dict)) and not value
def _dataclass_scalar_record(value):
    if not (dataclasses.is_dataclass(value) and not isinstance(value, type)):
        return None
    record: dict = {}
    for _field in dataclasses.fields(value):
        _item = getattr(value, _field.name, None)
        if _field.name == "args" and isinstance(value, SimEntryPoint):
            record[str(_field.name)] = _item
            continue
        if not _record_field_is_plain(_item):
            return None
        record[str(_field.name)] = _item
    return record
def _jsonable(value, _depth: int = 0, _seen: set | None = None):
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    if isinstance(value, os.PathLike):
        return _jsonable(os.fspath(value), _depth + 1, _seen)
    if _depth >= _JSON_MAX_DEPTH:
        return f"<{type(value).__name__}>"
    _seen = set() if _seen is None else _seen
    marker = id(value)
    if marker in _seen:
        return f"<cycle:{type(value).__name__}>"
    _seen.add(marker)
    try:
        if isinstance(value, dict):
            return {str(_key): _jsonable(_item, _depth + 1, _seen)
                    for _key, _item in value.items()}
        if isinstance(value, (list, tuple)):
            return [_jsonable(_item, _depth + 1, _seen) for _item in value]
        if isinstance(value, (set, frozenset)):
            return sorted(
                (_jsonable(_item, _depth + 1, _seen) for _item in value),
                key=str)
        _record = _dataclass_scalar_record(value)
        if _record is not None:
            return {_key: _jsonable(_item, _depth + 1, _seen)
                    for _key, _item in _record.items()}
        try:
            _to_dict = getattr(value, "to_dict", None)
            if not callable(_to_dict):
                return f"<{type(value).__name__}>"
            _plain = _to_dict()
        except Exception as _plain_e:  # noqa: BLE001 — 病态 to_dict 降级 __dict__
            logger.debug(
                "通道载荷 to_dict 读取/调用失败，降级 __dict__: %s", _plain_e)
        else:
            if isinstance(_plain, (dict, list, tuple, set, frozenset)):
                return _jsonable(_plain, _depth + 1, _seen)
            return f"<{type(value).__name__}>"
        _mapping = getattr(value, "__dict__", None)
        if isinstance(_mapping, dict):
            return {str(_key): _jsonable(_item, _depth + 1, _seen)
                    for _key, _item in _mapping.items()}
        return f"<{type(value).__name__}>"
    finally:
        _seen.discard(marker)
def _normalize_bs_data(blindspot_report) -> dict:
    if blindspot_report is None:
        return {}
    if isinstance(blindspot_report, dict):
        _data = blindspot_report
    else:
        try:
            _data = (_call_or_value(blindspot_report, "to_dict")
                     if hasattr(blindspot_report, "to_dict")
                     else getattr(blindspot_report, "__dict__", None))
        except Exception as _bs_e:  # noqa: BLE001 — 病态 to_dict() 降级空表，不击穿通道
            logger.warning(
                "[Simulate] blindspot_report.to_dict() 抛异常，降级空表: %s", _bs_e)
            return {}
    if not isinstance(_data, dict):
        if _data:
            logger.debug("blindspot_report 契约外形态（%s），降级空表",
                         type(_data).__name__)
        return {}
    return {key: value for key, value in _jsonable(_data).items()
            if not str(key).startswith("_")}
def _normalize_sim_results(sim_report) -> list:
    _results = getattr(sim_report, "results", None)
    if not isinstance(_results, (list, tuple)):
        if _results:
            logger.debug("sim_report.results 契约外形态（%s），跳过遍历",
                         type(_results).__name__)
        _results = []
    return list(_results)
_TYPED_EXCEPTION_RE = re.compile(
    r":\s*(?:[A-Za-z_]\w*\.)*(?P<name>[A-Za-z_]\w*)\s*(?::|\()")
def sandbox_env_skip_reason(error: str, *, timed_out: bool = False) -> str:
    text = str(error or "")
    if timed_out:
        return "entry_timeout"
    if text.startswith("[SIM-SKIP]"):
        return text.removeprefix("[SIM-SKIP]").strip() or "entry_skipped"
    typed = _TYPED_EXCEPTION_RE.search(text)
    structured_skip = text.startswith("skipped (") or ": skipped (" in text
    if "entry timeout" in text and (structured_skip or typed is None):
        return "entry_timeout"
    if "sandbox memory guard" in text and (structured_skip or typed is None):
        return "memory_guard"
    if "沙箱禁止加载未注册模块" in text:
        return "unregistered_dependency"
    if ("No module named" in text
            and (typed is None or typed.group("name") == "ModuleNotFoundError")):
        return "missing_dependency"
    if typed is not None and typed.group("name") == "SystemExit":
        # CLI 入口用 SystemExit 表达退出码（0/1/2 契约），沙箱里捕获到它说明
        # 入口正常走到了进程边界，不是执行失败。
        return "entry_system_exit"
    return ""
def _sandbox_failure_item(r, skill_dir: str) -> dict:
    _e = getattr(r, "entry", None)
    _e_fp = str(getattr(_e, "filepath", "") or "")
    if _e_fp and skill_dir:
        _e_fp = safe_relpath(_e_fp, skill_dir)
    _entry_name = (getattr(_e, "name", "unknown")
                   if _e is not None else "unknown")
    _error = str(getattr(r, "error", None) or "unknown")[:_ERROR_TEXT_LIMIT]
    _message = (_error if _error.startswith(f"{_entry_name}:")
                else f"{_entry_name}: {_error}")
    return {
        "entry": _entry_name,
        "error": _error,
        "message": _message[:_ERROR_TEXT_LIMIT],
        "severity": "P2",
        "duration_sec": getattr(r, "duration_sec", 0),
        "rule_id": "SANDBOX-FAIL",
        "file": _e_fp,
        "line": getattr(_e, "line", 0) or 0,
    }
def _collect_sandbox_failures(_results, skill_dir: str) -> tuple:
    findings = []
    degraded_skipped = []
    for r in _results:
        if getattr(r, "success", True) and not getattr(r, "timed_out", False):
            continue
        _item = _sandbox_failure_item(r, skill_dir)
        _reason = sandbox_env_skip_reason(
            _item["error"], timed_out=bool(getattr(r, "timed_out", False)))
        if _reason:
            _item["degrade_reason"] = _reason
            degraded_skipped.append(_item)
        else:
            findings.append(_item)
    return findings, degraded_skipped
def _sandbox_verdict(findings, degraded_skipped, exec_n: int,
                     succ_n: int) -> tuple:
    _sb_status = "pass"
    if findings or (degraded_skipped and succ_n == 0 and exec_n > 0):
        _sb_status = "warn"
    _degrade_note = (f", {len(degraded_skipped)}入口因环境/沙箱策略限制跳过(降级)"
                     if degraded_skipped else "")
    return _sb_status, _degrade_note
def _collect_sim_errors(_results) -> list:
    _sim_errors_all: list[str] = []
    for _r in _results:
        _se_raw = getattr(_r, "sim_errors", None)
        if not isinstance(_se_raw, (list, tuple)):
            if _se_raw:
                logger.debug("sim_errors 契约外形态（%s），跳过收集",
                             type(_se_raw).__name__)
            continue
        _sim_errors_all.extend(
            str(_se)[:_ERROR_TEXT_LIMIT] for _se in _se_raw)
    return _sim_errors_all
def project_sandbox_channel(sim_report, blindspot_report,
                            skill_dir: str) -> dict:
    sim_summary, summary_available = _normalize_sim_summary(sim_report)
    bs_data = _normalize_bs_data(blindspot_report)
    _results = _normalize_sim_results(sim_report)
    findings, degraded_skipped = _collect_sandbox_failures(
        _results, skill_dir)
    dead_code_phases = getattr(sim_report, "dead_code_confirmation", None)
    if isinstance(dead_code_phases, dict):
        dead_code_phases = _jsonable(dead_code_phases)
    else:
        dead_code_phases = None
    _sim_exec = int_or(sim_summary.get("executed"))
    _sim_succ = int_or(sim_summary.get("succeeded"))
    _sb_status, _degrade_note = _sandbox_verdict(
        findings, degraded_skipped, _sim_exec, _sim_succ)
    if sim_report is None:
        _sb_status = "warn"
        _degrade_note = ", 模拟报告缺失（无执行证据，降级）"
    elif not summary_available:
        _sb_status = "warn"
        _degrade_note = ", 模拟摘要不可用（无有效汇总证据，降级）"
    elif _sim_exec > 0 and not _results:
        _sb_status = "warn"
        _degrade_note = ", 模拟入口结果缺失（无逐项执行证据，降级）"
    _sim_errors_all = _collect_sim_errors(_results)
    return {
        "status": _sb_status,
        "findings_count": len(findings),
        "summary": (
            f"D3 沙箱模拟: {_sim_exec}执行/"
            f"{_sim_succ}成功/"
            f"{int_or(sim_summary.get('failed'))}失败, {len(findings)}项发现"
            f"{_degrade_note}"
        ),
        "sim_errors_count": len(_sim_errors_all),
        "sim_errors_sample": _sim_errors_all[:_SIM_ERRORS_SAMPLE_CAP],
        "entries_discovered": int_or(sim_summary.get("entries_discovered")),
        "entries_truncated": int_or(sim_summary.get("entries_truncated")),
        "simulation": sim_summary,
        "blindspots": bs_data,
        "findings": findings,
        "degraded_skipped": degraded_skipped,
        "dead_code_phases": dead_code_phases,
    }
def save_coverage(coverage_hook, sim_report) -> None:
    if not coverage_hook or sim_report is None:
        return
    try:
        coverage_hook.snapshot()
    except (OSError, RuntimeError, AttributeError):
        logger.debug(
            "suppressed OSError/RuntimeError/AttributeError in save_coverage",
            exc_info=True)
    try:
        sim_report.coverage_data = coverage_hook.data
    except (OSError, KeyError, RuntimeError, AttributeError) as e:
        logger.warning("[Simulate] 收割覆盖率数据失败,置空: %s", e)
        sim_report.coverage_data = {}
    try:
        coverage_hook.pause()
    except (OSError, RuntimeError, AttributeError):
        logger.debug(
            "suppressed OSError/RuntimeError/AttributeError in save_coverage",
            exc_info=True)

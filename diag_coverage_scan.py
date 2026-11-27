from __future__ import annotations

import argparse
import ast
import gc
import importlib.util
import json
import logging
import os
import re
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any, NamedTuple

import coverage as _coverage

from jwsgj.prevention_scope_facts import walk_nodes

from .diag_coverage_runtime import (
    _CLEAR_ADDOPTS,
    _MANAGED_HOOK_PTH_NAMES,
    _NO_CACHE_PROVIDER_ARGS,
    _PREWARM_TIMEOUT_S,
    _PYTEST_NO_TESTS_COLLECTED,
    _PYTEST_QUIET,
    DEFAULT_CACHE_MAX_AGE_S,
    DEFAULT_WAIT_TIMEOUT_S,
    DEFAULT_WORKERS,
    MIN_COPY_LINE_RECORDS,
    ScanStepError,
    _as_int_or_none,
    _atomic_write_json,
    _discover_default_tests_dir,
    _gov_observables,
    _iter_test_source_files,
    _measure_env,
    _norm_timeout_s,
    _pytest_failure_warning,
    _release_hook_once,
    _require_path_like,
    _resolve_tests_dir,
    _scan_artifact_fields,
    _ScanContext,
    _try_coordination_cache,
    _validate_scan_inputs,
    audit_combine_copies,
    build_scan_rc,
    cleanup_consumed_coverage_data,
    coordination_exit,
    coordination_publish,
    detect_collection_corruption,
    ensure_autostart_hook,
    new_run_dir,
    prepare_branch_combine_dir,
    resolve_effective_workers,
    scan_base_dir,
    write_covsave_plugin,
)
from .diag_guard_io import (
    SourceReadError,
    read_source_text_strict,
    two_level_unlink,
)
from .diag_self_check import current_process_rss_mb
from .diag_testing_coverage import (
    DEFAULT_COVERAGE_THRESHOLD,
    _normalize_count_text,
    history_variance_warning,
    locate_pytest_summary_line,
    parse_pytest_summary_counts,
    step_err,
    step_ok,
    step_skip,
    summarize_coverage_report,
)
from .diag_types_normalize import (
    as_number,
    int_or,
)
from .html_render_pipeline import emit_step_html
from .log_config import (
    get_module_logger,
    log_swallowed,
)

try:
    import psutil
except ImportError as _imp_err:
    psutil = None  # type: ignore[assignment]
    logging.getLogger(__name__).debug(
        "[diag_coverage_scan] psutil 导入失败，进程治理降级空操作: %s",
        _imp_err)
_log = get_module_logger(__name__, __file__)
__all__ = [
    "DEFAULT_COVERAGE_THRESHOLD",
    "CommandTimeoutError",
    "collect_suite_stats",
    "main",
    "profile_test_performance",
    "pytest_command",
    "run_command",
    "run_governed",
    "sample_slow_tests",
    "scan_parametrize_tail",
    "scan_serial_wait_surface",
    "scan_test_coverage",
    "xdist_available",
]
def _step1_prepare_env(ctx: _ScanContext) -> dict | None:
    _log.info("[scanner] step 1/7 钩子与环境准备")
    ctx.run_dir = new_run_dir(scan_base_dir(ctx.data_dir, ctx.root))
    ctx.rc = build_scan_rc(ctx.run_dir, ctx.root)
    plugin = write_covsave_plugin(ctx.run_dir)
    hook_error = _install_scan_hook(ctx)
    if hook_error is not None:
        return hook_error
    ctx.env = _compose_scan_env(ctx.run_dir, ctx.rc, plugin)
    return None
def _is_managed_autostart_hook(hook: dict) -> bool:
    hook_path = hook.get("hook")
    if not isinstance(hook_path, (str, os.PathLike)):
        return False
    try:
        return Path(hook_path).name in _MANAGED_HOOK_PTH_NAMES
    except (OSError, TypeError, ValueError) as exc:
        _log.debug("[scanner] 钩子路径不可判读（按第三方钩子保留）: %r (%s)",
                   hook_path, exc)
        return False
def _reuse_scan_hook(ctx: _ScanContext, hook: dict) -> None:
    ctx.warnings.append(f"复用既有自启动钩子: {hook.get('hook', '?')}")
    ctx.hook_cleanup_pending = _is_managed_autostart_hook(hook)
def _install_scan_hook(ctx: _ScanContext) -> dict | None:
    hook = ensure_autostart_hook(dry_run=True)
    if hook.get("error"):
        return step_err(f"自启动钩子不可用: {hook['error']}", hook)
    if hook.get("reused"):
        _reuse_scan_hook(ctx, hook)
    elif hook.get("would_install"):
        real = ensure_autostart_hook(dry_run=False)
        if real.get("reused"):
            _reuse_scan_hook(ctx, real)
        elif not real.get("installed"):
            return step_err(
                f"自启动钩子安装失败: {real.get('error') or '未知原因'}", real)
        else:
            ctx.warnings.append(f"已安装自启动钩子: {real['hook']}")
            ctx.hook_cleanup_pending = True
    return None
def _compose_scan_env(run_dir: Path, rc: Path, plugin: Path) -> dict:
    env = _measure_env()
    env["COVERAGE_PROCESS_START"] = str(rc)
    env["COVERAGE_FILE"] = str(run_dir / ".coverage")
    plugin_dir = str(plugin.parent)
    env["PYTHONPATH"] = (
        plugin_dir + os.pathsep + env["PYTHONPATH"]
        if env.get("PYTHONPATH") else plugin_dir)
    return env
def _step2_prewarm(ctx: _ScanContext) -> dict | None:
    _log.info("[scanner] step 2/7 串行预热收集")
    if ctx.skip_prewarm:
        return None
    prewarm_env = dict(ctx.env)
    prewarm_env.pop("COVERAGE_PROCESS_START", None)
    try:
        rc_pre, out_pre = run_command(
            pytest_command(ctx.tdir, "--collect-only", "-q",
                            *_MEASURE_BASE_ARGS),
            cwd=str(ctx.root), env=prewarm_env, timeout=_PREWARM_TIMEOUT_S)
    except CommandTimeoutError as _e:
        _log.debug(
            '静默降级[_step2_prewarm:CommandTimeout]: %s: %s',
            type(_e).__name__, _e)
        ctx.warnings.append(
            f"预热收集超时（>{_PREWARM_TIMEOUT_S}s），已降级跳过预热"
            "直接并行主跑；若触发 xdist 收集不一致可重试")
        return None
    if rc_pre != 0:
        if rc_pre == _PYTEST_NO_TESTS_COLLECTED:
            return step_skip(
                "未收集到任何用例（空测试目录或全部被忽略），覆盖率扫描不适用",
                {"returncode": rc_pre, "log_tail": out_pre[-2000:]})
        return step_err("预热收集失败（先修收集错误再扫描）",
                    {"returncode": rc_pre,
                     "log_tail": out_pre[-2000:]})
    return None
def _run_failure(message: str, gov: dict, log: str | None = None,
                 **detail) -> dict:
    payload: dict = {"resource_governance": _gov_observables(gov)}
    if log is not None:
        payload["log_tail"] = log[-2000:]
    payload.update(detail)
    return step_err(message, payload)
def _classify_run_outcome(ctx: _ScanContext, rcode: int,
                           log: str, gov: dict) -> dict | None:
    ctx.pytest_log = log
    ctx.gov = gov
    gov["pytest_returncode"] = rcode
    if gov["sweep_degraded"]:
        ctx.warnings.append(
            "进程治理能力降级（psutil 缺失、快照/身份校验不可用或终止未确认）："
            "资源采样与孤儿清扫可能不完整（超时树终止已尝试系统级兜底；"
            "psutil 缺失时建议 pip install psutil）")
    if gov["timed_out"]:
        if gov.get("tree_terminated") is False:
            message = (
                f"pytest 主跑超时（timeout_s={ctx.timeout_s}），"
                "未能确认完整终止进程树；已回收 "
                f"{len(gov['orphans_swept'])} 个残留进程"
            )
        else:
            message = (
                f"pytest 主跑超时（timeout_s={ctx.timeout_s}），已终止整个"
                f"进程树并回收 {len(gov['orphans_swept'])} 个残留进程"
            )
        return _run_failure(
            message, gov, log, timeout_s=ctx.timeout_s)
    if gov["orphans_swept"]:
        ctx.warnings.append(
            f"已回收 {len(gov['orphans_swept'])} 个残留进程: "
            f"{gov['orphans_swept'][:10]}")
    if rcode == _PYTEST_NO_TESTS_COLLECTED:
        return step_skip(
            "未收集到任何用例（空测试目录或全部被忽略），覆盖率扫描不适用",
            {"returncode": rcode, "log_tail": log[-2000:],
             "resource_governance": _gov_observables(gov)})
    failure_warning = _pytest_failure_warning(rcode)
    if failure_warning:
        ctx.warnings.append(failure_warning)
    if rcode not in (0, 1):
        return _run_failure(f"pytest 异常退出 code={rcode}", gov, log)
    if rcode != 0:
        corrupt_marker = detect_collection_corruption(
            _normalize_count_text(log))
        if corrupt_marker:
            return _run_failure(
                f"pytest 收集阶段异常（命中特征「{corrupt_marker}」）："
                "测试集不完整，覆盖率数字失真不可信，已拒绝产出报告；"
                "请重试扫描，复现则以 workers=1 串行验证或检查并发写 tests/",
                gov, log, corruption_marker=corrupt_marker)
    return None
def _resolve_scan_workers(ctx: _ScanContext) -> str | int:
    workers_eff = resolve_effective_workers(ctx.workers, ctx.max_workers)
    budget = (_as_int_or_none(ctx.coord_ctx.get("budget_workers"))
              if ctx.coord_ctx else None)
    is_auto = (isinstance(ctx.workers, str)
               and ctx.workers.strip().lower() == DEFAULT_WORKERS)
    if (budget is not None and budget > 0
            and is_auto and workers_eff != 0):
        workers_eff = max(1, min(int(workers_eff), budget))
    return workers_eff
def _step3_full_run(ctx: _ScanContext) -> dict | None:
    _log.info("[scanner] step 3/7 全量运行（workers=%s, max_workers=%s）",
              ctx.workers, ctx.max_workers)
    workers_eff = _resolve_scan_workers(ctx)
    if workers_eff != 0 and not xdist_available():
        ctx.warnings.append(
            "pytest-xdist 未安装：并行度请求降级为串行（0），"
            "pip install pytest-xdist 可恢复并行采集")
        workers_eff = 0
    ctx.workers_eff = workers_eff
    cmd = pytest_command(ctx.tdir, *_PYTEST_QUIET, "-p", "covsave_plugin",
                         *_CLEAR_ADDOPTS)
    if workers_eff != 0:
        cmd += ["-n", str(workers_eff), "--dist", "loadscope"]
    try:
        rcode, log, gov = run_governed(cmd, cwd=str(ctx.root), env=ctx.env,
                                        timeout_s=ctx.timeout_s)
    finally:
        _release_hook_once(ctx)
    return _classify_run_outcome(ctx, rcode, log, gov)
def _step4_audit_copies(ctx: _ScanContext) -> None:
    _log.info("[scanner] step 4/7 副本有效性审计")
    audit = audit_combine_copies(ctx.run_dir)
    ctx.audit = audit
    if audit["copies"] == 0:
        raise ScanStepError(
            4, "检查 COVERAGE_FILE 与 rc data_file 是否同路径、"
               "worker 是否被硬杀在保存前",
            f"run_dir 内无 worker 副本落盘（run_dir={ctx.run_dir}）")
    if audit["unreadable"] == audit["copies"]:
        ctx.warnings.append(
            f"[强指纹] 全部 {audit['copies']} 份副本不可读"
            f"（如 {audit['unreadable_names'][0]}）——无可合并数据，"
            "合并将失败关闭")
    elif audit["valid"] == 0 and audit["suspect"] == 0:
        ctx.warnings.append(
            f"[强指纹] {audit['copies']} 份副本均无可合并的 branch 数据"
            f"（statement={audit['statement_only']}, empty={audit['empty']}）"
            "——合并将失败关闭；请确认采集口径为 branch=True")
    elif audit["valid"] == 0:
        ctx.warnings.append(
            f"[强指纹] 全部 {audit['suspect']} 份 branch 副本行记录 < "
            f"{MIN_COPY_LINE_RECORDS}——worker 测量可能整体失效，"
            "覆盖率数字不可信（非迷你项目时务必串行单文件交叉验证）")
    elif audit["suspect"] > 0:
        ctx.warnings.append(
            f"{audit['suspect']}/{audit['copies']} 份副本行记录较少"
            "（被测代码 subprocess 的 import 面，属正常）；"
            f"有效副本 {audit['valid']} 份、行记录总量 "
            f"{audit['total_line_records']}")
    if audit["unreadable"] and audit["unreadable"] != audit["copies"]:
        ctx.warnings.append(
            f"[强指纹] {audit['unreadable']}/{audit['copies']} 份副本损坏"
            f"不可读（如 {audit['unreadable_names'][0]}）：已跳过合并，"
            "覆盖率可能低估")
def _combine_data_paths(run_dir: Path, prep: dict) -> list[str]:
    staging = run_dir / "_combine_branch"
    paths = [str(staging / name) for name in prep.get("staged_names") or []]
    paths.extend(str(run_dir / name)
                 for name in prep.get("failed_names") or [])
    return paths
def _warn_skipped_sidecars(ctx: _ScanContext, prep: dict) -> None:
    if prep["stmt_skipped"]:
        ctx.warnings.append(
            f"已隔离 {prep['stmt_skipped']} 份非 branch 口径副本"
            f"（statement sidecar，如 {prep['skipped_names'][0] if prep['skipped_names'] else '?'}），"
            "防 combine 混合口径失败；其行记录未计入本次报告")
    if prep["empty"]:
        ctx.warnings.append(
            f"已跳过 {prep['empty']} 份空副本（无行记录、无分支数据），"
            "不计入合并输入")
def _step5_combine(ctx: _ScanContext) -> None:
    _log.info("[scanner] step 5/7 合并副本")
    prep = prepare_branch_combine_dir(ctx.run_dir)
    _warn_skipped_sidecars(ctx, prep)
    data_paths = _combine_data_paths(ctx.run_dir, prep)
    if not data_paths:
        raise ScanStepError(
            5, "确认采集口径为 branch=True（检查 rc 的 branch 配置与 "
               "COVERAGE_PROCESS_START 注入）后重跑；本扫描器只能产出 "
               "branch 口径报告",
            f"无可合并的 branch 口径副本（scanned={prep['scanned']}, "
            f"statement={prep['stmt_skipped']}, empty={prep['empty']}, "
            f"failed={prep['failed']}, unreadable={prep['unreadable']}）")
    ctx.dfm = ctx.run_dir / ".coverage"
    try:
        if ctx.dfm.exists() and not two_level_unlink(ctx.dfm):
            raise OSError("预置合并数据删除被拒（占用或跨盘中转不可达）")
        ctx.cvm = _coverage.Coverage(data_file=str(ctx.dfm), branch=True,
                                     config_file=False)
        ctx.cvm.combine(data_paths=data_paths)
        ctx.cvm.save()
    except Exception as exc:
        raise ScanStepError(
            5, "换新 --data-dir 重试（run_dir 版本化下同一 data_dir 直接"
               "重跑也可自愈）；若复现请检查目录权限与副本基名",
            f"{type(exc).__name__}: {exc}") from exc
def _absolutize_report_file_keys(report: dict,
                                 project_root: str | Path | None = None
                                 ) -> dict:
    files = report.get("files") if isinstance(report, dict) else None
    if not isinstance(files, dict):
        return report
    base = Path(project_root) if project_root is not None else None
    fixed: dict = {}
    for key, value in files.items():
        if isinstance(key, str) and not os.path.isabs(key):
            fixed[str((base / key).resolve()) if base is not None
                  else os.path.abspath(key)] = value
        else:
            fixed[key] = value
    report["files"] = fixed
    return report
def release_coverage_objects(*objs) -> float:
    before = current_process_rss_mb()
    for obj in objs:
        if obj is None:
            continue
        try:
            data = obj.get_data() if hasattr(obj, "get_data") else obj
            if hasattr(data, "close"):
                data.close()
        except Exception:  # noqa: BLE001
            _log.debug("[scanner] coverage 对象释放失败(不阻断)", exc_info=True)
    gc.collect()
    after = current_process_rss_mb()
    return max(0.0, before - after)
def _step6_report(ctx: _ScanContext) -> None:
    _log.info("[scanner] step 6/7 生成 JSON 报告")
    ctx.json_path = ctx.run_dir / "coverage_scan.json"
    try:
        ctx.cr = _coverage.Coverage(data_file=str(ctx.dfm),
                                    source=[str(ctx.root)],
                                    branch=True, config_file=False)
        ctx.cr.load()
        ctx.cr.config.ignore_errors = True
        ctx.cr.json_report(outfile=str(ctx.json_path))
        with open(ctx.json_path, encoding="utf-8") as fh:  # jwsgj:suppress TAINT
            ctx.report = json.load(fh)
        ctx.report = _absolutize_report_file_keys(ctx.report, ctx.root)
        _atomic_write_json(ctx.json_path, ctx.report)
    except Exception as exc:
        raise ScanStepError(
            6, "核对 workers_data.valid>0、合并数据可读与磁盘空间；无数据多"
               "为采集口径或副本全不可读，换 --data-dir 重跑可排除残留",
            f"{type(exc).__name__}: {exc}") from exc
    ctx.gc_reclaimed_mb = release_coverage_objects(ctx.cr, ctx.cvm)
    ctx.cr = ctx.cvm = None
    ctx.consumed_cleanup = cleanup_consumed_coverage_data(ctx.run_dir)
def _resource_governance_view(ctx: _ScanContext) -> dict:
    return {
        "workers_effective": ctx.workers_eff,
        "max_workers": ctx.max_workers,
        "peak_rss_mb": ctx.gov["peak_rss_mb"],
        "avg_cpu_cores": ctx.gov["avg_cpu_cores"],
        "tree_procs_peak": ctx.gov["tree_procs_peak"],
        "orphans_swept": ctx.gov["orphans_swept"],
        "sweep_degraded": ctx.gov["sweep_degraded"],
        "pytest_returncode": ctx.gov.get("pytest_returncode"),
        "hook_recycled": ctx.hook_recycled,
        "hook_recycle_error": ctx.hook_err,
        "gc_reclaimed_mb": round(ctx.gc_reclaimed_mb, 1),
        "consumed_data_cleanup": ctx.consumed_cleanup,
    }
def _step7_summarize(ctx: _ScanContext) -> dict:
    _log.info("[scanner] step 7/7 缺口汇总")
    summary = summarize_coverage_report(ctx.report, threshold=ctx.threshold,
                                        scope="source",
                                        project_root=str(ctx.root))
    _hv = history_variance_warning(ctx.coord_ctx,
                                    summary["totals"]["percent"])
    if _hv:
        ctx.warnings.append(_hv)
    summary.update({
        **_scan_artifact_fields(ctx.run_dir, ctx.json_path),
        "workers_data": ctx.audit,
        "warnings": ctx.warnings,
        "resource_governance": _resource_governance_view(ctx),
        "pytest_tail": "\n".join(ctx.pytest_log.strip().splitlines()[-3:]),
    })
    if ctx.coord_ctx:
        try:
            coordination_publish(ctx.coord_ctx, ctx.report, summary,
                                  ctx.root, ctx.threshold, ctx.tdir)
        except Exception:  # noqa: BLE001
            _log.warning("[scanner] 协调登记写入失败(不阻断)",
                         exc_info=True)
    return step_ok(summary, f"覆盖率扫描完成: 总体 {summary['totals']['percent']}%, "
                        f"{summary['below_count']}/{summary['module_count']} 模块低于 {ctx.threshold}%")
def _finalize_scan_context(ctx: _ScanContext) -> None:
    if ctx.cr is not None or ctx.cvm is not None:
        release_coverage_objects(ctx.cr, ctx.cvm)
    try:
        if ctx.coord_ctx:
            try:
                coordination_exit(ctx.coord_ctx)
            except Exception:  # noqa: BLE001
                _log.warning("[scanner] 协调层退出异常(不阻断)",
                             exc_info=True)
    finally:
        _release_hook_once(ctx)
def _run_precheck_steps(ctx: _ScanContext) -> dict | None:
    for step in (_step1_prepare_env, _step2_prewarm, _step3_full_run):
        step_error = step(ctx)
        if step_error is not None:
            return step_error
    return None
def _scan_test_coverage_impl(ctx: _ScanContext,
                             project_dir: str | Path,
                             tests_dir: str | Path | None = None,
                             ) -> dict:
    try:
        root, tdir, input_error = _validate_scan_inputs(
            project_dir, tests_dir, ctx.threshold)
        if input_error is not None:
            return input_error
        ctx.root = root
        ctx.tdir = tdir
        cached = _try_coordination_cache(ctx)
        if cached is not None:
            return cached
        step_error = _run_precheck_steps(ctx)
        if step_error is not None:
            return step_error
        _step4_audit_copies(ctx)
        _step5_combine(ctx)
        _step6_report(ctx)
        return _step7_summarize(ctx)
    except ScanStepError as exc:
        _log.warning("[scanner] 覆盖率扫描失败[步骤 %s/7]: %s", exc.step, exc.detail)
        return step_err(f"覆盖率扫描失败[步骤 {exc.step}/7] {exc.detail}。建议: {exc.advice}",
                    {"step": exc.step, "advice": exc.advice})
    except Exception as exc:  # noqa: BLE001
        _log.warning("[scanner] 覆盖率扫描顶层兜底异常: %s", exc, exc_info=True)
        return step_err(f"覆盖率扫描失败: {exc}")
    finally:
        _finalize_scan_context(ctx)
def _emit_coverage_scan_html(result: dict, project_dir) -> None:
    try:
        payload = dict(result) if isinstance(result, dict) else {
            "status": "error", "message": str(result)[:500]}
        payload.setdefault("project_dir", str(project_dir))
        emit_step_html("coverage_scan", str(project_dir), payload)
    except Exception as _che:  # noqa: BLE001
        _log.warning("[scanner] 覆盖率扫描 HTML 报告生成失败(不阻断): %s", _che)
def _emit_profile_html(result: dict, project_dir) -> None:
    try:
        emit_step_html("perf_profile", str(project_dir), result)
    except Exception as exc:  # noqa: BLE001
        _log.warning("[scanner] 测试性能画像 HTML 报告生成失败(不阻断): %s", exc)

def scan_test_coverage(project_dir: str | Path,
                       tests_dir: str | Path | None = None,
                       threshold: float = DEFAULT_COVERAGE_THRESHOLD,
                       workers: str | int = DEFAULT_WORKERS,
                       max_workers: int | None = None,
                       data_dir: str | Path | None = None,
                       coordination: bool = True,
                       force_refresh: bool = False,
                       force_parallel: bool = False,
                       wait_timeout_s: float = DEFAULT_WAIT_TIMEOUT_S,
                       cache_max_age_s: float = DEFAULT_CACHE_MAX_AGE_S,
                       skip_prewarm: bool = False,
                       timeout_s: int | None = None,
                       ) -> dict:
    ctx = _ScanContext(
        threshold=threshold, workers=workers, max_workers=max_workers,
        data_dir=data_dir, coordination=coordination,
        force_refresh=force_refresh, force_parallel=force_parallel,
        wait_timeout_s=wait_timeout_s, cache_max_age_s=cache_max_age_s,
        skip_prewarm=skip_prewarm, timeout_s=timeout_s)
    _result = _scan_test_coverage_impl(ctx, project_dir,
                                       tests_dir=tests_dir)
    _emit_coverage_scan_html(_result, project_dir)
    return _result
_SLOW_TEST_THRESHOLD_S = 0.30
_SERIAL_ADVICE_MIN_CALLS = 30
_COLLECT_ADVICE_MIN_S = 15.0
_DEFAULT_SLOW_TEST_TOP_N = 10
_PARAMETRIZE_TAIL_TOP_N = 10
_DEFAULT_PROFILE_SAMPLE_TOP = 3
_DURATION_NUM = r"\d+(?:\.\d+)?"
_COLLECT_TIMEOUT_S = 180
_SAMPLE_TIMEOUT_S = 300
_MEASURE_BASE_ARGS = (*_NO_CACHE_PROVIDER_ARGS, *_CLEAR_ADDOPTS)
def _measure_cmd(target: str | None, *args: str) -> list[str]:
    base = (pytest_command(target) if target is not None
            else [sys.executable, "-m", "pytest"])
    return [*base, *args, *_MEASURE_BASE_ARGS]
def _run_pytest_guarded(cmd: list[str], project_dir: str | Path, *,
                        timeout: float, env: dict, label: str,
                        target, timeout_hint: str = ""):
    try:
        rcode, output = run_command(
            cmd, cwd=str(project_dir), env=env, timeout=timeout)
        return (rcode, output), "", ""
    except CommandTimeoutError:
        _log.warning("%s超时（>%ss）%s: %s",
                     label, timeout, timeout_hint, target)
        return None, "timeout", f"{label}超时（>{timeout}s）{timeout_hint}"
    except OSError as _oe:
        _log.warning("%s执行失败: %s, target=%s", label, _oe, target)
        return None, "error", f"{label}执行失败: {_oe}"
_SERIAL_CALL_PATTERNS = (
    "subprocess", "Popen", "check_output", "os.system", "os.popen",
    "requests", "httpx", "urllib", "socket", "time.sleep",
)
_SERIAL_FUNC_NAMES = frozenset(
    p.split(".")[-1] for p in _SERIAL_CALL_PATTERNS)
_SERIAL_MODULE_ROOTS = frozenset(
    p for p in _SERIAL_CALL_PATTERNS if "." not in p)
def _callee_root_name(node: ast.AST) -> str | None:
    while isinstance(node, ast.Attribute):
        node = node.value
    return node.id if isinstance(node, ast.Name) else None
def _is_serial_call(node: ast.Call,
                    imported_names: frozenset[str] = frozenset()) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in _SERIAL_FUNC_NAMES or func.id in imported_names
    if not isinstance(func, ast.Attribute):
        return False
    if func.attr in _SERIAL_FUNC_NAMES:
        return True
    root_name = _callee_root_name(func.value)
    return root_name in _SERIAL_MODULE_ROOTS or root_name in imported_names
def _serial_import_names(tree: ast.AST) -> frozenset[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module_root = alias.name.split(".", 1)[0]
                if module_root in _SERIAL_MODULE_ROOTS:
                    names.add(alias.asname or module_root)
            continue
        if (not isinstance(node, ast.ImportFrom) or node.level != 0
                or node.module is None):
            continue
        module_root = node.module.split(".", 1)[0]
        for alias in node.names:
            if alias.name == "*":
                continue
            if (module_root in _SERIAL_MODULE_ROOTS
                    or alias.name in _SERIAL_FUNC_NAMES):
                names.add(alias.asname or alias.name)
    return frozenset(names)
class _ParsedTestFile(NamedTuple):
    path: Path
    src: str
    tree: ast.AST
def _analyze_test_file(parsed: _ParsedTestFile, root: Path) -> dict:
    serial_calls = 0
    parametrize_n = 0
    imported_names = _serial_import_names(parsed.tree)
    for node in walk_nodes(parsed.tree):
        if (isinstance(node, ast.Call)
                and _is_serial_call(node, imported_names)):
            serial_calls += 1
        elif isinstance(node, ast.Attribute) and node.attr == "parametrize":
            parametrize_n += 1
    loc = len(parsed.src.splitlines())
    try:
        _rel_name = parsed.path.relative_to(root).as_posix()
    except ValueError as _ve:
        log_swallowed(__name__, _ve, context='scan_serial_wait_surface:relative_to')
        _log.debug("scan_serial_wait_surface: relative_to 失败，回退文件名: %s", _ve)
        _rel_name = parsed.path.name
    return {
        "file": _rel_name,
        "serial_calls": serial_calls,
        "parametrize": parametrize_n,
        "loc": loc,
        "serial_density": round(serial_calls / max(loc, 1) * 1000, 2),
    }
def scan_serial_wait_surface(tests_dir: str | Path) -> dict:
    _require_path_like(tests_dir, "tests_dir")
    if not str(tests_dir).strip():
        raise FileNotFoundError(f"tests_dir 不得为空白路径: {tests_dir!r}")
    _root = Path(tests_dir)
    if not _root.is_dir():
        raise FileNotFoundError(f"tests_dir 不存在或不是目录: {_root}")
    rows = []
    _test_paths = _iter_test_source_files(_root)
    for path in _test_paths:
        try:
            src = read_source_text_strict(str(path))
            tree = ast.parse(src)
        except (SyntaxError, ValueError, SourceReadError,
                RecursionError, MemoryError) as _se:
            _log.warning("scan_serial_wait_surface: 测试文件语法/编码不可用，画像跳过 %s: %s", path, _se)
            continue
        except OSError as _oe:
            _log.debug("scan_serial_wait_surface: suppressed OSError: %s", _oe)
            continue
        rows.append(_analyze_test_file(_ParsedTestFile(path, src, tree), _root))
    rows.sort(key=lambda r: (-r["serial_calls"], -r["parametrize"]))
    return {"files_scanned": len(rows), "files": rows}
def scan_parametrize_tail(tests_dir: str | Path,
                          surface: dict | None = None) -> dict:
    if surface is None:
        surface = scan_serial_wait_surface(tests_dir)
    elif not isinstance(surface, dict):
        surface = {}
    rows = surface.get("files")
    if not isinstance(rows, list):
        return {"top_files": []}
    ranked = [row for row in rows if _is_parametrized_row(row)]
    ranked.sort(key=lambda row: -row["parametrize"])
    return {"top_files": ranked[:_PARAMETRIZE_TAIL_TOP_N]}
def _is_parametrized_row(row: Any) -> bool:
    if not isinstance(row, dict):
        return False
    count = row.get("parametrize")
    return (isinstance(count, int) and not isinstance(count, bool)
            and count > 0)
def collect_suite_stats(project_dir: str | Path,
                        timeout: int = _COLLECT_TIMEOUT_S, *,
                        tests_dir: str | Path | None = None) -> dict:
    _require_path_like(tests_dir, "tests_dir", allow_none=True)
    _timeout = as_number(timeout, 0.0)
    timeout = _timeout if _timeout > 0 else _COLLECT_TIMEOUT_S
    target = None if tests_dir is None else str(tests_dir)
    cmd = _measure_cmd(target, "--collect-only", "-q")
    t0 = time.perf_counter()
    proc, _status, _detail = _run_pytest_guarded(
        cmd, project_dir, timeout=timeout, env=_measure_env(),
        label="收集", target=project_dir,
        timeout_hint="，import 开销异常偏大")
    if proc is None:
        return {"test_count": None, "collect_seconds": None,
                "status": _status, "detail": _detail}
    elapsed = round(time.perf_counter() - t0, 2)
    rcode, output = proc
    normalized_output = _normalize_count_text(output)
    m = re.search(r"\b(\d[\d,]*) tests? collected\b", normalized_output)
    count = (int(m.group(1).replace(",", "")) if m
             else 0 if rcode == _PYTEST_NO_TESTS_COLLECTED else None)
    status = ("skipped" if rcode == _PYTEST_NO_TESTS_COLLECTED
              else "ok" if rcode == 0 else "error")
    _tail = output.strip()
    return {"test_count": count, "collect_seconds": elapsed,
            "status": status,
            "detail": _tail.splitlines()[-1] if _tail else ""}
def _per_test_durations(stdout: str) -> dict[str, float]:
    _per_test: dict[str, float] = {}
    for m in re.finditer(
            r"^(" + _DURATION_NUM + r")s (?:setup|call|teardown)\s+(.+?)\s*$",
            stdout, re.MULTILINE):
        _per_test[m.group(2)] = _per_test.get(m.group(2), 0.0) \
            + float(m.group(1))
    return _per_test
def _summary_line_stats(stdout: str) -> tuple[float | None, int]:
    summary = locate_pytest_summary_line(stdout)
    if not summary:
        return (None, 0)
    sm = re.search(r"\bin (" + _DURATION_NUM + r")s", summary)
    if sm is None:
        return (None, 0)
    passed = parse_pytest_summary_counts(summary)["passed"]
    return (round(float(sm.group(1)), 2), passed)
def _parse_durations_output(stdout: str, top_n: int) -> dict:
    slow = [{"id": _tid, "seconds": round(_secs, 2)}
            for _tid, _secs in _per_test_durations(stdout).items()
            if _secs >= _SLOW_TEST_THRESHOLD_S]
    slow.sort(key=lambda _r: -_r["seconds"])
    seconds, passed = _summary_line_stats(stdout)
    return {"seconds": seconds, "passed": passed,
            "slow_tests": slow[:top_n]}
def _failed_sample(name: str, note: str) -> dict:
    return {"file": name, "seconds": None, "passed": 0,
            "slow_tests": [], "note": note}
def _sample_one_file(project_dir: str | Path, name: str, target: str,
                     top_n: int, env: dict) -> dict:
    cmd = _measure_cmd(target, "--durations=0", "-q")
    proc, _status, _detail = _run_pytest_guarded(
        cmd, project_dir, timeout=_SAMPLE_TIMEOUT_S, env=env,
        label="采样", target=name,
        timeout_hint="本身即为瓶颈信号")
    if proc is None:
        return _failed_sample(name, _detail)
    _rcode, output = proc
    if _rcode != 0:
        tail = output.strip().splitlines()[-1] if output.strip() else "无输出"
        return _failed_sample(
            name, f"采样 pytest 退出码 {_rcode}，结果无效: {tail}")
    return {"file": name, **_parse_durations_output(output, top_n)}
def sample_slow_tests(project_dir: str | Path,
                      files: list[str],
                      tests_dir: str | Path,
                      top_n: int = _DEFAULT_SLOW_TEST_TOP_N) -> dict:
    _require_path_like(tests_dir, "tests_dir")
    if not isinstance(files, list):
        _fe = TypeError(
            f"files 必须为 list，实际 {type(files).__name__}")
        log_swallowed(__name__, _fe, context='sample_slow_tests:files')
        files = []
    names = [name for name in files if isinstance(name, str) and name]
    if len(names) != len(files):
        _log.warning("sample_slow_tests: 跳过 %d 个非字符串或空文件项",
                       len(files) - len(names))
    top_n = _norm_int_param(top_n, _DEFAULT_SLOW_TEST_TOP_N)
    env = _measure_env()
    return {"samples": [
        _sample_one_file(project_dir, name, str(Path(tests_dir) / name),
                         top_n, env)
        for name in names
    ]}
def _serial_total(static: dict) -> int:
    return sum(r["serial_calls"] for r in static["files"])
def _advice_serial_surface(static: dict) -> list[str]:
    files = static["files"]
    if not files:
        return []
    serial_total = _serial_total(static)
    if serial_total < _SERIAL_ADVICE_MIN_CALLS:
        return []
    names = "、".join(r["file"] for r in files[:3])
    return [
        (f"【并行优先】串行等待嫌疑面 {serial_total} 处（重灾区: {names}）"
         f"——先上 pytest-xdist（-n auto），零代码改动，收益≈核数"),
        ("【分层回归】对 subprocess 重灾区文件贴 @pytest.mark.slow，"
         "日常回归跑快集，夜间/发版跑全量——根治串行等待"),
    ]
def _advice_slow_tests(sampled: dict) -> list[str]:
    slow_hits = [(s["file"], st) for s in sampled.get("samples", [])
                 for st in s.get("slow_tests", [])]
    if not slow_hits:
        return []
    worst = max(slow_hits, key=lambda x: x[1]["seconds"])
    return [
        (f"【定点归因】单条慢测试 {worst[1]['id']}"
         f"（{worst[1]['seconds']}s，文件 {worst[0]}）——缩小扫描面或"
         f"mock 化；哨兵类全扫测试保持独立解析但可增量缓存")
    ]
def _advice_collect(collect: dict) -> list[str]:
    seconds = as_number(collect.get("collect_seconds"), 0.0)
    if seconds <= _COLLECT_ADVICE_MIN_S:
        return []
    return [
        (f"【固定开销】收集 import {collect['collect_seconds']}s"
         f"（{_fmt_opt(collect.get('test_count'))} 条用例）——占比高时考虑"
         f"拆分测试包或延迟重导入；占比低则忽略")
    ]
def _build_advice(static: dict, collect: dict, sampled: dict) -> list[str]:
    advice = [
        *_advice_serial_surface(static),
        *_advice_slow_tests(sampled),
        *_advice_collect(collect),
    ]
    if not advice:
        advice.append("画像未发现显著瓶颈模式；耗时大概率来自海量小计算"
                      "长尾——直接并行化（pytest-xdist）即可")
    return advice
def _norm_int_param(value, default: int, minimum: int = 0) -> int:
    return max(minimum, int_or(value, default))
def _fmt_opt(value) -> str:
    return "?" if value is None else str(value)
def profile_test_performance(project_dir: str | Path,
                             tests_dir: str | None = None,
                             sample: bool = False,
                             sample_top: int = _DEFAULT_PROFILE_SAMPLE_TOP) -> dict:
    sample_top = _norm_int_param(sample_top, _DEFAULT_PROFILE_SAMPLE_TOP)
    try:
        _require_path_like(project_dir, "project_dir")
        if not str(project_dir).strip():
            raise FileNotFoundError(
                f"project_dir 不得为空白路径: {project_dir!r}")
        root = Path(project_dir).resolve()
    except (OSError, TypeError, ValueError) as exc:
        log_swallowed(__name__, exc, context="profile_test_performance:path_resolve")
        _log.debug("profile_test_performance: 项目路径解析失败: %s", exc)
        _out = step_err(f"项目路径解析失败: {exc}")
        _emit_profile_html(_out, project_dir)
        return _out
    if (tests_dir is None and root.is_dir()
            and _discover_default_tests_dir(root) is None):
        _out = step_skip(
            "未发现测试目录或根级测试文件（非测试型项目，测试性能画像不适用）",
            {"project_dir": str(root)})
        _emit_profile_html(_out, project_dir)
        return _out
    try:
        tdir = _resolve_tests_dir(root, tests_dir)
    except FileNotFoundError as exc:
        _log.warning(
            "profile_test_performance: 未发现测试目录或根级测试文件，画像中止: %s",
            exc)
        _out = step_err(str(exc))
        _emit_profile_html(_out, project_dir)
        return _out
    static = scan_serial_wait_surface(tdir)
    tail = scan_parametrize_tail(tdir, surface=static)
    collect = collect_suite_stats(project_dir, tests_dir=tdir)
    sampled: dict = {"samples": []}
    collect_status = collect.get("status")
    no_tests = collect_status == "skipped"
    collect_failed = collect_status in ("error", "timeout")
    if sample and not no_tests and not collect_failed:
        top_files = [r["file"] for r in static["files"][:sample_top]
                     if r["serial_calls"] > 0]
        if top_files:
            sampled = sample_slow_tests(str(root), top_files, tdir)
    advice = ([] if no_tests or collect_failed
              else _build_advice(static, collect, sampled))
    data = {
        "project_dir": str(root),
        "tests_dir": str(tdir),
        "static_surface": static,
        "parametrize_tail": tail,
        "collect_stats": collect,
        "sampled_durations": sampled,
        "advice": advice,
    }
    if no_tests:
        _out = step_skip(
            "未收集到任何用例（空测试目录或全部被忽略），测试性能画像不适用",
            data)
    elif collect_failed:
        _out = step_err(
            f"测试收集失败（{collect_status}）："
            f"{collect.get('detail') or '未返回明细'}", data)
    else:
        msg = (f"画像完成: {static['files_scanned']} 个测试文件, "
               f"串行等待嫌疑 {_serial_total(static)} 处, "
               f"收集 {_fmt_opt(collect.get('collect_seconds'))}s/"
               f"{_fmt_opt(collect.get('test_count'))} 条, 建议 {len(advice)} 条")
        _out = step_ok(data, msg)
    _emit_profile_html(_out, project_dir)
    return _out
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="测试性能画像器 — 全量回归耗时归因（任意 pytest 项目）")
    parser.add_argument("project_dir", help="项目根目录")
    parser.add_argument("--tests-dir", default=None,
                        help="测试目录名（默认自动发现 tests/test 或根级测试文件）")
    parser.add_argument("--sample", action="store_true",
                        help="执行实测采样（收集统计+嫌疑文件 --durations）")
    parser.add_argument("--sample-top", type=int,
                        default=_DEFAULT_PROFILE_SAMPLE_TOP,
                        help=f"采样文件数（默认 {_DEFAULT_PROFILE_SAMPLE_TOP}）")
    parser.add_argument("--json", action="store_true",
                        help="输出原始 JSON")
    args = parser.parse_args(argv)
    result = profile_test_performance(
        args.project_dir, tests_dir=args.tests_dir,
        sample=args.sample, sample_top=args.sample_top)
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2, default=str))
        return 0 if result["status"] in ("ok", "skipped") else 1
    if result["status"] == "skipped":
        print(result["message"])
        return 0
    if result["status"] != "ok":
        print(f"错误: {result['message']}")
        return 1
    print(f"== 测试性能画像: {result['message']}")
    data = result["data"]
    print("\n-- 串行等待嫌疑 top（subprocess/网络/sleep 密度）--")
    for row in data["static_surface"]["files"][:8]:
        print(f"  {row['file']:<44} serial={row['serial_calls']:<4} "
              f"parametrize={row['parametrize']:<3} loc={row['loc']}")
    for line in data["advice"]:
        print(f"\n* {line}")
    return 0
class CommandTimeoutError(Exception):
    pass
def run_command(cmd: list[str], *, cwd: str, env: dict,
                timeout: int | None = None) -> tuple[int, str]:
    timeout_s = _norm_timeout_s(timeout)
    rcode, output, gov = run_governed(
        cmd, cwd=cwd, env=env, timeout_s=timeout_s)
    if gov["timed_out"]:
        raise CommandTimeoutError(
            f"命令执行超时（timeout={timeout_s}s）: {cmd!r}")
    return rcode, output
def pytest_command(tests_dir: str | os.PathLike, *extra: str) -> list[str]:
    return [sys.executable, "-m", "pytest", str(tests_dir), *extra]
def xdist_available() -> bool:
    try:
        return importlib.util.find_spec("xdist") is not None
    except (ImportError, ValueError) as exc:
        logging.getLogger(__name__).warning(
            "[scanner] xdist 可用性探测异常，按不可用降级串行: %s", exc)
        return False
_SAMPLE_INTERVAL_S = 2.0
_TREE_KILL_WAIT_S = 5
def _kill_descendants(children) -> None:
    for child in children:
        try:
            child.kill()
        except psutil.Error:
            _log.debug("[scanner] 子进程 kill 失败(继续下一个)",
                         exc_info=True)
def _terminate_process_tree(proc, children=None) -> bool:
    if children is None:
        children = proc.children(recursive=True)
    _kill_descendants(children)
    _gone, alive = psutil.wait_procs(children, timeout=_TREE_KILL_WAIT_S)
    if alive:
        _log.warning(
            "[scanner] psutil 终止后仍有 %d 个子进程存活，转系统级兜底",
            len(alive))
        return False
    proc.kill()
    _gone, alive = psutil.wait_procs([proc], timeout=_TREE_KILL_WAIT_S)
    if alive:
        _log.warning("[scanner] psutil 终止后根进程仍存活，转系统级兜底")
        return False
    return True
def _terminate_tree_psutil(pid: int, *,
                           process_group: bool = False) -> bool | None:
    if psutil is None:
        return None
    try:
        root = psutil.Process(pid)
    except psutil.NoSuchProcess:
        if process_group:
            _log.debug("[scanner] 树终止: 根已消亡但进程组可能仍有后代，转系统级兜底")
            return None
        _log.debug("[scanner] 树终止: 枚举阶段根已消亡，终止目标已达成")
        return True
    except (psutil.Error, OSError):
        _log.debug("[scanner] psutil 树终止失败，转系统级兜底",
                     exc_info=True)
        return None
    try:
        try:
            children = root.children(recursive=True)
        except psutil.NoSuchProcess:
            if process_group:
                _log.debug("[scanner] 树终止: 枚举前根已消亡，转进程组兜底")
                return None
            _log.debug("[scanner] 树终止: 枚举阶段根已消亡，终止目标已达成")
            return True
        if _terminate_process_tree(root, children=children):
            return True
    except psutil.NoSuchProcess:
        _log.debug("[scanner] 树终止: kill 阶段根已消亡，终止目标已达成")
        return True
    except (psutil.Error, OSError):
        _log.debug("[scanner] psutil 树终止失败，转系统级兜底",
                     exc_info=True)
    return None
def _terminate_tree_system(pid: int, *,
                           process_group: bool = False) -> bool:
    try:
        if sys.platform.startswith("win"):
            _system_root = os.environ.get("SYSTEMROOT", r"C:\Windows")
            if not os.path.isabs(_system_root) or not os.path.isdir(_system_root):
                _system_root = r"C:\Windows"
            _taskkill = os.path.join(_system_root, "System32", "taskkill.exe")
            proc = subprocess.run(  # nosec B603
                [_taskkill, "/F", "/T", "/PID", str(pid)],
                capture_output=True, text=True, encoding="utf-8",
                errors="replace", check=False, timeout=15)
            return proc.returncode == 0
        if process_group and hasattr(os, "killpg"):
            os.killpg(pid, signal.SIGKILL)
        else:
            os.kill(pid, signal.SIGKILL)
        return True
    except (OSError, subprocess.SubprocessError):
        _log.debug("[scanner] 树终止兜底失败(taskkill/os.kill 路径)", exc_info=True)
        return False
def _terminate_tree(pid: int, *, process_group: bool = False) -> bool:
    if psutil is not None:
        result = _terminate_tree_psutil(pid, process_group=process_group)
        if result is not None:
            return result
    return _terminate_tree_system(pid, process_group=process_group)
def _tree_processes(root_pid: int) -> list:
    if psutil is None:
        return []
    root = psutil.Process(root_pid)
    return [root, *root.children(recursive=True)]
def _snapshot_tree(root_pid: int) -> dict[int, float] | None:
    if psutil is None:
        return None
    try:
        procs = _tree_processes(root_pid)
    except psutil.NoSuchProcess:
        _log.debug("[scanner] 进程树快照: 根进程已退出，无残留可采样")
        return {}
    except Exception as _snap_err:  # noqa: BLE001
        _log.warning("[scanner] 进程树快照失败(孤儿清扫失去 PID 重用校验依据): %s",
                      _snap_err, exc_info=True)
        return None
    out: dict[int, float] = {}
    for p in procs:
        try:
            out[p.pid] = p.create_time()
        except Exception as _sample_err:  # noqa: BLE001
            _log.debug(
                "[scanner] 启动时间采样失败（进程已退出等），跳过: pid=%s (%s)",
                p.pid, _sample_err)
    return out
def _sweep_orphans(tree_snapshot: dict[int, float],
                   gov: dict | None = None) -> list[int]:
    if psutil is None or not tree_snapshot:
        return []
    swept: list[int] = []
    for pid, ctime in tree_snapshot.items():
        try:
            proc = psutil.Process(pid)
            if abs(proc.create_time() - ctime) > 1e-3:
                continue
        except psutil.NoSuchProcess:
            _log.debug("[scanner] 孤儿进程已退出，无需回收: pid=%s", pid)
            continue
        except (psutil.Error, OSError) as exc:
            if gov is not None:
                gov["sweep_degraded"] = True
            _log.warning("[scanner] 无法校验孤儿进程身份；为避免 PID 重用误杀，"
                         "已跳过回收: pid=%s (%s)", pid, exc)
            continue
        if _sweep_one_orphan(proc, pid, gov):
            swept.append(pid)
    return swept
def _sweep_one_orphan(proc, pid: int, gov: dict | None = None) -> bool:
    try:
        if _terminate_process_tree(proc):
            return True
    except psutil.NoSuchProcess:
        _log.debug("[scanner] 孤儿进程在回收前自然退出: pid=%s", pid)
        return False
    except (psutil.Error, OSError):
        if gov is not None:
            gov["sweep_degraded"] = True
        _log.warning("[scanner] psutil 回收失败；为避免 PID 重用误杀，"
                     "不按 PID 转系统级兜底: pid=%s", pid, exc_info=True)
        return False
    if gov is not None:
        gov["sweep_degraded"] = True
    _log.warning("[scanner] 已校验孤儿进程树未完全终止；为避免 PID 重用误杀，"
                 "不按 PID 转系统级兜底: pid=%s", pid)
    return False
def _collect_tree_sample(root_pid: int, box: dict) -> tuple[int, int, float]:
    procs = _tree_processes(root_pid)
    if not procs:
        return 0, 0, 0.0
    rss = 0
    cpu_total = 0.0
    for p in procs:
        try:
            t = p.cpu_times()
            rss += p.memory_info().rss
            cpu_total += t.user + t.system
            box["tree_snapshot"].setdefault(p.pid, p.create_time())
        except Exception:  # noqa: BLE001
            _log.debug("[scanner] 采样中进程瞬时消失(跳过)", exc_info=True)
            continue
    return len(procs), rss, cpu_total
def _sample_tree_forever(root_pid: int, stop: threading.Event,
                         box: dict, prev_cpu: float | None = None,
                         prev_ts: float | None = None) -> None:
    while not stop.wait(_SAMPLE_INTERVAL_S):
        try:
            sample = _collect_tree_sample(root_pid, box)
        except psutil.NoSuchProcess:
            _log.debug("[scanner] 采样循环: 根进程已消亡，自然结束采样")
            break
        except Exception as _exc:  # noqa: BLE001
            _log.warning("[scanner] 内存采样线程异常退出: %s", _exc)
            break
        proc_count, rss, cpu_total = sample
        now = time.monotonic()
        box["peak_rss_mb"] = max(box["peak_rss_mb"], rss / (1024 * 1024))
        box["tree_procs_peak"] = max(box["tree_procs_peak"], proc_count)
        _accumulate_cpu_sample(box, cpu_total, prev_cpu, prev_ts, now)
        prev_cpu, prev_ts = cpu_total, now
def _accumulate_cpu_sample(box: dict, cpu_total: float, prev_cpu: float | None,
                           prev_ts: float | None, now: float) -> None:
    if prev_cpu is None or prev_ts is None or now <= prev_ts:
        return
    box["cpu_time_acc"] += max(0.0, cpu_total - prev_cpu)
    box["wall_acc"] += now - prev_ts
def _start_sampler(root_pid: int, box: dict) -> tuple[threading.Event,
                                                      threading.Thread | None]:
    stop = threading.Event()
    if psutil is None:
        return stop, None
    prev_cpu: float | None = None
    prev_ts: float | None = None
    try:
        proc_count, rss, prev_cpu = _collect_tree_sample(root_pid, box)
        prev_ts = time.monotonic()
        box["peak_rss_mb"] = max(box["peak_rss_mb"], rss / (1024 * 1024))
        box["tree_procs_peak"] = max(box["tree_procs_peak"], proc_count)
    except psutil.NoSuchProcess:
        _log.debug("[scanner] 启动前采样: 根进程已退出，跳过一次样本")
    except Exception:  # noqa: BLE001
        _log.debug("[scanner] 启动前资源采样失败(继续后台采样)", exc_info=True)
    try:
        sampler = threading.Thread(
            target=_sample_tree_forever,
            args=(root_pid, stop, box, prev_cpu, prev_ts), daemon=True)
        sampler.start()
        return stop, sampler
    except Exception:  # noqa: BLE001
        _log.debug("[scanner] 采样线程启动失败(降级无采样)", exc_info=True)
        return stop, None
def _wait_output(proc, timeout_s: float | None) -> tuple[str, bool]:
    try:
        out, _ = proc.communicate(timeout=timeout_s)
        return out or "", False
    except subprocess.TimeoutExpired:
        _log.debug("[scanner] 管道读取超时（>%ss），按超时语义返回", timeout_s)
        return "", True
def _force_close_pipes(proc) -> None:
    for stream in (proc.stdout, proc.stderr):
        if stream is not None:
            try:
                stream.close()
            except OSError:
                _log.debug("[scanner] 管道句柄关闭失败", exc_info=True)
def _recover_output(proc) -> str:
    try:
        proc.kill()
    except OSError as exc:
        _log.debug("[scanner] 根进程已退出，跳过重复 kill: %s", exc)
    try:
        out, _ = proc.communicate(timeout=10)
        return out or ""
    except subprocess.TimeoutExpired:
        _log.warning("[scanner] 树终止后输出回收超时（管道被不可杀进程占写），已放弃输出")
        _force_close_pipes(proc)
        return ""
def _finalize_governance(gov: dict, box: dict) -> None:
    gov["tree_snapshot"].update(box["tree_snapshot"])
    gov["orphans_swept"] = _sweep_orphans(gov["tree_snapshot"], gov)
    gov["peak_rss_mb"] = round(box["peak_rss_mb"], 1)
    gov["avg_cpu_cores"] = (
        round(box["cpu_time_acc"] / box["wall_acc"], 2)
        if box["wall_acc"] > 0 else 0.0)
    gov["tree_procs_peak"] = box["tree_procs_peak"]
def _await_process(proc, stop: threading.Event,
                   sampler: threading.Thread | None,
                   timeout_s: int | None) -> tuple[str, bool, BaseException | None]:
    out = ""
    timed_out = False
    comm_err: BaseException | None = None
    try:
        out, timed_out = _wait_output(proc, timeout_s)
    except BaseException as exc:  # noqa: BLE001
        _log.debug("[scanner] 管道读取异常（先回收树再上抛）: %r", exc)
        comm_err = exc
    finally:
        stop.set()
        if sampler is not None:
            sampler.join(timeout=_SAMPLE_INTERVAL_S + 2)
    return out, timed_out, comm_err
def run_governed(cmd: list[str], cwd: str, env: dict,
                  timeout_s: int | None) -> tuple[int, str, dict]:
    timeout_s = _norm_timeout_s(timeout_s)
    gov, box = _new_governance_state()
    proc = subprocess.Popen(  # jwsgj:suppress SYM-TAINT
        cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, encoding="utf-8",
        errors="replace", start_new_session=(os.name == "posix"))
    snapshot = _snapshot_tree(proc.pid)
    if snapshot is None:
        gov["sweep_degraded"] = True
    else:
        gov["tree_snapshot"].update(snapshot)
    stop, sampler = _start_sampler(proc.pid, box)
    out, timed_out, comm_err = _await_process(proc, stop, sampler, timeout_s)
    try:
        if timed_out or comm_err is not None:
            out = _recover_terminated_run(proc, gov, timed_out, comm_err)
    finally:
        _finalize_governance(gov, box)
    rcode = proc.returncode if proc.returncode is not None else -1
    return rcode, out or "", gov
def _new_governance_state() -> tuple[dict, dict]:
    gov: dict = {
        "timed_out": False, "orphans_swept": [], "peak_rss_mb": 0.0,
        "avg_cpu_cores": 0.0, "tree_procs_peak": 0,
        "sweep_degraded": psutil is None, "tree_snapshot": {},
        "tree_terminated": None,
    }
    box: dict = {"peak_rss_mb": 0.0, "tree_procs_peak": 0,
                 "tree_snapshot": {}, "cpu_time_acc": 0.0, "wall_acc": 0.0}
    return gov, box
def _recover_terminated_run(proc, gov: dict, timed_out: bool,
                            comm_err: BaseException | None) -> str:
    if timed_out:
        gov["timed_out"] = True
    gov["tree_terminated"] = _terminate_tree(
        proc.pid, process_group=(os.name == "posix"))
    out = _recover_output(proc)
    if comm_err is not None:
        raise comm_err
    return out

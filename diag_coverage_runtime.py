from __future__ import annotations

import ast
import hashlib
import json
import logging
import os
import shutil
import site
import sqlite3
import time
from pathlib import Path
from typing import Any, NamedTuple

import coverage as _coverage

from .diag_guard_io import (
    atomic_write_text,
    move_to_recycle_bin,
    two_level_rmtree,
    two_level_unlink,
)
from .diag_testing_coverage import (
    SKIP_DIRS_LOWER,
    TEST_DIR_CANDIDATES,
    norm_nonneg_int,
    step_err,
    step_ok,
    step_skip,
    summarize_coverage_report,
)
from .diag_testing_source import resolve_tests_dir
from .diag_types_normalize import as_number, safe_float
from .diag_types_vocab import DIAGNOSIS_METHOD_BUDGET_S
from .log_config import (
    get_module_logger,
    safe_stderr_write,
    setup_logging,
)
from .runtime_paths import (
    get_temp_base,
    subprocess_noartifact_env,
)
from .runtime_scope import (
    is_out_of_scope_dir,
    is_runtime_log_artifact,
    is_test_source_basename,
)

try:
    import psutil
except ImportError as _imp_err:
    psutil = None  # type: ignore[assignment]
    logging.getLogger(__name__).debug(
        "[diag_coverage_runtime] psutil 导入失败，进程活性探测降级: %s",
        _imp_err)
try:
    setup_logging()
except Exception as _lc_e:  # noqa: BLE001
    get_module_logger(__name__).debug(
        "diag_coverage_runtime 日志接入失败（降级 stderr 留痕）: %s", _lc_e)
    try:
        safe_stderr_write(
            f"[diag_coverage_runtime] 日志接入失败（降级无落盘）: {_lc_e}\n")
    except Exception as _sw_e:  # noqa: BLE001
        logging.getLogger(__name__).debug(
            "diag_coverage_runtime stderr 降级失败: %s", _sw_e)
_log = get_module_logger(__name__, __file__)
__all__ = [
    "DEFAULT_CACHE_MAX_AGE_S",
    "DEFAULT_WAIT_TIMEOUT_S",
    "DEFAULT_WORKERS",
    "CoordPolicy",
    "ScanParams",
    "ScanStepError",
    "audit_combine_copies",
    "build_scan_rc",
    "cleanup_consumed_coverage_data",
    "cleanup_scan_artifacts",
    "coordination_cache_attempt",
    "coordination_exit",
    "coordination_publish",
    "detect_collection_corruption",
    "ensure_autostart_hook",
    "hook_recycle_safe",
    "new_run_dir",
    "pid_exists",
    "pid_or",
    "prepare_branch_combine_dir",
    "prune_old_run_dirs",
    "psutil_available",
    "remove_autostart_hook",
    "resolve_effective_workers",
    "scan_base_dir",
    "write_covsave_plugin",
]
_HOOK_PTH_NAME = "cov_autostart.pth"
_LEGACY_HOOK_PTH_NAMES = ("jwsgj_cov_autostart.pth",)
_MANAGED_HOOK_PTH_NAMES = frozenset((_HOOK_PTH_NAME, *_LEGACY_HOOK_PTH_NAMES))
MIN_COPY_LINE_RECORDS = 50
_MAX_REPORTED_COPY_NAMES = 20
RUN_KEEP = 5
_COVSAVE_PLUGIN_SRC = '''"""covsave 插件：pytest_sessionfinish 时主动保存 process_startup 的 Coverage 实例。

xdist worker 在 Windows 上被硬杀时 atexit 不执行，本插件在会话结束点主动 save()
保住测量数据；仅当 COVERAGE_PROCESS_START 已设置（采集模式）时生效。
"""

import logging
import os

__all__ = ["pytest_sessionfinish"]

_LOG = logging.getLogger("covsave")

def pytest_sessionfinish(session, exitstatus):
    """会话结束钩子：主动保存 coverage.process_startup 实例的测量数据。"""
    if not os.environ.get("COVERAGE_PROCESS_START"):
        return
    try:
        import coverage
    except ImportError:
        _LOG.warning("coverage 未安装，跳过 sessionfinish 保存（采集模式环境异常）")
        return
    try:
        cov = getattr(coverage.process_startup, "coverage", None)
        if cov is not None:
            cov.save()
    except Exception:  # noqa: BLE001 —— 保存失败仅告警不阻断 pytest 收尾
        _LOG.warning("covsave sessionfinish 保存失败（覆盖率数据可能丢失）",
                     exc_info=True)
'''
def _safe_rmtree(target: Path, within: Path) -> bool:
    try:
        tgt = target.resolve()
        root = within.resolve()
    except OSError:
        _log.debug("[coverage] 受控删除路径解析失败(中止,下轮再试)", exc_info=True)
        return False
    if tgt == root or root not in tgt.parents:
        _log.warning("[coverage] 拒绝删除归口外路径: %s (within=%s)",
                     target, within)
        return False
    if not tgt.is_dir():
        _log.debug("[coverage] 非目录目标拒绝递归删除: %s", target)
        return False
    return two_level_rmtree(str(tgt))
def _run_stamp(name: str) -> str | None:
    parts = name.split("-")
    if (len(parts) >= 3 and len(parts[1]) == 8 and len(parts[2]) == 6
            and parts[1].isdigit() and parts[2].isdigit()):
        return f"{parts[1]}-{parts[2]}"
    return None
def _stamped_run_dirs(scan_dir: Path) -> list[tuple[str, Path]]:
    stamped: list[tuple[str, Path]] = []
    for d in scan_dir.glob("run-*"):
        if not d.is_dir():
            continue
        stamp = _run_stamp(d.name)
        if stamp is not None:
            stamped.append((stamp, d))
    stamped.sort(key=lambda kv: kv[0])
    return stamped
def prune_old_run_dirs(scan_dir: Path, keep: int = RUN_KEEP,
                        protect: Path | None = None) -> int:
    stamped = _stamped_run_dirs(scan_dir)
    if len(stamped) <= keep:
        return 0
    protect_identity = (
        os.path.normcase(os.path.realpath(os.fspath(protect)))
        if protect is not None else None)
    removed = 0
    for _, old in stamped[: len(stamped) - keep]:
        old_identity = os.path.normcase(os.path.realpath(os.fspath(old)))
        if protect_identity is not None and old_identity == protect_identity:
            continue
        if _safe_rmtree(old, within=scan_dir):
            removed += 1
    return removed
def new_run_dir(scan_dir: Path) -> Path:
    ts = time.strftime("%Y%m%d-%H%M%S")
    run_dir = scan_dir / f"run-{ts}-{os.urandom(3).hex()}"
    run_dir.mkdir(parents=True, exist_ok=True)
    try:
        prune_old_run_dirs(scan_dir, protect=run_dir)
    except Exception as e:  # noqa: BLE001
        _log.warning("[coverage] 旧轮目录轮转异常(不阻断): %s", e)
    return run_dir
def cleanup_consumed_coverage_data(run_dir: Path) -> dict:
    removed = 0
    bytes_freed = 0
    errors = 0
    targets = sorted(run_dir.glob(".coverage*"))
    targets += sorted((run_dir / "_combine_branch").glob(".coverage*"))
    for p in targets:
        if not p.is_file():
            continue
        try:
            size = p.stat().st_size
        except OSError as _e:
            _log.debug(
                '静默降级[cleanup_consumed_coverage_data:OSError]: %s: %s',
                type(_e).__name__, _e)
            errors += 1
            continue
        if two_level_unlink(p):
            removed += 1
            bytes_freed += size
        else:
            errors += 1
    return {"files_removed": removed, "bytes_freed": bytes_freed,
            "errors": errors}
def scan_base_dir(data_dir: str | Path | None = None,
                  project_root: str | Path | None = None) -> Path:
    if data_dir:
        scan = Path(data_dir)
    else:
        base = (get_temp_base(str(project_root)) if project_root
                else get_temp_base())
        scan = Path(base) / "coverage" / "scan"
    scan.mkdir(parents=True, exist_ok=True)
    return scan
def build_scan_rc(scan_dir: str | Path, source_root: str | Path) -> Path:
    scan_dir = Path(scan_dir).resolve()
    scan_dir.mkdir(parents=True, exist_ok=True)
    source_root = Path(source_root).resolve()
    rc = scan_dir / "cov_autostart.rc"
    atomic_write_text(
        str(rc),
        "[run]\n"
        "branch = True\n"
        "parallel = True\n"
        f"data_file = {scan_dir / '.coverage'}\n"
        f"source = {source_root}\n",
        tag="cov_rc",
    )
    return rc
def write_covsave_plugin(scan_dir: str | Path) -> Path:
    scan_dir = Path(scan_dir).resolve()
    scan_dir.mkdir(parents=True, exist_ok=True)
    plugin = scan_dir / "covsave_plugin.py"
    atomic_write_text(str(plugin), _COVSAVE_PLUGIN_SRC, tag="cov_plugin")
    compile(_COVSAVE_PLUGIN_SRC, str(plugin), "exec")
    return plugin
_SITE_PACKAGE_DIR_NAMES = frozenset({"site-packages", "dist-packages"})
def _resolve_site_packages_dir() -> Path | None:
    site_dir = Path(_coverage.__file__).resolve().parent.parent
    if site_dir.name.lower() in _SITE_PACKAGE_DIR_NAMES:
        return site_dir
    candidates = [Path(p) for p in site.getsitepackages()
                  if Path(p).name.lower() in _SITE_PACKAGE_DIR_NAMES]
    return candidates[0] if candidates else None
def remove_autostart_hook() -> dict:
    site_dir = _resolve_site_packages_dir()
    if site_dir is None:
        return {"removed": False, "existed": False,
                "error": "site-packages not found"}
    targets = [site_dir / name for name in sorted(_MANAGED_HOOK_PTH_NAMES)
               if (site_dir / name).exists()]
    if not targets:
        return {"removed": False, "existed": False, "error": ""}
    removed: list[str] = []
    failed: list[str] = []
    for target in targets:
        if two_level_unlink(target):
            removed.append(str(target))
        else:
            failed.append(str(target))
    if failed:
        _log.warning("[coverage] 移除自启动钩子失败（直删与中转均被拒）: %s",
                     failed[0])
        return {"removed": bool(removed), "existed": True,
                "hook": failed[0], "hooks_removed": removed,
                "error": "钩子文件删除被拒（句柄占用或跨盘中转不可达）"}
    return {"removed": True, "existed": True, "hook": removed[0],
            "hooks_removed": removed, "error": ""}
_PTH_EXEC_PREFIXES = ("import ", "import\t")
_EXEC_WRAPPER_NAMES = frozenset({"exec", "eval"})
_MAX_PTH_EXEC_DEPTH = 3
_EMPTY_INHERITED_IMPORTS: tuple[ast.stmt, ...] = ()
def _environment_lookup_truth(node: ast.AST) -> bool | None:
    if not isinstance(node, ast.Call) or node.keywords:
        return None
    func = node.func
    if not isinstance(func, ast.Attribute):
        return None
    is_environ_get = (
        func.attr == "get"
        and isinstance(func.value, ast.Attribute)
        and func.value.attr == "environ"
        and isinstance(func.value.value, ast.Name)
        and func.value.value.id == "os")
    is_getenv = (func.attr == "getenv"
                 and isinstance(func.value, ast.Name)
                 and func.value.id == "os")
    if not (is_environ_get or is_getenv) or len(node.args) not in (1, 2):
        return None
    key_node = node.args[0]
    if not (isinstance(key_node, ast.Constant)
            and isinstance(key_node.value, str)):
        return None
    key = key_node.value
    if key == "COVERAGE_PROCESS_START":
        return True
    value = os.environ.get(key)
    if value is not None:
        return bool(value)
    if len(node.args) == 2:
        return _constant_truth(node.args[1])
    return False
def _constant_truth(node: ast.AST) -> bool | None:
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        operand = _constant_truth(node.operand)
        return None if operand is None else not operand
    return _environment_lookup_truth(node)
def _executable_nodes(tree: ast.AST) -> list[ast.AST]:
    nodes: list[ast.AST] = []
    stack = [tree]
    while stack:
        node = stack.pop()
        nodes.append(node)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            body = node.body
            deferred = set(body) if isinstance(body, list) else {body}
            stack.extend(child for child in ast.iter_child_nodes(node)
                         if child not in deferred)
            continue
        if isinstance(node, (ast.If, ast.IfExp)):
            truth = _constant_truth(node.test)
            body = node.body if isinstance(node, ast.If) else (node.body,)
            orelse = node.orelse if isinstance(node, ast.If) else (node.orelse,)
            stack.append(node.test)
            if truth is not False:
                stack.extend(body)
            if truth is not True:
                stack.extend(orelse)
            continue
        if isinstance(node, ast.While):
            stack.append(node.test)
            if _constant_truth(node.test) is not False:
                stack.extend(node.body)
            stack.extend(node.orelse)
            continue
        if isinstance(node, ast.BoolOp):
            evaluated = []
            for value in node.values:
                evaluated.append(value)
                truth = _constant_truth(value)
                if ((isinstance(node.op, ast.And) and truth is False)
                        or (isinstance(node.op, ast.Or) and truth is True)):
                    break
            stack.extend(evaluated)
            continue
        stack.extend(ast.iter_child_nodes(node))
    return nodes
def _is_coverage_import(statement: ast.AST) -> bool:
    return (isinstance(statement, ast.Import)
            and any(alias.name == "coverage" or alias.name.startswith("coverage.")
                    for alias in statement.names))
def _is_coverage_import_from(statement: ast.AST) -> bool:
    return (isinstance(statement, ast.ImportFrom)
            and statement.level == 0 and statement.module is not None
            and (statement.module == "coverage"
                 or statement.module.startswith("coverage.")))
def _exec_payload_sources(tree: ast.AST) -> list[str]:
    sources: list[str] = []
    for node in _executable_nodes(tree):
        if not isinstance(node, ast.Call) or node.keywords:
            continue
        if not (isinstance(node.func, ast.Name)
                and node.func.id in _EXEC_WRAPPER_NAMES):
            continue
        if len(node.args) not in (1, 2, 3):
            continue
        namespace_args = zip(node.args[1:], ("globals", "locals"))
        if any(not (isinstance(arg, ast.Call)
                    and isinstance(arg.func, ast.Name)
                    and arg.func.id == namespace
                    and not arg.args and not arg.keywords)
               for arg, namespace in namespace_args):
            continue
        payload = node.args[0]
        if isinstance(payload, ast.Constant) and isinstance(payload.value, str):
            sources.append(payload.value)
    return sources
def _pth_line_calls_process_startup(
        line: str, _depth: int = 0,
        _inherited_imports: tuple[ast.stmt, ...] = _EMPTY_INHERITED_IMPORTS,
        *, _inherited_names: tuple[frozenset[str], frozenset[str]] | None = None
) -> bool:
    try:
        tree = ast.parse(line, mode="exec")
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        _log.debug("[coverage] .pth 执行行无法解析，按未启用处理: %r", line)
        return False
    return _tree_calls_process_startup(
        tree, _inherited_imports, _depth=_depth,
        _inherited_names=_inherited_names)
def _tree_calls_process_startup(
        tree: ast.AST,
        inherited_imports: tuple[ast.stmt, ...] = _EMPTY_INHERITED_IMPORTS,
        *, _depth: int = 0,
        _inherited_names: tuple[frozenset[str], frozenset[str]] | None = None,
) -> bool:
    nodes = _executable_nodes(tree)
    if _inherited_names is not None:
        coverage_names = set(_inherited_names[0])
        startup_names = set(_inherited_names[1])
    else:
        coverage_names = {
            alias.asname or alias.name.split(".", 1)[0]
            for statement in inherited_imports if _is_coverage_import(statement)
            for alias in statement.names
            if alias.name == "coverage" or alias.name.startswith("coverage.")
        }
        startup_names = {
            (alias.asname or alias.name) if alias.name != "*"
            else "process_startup"
            for statement in inherited_imports if _is_coverage_import_from(statement)
            for alias in statement.names
            if alias.name == "process_startup" or alias.name == "*"
        }
    events: list[tuple[tuple[int, int], int, str, Any]] = []
    def _position(node: ast.AST) -> tuple[int, int]:
        return (getattr(node, "lineno", -1),
                getattr(node, "col_offset", -1))
    for statement in nodes:
        if isinstance(statement, ast.Import):
            for alias in statement.names:
                name = alias.asname or alias.name.split(".", 1)[0]
                is_coverage = (alias.name == "coverage"
                               or alias.name.startswith("coverage."))
                events.append((_position(statement), 0,
                               "coverage" if is_coverage else "unbind", name))
        elif isinstance(statement, ast.ImportFrom):
            from_coverage = _is_coverage_import_from(statement)
            for alias in statement.names:
                if alias.name == "*":
                    if from_coverage:
                        events.append((_position(statement), 0,
                                       "startup", "process_startup"))
                    else:
                        events.append((_position(statement), 0,
                                       "unbind_all", None))
                    continue
                name = alias.asname or alias.name
                is_startup = from_coverage and alias.name == "process_startup"
                events.append((_position(statement), 0,
                               "startup" if is_startup else "unbind", name))
    for node in nodes:
        name = None
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            name = node.id
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            name = node.name
        elif isinstance(node, ast.ExceptHandler):
            name = node.name or None
        if name:
            events.append((_position(node), 1, "unbind", name))
        if isinstance(node, ast.ClassDef):
            events.append((_position(node), 1, "scope_enter", None))
            events.append(((getattr(node, "end_lineno", -1),
                            getattr(node, "end_col_offset", -1)),
                           3, "scope_exit", None))
        if isinstance(node, ast.Call):
            events.append((_position(node), 2, "call", node))
    coverage_scopes: list[set[str]] = []
    startup_scopes: list[set[str]] = []
    def _is_coverage_module(node: ast.AST) -> bool:
        if isinstance(node, ast.Name):
            return node.id in coverage_names
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "__import__"
                and len(node.args) == 1 and not node.keywords
                and isinstance(node.args[0], ast.Constant)
                and node.args[0].value == "coverage")
    for _pos, _kind, action, value in sorted(events, key=lambda e: e[:2]):
        if action == "scope_enter":
            coverage_scopes.append(coverage_names)
            startup_scopes.append(startup_names)
            coverage_names = set(coverage_names)
            startup_names = set(startup_names)
            continue
        if action == "scope_exit":
            coverage_names = coverage_scopes.pop()
            startup_names = startup_scopes.pop()
            continue
        if action in {"coverage", "startup"}:
            coverage_names.discard(value)
            startup_names.discard(value)
            (coverage_names if action == "coverage" else startup_names).add(value)
            continue
        if action == "unbind":
            coverage_names.discard(value)
            startup_names.discard(value)
            continue
        if action == "unbind_all":
            coverage_names.clear()
            startup_names.clear()
            continue
        func = value.func
        if (isinstance(func, ast.Attribute)
                and func.attr == "process_startup"
                and _is_coverage_module(func.value)):
            return True
        if isinstance(func, ast.Name) and func.id in startup_names:
            return True
        if (_depth < _MAX_PTH_EXEC_DEPTH
                and isinstance(func, ast.Name)
                and func.id in _EXEC_WRAPPER_NAMES):
            inherited_names = (frozenset(coverage_names),
                               frozenset(startup_names))
            for payload in _exec_payload_sources(value):
                if _pth_line_calls_process_startup(
                        payload, _depth + 1,
                        _inherited_names=inherited_names):
                    return True
    return False
def _pth_enables_process_startup(content: str) -> bool:
    for raw in content.splitlines():
        if (raw.startswith(_PTH_EXEC_PREFIXES)
                and _pth_line_calls_process_startup(raw)):
            return True
    return False
def _find_autostart_hook(site_dir: Path) -> Path | None:
    managed = [site_dir / name for name in sorted(_MANAGED_HOOK_PTH_NAMES)]
    others = [pth for pth in sorted(site_dir.glob("*.pth"))
              if pth.name not in _MANAGED_HOOK_PTH_NAMES]
    for pth in (*managed, *others):
        try:
            content = pth.read_text(encoding="utf-8", errors="replace")
        except OSError as e:
            _log.debug("文件读取失败（跳过）: %s: %s", pth, e)
            continue
        if _pth_enables_process_startup(content):
            return pth
    return None
def _install_autostart_hook(target: Path) -> str:
    try:
        atomic_write_text(
            str(target),
            "import os; os.environ.get('COVERAGE_PROCESS_START') "
            "and __import__('coverage').process_startup()\n",
            tag="cov_hook",
        )
        return ""
    except OSError as exc:
        _log.warning("[coverage] 安装自启动钩子失败: %s", exc)
        return str(exc)
def ensure_autostart_hook(dry_run: bool = False) -> dict:
    site_dir = _resolve_site_packages_dir()
    if site_dir is None:
        return {"reused": False, "installed": False,
                "error": "site-packages not found"}
    existing = _find_autostart_hook(site_dir)
    if existing is not None:
        return {"reused": True, "installed": False, "hook": str(existing),
                "error": ""}
    target = site_dir / _HOOK_PTH_NAME
    result = {"reused": False, "installed": False, "hook": str(target),
              "error": ""}
    if dry_run:
        result["would_install"] = True
        return result
    error = _install_autostart_hook(target)
    result["installed"] = not error
    result["error"] = error
    return result
def _inspect_copy(copy: Path) -> tuple[bool | None, int]:
    cd = _coverage.CoverageData(basename=str(copy))
    try:
        cd.read()
        lines = sum(len(cd.lines(f) or []) for f in cd.measured_files())
        return bool(cd.has_arcs()), lines
    except (OSError, sqlite3.Error, _coverage.CoverageException) as _ce:
        _log.debug("[coverage] 副本不可读（按调用方口径降级）: %s: %s",
                   copy.name, _ce)
        return None, 0
    finally:
        try:
            cd.close()
        except Exception:  # noqa: BLE001
            _log.debug("[coverage] 副本句柄 close 失败(不阻断)", exc_info=True)
def audit_combine_copies(run_dir,
                         min_line_records: int = MIN_COPY_LINE_RECORDS) -> dict:
    min_line_records = norm_nonneg_int(
        min_line_records, MIN_COPY_LINE_RECORDS, "min_line_records")
    run_dir = Path(run_dir)
    copies = sorted(run_dir.glob(".coverage.*"))
    valid = suspect = statement_only = empty = unreadable = total = 0
    unreadable_names: list[str] = []
    for copy in copies:
        has_arcs, n = _inspect_copy(copy)
        total += n
        if has_arcs is None:
            unreadable += 1
            if len(unreadable_names) < _MAX_REPORTED_COPY_NAMES:
                unreadable_names.append(copy.name)
        elif n == 0:
            empty += 1
        elif not has_arcs:
            statement_only += 1
        elif n >= min_line_records:
            valid += 1
        else:
            suspect += 1
    return {"copies": len(copies), "valid": valid, "suspect": suspect,
            "statement_only": statement_only, "empty": empty,
            "unreadable": unreadable,
            "unreadable_names": unreadable_names,
            "total_line_records": total}
def prepare_branch_combine_dir(run_dir) -> dict:
    run_dir = Path(run_dir)
    staging = run_dir / "_combine_branch"
    scanned = staged = stmt_skipped = empty = failed = unreadable = 0
    skipped_names: list[str] = []
    staged_names: list[str] = []
    failed_names: list[str] = []
    unreadable_names: list[str] = []
    for copy in sorted(run_dir.glob(".coverage.*")):
        scanned += 1
        has_arcs, lines = _inspect_copy(copy)
        if has_arcs is None:
            unreadable += 1
            if len(unreadable_names) < _MAX_REPORTED_COPY_NAMES:
                unreadable_names.append(copy.name)
            continue
        if lines == 0:
            empty += 1
            continue
        if not has_arcs:
            stmt_skipped += 1
            if len(skipped_names) < _MAX_REPORTED_COPY_NAMES:
                skipped_names.append(copy.name)
            continue
        if _stage_branch_copy(copy, staging):
            staged += 1
            staged_names.append(copy.name)
        else:
            failed += 1
            failed_names.append(copy.name)
    return {"scanned": scanned, "staged": staged,
            "stmt_skipped": stmt_skipped, "empty": empty, "failed": failed,
            "unreadable": unreadable,
            "skipped_names": skipped_names,
            "staged_names": staged_names,
            "unreadable_names": unreadable_names,
            "failed_names": failed_names}
def _stage_branch_copy(copy: Path, staging: Path) -> bool:
    try:
        staging.mkdir(exist_ok=True)
        shutil.copy2(copy, staging / copy.name)
        return True
    except OSError as exc:
        _log.warning("[coverage] branch 副本归集失败（回退判定见调用方）: %s: %s",
                     copy.name, exc)
        return False
_PREWARM_TIMEOUT_S = 300
_PYTEST_NO_TESTS_COLLECTED = 5
_NO_CACHE_PROVIDER_ARGS = ("-p", "no:cacheprovider")
_PYTEST_QUIET = ["-q", "--tb=no", *_NO_CACHE_PROVIDER_ARGS]
_CLEAR_ADDOPTS = ("-o", "addopts=")
_AUTO_WORKERS_CAP = 4
class ScanStepError(Exception):
    def __init__(self, step: int, advice: str, detail: str = ""):
        super().__init__(detail)
        self.step = step
        self.advice = advice
        self.detail = detail
def pid_or(value) -> int:
    return int(as_number(value, -1))
def psutil_available() -> bool:
    return psutil is not None
def pid_exists(pid: int) -> bool:
    if psutil is None:
        return True
    return bool(psutil.pid_exists(pid))
def _norm_timeout_s(value) -> int | None:
    norm = _as_int_or_none(value)
    if norm is not None and norm > 0:
        return norm
    seconds = safe_float(value, -1)
    if seconds <= 0:
        return None
    return max(1, int(seconds))
def _coverage_scan_roots(project_root: str | Path | None = None) -> list[Path]:
    if project_root:
        return [Path(get_temp_base(str(project_root))) / "coverage" / "scan"]
    temp_root = Path(get_temp_base())
    roots: list[Path] = [temp_root / "coverage" / "scan"]
    seen = {os.path.normcase(os.path.abspath(str(roots[0])))}
    try:
        children = sorted(temp_root.iterdir())
    except OSError as exc:
        _log.debug("[coverage] 命名空间枚举失败（仅清理默认根）: %s", exc)
        return roots
    for child in children:
        candidate = child / "coverage" / "scan"
        if not child.is_dir() or not candidate.is_dir():
            continue
        key = os.path.normcase(os.path.abspath(str(candidate)))
        if key in seen:
            continue
        seen.add(key)
        roots.append(candidate)
    return roots
def cleanup_scan_artifacts(data_dir: str | Path | None = None,
                           keep: int = RUN_KEEP,
                           project_root: str | Path | None = None) -> dict:
    try:
        keep_n = norm_nonneg_int(keep, RUN_KEEP, "keep")
        roots = ([Path(data_dir)] if data_dir
                 else _coverage_scan_roots(project_root))
        removed = 0
        for scan in roots:
            if scan.is_dir():
                removed += prune_old_run_dirs(scan, keep=keep_n)
        return step_ok({"removed": removed, "scan_dir": str(roots[0]),
                    "scan_dirs": [str(root) for root in roots],
                    "keep": keep_n},
                   f"历史扫描产物清理完成: 删除 {removed} 个旧轮目录")
    except Exception as exc:  # noqa: BLE001
        _log.warning("[scanner] 扫描产物清理失败: %s", exc, exc_info=True)
        return step_err(f"扫描产物清理失败: {exc}")
_COLLECTION_CORRUPTION_MARKERS = (
    "Different tests were collected",
    "Workers do not have the same tests",
    "error during collection",
    "errors during collection",
    "ERROR collecting",
)
_COLLECTION_RAW_MARKERS = frozenset(_COLLECTION_CORRUPTION_MARKERS[:2])
_COLLECTION_INTERRUPT_MARKERS = frozenset(_COLLECTION_CORRUPTION_MARKERS[2:4])
def _collection_diagnostic_has_marker(line: str, marker: str) -> bool:
    if marker not in line:
        return False
    if line.startswith(("ERROR ", "ERROR:")):
        return True
    if marker in _COLLECTION_RAW_MARKERS:
        return line.startswith(marker)
    if marker in _COLLECTION_INTERRUPT_MARKERS:
        return line.lstrip("! ").startswith("Interrupted:")
    return False
def detect_collection_corruption(log: str) -> str | None:
    if not log:
        return None
    lines = [raw.strip() for raw in log.splitlines()]
    for marker in _COLLECTION_CORRUPTION_MARKERS:
        if any(_collection_diagnostic_has_marker(line, marker) for line in lines):
            return marker
    return None
_COORD_SCHEMA = 2
_COORD_VERSION = "coord-v4"
# 锁「过期」阈值：无 psutil 时靠时间戳判活，若短于单个方法预算，
# 正在正常跑的方法会被并发会话判成「死锁」并被强制接管，产物直接损坏。
# 必须与方法预算同源。
_LOCK_STALE_S = DIAGNOSIS_METHOD_BUDGET_S
_LOCK_INCOMPLETE_STALE_S = 60.0
_LOCK_POLL_S = 5.0
_LOCK_CLEANUP_FAIL_ROUNDS = 3
_ENV_COORD_DIR = "COVERAGE_SCAN_COORD_DIR"
_COORD_KEEP_ENTRIES = 10
_COORD_ENTRY_MAX_AGE_S = 604800.0
_COORD_FINGERPRINT_MAX_ATTEMPTS = 3
# 等待其他会话完成的上限：不得短于单个方法预算，否则「持锁方还在正常
# 跑」也会被并发会话判成死锁。单一真源见
# ``diag_types_vocab.DIAGNOSIS_METHOD_BUDGET_S``。
DEFAULT_WAIT_TIMEOUT_S = DIAGNOSIS_METHOD_BUDGET_S
DEFAULT_CACHE_MAX_AGE_S = 86400.0
DEFAULT_WORKERS = "auto"
_TMP_RESIDUE_MAX_AGE_S = 3600.0
_BUDGET_LOCK_WAIT_S = 2.0
_BUDGET_LOCK_POLL_S = 0.05
_BUDGET_LOCK_STALE_S = 60.0
class ScanParams(NamedTuple):
    root: Path
    threshold: float
    data_dir: str | Path | None
    warnings: list
    tests_dir: Path | None = None
class CoordPolicy(NamedTuple):
    force_refresh: bool
    force_parallel: bool
    wait_timeout_s: float
    cache_max_age_s: float
def _tests_dir_identity(project_root: Path,
                        tests_dir: Path | None) -> str:
    candidate = (Path(tests_dir) if tests_dir is not None
                 else _discover_default_tests_dir(project_root))
    if candidate is None:
        candidate = project_root
    if not candidate.is_absolute():
        candidate = project_root / candidate
    return str(candidate.resolve())
def _coord_base() -> Path | None:
    env_dir = os.environ.get(_ENV_COORD_DIR, "").strip()
    if not env_dir:
        try:
            return Path(get_temp_base()) / "coverage-coord"
        except (RuntimeError, ValueError) as e:
            _log.debug("[scanner] 无可用工作空间，协调层降级直扫: %s", e)
            return None
    base = Path(env_dir)
    return base if _override_within_workspace(base) else None
def _override_within_workspace(base: Path) -> bool:
    try:
        _ws = Path(get_temp_base()).parent
        _base_real = os.path.normcase(os.path.realpath(str(base)))
        _ws_real = os.path.normcase(os.path.realpath(str(_ws)))
    except (RuntimeError, ValueError, OSError) as e:
        _log.debug("[scanner] override 落点守卫判定失败(降级直扫): %s", e)
        return False
    if _base_real == _ws_real or _base_real.startswith(_ws_real + os.sep):
        return True
    _log.warning(
        "[scanner] %s=%s 不在会话工作空间内（Temp 治理契约），"
        "忽略 override 降级直扫", _ENV_COORD_DIR, base)
    return False
def _coord_root(project_root: Path) -> Path | None:
    base = _coord_base()
    if base is None:
        return None
    try:
        key = hashlib.sha256(
            str(Path(project_root).resolve()).encode("utf-8")).hexdigest()[:16]
        path = base / key
        path.mkdir(parents=True, exist_ok=True)
    except (OSError, ValueError, TypeError) as e:
        _log.warning("[scanner] 协调目录不可用（降级无协调）: %s", e)
        return None
    return path
def _sweep_tmp_residue(directory: Path,
                       max_age_s: float = _TMP_RESIDUE_MAX_AGE_S) -> int:
    removed = 0
    try:
        for tmp in directory.glob("*.tmp*"):
            try:
                if (time.time() - tmp.stat().st_mtime > max_age_s
                        and _remove_or_tombstone(tmp)):
                    removed += 1
            except OSError as e:
                _log.debug("临时文件清理失败（残留待后续回收）: %s: %s", tmp, e)
    except OSError:
        _log.debug("[scanner] tmp 残留清扫异常(不阻断)", exc_info=True)
    return removed
def _prune_coord_entries(coord_dir: Path, keep: int = _COORD_KEEP_ENTRIES,
                         max_age_s: float = _COORD_ENTRY_MAX_AGE_S) -> dict:
    keep = norm_nonneg_int(keep, _COORD_KEEP_ENTRIES, "keep")
    removed = _sweep_tmp_residue(coord_dir)
    now = time.time()
    aged: list[tuple[float, Path]] = []
    for f in coord_dir.glob("*.json"):
        try:
            age = now - f.stat().st_mtime
        except OSError as e:
            _log.debug("文件状态探测失败（跳过）: %s", e)
            continue
        if age > max_age_s:
            if _remove_or_tombstone(f):
                removed += 1
            else:
                _log.debug("[scanner] 过期登记删除失败(下轮再试)",
                           exc_info=True)
        else:
            aged.append((age, f))
    aged.sort(key=lambda t: t[0])
    for _, f in aged[keep:]:
        if _remove_or_tombstone(f):
            removed += 1
        else:
            _log.debug("[scanner] 超量登记删除失败(下轮再试)",
                       exc_info=True)
    return {"removed": removed,
            "kept": min(len(aged), keep)}
def _file_content_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()
def _fingerprint_file_candidate(name: str, in_tests: bool = False) -> bool:
    lowered = name.lower()
    if lowered.startswith(".coverage") or lowered.endswith((".pyc", ".pyo")):
        return False
    return in_tests or not is_runtime_log_artifact(name)
def _fingerprint_entries(root: Path,
                         scan_dir: Path | None = None) -> list[str]:
    root = root.resolve()
    scan_root = scan_dir.resolve() if scan_dir is not None else None
    entries: list[str] = []
    for dirpath, dirnames, filenames in os.walk(root):
        current = Path(dirpath)
        if current == scan_root and scan_root != root:
            dirnames.clear()
            continue
        dirnames[:] = sorted(
            d for d in dirnames
            if d.lower() not in SKIP_DIRS_LOWER
            and (d.lower() in TEST_DIR_CANDIDATES
                 or not is_out_of_scope_dir(d))
            and not (current == scan_root and _run_stamp(d) is not None))
        rel_parts = current.relative_to(root).parts
        in_tests = any(
            part.lower() in TEST_DIR_CANDIDATES for part in rel_parts)
        for fn in sorted(filenames):
            if not _fingerprint_file_candidate(fn, in_tests):
                continue
            p = Path(dirpath) / fn
            rel = p.relative_to(root).as_posix()
            try:
                st = p.stat()
                entries.append(
                    f"{rel}|{st.st_size}|{st.st_mtime_ns}|"
                    f"{_file_content_digest(p)}")
            except OSError:
                _log.debug("[scanner] 清单 stat/读取失败，记 missing: %s", rel)
                entries.append(f"{rel}|missing")
    return entries
def _fingerprint_project(root: Path,
                         data_dir: str | Path | None = None,
                         tests_dir: Path | None = None) -> str:
    root = Path(root).resolve()
    scan_dir = Path(data_dir) if data_dir is not None else None
    scopes: list[tuple[str, Path]] = [("project", root)]
    tests_root = Path(_tests_dir_identity(root, tests_dir)).resolve()
    try:
        tests_root.relative_to(root)
    except ValueError:
        scopes.append(("external-tests", tests_root))
    h = hashlib.sha256()
    h.update(_COORD_VERSION.encode("utf-8"))
    for label, scope_root in scopes:
        entries = _fingerprint_entries(scope_root, scan_dir=scan_dir)
        h.update(label.encode("utf-8"))
        h.update(b"\x00")
        h.update(str(len(entries)).encode("ascii"))
        h.update(b"\x00")
        for entry in entries:
            h.update(entry.encode("utf-8"))
            h.update(b"\x00")
    return h.hexdigest()
def _atomic_write_json(path: Path, payload: dict, *,
                       indent: int | None = None) -> None:
    atomic_write_text(
        str(path),
        json.dumps(payload, ensure_ascii=False, indent=indent, default=str),
        tag="cov_scan")
def _remove_or_tombstone(path: Path) -> bool:
    try:
        path.unlink()
        return True
    except FileNotFoundError:
        _log.debug("[scanner] unlink 幂等命中: 文件已不存在: %s", path)
        return True
    except OSError:
        if move_to_recycle_bin(str(path)):
            _log.debug("[scanner] unlink 受限，经回收站通道清理: %s", path)
            return True
        if ".tmp-dead-" in path.name:
            return False
        try:
            tomb = path.with_name(f"{path.name}.tmp-dead-{os.getpid()}")
            os.replace(str(path), str(tomb))
            _log.debug("[scanner] 回收站不可用，已降级墓碑改名: %s", tomb.name)
            return True
        except OSError:
            _log.debug("[scanner] unlink 与墓碑改名均失败: %s", path)
            return False
def _acquire_lock(lock_path: Path, holder_pid: int) -> bool:
    try:
        fd = os.open(str(lock_path),
                     os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except OSError:
        _log.debug("[scanner] 跨进程锁获取被拒（他人持有/IO 失败）: %s", lock_path)
        return False
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(json.dumps({"pid": holder_pid, "ts": time.time()}))
        return True
    except OSError:
        _log.debug("[scanner] 半写锁清理（留待 stale 清理）: %s", lock_path)
        _remove_or_tombstone(lock_path)
        return False
def _read_json_object(path: Path, label: str) -> dict | None:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError, RecursionError):
        _log.debug("[scanner] %s 不可读/损坏，按缺失处理: %s", label, path)
        return None
    return data if isinstance(data, dict) else None
def _nonnegative_age(now: float, timestamp) -> float | None:
    ts = safe_float(timestamp, -1)
    if ts <= 0:
        return None
    age = now - ts
    return age if age >= 0 else None
def _lock_is_stale(lock_path: Path, now: float,
                   stale_after_s: float = _LOCK_STALE_S, *,
                   label: str = "锁") -> bool:
    info = _read_json_object(lock_path, "锁内容")
    if info is not None:
        if psutil_available():
            return not pid_exists(pid_or(info.get("pid")))
        age = _nonnegative_age(now, info.get("ts"))
        return age is None or age > stale_after_s
    try:
        grace_s = min(stale_after_s, _LOCK_INCOMPLETE_STALE_S)
        age = now - lock_path.stat().st_mtime
        return age < 0 or age > grace_s
    except OSError:
        _log.debug("[scanner] %s mtime 不可读，按过期处理: %s",
                   label, lock_path)
        return True
def _release_lock(lock_path: Path, holder_pid: int,
                  force: bool = False) -> None:
    if _lock_owned_elsewhere(lock_path, holder_pid, force):
        return
    if not _remove_or_tombstone(lock_path):
        _log.warning("[scanner] 锁文件删除失败(不阻断，锁将留待 stale 清理)")
def _lock_owned_elsewhere(lock_path: Path, holder_pid: int, force: bool) -> bool:
    info = _read_json_object(lock_path, "锁内容")
    if info is None:
        return (not force) or (not lock_path.exists())
    other = pid_or(info.get("pid"))
    if other == holder_pid:
        return False
    if not force:
        return True
    return psutil_available() and bool(pid_exists(other))
def _active_or_none(data: dict) -> list | None:
    raw = data.get("active")
    return raw if isinstance(raw, list) else None
def _session_live(entry, now: float) -> bool:
    if not isinstance(entry, dict):
        return False
    if psutil_available():
        return pid_exists(pid_or(entry.get("pid")))
    age = _nonnegative_age(now, entry.get("ts"))
    return age is not None and age <= _LOCK_STALE_S
def _iter_live_sessions(data: dict, now: float):
    for entry in (_active_or_none(data) or []):
        if _session_live(entry, now):
            yield entry
def _collect_active_sessions(data: dict, now: float, fp16: str,
                            pid: int) -> list:
    return [a for a in _iter_live_sessions(data, now)
            if not _is_own_session_entry(a, fp16, pid)]
def _budget_lock_path(base: Path) -> Path:
    return base / "global_budget.lock"
def _acquire_budget_lock(base: Path, holder_pid: int) -> bool:
    lock_path = _budget_lock_path(base)
    deadline = time.time() + _BUDGET_LOCK_WAIT_S
    while True:
        if _acquire_lock(lock_path, holder_pid):
            return True
        if _lock_is_stale(
                lock_path, time.time(), stale_after_s=_BUDGET_LOCK_STALE_S,
                label="预算锁"):
            _release_lock(lock_path, holder_pid, force=True)
            if _acquire_lock(lock_path, holder_pid):
                return True
        if time.time() >= deadline:
            _log.warning(
                "[scanner] 全局预算锁等待超时（降级无预算限制）: %s",
                lock_path)
            return False
        time.sleep(_BUDGET_LOCK_POLL_S)
def _budget_register(base: Path, fp16: str, pid: int,
                     cpu_count: int) -> int | None:
    path = base / "global_budget.json"
    if not _acquire_budget_lock(base, pid):
        return None
    try:
        now = time.time()
        _sweep_tmp_residue(base)
        data = _read_json_object(path, "全局预算注册表")
        if data is None:
            try:
                path.stat()
            except FileNotFoundError:
                data = {}
            except OSError:
                _log.warning(
                    "[scanner] 预算注册表状态不可判定，降级无预算限制且保留原文件",
                    exc_info=True)
                return None
            else:
                _log.warning(
                    "[scanner] 预算注册表不可读或损坏，降级无预算限制且保留原文件")
                return None
        elif _active_or_none(data) is None:
            _log.warning(
                "[scanner] 预算注册表 active 缺失或形态非法，"
                "降级无预算限制且保留原文件")
            return None
        active = _collect_active_sessions(data, now, fp16, pid)
        budget = max(2, cpu_count // (len(active) + 1))
        active.append({"fp16": fp16, "pid": pid, "ts": now})
        data["schema"] = _COORD_SCHEMA
        data["active"] = active
        try:
            _atomic_write_json(path, data)
        except OSError:
            _log.warning(
                "[scanner] 预算注册写入失败(降级无预算限制)", exc_info=True)
            return None
        return budget
    finally:
        _release_lock(_budget_lock_path(base), pid)
def _is_own_session_entry(item: Any, fp16: str, pid: int) -> bool:
    return (isinstance(item, dict) and item.get("fp16") == fp16
            and item.get("pid") == pid)
def _budget_unregister(base: Path, fp16: str, pid: int) -> None:
    if not _acquire_budget_lock(base, pid):
        return
    try:
        path = base / "global_budget.json"
        data = _read_json_object(path, "全局预算注册表")
        if data is None:
            return
        raw_active = _active_or_none(data)
        if raw_active is None:
            return
        data["active"] = [a for a in raw_active
                          if not _is_own_session_entry(a, fp16, pid)]
        try:
            _atomic_write_json(path, data)
        except (OSError, ValueError):
            _log.warning("[scanner] 预算注销失败(best-effort 活性过滤自愈)",
                         exc_info=True)
    finally:
        _release_lock(_budget_lock_path(base), pid)
def _has_other_active_session(data: dict, now: float,
                              self_pid: int, self_fp16: str = "") -> bool:
    for a in _iter_live_sessions(data, now):
        pid = a.get("pid")
        if pid is None:
            continue
        if self_fp16:
            if _is_own_session_entry(a, self_fp16, self_pid):
                continue
        elif pid == self_pid:
            continue
        return True
    return False
def hook_recycle_safe(coord_ctx: dict | None, self_pid: int) -> bool:
    if not coord_ctx or not coord_ctx.get("base"):
        return True
    registry = Path(coord_ctx["base"]) / "global_budget.json"
    data = _read_json_object(registry, "全局预算注册表")
    if data is None:
        try:
            registry.stat()
        except FileNotFoundError:
            return True
        except OSError:
            _log.warning("[scanner] 活跃注册表状态不可判定，推迟钩子回收: %s",
                         registry)
            return False
        _log.warning("[scanner] 活跃注册表不可读或损坏，推迟钩子回收: %s",
                     registry)
        return False
    if _active_or_none(data) is None:
        _log.warning("[scanner] 活跃注册表 active 缺失或形态非法，推迟钩子回收: %s",
                     registry)
        return False
    self_fp16 = coord_ctx.get("fp16", "")
    if not isinstance(self_fp16, str):
        self_fp16 = ""
    return not _has_other_active_session(
        data, time.time(), self_pid, self_fp16)
def _normalize_cached_siblings(entry: dict) -> tuple[dict | None, str]:
    wd = entry.get("workers_data")
    pt = entry.get("pytest_tail")
    return (wd if isinstance(wd, dict) else None,
            pt if isinstance(pt, str) else "")
def _persist_cached_report(report: Any,
                           params: ScanParams) -> tuple[Path | None, Path | None]:
    run_dir: Path | None = None
    json_path: Path | None = None
    try:
        run_dir = new_run_dir(scan_base_dir(params.data_dir, params.root))
        json_path = run_dir / "coverage_scan.json"
        _atomic_write_json(json_path, report, indent=2)
    except (OSError, RuntimeError, ValueError) as exc:
        _log.warning("[scanner] 缓存报告落盘失败（降级仅返回摘要）: %s",
                     exc, exc_info=True)
        _note_persist_failure(params, exc)
        json_path = None
    return run_dir, json_path
def _note_persist_failure(params: ScanParams, exc: BaseException) -> None:
    params.warnings.append(
        "缓存命中但报告落盘失败（json_path 不可用，下游导出/对比"
        f"将不可用）: {exc}")
def _scan_artifact_fields(run_dir: Path | None,
                          json_path: Path | None) -> dict[str, str]:
    return {"scan_dir": str(run_dir.parent) if run_dir else "",
            "run_dir": str(run_dir or ""),
            "json_path": str(json_path or "")}
def _pytest_failure_warning(returncode: int | None) -> str:
    return ("pytest 主跑存在失败用例（returncode=1）；覆盖率仅反映已执行路径，"
            "不能作为测试通过证据" if returncode == 1 else "")
def _empty_workers_data() -> dict:
    return {"copies": 0, "valid": 0, "suspect": 0,
            "statement_only": 0, "empty": 0, "unreadable": 0,
            "unreadable_names": [], "total_line_records": 0}
def _build_cached_summary(entry: dict, params: ScanParams,
                          coord_dir: Path, cache_age_s: float) -> dict:
    report = entry.get("raw_report")
    workers_data, pytest_tail = _normalize_cached_siblings(entry)
    pytest_returncode = _as_int_or_none(entry.get("pytest_returncode"))
    summary = summarize_coverage_report(report, threshold=params.threshold,
                                        scope="source",
                                        project_root=str(params.root))
    run_dir, json_path = _persist_cached_report(report, params)
    params.warnings.append(
        "复用跨会话扫描缓存（项目指纹一致，扫于 "
        f"{entry.get('created_human', '?')}，age={cache_age_s:.0f}s；"
        "force_refresh=True 可强制重扫）")
    failure_warning = _pytest_failure_warning(pytest_returncode)
    if failure_warning:
        params.warnings.append(failure_warning)
    summary.update({
        **_scan_artifact_fields(run_dir, json_path),
        "workers_data": workers_data or _empty_workers_data(),
        "warnings": params.warnings,
        "from_cache": True,
        "cache": {"created_ts": entry.get("created_ts"),
                  "age_s": round(cache_age_s, 1),
                  "fingerprint": entry.get("fingerprint", "")[:16],
                  "coord_dir": str(coord_dir)},
        "resource_governance": {"from_cache": True,
                                  "pytest_returncode": pytest_returncode},
        "pytest_tail": pytest_tail,
    })
    return summary
def _load_fresh_entry(coord_dir: Path, fp16: str, fp: str,
                      ttl: float, project_root: Path,
                      tests_dir: Path | None) -> dict | None:
    if not ttl > 0:
        return None
    entry = _read_json_object(coord_dir / f"{fp16}.json", "协调登记")
    if entry is None or entry.get("fingerprint") != fp:
        return None
    if entry.get("schema") != _COORD_SCHEMA:
        return None
    created_ts = safe_float(entry.get("created_ts"), -1)
    if created_ts <= 0 or not _entry_payload_ok(entry):
        return None
    cache_age_s = time.time() - created_ts
    if cache_age_s < 0 or cache_age_s > ttl:
        return None
    expected_tests_dir = _tests_dir_identity(project_root, tests_dir)
    cached_tests_dir = entry.get("tests_dir")
    if cached_tests_dir is None:
        cached_tests_dir = _tests_dir_identity(project_root, None)
    if cached_tests_dir != expected_tests_dir:
        return None
    return entry
def _entry_payload_ok(entry: dict) -> bool:
    raw_report = entry.get("raw_report")
    if not isinstance(raw_report, dict):
        return False
    files = raw_report.get("files")
    if not isinstance(files, dict) or not files:
        return False
    return all(isinstance(info, dict) and isinstance(info.get("summary"), dict)
               for info in files.values())
def _cache_hit_payload(entry: dict, coord_dir: Path, fp: str,
                       fp16: str) -> dict:
    return {"cache_hit": True, "entry": entry, "coord_dir": coord_dir,
            "fingerprint": fp, "fp16": fp16,
            "cache_age_s": time.time() - safe_float(entry.get("created_ts"))}
def _reclaim_stale_lock(lock_path: Path, holder_pid: int,
                        stale_rounds: int) -> tuple[bool, int]:
    _release_lock(lock_path, holder_pid, force=True)
    if _acquire_lock(lock_path, holder_pid):
        return True, stale_rounds
    if not _lock_is_stale(lock_path, time.time()):
        return False, 0
    stale_rounds += 1
    _log.warning("[scanner] stale 锁清理未生效（第 %d/%d 轮）: %s",
                 stale_rounds, _LOCK_CLEANUP_FAIL_ROUNDS, lock_path.name)
    if stale_rounds >= _LOCK_CLEANUP_FAIL_ROUNDS:
        raise ScanStepError(
            0, "传 force_parallel=True 直接并行扫、coordination=False 禁用协调",
            f"stale 锁清理失败：锁文件无法删除"
            f"（权限或安全策略拒绝），锁: {lock_path}")
    return False, stale_rounds
def _acquire_lock_with_wait(lock_path: Path, holder_pid: int, *,
                            force_parallel: bool,
                            wait_timeout_s: float) -> bool:
    deadline = time.time() + wait_timeout_s
    waited = False
    stale_stuck_rounds = 0
    has_lock = _acquire_lock(lock_path, holder_pid)
    while not has_lock and not force_parallel:
        if _lock_is_stale(lock_path, time.time()):
            has_lock, stale_stuck_rounds = _reclaim_stale_lock(
                lock_path, holder_pid, stale_stuck_rounds)
            if has_lock:
                break
        else:
            stale_stuck_rounds = 0
        if time.time() >= deadline:
            raise ScanStepError(
                0, "传 force_parallel=True 不等待直接并行扫，或 "
                   "coordination=False 直扫，或稍后重试"
                   "（先到会话完成后本会话将直接复用）",
                "等待其他会话完成同一项目扫描超时")
        if not waited and not stale_stuck_rounds:
            _log.info("[scanner] 其他会话正在扫描同一项目，等待完成后复用其"
                      "结果（轮询 %.0fs，上限 %.0fs）…", _LOCK_POLL_S,
                      wait_timeout_s)
            waited = True
        time.sleep(_LOCK_POLL_S)
        has_lock = _acquire_lock(lock_path, holder_pid)
    return has_lock
def _normalize_coord_windows(wait_timeout_s: float,
                             cache_max_age_s: float
                             ) -> tuple[float, float]:
    return (max(0.0, as_number(wait_timeout_s, 0.0)),
            max(0.0, as_number(cache_max_age_s, DEFAULT_CACHE_MAX_AGE_S)))
def _prune_coord_entries_logged(coord_dir: Path) -> None:
    try:
        pruned = _prune_coord_entries(coord_dir)
        if pruned["removed"]:
            _log.info("[scanner] 协调登记惰性回收: 删除 %d 份（保留 %d 份在窗口内）",
                      pruned["removed"], pruned["kept"])
    except Exception:  # noqa: BLE001
        _log.debug("[scanner] 协调登记回收异常(不阻断)", exc_info=True)
def _register_budget_guarded(base: Path, fp16: str, holder_pid: int,
                             lock_path: Path | None) -> int | None:
    try:
        return _budget_register(base, fp16, holder_pid, _auto_worker_cap())
    except BaseException:
        if lock_path is not None:
            _release_lock(lock_path, holder_pid)
        raise
def _coordination_enter(project_root: Path, policy: CoordPolicy,
                        holder_pid: int,
                        tests_dir: Path | None = None,
                        data_dir: str | Path | None = None) -> dict | None:
    coord_dir = _coord_root(project_root)
    if coord_dir is None:
        _log.warning("[scanner] 协调目录不可用，降级为无协调直扫")
        return None
    _prune_coord_entries_logged(coord_dir)
    fp = _fingerprint_project(
        project_root, data_dir=data_dir, tests_dir=tests_dir)
    base = coord_dir.parent
    wait_timeout_s, ttl = _normalize_coord_windows(
        policy.wait_timeout_s, policy.cache_max_age_s)
    for attempt in range(_COORD_FINGERPRINT_MAX_ATTEMPTS):
        fp16 = fp[:16]
        entry = (None if policy.force_refresh
                 else _load_fresh_entry(
                     coord_dir, fp16, fp, ttl, project_root, tests_dir))
        if entry is not None:
            return _cache_hit_payload(entry, coord_dir, fp, fp16)
        lock_path = coord_dir / f"{fp16}.lock"
        has_lock = _acquire_lock_with_wait(
            lock_path, holder_pid, force_parallel=policy.force_parallel,
            wait_timeout_s=wait_timeout_s)
        if has_lock:
            latest_fp = _fingerprint_project(
                project_root, data_dir=data_dir, tests_dir=tests_dir)
            if latest_fp != fp:
                _release_lock(lock_path, holder_pid)
                fp = latest_fp
                if attempt + 1 < _COORD_FINGERPRINT_MAX_ATTEMPTS:
                    continue
                _log.warning(
                    "[scanner] 等锁期间项目指纹连续变化（%d 轮），"
                    "降级无协调直扫以避免旧指纹缓存",
                    _COORD_FINGERPRINT_MAX_ATTEMPTS)
                return None
        if has_lock and not policy.force_refresh:
            entry = _load_fresh_entry(
                coord_dir, fp16, fp, ttl, project_root, tests_dir)
            if entry is not None:
                _release_lock(lock_path, holder_pid)
                return _cache_hit_payload(entry, coord_dir, fp, fp16)
        budget = _register_budget_guarded(
            base, fp16, holder_pid, lock_path if has_lock else None)
        return {"cache_hit": False, "coord_dir": coord_dir, "base": base,
                "fingerprint": fp, "fp16": fp16, "lock_path": lock_path,
                "has_lock": has_lock, "holder_pid": holder_pid,
                "budget_workers": budget,
                "budget_registered": budget is not None,
                "data_dir": data_dir}
    return None
def coordination_publish(ctx: dict, report: dict, summary: dict,
                          project_root: Path, threshold: float,
                          tests_dir: Path | None = None) -> None:
    if not ctx.get("has_lock"):
        return
    current_fp = _fingerprint_project(
        project_root, data_dir=ctx.get("data_dir"), tests_dir=tests_dir)
    if current_fp != ctx["fingerprint"]:
        _log.warning(
            "[scanner] 扫描期间项目指纹变化，丢弃协调缓存登记: "
            "before=%s after=%s", ctx["fingerprint"][:16], current_fp[:16])
        return
    entry = {
        "schema": _COORD_SCHEMA,
        "fingerprint": ctx["fingerprint"],
        "project_root": str(project_root),
        "created_ts": time.time(),
        "created_human": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "threshold": threshold,
        "tests_dir": _tests_dir_identity(project_root, tests_dir),
        "holder_pid": ctx["holder_pid"],
        "workers_data": summary.get("workers_data"),
        "pytest_tail": summary.get("pytest_tail", ""),
        "pytest_returncode": summary.get(
            "resource_governance", {}).get("pytest_returncode"),
        "raw_report": report,
    }
    _atomic_write_json(ctx["coord_dir"] / f"{ctx['fp16']}.json", entry)
def coordination_exit(ctx: dict) -> None:
    try:
        if ctx.get("budget_registered"):
            _budget_unregister(ctx["base"], ctx["fp16"], ctx["holder_pid"])
    finally:
        if ctx.get("has_lock"):
            _release_lock(ctx["lock_path"], ctx["holder_pid"])
            ctx["has_lock"] = False
def coordination_cache_attempt(
        params: ScanParams,
        policy: CoordPolicy) -> tuple[dict | None, dict | None]:
    coord_ctx = _coordination_enter(params.root, policy,
                                   holder_pid=os.getpid(),
                                   tests_dir=params.tests_dir,
                                   data_dir=params.data_dir)
    if coord_ctx and coord_ctx.get("cache_hit"):
        csum = _build_cached_summary(
            coord_ctx["entry"], params,
            coord_dir=coord_ctx["coord_dir"],
            cache_age_s=coord_ctx["cache_age_s"])
        result = step_ok(
            csum,
            f"覆盖率扫描(跨会话缓存复用): 总体 {csum['totals']['percent']}%, "
            f"{csum['below_count']}/{csum['module_count']} 模块低于 "
            f"{params.threshold}%")
        return result, coord_ctx
    return None, coord_ctx
def _as_int_or_none(value) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError) as _e:
        _log.debug("[scanner] 整数参数不可归一（按 None 处理）: %r (%s)",
                   value, type(_e).__name__)
        return None
def _norm_workers(workers: str | int) -> str | int:
    if (isinstance(workers, str)
            and workers.strip().lower() == DEFAULT_WORKERS):
        return DEFAULT_WORKERS
    norm = _as_int_or_none(workers)
    if norm is None:
        _log.warning("[scanner] workers 形态非法（%r），降级串行 0", workers)
        return 0
    if norm < 0:
        _log.warning("[scanner] workers 为负（%r），降级串行 0", workers)
        return 0
    return norm
def _norm_cap(max_workers: int | None) -> int | None:
    if max_workers is None:
        return None
    norm = _as_int_or_none(max_workers)
    if norm is None:
        _log.warning("[scanner] max_workers 形态非法（%r），按未设限处理",
                     max_workers)
        return None
    if norm < 0:
        _log.warning("[scanner] max_workers 为负（%r），按未设限处理",
                     max_workers)
        return None
    return norm
def _auto_worker_cap() -> int:
    return min(os.cpu_count() or 2, _AUTO_WORKERS_CAP)
def resolve_effective_workers(workers: str | int,
                               max_workers: int | None) -> str | int:
    workers = _norm_workers(workers)
    if workers == 0:
        return 0
    cap = _norm_cap(max_workers)
    if workers == "auto":
        auto = _auto_worker_cap()
        return auto if cap is None else min(auto, cap)
    if cap is None:
        return workers
    return min(int(workers), cap)
def _gov_observables(gov: dict) -> dict:
    return {k: v for k, v in gov.items() if k != "tree_snapshot"}
class _ScanContext:
    __slots__ = (
        "audit",
        "cache_max_age_s",
        "consumed_cleanup",
        "coord_ctx",
        "coordination",
        "cr",
        "cvm",
        "data_dir",
        "dfm",
        "env",
        "force_parallel",
        "force_refresh",
        "gc_reclaimed_mb",
        "gov",
        "hook_cleanup_pending",
        "hook_err",
        "hook_recycled",
        "hook_released",
        "json_path",
        "max_workers",
        "pytest_log",
        "rc",
        "report",
        "root",
        "run_dir",
        "skip_prewarm",
        "tdir",
        "threshold",
        "timeout_s",
        "wait_timeout_s",
        "warnings",
        "workers",
        "workers_eff",
    )
    def __init__(self, *, threshold: float, workers: str | int,
                 max_workers: int | None, data_dir, coordination: bool,
                 force_refresh: bool, force_parallel: bool,
                 wait_timeout_s: float, cache_max_age_s: float,
                 skip_prewarm: bool, timeout_s: int | None):
        self.threshold = threshold
        self.workers = workers
        self.max_workers = max_workers
        self.data_dir = data_dir
        self.coordination = coordination
        self.force_refresh = force_refresh
        self.force_parallel = force_parallel
        self.wait_timeout_s = wait_timeout_s
        self.cache_max_age_s = cache_max_age_s
        self.skip_prewarm = skip_prewarm
        self.timeout_s = _norm_timeout_s(timeout_s)
        self._init_state()
        self._init_artifacts(workers)
    def _init_state(self) -> None:
        self.warnings: list[str] = []
        self.coord_ctx: dict | None = None
        self.hook_cleanup_pending = False
        self.hook_released = False
        self.hook_recycled = False
        self.hook_err = ""
    def _init_artifacts(self, workers: str | int) -> None:
        self.root: Path | None = None
        self.tdir: Path | None = None
        self.run_dir: Path | None = None
        self.rc: Path | None = None
        self.env: dict = {}
        self.workers_eff: str | int = workers
        self.pytest_log = ""
        self.gov: dict = {}
        self.audit: dict = {}
        self.dfm: Path | None = None
        self.cr: _coverage.Coverage | None = None
        self.cvm: _coverage.Coverage | None = None
        self.json_path: Path | None = None
        self.report: dict = {}
        self.gc_reclaimed_mb = 0.0
        self.consumed_cleanup: dict = {}
def _release_hook_once(ctx: _ScanContext) -> None:
    if ctx.hook_released or not ctx.hook_cleanup_pending:
        return
    try:
        done = _recycle_managed_hook(ctx)
    except Exception:  # noqa: BLE001
        ctx.hook_err = "回收链异常（已消化，见日志）"
        _log.warning("[scanner] 自启动钩子回收兜底异常(不阻断)",
                     exc_info=True)
        done = False
    if done:
        ctx.hook_released = True
def _recycle_managed_hook(ctx: _ScanContext) -> bool:
    coord_ctx = ctx.coord_ctx or {}
    base_value = coord_ctx.get("base")
    base = Path(base_value) if base_value else None
    holder_pid = os.getpid()
    lock_acquired = False
    if base is not None:
        lock_acquired = _acquire_budget_lock(base, holder_pid)
        if not lock_acquired:
            _log.info("[scanner] 全局预算锁不可用，本轮推迟钩子回收"
                      "（钩子惰性残留无害）")
            return False
    try:
        # 与 _budget_register 共用同一把锁，闭合“检查活跃会话”到
        # “删除钩子”之间的注册竞态，避免新会话复用即将被删除的钩子。
        if not hook_recycle_safe(ctx.coord_ctx, holder_pid):
            _log.info("[scanner] 检测到其他活跃扫描复用钩子，本轮推迟"
                      "回收（钩子惰性残留无害）")
            return False
        rem = remove_autostart_hook()
        if not rem.get("existed"):
            ctx.hook_err = rem.get("error") or ""
            return True
        removed = bool(rem.get("removed"))
        error = rem.get("error") or ""
        ctx.hook_recycled = removed and not error
        ctx.hook_err = error
        if ctx.hook_recycled:
            _log.info("[scanner] 本轮安装的自启动钩子已回收: %s",
                      rem.get("hook", ""))
            return True
        _log.warning("[scanner] 自启动钩子回收未完成(不阻断): %s",
                     error or "钩子仍存在")
        return False
    finally:
        if base is not None and lock_acquired:
            _release_lock(_budget_lock_path(base), holder_pid)
def _validate_scan_inputs(project_dir: str | Path,
                          tests_dir: str | Path | None,
                          threshold: float,
                          ) -> tuple[Path | None, Path | None, dict | None]:
    root, tdir, dir_error = _resolve_scan_dirs(project_dir, tests_dir)
    if dir_error is not None:
        return None, None, dir_error
    threshold_error = _threshold_error(threshold)
    if threshold_error is not None:
        return None, None, threshold_error
    return root, tdir, None
def _discover_default_tests_dir(root: Path) -> Path | None:
    resolved = resolve_tests_dir(str(root))
    return Path(resolved) if resolved is not None else None
def _resolve_scan_dirs(project_dir: str | Path,
                       tests_dir: str | Path | None,
                       ) -> tuple[Path | None, Path | None, dict | None]:
    for _label, _value in (("project_dir", project_dir),
                           ("tests_dir", tests_dir)):
        if isinstance(_value, str) and not _value.strip():
            return None, None, step_err(f"{_label} 不得为空字符串")
        if _value is not None and not isinstance(_value, (str, os.PathLike)):
            return None, None, step_err(
                f"{_label} 形态非法: {type(_value).__name__}")
    root = Path(project_dir).resolve()
    if not root.is_dir():
        return None, None, step_err(f"project_dir 不存在: {root}")
    explicit = tests_dir is not None
    tdir = (Path(tests_dir) if explicit
            else _discover_default_tests_dir(root))
    if tdir is None:
        return None, None, step_skip(
            "未发现测试目录或测试文件（非测试型项目，覆盖率扫描不适用）")
    if not tdir.is_absolute():
        tdir = root / tdir
    if not tdir.is_dir():
        return None, None, step_err(f"tests 目录不存在: {tdir}")
    return root, tdir, None
def _threshold_error(threshold: float) -> dict | None:
    if (isinstance(threshold, bool)
            or not isinstance(threshold, (int, float))
            or not 0 <= threshold <= 100):
        return step_err(
            f"threshold 非法: {threshold!r}（须为 0-100 的数值）")
    return None
def _try_coordination_cache(ctx: _ScanContext) -> dict | None:
    if not ctx.coordination:
        return None
    cached, ctx.coord_ctx = coordination_cache_attempt(
        ScanParams(ctx.root, ctx.threshold, ctx.data_dir, ctx.warnings,
                   ctx.tdir),
        CoordPolicy(ctx.force_refresh, ctx.force_parallel,
                    ctx.wait_timeout_s, ctx.cache_max_age_s))
    return cached
def _measure_env() -> dict:
    env = subprocess_noartifact_env()
    env.pop("PYTEST_ADDOPTS", None)
    return env
def _require_path_like(value: Any, label: str, *,
                       allow_none: bool = False) -> None:
    if value is None and allow_none:
        return
    if not isinstance(value, (str, os.PathLike)) or not str(value):
        raise FileNotFoundError(
            f"{label} 必须为非空字符串或 Path: {value!r}")
def _resolve_tests_dir(project_dir: str | Path,
                       tests_dir: str | Path | None = None) -> Path:
    _require_path_like(project_dir, "project_dir")
    _require_path_like(tests_dir, "tests_dir", allow_none=True)
    try:
        root = Path(project_dir).resolve()
        candidate = (Path(tests_dir) if tests_dir is not None
                     else _discover_default_tests_dir(root))
    except (TypeError, ValueError, OSError) as _pe:
        raise FileNotFoundError(f"路径非法: {_pe}") from _pe
    if candidate is None:
        raise FileNotFoundError(
            f"未发现测试目录或根级测试文件: {root}"
            f"（约定容器 {'/'.join(TEST_DIR_CANDIDATES)} 均不存在，"
            f"可用 --tests-dir 指定）")
    if not candidate.is_absolute():
        candidate = root / candidate
    if not candidate.is_dir():
        raise FileNotFoundError(
            f"tests 目录不存在: {candidate}（可用 --tests-dir 指定）")
    return candidate
def _iter_test_source_files(root: Path) -> list[Path]:
    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(
            d for d in dirnames
            if d.lower() not in SKIP_DIRS_LOWER
            and (d.lower() in TEST_DIR_CANDIDATES
                 or not is_out_of_scope_dir(d)))
        found.extend(Path(dirpath) / name for name in sorted(filenames)
                     if is_test_source_basename(name))
    return found

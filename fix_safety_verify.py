from __future__ import annotations

import ast
import logging
import math
import os
import re
import subprocess
import sys
import time
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from jwsgj.build_safe_write import run_with_swap
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    assign_targets_value,
    collect_param_names,
    is_shell_true_keyword,
    iter_def_site_nodes,
    iter_scope_nodes,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_surface import (
    collect_module_exports_state,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    parse_cached,
    read_source_interpreter_encoding,
)
from jwsgj.diag_types_normalize import (
    coerce_path_str,
    coerce_tolerance,
    finite_float_or_none,
    strip_bom,
)
from jwsgj.diag_types_vocab import (
    CODING_UTF8,
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    SENSITIVE_NAME_KEYWORDS,
)
from jwsgj.log_config import log_swallowed, trace_module_run
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    detect_package_root,
    subprocess_noartifact_env,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.diag_testing_coverage import (
    locate_pytest_summary_line,
    parse_pytest_summary_counts,
)
from jwsgj.testsuite_runner import (
    DEFAULT_TEST_TIMEOUT,
    PYTEST_EXIT_NO_TESTS,
    _build_run_facts,
    _merged_output,
    last_failure_line,
    locate_targeted_tests,
    run_pytest_files,
)

logger = logging.getLogger(__name__)
_MODULE_TAG = "fix_safety_verify"
def _positive_timeout(value: object, default: float) -> float:
    if isinstance(value, bool):
        return float(default)
    try:
        number = float(value)
    except (TypeError, ValueError, OverflowError):
        return float(default)
    return number if math.isfinite(number) and number > 0 else float(default)
DEFAULT_IMPORT_TIMEOUT = 15
_DEFAULT_PROJECT_ROOT = ""
_DEFAULT_SOURCE_ROOTS: tuple[str, ...] = ()
_DEFAULT_SCORE_TOLERANCE = coerce_tolerance(None)
@dataclass(frozen=True)
class LayerConfig:
    skill_dir: str
    test_timeout: int = DEFAULT_TEST_TIMEOUT
    import_timeout: int = DEFAULT_IMPORT_TIMEOUT
    source_roots: tuple[str, ...] = _DEFAULT_SOURCE_ROOTS
_SAFE_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
def _dedup_absolute_paths(paths) -> list[str]:
    result: list[str] = []
    seen: set[str] = set()
    for path in paths:
        path = coerce_path_str(path)
        if not path:
            continue
        absolute = os.path.abspath(path)
        key = os.path.normcase(absolute)
        if key not in seen:
            seen.add(key)
            result.append(absolute)
    return result
def _configured_source_roots(
    project_root: str, source_roots=_DEFAULT_SOURCE_ROOTS,
) -> list[str]:
    candidates = []
    project_root = coerce_path_str(project_root)
    if project_root:
        project_root = os.path.abspath(project_root)
        candidates.extend((project_root, os.path.join(project_root, "src")))
    if isinstance(source_roots, (str, bytes, os.PathLike)):
        source_roots = (source_roots,)
    candidates.extend(source_roots or ())
    return _dedup_absolute_paths(candidates)
def _path_within_root(filepath: str, root: str) -> bool:
    path_key = os.path.normcase(os.path.abspath(filepath))
    root_key = os.path.normcase(os.path.abspath(root))
    try:
        return os.path.commonpath((path_key, root_key)) == root_key
    except ValueError:  # jwsgj:silent-ok
        return False
def _package_name_from_root(filepath: str, package_root: str) -> str:
    if not _path_within_root(filepath, package_root):
        return ""
    try:
        rel_path = os.path.relpath(os.path.abspath(filepath), package_root)
    except (OSError, ValueError) as exc:
        log_swallowed(__name__, exc, context='_package_name_from_root')
        return ""
    parts = [p for p in rel_path.replace(os.sep, "/").split("/")
             if p and p != "."]
    if not parts:
        return ""
    stem, is_package = os.path.splitext(parts[-1])[0], False
    if stem == "__init__":
        parts, is_package = parts[:-1], True
    else:
        parts[-1] = stem
    if not parts or not all(_SAFE_IDENTIFIER_RE.fullmatch(p) for p in parts):
        return ""
    full_name = ".".join(parts)
    if is_package:
        return full_name
    return full_name.rsplit(".", 1)[0] if "." in full_name else ""
def _verification_package_root(
    filepath: str, project_root: str = _DEFAULT_PROJECT_ROOT,
    source_roots=_DEFAULT_SOURCE_ROOTS,
) -> str:
    abs_path = os.path.abspath(filepath)
    regular_root = detect_package_root(abs_path)
    if _package_name_from_root(abs_path, regular_root):
        return regular_root
    matches = [root for root in _configured_source_roots(
        project_root, source_roots) if _path_within_root(abs_path, root)]
    return max(matches, key=len) if matches else regular_root
def _package_context(
    filepath: str, project_root: str = _DEFAULT_PROJECT_ROOT,
    source_roots=_DEFAULT_SOURCE_ROOTS,
) -> str:
    package_root = _verification_package_root(
        filepath, project_root, source_roots)
    return _package_name_from_root(filepath, package_root)
def _verification_sys_paths(
    filepath: str, project_root: str,
    source_roots=_DEFAULT_SOURCE_ROOTS, include_source_dir: bool = True,
) -> list[str]:
    candidates = _configured_source_roots(project_root, source_roots)
    if include_source_dir:
        candidates.append(os.path.dirname(os.path.abspath(filepath)))
    candidates.append(_verification_package_root(
        filepath, project_root, source_roots))
    return _dedup_absolute_paths(candidates)
def _build_subprocess_exec_script(*,
                                  mod_name: str,
                                  filepath: str,
                                  sys_paths: list[str],
                                  conditional_register: bool,
                                  package_name: str = "") -> list[str]:
    if not sys_paths:
        raise ValueError("sys_paths 语义契约：至少一条，按优先级递增")
    lines = [
        CODING_UTF8,
        "import sys",
        "import types",
    ]
    lines.extend(f"sys.path.insert(0, {_p!r})" for _p in sys_paths)
    lines.extend([
        "",
        "source = sys.stdin.buffer.read().decode('utf-8-sig')",
        "try:",
        f"    mod = types.ModuleType({mod_name!r})",
        f"    mod.__file__ = {filepath!r}",
    ])
    if os.path.basename(filepath) == "__init__.py":
        lines.append(
            f"    mod.__path__ = [{os.path.dirname(filepath)!r}]")
    if package_name:
        lines.append(f"    mod.__package__ = {package_name!r}")
    lines.extend([
        "    # 先注册后执行：模拟正常 import 语义（兼容依赖 sys.modules",
        "    # 的机制）；撞名不覆盖——sys.modules 缓存条目（标准库等）",
        "    # 在真实导入语义中恒优先于同名文件",
    ])
    if conditional_register:
        lines.append(f"    if {mod_name!r} not in sys.modules:")
        lines.append(f"        sys.modules[{mod_name!r}] = mod")
    else:
        lines.append(f"    sys.modules[{mod_name!r}] = mod")
    lines.extend([
        f"    exec(compile(source, {filepath!r}, 'exec'), mod.__dict__)",
        "except SystemExit:",
        "    raise",
        "except Exception as e:",
        "    print(f'IMPORT_FAIL: {type(e).__name__}: {e}')",
        "    sys.exit(1)",
    ])
    return lines
def _verify_syntax(source: str, filepath: str = "") -> tuple[bool, str]:
    filepath = coerce_path_str(filepath)
    try:
        compile(strip_bom(source), filepath or "<fixed>", 'exec')
        return True, ""
    except SyntaxError as e:
        logger.debug("_verify_syntax: 修复后源码语法错误", exc_info=True)
        msg = f"语法错误 L{e.lineno}: {e.msg}"
        if e.text:
            msg += f" | {e.text.strip()}"
        return False, msg
    except PARSE_DEGRADE_EXC as e:
        logger.debug("_verify_syntax: 修复后源码非法", exc_info=True)
        return False, f"源码非法: {e}"
def _verify_import(
    filepath: str,
    source: str,
    cfg: LayerConfig,
) -> tuple[bool, str]:
    filepath = coerce_path_str(filepath)
    if not filepath:
        return False, "filepath 形态异常: 需要非空路径字符串"
    if os.path.isfile(filepath):
        return run_with_swap(
            filepath, source,
            lambda fp: _import_module_safely(
                fp, cfg.import_timeout, os.path.dirname(fp),
                project_root=cfg.skill_dir, source_roots=cfg.source_roots))
    return _verify_source_in_subprocess(
        source, filepath, cfg.import_timeout, cfg.skill_dir,
        source_roots=cfg.source_roots)
def _import_module_safely(
    filepath: str, import_timeout: float,
    extra_sys_path: str | None = None, *,
    project_root: str = _DEFAULT_PROJECT_ROOT,
    source_roots=_DEFAULT_SOURCE_ROOTS,
    timeout_note: str = "导入超时",
    error_note: str = "导入验证异常",
) -> tuple[bool, str]:
    import_timeout = _positive_timeout(
        import_timeout, DEFAULT_IMPORT_TIMEOUT)
    try:
        return subprocess_import_module(
            filepath, import_timeout, extra_sys_path=extra_sys_path,
            project_root=project_root, source_roots=source_roots)
    except subprocess.TimeoutExpired:
        logger.warning("%s: 子进程超时(%ss)", timeout_note, import_timeout)
        return False, f"{timeout_note} ({import_timeout:g}s)"
    except (OSError, ValueError) as e:
        logger.warning("%s: %s", error_note, e, exc_info=True)
        return False, f"{error_note}: {e}"
def _marker_payload(stdout: str, marker: str) -> str:
    return stdout.rsplit(marker, maxsplit=1)[-1].strip().split("\n")[0]
def _has_marker_line(stdout: str, marker: str) -> bool:
    return any(line.strip() == marker for line in stdout.splitlines())
def _verification_marker(prefix: str) -> str:
    return f"{prefix}:{os.urandom(16).hex()}"
def _interpret_exec_output(
    proc: Any, success_marker: str, *, ok_message: str = "",
    fail_label: str = "导入验证", include_exit: bool = False,
) -> tuple[bool, str]:
    stdout = (getattr(proc, "stdout", "") or "").strip()
    if proc.returncode == 0 and _has_marker_line(stdout, success_marker):
        return True, ok_message
    stderr = (getattr(proc, "stderr", "") or "").strip()
    if "IMPORT_FAIL" in stdout:
        msg = _marker_payload(stdout, "IMPORT_FAIL:")
        if include_exit:
            return False, f"{fail_label}导入失败: {msg}"
        return False, msg[:200] or f"{fail_label}失败"
    if include_exit:
        error = stderr[:500] if stderr else stdout[:500]
        return False, f"{fail_label}异常 (exit={proc.returncode}): {error}"
    return False, _last_stderr_error_line(stderr, stdout)
def _last_stderr_error_line(stderr: str, stdout: str,
                            default: str = "导入验证失败(无输出)") -> str:
    error_lines = [ln for ln in stderr.splitlines() if ln.strip()]
    last_error = error_lines[-1] if error_lines else stdout[:200]
    return last_error[:200] or default
def _run_python_stdin(script: str, source: str, timeout: int, cwd: str):
    timeout = _positive_timeout(timeout, DEFAULT_IMPORT_TIMEOUT)
    cwd = coerce_path_str(cwd) or None
    return subprocess.run(  # nosec B603
        [sys.executable, "-c", script],
        input=source,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
        env=subprocess_noartifact_env(), cwd=cwd, check=False,
    )
def _verify_source_in_subprocess(
    source: str, filepath: str, import_timeout: int, skill_dir: str,
    source_roots=_DEFAULT_SOURCE_ROOTS,
) -> tuple[bool, str]:
    import_timeout = _positive_timeout(
        import_timeout, DEFAULT_IMPORT_TIMEOUT)
    path = coerce_path_str(filepath)
    if not path:
        return False, f"filepath 形态异常: 需要非空路径字符串: {filepath!r}"
    abspath = os.path.abspath(path)
    package_root = _verification_package_root(
        abspath, skill_dir, source_roots)
    mod_name = (_module_path_for_import(abspath, package_root)
                or os.path.splitext(os.path.basename(abspath))[0])
    sys_paths = _verification_sys_paths(
        abspath, skill_dir, source_roots, include_source_dir=True)
    script_lines = _build_subprocess_exec_script(
        mod_name=mod_name,
        filepath=abspath,
        sys_paths=sys_paths,
        conditional_register=True,
        package_name=_package_context(abspath, skill_dir, source_roots),
    )
    success_marker = _verification_marker("OK")
    script_lines.append(f"print({success_marker!r})")
    test_script = "\n".join(script_lines) + "\n"
    try:
        proc = _run_python_stdin(test_script, source, import_timeout, skill_dir)
        return _interpret_exec_output(proc, success_marker)
    except subprocess.TimeoutExpired:
        logger.warning("L2片段验证子进程超时(%ss)", import_timeout)
        return False, f"导入超时 ({import_timeout}s)"
    except Exception as e:
        logger.warning("L2片段验证环境异常（按失败处理）: %s", e,
                       exc_info=True)
        return False, f"导入验证异常: {e}"
def _l4_source_or_skip(
        filepath: str, fixed_source: str | None,
) -> tuple[str, tuple[bool, str] | None]:
    if fixed_source is not None:
        return fixed_source, None
    if not os.path.isfile(filepath):
        return "", (True, "文件不存在，跳过L4")
    try:
        return read_source_interpreter_encoding(filepath), None
    except (OSError, UnicodeError, LookupError, SyntaxError) as e:
        logger.warning("L4读取文件失败: %s", e)
        return "", (False, f"L4读取文件失败，运行时验证未执行: {e}")
def _run_l4_script(filepath: str, fixed_source: str,
                   cfg: LayerConfig) -> tuple[bool, str]:
    lines = _build_subprocess_exec_script(
        mod_name='_l4_smoke',
        filepath=filepath,
        sys_paths=_verification_sys_paths(
            filepath, cfg.skill_dir, cfg.source_roots,
            include_source_dir=False),
        conditional_register=False,
        package_name=_package_context(
            filepath, cfg.skill_dir, cfg.source_roots),
    )
    success_marker = _verification_marker("L4_OK")
    lines.append(f"print({success_marker!r})")
    test_script = "\n".join(lines) + "\n"
    try:
        proc = _run_python_stdin(
            test_script, fixed_source, cfg.import_timeout, cfg.skill_dir)
        return _interpret_exec_output(
            proc, success_marker, ok_message="L4运行时验证通过",
            fail_label="L4运行时", include_exit=True)
    except subprocess.TimeoutExpired:
        logger.warning("L4运行时验证子进程超时(可能引入死循环或慢导入)")
        return False, "L4运行时验证超时（可能引入死循环或慢导入）"
    except Exception as e:
        logger.warning("L4验证环境异常（按失败处理）: %s", e, exc_info=True)
        return False, f"L4验证环境异常: {e}"
def _verify_runtime(
    filepath: str,
    fixed_source: str | None,
    cfg: LayerConfig,
) -> tuple[bool, str]:
    filepath = coerce_path_str(filepath)
    if not filepath:
        return False, "filepath 形态异常: 需要非空路径字符串"
    fixed_source, _early = _l4_source_or_skip(filepath, fixed_source)
    if _early is not None:
        return _early
    return _run_l4_script(filepath, fixed_source, cfg)
_TEST_RUN_PASSED = "passed"
_TEST_RUN_NO_TESTS = "no_tests"
_TEST_RUN_SKIPPED = "skipped"
_TEST_RUN_TIMEOUT = "timeout"
_TEST_RUN_ERROR = "error"
_TEST_RUN_FAILED = "failed"
def _execute_targeted_tests(
    skill_dir: str, filepath: str, test_timeout: float, *,
    extra_args: tuple[str, ...] = (),
) -> dict[str, Any]:
    timeout = _positive_timeout(test_timeout, DEFAULT_TEST_TIMEOUT)
    test_files, _mode = locate_targeted_tests(skill_dir, filepath)
    if not test_files:
        return {"status": _TEST_RUN_NO_TESTS, "test_files": [],
                "summary": "", "detail": ""}
    try:
        result = run_pytest_files(skill_dir, (*extra_args, *test_files),
                                  timeout=timeout)
    except subprocess.TimeoutExpired:
        logger.warning("定向测试运行超时(%ss)", timeout)
        return {"status": _TEST_RUN_TIMEOUT, "test_files": test_files,
                "summary": f"测试超时 ({timeout:g}s)", "detail": ""}
    except (OSError, ValueError) as e:
        logger.warning("定向测试执行异常: %s", e, exc_info=True)
        return {"status": _TEST_RUN_ERROR, "test_files": test_files,
                "summary": f"测试验证异常: {e}", "detail": str(e)}
    if result.returncode == 0:
        output = _merged_output(result)
        facts = _build_run_facts(
            result, output,
            parse_pytest_summary_counts(locate_pytest_summary_line(output)))
        if facts.no_tests_ran:
            # 退出码 0 不等于回归已验证：匹配到的测试文件可能全部被
            # skip/deselect，一个用例都没执行。此对必须与 testsuite_runner
            # 的 run_targeted_regression 同口径判为“未执行”，不得记为通过。
            return {"status": _TEST_RUN_SKIPPED, "test_files": test_files,
                    "summary": "匹配测试文件存在但未执行任何用例"
                               "（全部跳过/被排除），回归未验证",
                    "detail": ""}
        return {"status": _TEST_RUN_PASSED, "test_files": test_files,
                "summary": "", "detail": ""}
    summary = last_failure_line(result.stdout, result.stderr)
    status = (_TEST_RUN_NO_TESTS if result.returncode == PYTEST_EXIT_NO_TESTS
              else _TEST_RUN_FAILED)
    return {"status": status, "test_files": test_files,
            "summary": summary, "detail": summary}
def _verify_tests(
    filepath: str,
    fixed_source: str,
    cfg: LayerConfig,
) -> tuple[bool, str]:
    skill_dir = coerce_path_str(cfg.skill_dir)
    filepath = coerce_path_str(filepath)
    if not skill_dir or not filepath:
        return False, "skill_dir/filepath 形态异常: 需要非空路径字符串"
    def _run(_target: str) -> tuple[bool, str]:
        outcome = _execute_targeted_tests(skill_dir, _target,
                                          cfg.test_timeout)
        status = outcome["status"]
        if status == _TEST_RUN_NO_TESTS and not outcome["test_files"]:
            return True, "无匹配测试文件，跳过L3"
        if status == _TEST_RUN_PASSED:
            return True, ""
        if status in (_TEST_RUN_TIMEOUT, _TEST_RUN_ERROR, _TEST_RUN_SKIPPED):
            return False, outcome["summary"]
        return False, f"测试失败: {outcome['summary'][:200]}"
    if os.path.isfile(filepath):
        return run_with_swap(filepath, fixed_source, _run)
    return _run(filepath)
VERIFY_LAYERS = (
    ("L1_syntax", "L1语法验证",
     lambda fp, fixed, cfg: _verify_syntax(fixed, fp)),
    ("L2_import", "L2导入验证", _verify_import),
    ("L3_test", "L3测试验证", _verify_tests),
    ("L4_runtime", "L4运行时验证", _verify_runtime),
)
_SAFE_DOTTED_MODULE_RE = re.compile(r"[A-Za-z_](?:[A-Za-z0-9_]|\.(?=[A-Za-z_]))*")
def _module_path_for_import(filepath: str, package_root: str) -> str:
    rel_parts = os.path.relpath(filepath, package_root).replace(os.sep, "/").split("/")
    rel_parts[-1] = os.path.splitext(rel_parts[-1])[0]
    if rel_parts[-1] == "__init__":
        rel_parts = rel_parts[:-1]
    return ".".join(rel_parts)
def subprocess_import_module(
    filepath: str, import_timeout: int, extra_sys_path: str | None = None,
    *, project_root: str = _DEFAULT_PROJECT_ROOT,
    source_roots=_DEFAULT_SOURCE_ROOTS,
) -> tuple[bool, str]:
    raw_filepath = filepath
    filepath = coerce_path_str(filepath)
    if not filepath:
        logger.warning(
            "[FixSafety] 非法文件路径，拒绝子进程导入验证: %r", raw_filepath)
        return False, f"filepath must be a non-empty str: {raw_filepath!r}"
    filepath = os.path.abspath(filepath)
    import_timeout = _positive_timeout(
        import_timeout, DEFAULT_IMPORT_TIMEOUT)
    package_root = _verification_package_root(
        filepath, project_root, source_roots)
    module_path = _module_path_for_import(filepath, package_root)
    if not _SAFE_DOTTED_MODULE_RE.fullmatch(module_path):
        logger.warning(
            "[FixSafety] 非法模块路径，拒绝子进程导入验证: %r", module_path)
        return False, f"module path is not a safe dotted identifier: {module_path!r}"
    success_marker = _verification_marker("OK")
    sys_paths = _dedup_absolute_paths([
        extra_sys_path or "",
        *_verification_sys_paths(
            filepath, project_root, source_roots, include_source_dir=False),
    ])
    package_kwargs = (
        f", submodule_search_locations=[{os.path.dirname(filepath)!r}]"
        if os.path.basename(filepath) == "__init__.py" else ""
    )
    # 包内模块必须走「包导入」，不能按文件路径加载：
    # spec_from_file_location + 预登记 sys.modules 会让模块对象处于「部分初始化」
    # 状态，一旦包内存在回边导入（如 diag_gate_class_protocol 反向 import
    # diag_gate_class 的 _AUTO_FIELD_BASE_NAMES），exec_module 期间触发的
    # from ... import 就会命中尚未定义的属性而 ImportError——该模块的任何修复
    # 都会被误判为「导入失败」而回滚。改由包自身的导入顺序化解环；
    # 只有无父包的独立脚本才退回按文件路径加载。
    parent_package = module_path.rpartition(".")[0]
    load_by_file_path = "\n".join([
        (f"spec = importlib.util.spec_from_file_location("
         f"{module_path!r}, {filepath!r}{package_kwargs})"),
        "if spec is None or spec.loader is None:",
        "    raise ImportError('cannot load target module from file')",
        "module = importlib.util.module_from_spec(spec)",
        f"sys.modules[{module_path!r}] = module",
        "spec.loader.exec_module(module)",
    ])
    import_code = "\n".join([
        "import importlib",
        "import importlib.util",
        "import sys",
        *(f"sys.path.insert(0, {path!r})" for path in sys_paths),
        (f"if {parent_package!r} and importlib.util.find_spec("
         f"{parent_package!r}) is not None:"),
        f"    importlib.import_module({module_path!r})",
        "else:",
        *[f"    {line}" for line in load_by_file_path.split("\n")],
        f"print({success_marker!r})",
    ])
    result = subprocess.run(  # nosec B603
        [sys.executable, "-c", import_code],
        capture_output=True,
        text=True,
        timeout=import_timeout,
        encoding="utf-8",
        errors="replace", check=False,
        env=subprocess_noartifact_env(),
    )
    if result.returncode == 0 and _has_marker_line(
            result.stdout or "", success_marker):
        return True, ""
    return False, _last_stderr_error_line(
        (result.stderr or "").strip(),
        (result.stdout or "").strip(),
        default="import failed with no output")
def post_write_import_check(
    filepath: str, import_timeout: int,
    *, project_root: str = _DEFAULT_PROJECT_ROOT,
    source_roots=_DEFAULT_SOURCE_ROOTS,
) -> tuple[bool, str]:
    normalized = coerce_path_str(filepath)
    extra_sys_path = (os.path.dirname(os.path.abspath(normalized))
                      if normalized else None)
    passed, error = _import_module_safely(
        filepath, import_timeout, extra_sys_path,
        project_root=project_root, source_roots=source_roots,
        timeout_note="写入后导入超时", error_note="写入后验证环境异常")
    if passed:
        return True, ""
    return False, f"写入后导入失败: {error}"
def _verify_l1_syntax_layer(filepath: str) -> tuple[dict, str | None, str | None]:
    try:
        actual_source = strip_bom(read_source_interpreter_encoding(filepath))
    except (OSError, UnicodeError, LookupError, SyntaxError) as e:
        logger.warning("回归验证L1: 读取文件失败: %s", e)
        return {"passed": False, "error": str(e)}, f"L1读取: {e}", None
    passed, error = _verify_syntax(actual_source, filepath)
    if passed:
        return {"passed": True}, None, actual_source
    return {"passed": False, "error": error}, f"L1语法: {error}", None
def _verify_l2_import_layer(
    filepath: str, import_timeout: int,
    project_root: str = _DEFAULT_PROJECT_ROOT,
    source_roots=_DEFAULT_SOURCE_ROOTS,
) -> tuple[dict, str | None]:
    passed, l2_error = _import_module_safely(
        filepath, import_timeout, os.path.dirname(os.path.abspath(filepath)),
        project_root=project_root, source_roots=source_roots)
    layer = {"passed": passed}
    if not passed:
        layer["error"] = l2_error[:200]
        return layer, f"L2导入: {l2_error[:100]}"
    return layer, None
def _check_all_exports_layer(actual_source: str, original_source: str,
                             ) -> tuple[dict, str | None]:
    try:
        actual_tree = ast.parse(strip_bom(actual_source))
        orig_tree = ast.parse(strip_bom(original_source))
        all_names, actual_exact = collect_module_exports_state(actual_tree)
        orig_all, orig_exact = collect_module_exports_state(orig_tree)
        if not (actual_exact and orig_exact):
            return {"passed": True, "note": (
                "__all__ 含非字面量变更（星号展开/动态求值），导出集合"
                "无法静态确定，跳过导出丢失比对")}, None
        removed_exports = orig_all - all_names
        if removed_exports:
            return ({"passed": False,
                     "error": f"__all__导出丢失: {sorted(removed_exports)[:10]}"},
                    f"L3导出丢失: {sorted(removed_exports)[:5]}")
        return {"passed": True,
                "new_exports": sorted(all_names - orig_all)[:10]}, None
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[FixSafety] L3源码不可解析，跳过导出对比: %s", e)
        return {"passed": True,
                "note": f"源码不可解析，导出对比跳过: {e}"}, None
    except Exception as e:
        logger.warning("[FixSafety] L3导出面对比异常: %s", e, exc_info=True)
        return ({"passed": False, "error": f"导出面对比异常: {e}"},
                f"L3导出面对比异常: {e}")
def _apply_layer(layers: dict[str, dict], errors: list[str],
                 name: str, outcome: tuple) -> str | None:
    if isinstance(outcome, (tuple, list)) and len(outcome) >= 2:
        layer, err = outcome[0], outcome[1]
        actual_source = outcome[2] if len(outcome) > 2 else None
    else:
        layer, err, actual_source = None, None, None
    if not isinstance(layer, dict):
        kind = (type(layer).__name__ if layer is not None
                else type(outcome).__name__)
        layer = {"passed": False,
                 "error": f"验证层返回形态异常({kind})"}
        err = err or layer["error"]
        actual_source = None
    if err is not None and not isinstance(err, str):
        err = (f"验证层错误形态异常({type(err).__name__}): "
               f"{repr(err)[:200]}")
    layers[name] = layer
    if err:
        errors.append(err)
    return actual_source
def _verify_l4_test_layer(skill_dir: str, filepath: str, test_timeout: int,
                          ) -> tuple[dict, str | None]:
    outcome = _execute_targeted_tests(
        skill_dir, filepath, test_timeout, extra_args=("-x",))
    status = outcome["status"]
    test_files = outcome["test_files"]
    if status == _TEST_RUN_NO_TESTS and not test_files:
        return {"passed": True, "note": "无相关测试文件"}, None
    if status == _TEST_RUN_TIMEOUT:
        logger.warning("回归验证L4: 测试运行超时")
        return {"passed": False, "error": "测试运行超时"}, "L4测试超时"
    if status == _TEST_RUN_ERROR:
        logger.warning("回归验证L4: 测试验证异常: %s", outcome["detail"])
        return ({"passed": False,
                 "error": f"测试验证环境异常: {outcome['detail']}"},
                f"L4测试环境异常: {outcome['detail']}")
    if status == _TEST_RUN_NO_TESTS:
        return ({"passed": False, "test_file": test_files[0],
                 "error": "匹配测试文件无用例可收集，回归未执行"},
                "L4测试: 匹配测试文件无用例可收集，回归未执行")
    if status == _TEST_RUN_SKIPPED:
        return ({"passed": False, "test_file": test_files[0],
                 "error": "匹配测试全部跳过/被排除，未执行任何用例，"
                          "回归未验证"},
                "L4测试: 匹配测试全部跳过/被排除，回归未验证")
    if status == _TEST_RUN_PASSED:
        return {"passed": True, "test_file": test_files[0]}, None
    summary = outcome["summary"]
    return ({"passed": False, "test_file": test_files[0],
             "error": summary[:200]}, f"L4测试: {summary[:100]}")
def _normalized_source_text(source: str) -> str:
    return strip_bom(source).replace("\r\n", "\n").replace("\r", "\n")
def _written_source_matches(actual_source: str, fixed_source: str) -> bool:
    if not isinstance(actual_source, str):
        return False
    return (_normalized_source_text(actual_source)
            == _normalized_source_text(fixed_source))
def verify_regression(
    filepath: str,
    original_source: str,
    fixed_source: str,
    skill_dir: str,
    test_timeout: int,
    import_timeout: int,
) -> dict[str, Any]:
    normalized_path = coerce_path_str(filepath)
    normalized_root = coerce_path_str(skill_dir)
    if not normalized_path or not normalized_root:
        bad_name = "filepath" if not normalized_path else "skill_dir"
        return {"passed": False, "layers": {},
                "error": f"{bad_name} 形态异常: 需要非空路径字符串"}
    if not isinstance(original_source, str) or not isinstance(fixed_source, str):
        return {"passed": False, "layers": {},
                "error": ("original_source/fixed_source 形态异常: "
                          "需要源码字符串")}
    filepath = normalized_path
    skill_dir = normalize_skill_dir(normalized_root)
    test_timeout = _positive_timeout(test_timeout, DEFAULT_TEST_TIMEOUT)
    import_timeout = _positive_timeout(
        import_timeout, DEFAULT_IMPORT_TIMEOUT)
    _t0 = time.monotonic()
    layers: dict[str, dict] = {}
    errors: list[str] = []
    actual_source = _apply_layer(
        layers, errors, "L1_syntax",
        _verify_l1_syntax_layer(filepath))
    if (actual_source is not None
            and not _written_source_matches(actual_source, fixed_source)):
        errors.append("写盘校验: 磁盘内容与修复源码不一致（写盘未生效或被并发改写）")
    _apply_layer(layers, errors, "L2_import",
                 _verify_l2_import_layer(
                     filepath, import_timeout, project_root=skill_dir))
    if actual_source is not None:
        _apply_layer(layers, errors, "L3_exports",
                     _check_all_exports_layer(actual_source, original_source))
    _apply_layer(layers, errors, "L4_test",
                 _verify_l4_test_layer(skill_dir, filepath, test_timeout))
    trace_module_run(
        _MODULE_TAG, "verify_regression", _t0,
        outcome="ok" if not errors else "failed",
        file=filepath, layers=len(layers),
        layer_errors=sum(1 for v in layers.values()
                         if not v.get("passed", False)))
    return _regression_verdict(layers, errors)
def _regression_verdict(layers: dict[str, dict],
                        errors: list[str]) -> dict[str, Any]:
    failed_layers = [name for name, layer in layers.items()
                     if layer.get("passed") is not True]
    passed = bool(layers) and not errors and not failed_layers
    if errors:
        error = "; ".join(errors)
    elif failed_layers:
        error = "验证层未通过: " + ", ".join(failed_layers)
    elif not layers:
        error = "未执行任何验证层"
    else:
        error = ""
    return {"passed": passed, "layers": layers, "error": error}
_SECRET_NAME_KEYS = frozenset(k.lower() for k in SENSITIVE_NAME_KEYWORDS)
_SECRET_NAME_NORMALIZED = frozenset(
    key.replace("_", "") for key in _SECRET_NAME_KEYS)
_SECRET_METADATA_SUFFIXES = frozenset({
    "regex", "pattern", "patterns", "name", "names", "hash", "hashes",
    "id", "ids", "path", "paths", "file", "files", "type", "types",
    "field", "fields", "label", "labels", "template", "templates",
    "example", "examples", "sample", "samples", "placeholder", "prefix",
    "suffix", "len", "length", "count", "index", "env", "var",
})
def _secret_name_tokens(name: str) -> list[str]:
    spaced = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name)
    spaced = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", spaced)
    return [part.lower() for part in re.split(r"[^A-Za-z0-9]+", spaced)
            if part]
def _is_secret_name(name: str) -> bool:
    tokens = _secret_name_tokens(name)
    if not tokens or tokens[-1] in _SECRET_METADATA_SUFFIXES:
        return False
    if "".join(tokens) in _SECRET_NAME_NORMALIZED:
        return True
    for key in _SECRET_NAME_KEYS:
        key_tokens = tuple(part for part in key.split("_") if part)
        if (len(key_tokens) > 1
                and tuple(tokens[-len(key_tokens):]) == key_tokens):
            return True
    return any(token == key or token.endswith(key)
               for token in tokens for key in _SECRET_NAME_KEYS)
_DIAG_BASE_SCORE = 80.0
_DIAG_TINY_LINES = 10
_DIAG_HUGE_LINES = 4000
_DIAG_TINY_PENALTY = 10.0
_DIAG_HUGE_PENALTY = 15.0
_DIAG_BARE_EXCEPT_PENALTY = 20.0
_DIAG_EVAL_EXEC_PENALTY = 30.0
_DIAG_SHELL_TRUE_PENALTY = 20.0
_DIAG_SECRET_PENALTY = 15.0
_DIAG_SCORE_MIN = 0
_DIAG_SCORE_MAX = 100
def _secret_targets_of(node: ast.AST) -> set[str]:
    parts = assign_targets_value(node)
    if parts is None:
        return set()
    targets, value = parts
    if not (isinstance(value, ast.Constant) and isinstance(value.value, str)):
        return set()
    return {target.id for target in targets
            if isinstance(target, ast.Name)
            and _is_secret_name(target.id)}
def _normalize_redline_call(name: str) -> str:
    if isinstance(name, str) and name.startswith("builtins."):
        return name[len("builtins."):]
    return name
_REDLINE_EXEC_CALLS = ('eval', 'exec', 'compile')
_REDLINE_SHELL_CALLS = ('os.system', 'os.popen')
_REDLINE_DANGEROUS_IMPORTS = frozenset(('os', 'builtins'))
_STAR_IMPORT_REDLINES: dict[str, dict[str, str]] = {
    'os': {'system': 'os.system', 'popen': 'os.popen'},
    'builtins': {'eval': 'eval', 'exec': 'exec', 'compile': 'compile'},
}
_REDLINE_COMPREHENSION_NODES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
_REDLINE_COLLECTION = "<collection>"
def _redline_scope_nodes(stmts: list[ast.stmt]):
    scope = ast.Module(body=list(stmts), type_ignores=[])
    yield from iter_scope_nodes(scope)
def _import_from_target(module: str | None, name: str) -> str:
    if module == "builtins":
        return name
    if module == "os":
        return f"os.{name}"
    return ""
def _update_scope_alias(aliases: dict[str, str], shadowed: set[str],
                        local: str, target: str) -> None:
    if target:
        aliases[local] = target
        shadowed.discard(local)
        return
    aliases.pop(local, None)
    shadowed.add(local)
def _scope_import_aliases(
    stmts: list[ast.stmt],
) -> tuple[dict[str, str], set[str]]:
    aliases: dict[str, str] = {}
    shadowed: set[str] = set()
    for node in _redline_scope_nodes(stmts):
        if isinstance(node, ast.Import):
            for alias in node.names:
                root = alias.name.split(".")[0]
                dangerous = root in _REDLINE_DANGEROUS_IMPORTS and (
                    alias.asname is None or "." not in alias.name)
                local = alias.asname or root
                _update_scope_alias(
                    aliases, shadowed, local, root if dangerous else "")
        elif isinstance(node, ast.ImportFrom):
            module = node.module if node.level == 0 else None
            for alias in node.names:
                if alias.name == "*":
                    for local, target in _STAR_IMPORT_REDLINES.get(
                            module or "", {}).items():
                        _update_scope_alias(aliases, shadowed, local, target)
                    continue
                local = alias.asname or alias.name
                target = _import_from_target(module, alias.name)
                if (target not in _REDLINE_EXEC_CALLS
                        and target not in _REDLINE_SHELL_CALLS):
                    target = ""
                _update_scope_alias(aliases, shadowed, local, target)
    return aliases, shadowed
def _scope_bound_names(stmts: list[ast.stmt]) -> set[str]:
    bound_counts: Counter = Counter()
    comprehension_counts: Counter = Counter()
    names: set[str] = set()
    nodes = list(_redline_scope_nodes(stmts))
    for node in nodes:
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, (ast.Store, ast.Del))):
            bound_counts[node.id] += 1
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef)):
            names.add(node.name)
    for node in nodes:
        if not isinstance(node, _REDLINE_COMPREHENSION_NODES):
            continue
        for generator in node.generators:
            for target in walk_nodes(generator.target):
                if (isinstance(target, ast.Name)
                        and isinstance(target.ctx, (ast.Store, ast.Del))):
                    comprehension_counts[target.id] += 1
    names.update(
        name for name, count in bound_counts.items()
        if count > comprehension_counts[name]
    )
    return names
class _RedlineAliasResolver:
    def __init__(self) -> None:
        self.call_names: dict[int, str] = {}
        self._default_param_targets: dict[int, dict[str, str]] = {}
        self._definition_redlines: dict[int, dict[str, str]] = {}
        self._external_redlines: dict[int, dict[str, str]] = {}
        self._module_scope_id = 0
        self._external_context = None
    def resolve(self, tree: ast.AST) -> dict[int, str]:
        self._external_redlines = {}
        self._module_scope_id = id(tree)
        while True:
            self.call_names = {}
            self._default_param_targets = {}
            self._definition_redlines = {}
            self._external_context = None
            previous_external = {
                scope: dict(aliases)
                for scope, aliases in self._external_redlines.items()
            }
            self._scan_body(
                getattr(tree, "body", []), {}, scope_node=tree)
            if self._external_redlines == previous_external:
                return dict(self.call_names)
    def _scan_body(
        self, stmts: list[ast.stmt], inherited: dict[str, str],
        in_class: bool = False, scope_node: ast.AST | None = None,
        enclosing_function: int | None = None,
    ) -> None:
        scope_key = id(scope_node) if scope_node is not None else -1
        external = self._external_redlines.get(scope_key, {})
        if external:
            inherited = {**inherited, **external}
        final_aliases = dict(inherited)
        own, shadowed = _scope_import_aliases(stmts)
        for name in shadowed:
            final_aliases[name] = ""
        final_aliases.update(own)
        bound_names = _scope_bound_names(stmts)
        for name in bound_names:
            final_aliases[name] = ""
        global_names, nonlocal_names = self._external_declaration_names(stmts)
        previous_context = self._external_context
        self._external_context = (
            (scope_key, enclosing_function, global_names, nonlocal_names)
            if external or global_names or nonlocal_names else None)
        ordered = self._record_ordered_block(
            stmts, self._candidate_map(inherited))
        self._external_context = previous_context
        for name in self._direct_assignment_names(stmts):
            targets = ordered.get(name, {None})
            concrete = {target for target in targets if target is not None}
            target = self._preferred_redline_alias(targets)
            if target is None and len(targets) == 1 and len(concrete) == 1:
                target = concrete.pop()
            if target is None:
                final_aliases[name] = ""
            else:
                final_aliases[name] = target
        for name, targets in ordered.items():
            target = self._preferred_redline_alias(targets)
            if target is not None:
                final_aliases[name] = target
        for name in bound_names:
            if name not in ordered:
                final_aliases.pop(name, None)
        if external:
            for name, target in external.items():
                final_aliases[name] = self._preferred_redline_alias(
                    (target, final_aliases.get(name))) or target
        nested_inherited = inherited if in_class else final_aliases
        child_enclosing = (
            id(scope_node)
            if isinstance(scope_node, (ast.FunctionDef, ast.AsyncFunctionDef))
            else enclosing_function)
        nodes = list(_redline_scope_nodes(stmts))
        comprehension_lambdas = {
            id(descendant)
            for node in nodes if isinstance(node, _REDLINE_COMPREHENSION_NODES)
            for descendant in walk_nodes(node)
            if isinstance(descendant, ast.Lambda)
        }
        for node in nodes:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                child = dict(nested_inherited)
                if not in_class:
                    child.update(self._definition_redlines.get(id(node), {}))
                for param in collect_param_names(node):
                    child[param] = ""
                child.update(self._default_param_targets.get(id(node), {}))
                self._scan_body(
                    node.body, child, scope_node=node,
                    enclosing_function=child_enclosing)
            elif isinstance(node, ast.ClassDef):
                child = dict(nested_inherited)
                if not in_class:
                    child.update(self._definition_redlines.get(id(node), {}))
                self._scan_body(
                    node.body, child, in_class=True, scope_node=node,
                    enclosing_function=child_enclosing)
            elif (isinstance(node, ast.Lambda)
                  and (in_class or id(node) not in comprehension_lambdas)):
                child = dict(nested_inherited)
                if not in_class:
                    child.update(self._definition_redlines.get(id(node), {}))
                for param in collect_param_names(node):
                    child[param] = ""
                child.update(self._default_param_targets.get(id(node), {}))
                self._scan_expr_ordered(node.body, self._candidate_map(child))
    @staticmethod
    def _candidate_map(aliases: dict[str, str]) -> dict[str, set[str | None]]:
        return {name: {target} for name, target in aliases.items()}
    @staticmethod
    def _redline_alias_targets(targets) -> set[str]:
        return {
            target for target in targets if target is not None and (
                target in _REDLINE_EXEC_CALLS
                or target in _REDLINE_SHELL_CALLS
                or target in _REDLINE_DANGEROUS_IMPORTS)
        }
    @classmethod
    def _preferred_redline_alias(cls, targets) -> str | None:
        concrete = sorted(cls._redline_alias_targets(targets))
        return concrete[0] if concrete else None
    @classmethod
    def _redline_state_signature(cls, candidates) -> dict[str, set[str]]:
        return {
            name: targets
            for name, raw_targets in candidates.items()
            for targets in (cls._redline_alias_targets(raw_targets),)
            if targets
        }
    @classmethod
    def _definition_redline_aliases(cls, candidates) -> dict[str, str]:
        aliases = {}
        for name, targets in candidates.items():
            target = cls._preferred_redline_alias(targets)
            if target is not None:
                aliases[name] = target
        return aliases
    @staticmethod
    def _direct_assignment_names(stmts: list[ast.stmt]) -> set[str]:
        names: set[str] = set()
        for node in _redline_scope_nodes(stmts):
            if isinstance(node, ast.Assign):
                targets = list(node.targets)
            elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
                targets = [node.target]
            else:
                continue
            for target in targets:
                for descendant in walk_nodes(target):
                    if (isinstance(descendant, ast.Name)
                            and isinstance(descendant.ctx, (ast.Store, ast.Del))):
                        names.add(descendant.id)
        return names
    @staticmethod
    def _default_params(node: ast.AST) -> list[tuple[ast.arg, ast.AST]]:
        args = getattr(node, "args", None)
        if args is None:
            return []
        positional = [*getattr(args, "posonlyargs", ()), *args.args]
        defaults = list(getattr(args, "defaults", ()) or ())
        pairs = list(zip(positional[len(positional) - len(defaults):],
                         defaults, strict=True))
        pairs.extend(
            (param, default)
            for param, default in zip(
                getattr(args, "kwonlyargs", ()),
                getattr(args, "kw_defaults", ()), strict=True)
            if default is not None)
        return pairs
    def _record_default_params(
        self, node: ast.AST, candidates: dict[str, set[str | None]],
    ) -> None:
        dangerous: dict[str, str] = {}
        for param, default in self._default_params(node):
            targets = self._value_alias_names(default, candidates)
            target = self._preferred_redline_alias(targets)
            if target is not None:
                dangerous[param.arg] = target
            self._scan_expr_ordered(default, candidates)
        self._default_param_targets[id(node)] = dangerous
    @staticmethod
    def _external_declaration_names(
        stmts: list[ast.stmt],
    ) -> tuple[set[str], set[str]]:
        global_names: set[str] = set()
        nonlocal_names: set[str] = set()
        for node in _redline_scope_nodes(stmts):
            if isinstance(node, ast.Global):
                global_names.update(node.names)
            elif isinstance(node, ast.Nonlocal):
                nonlocal_names.update(node.names)
        return global_names, nonlocal_names
    def _record_external_redline_state(self, candidates) -> None:
        if self._external_context is None:
            return
        (scope_key, enclosing_function,
         global_names, nonlocal_names) = self._external_context
        for name, target in self._external_redlines.get(scope_key, {}).items():
            candidates.setdefault(name, set()).add(target)
        declarations = (
            (global_names, self._module_scope_id),
            (nonlocal_names, enclosing_function),
        )
        for names, target_scope in declarations:
            if target_scope is None:
                continue
            for name in names:
                target = self._preferred_redline_alias(
                    candidates.get(name, ()))
                if target is None:
                    continue
                aliases = self._external_redlines.setdefault(target_scope, {})
                preferred = self._preferred_redline_alias(
                    (target, aliases.get(name)))
                if preferred != aliases.get(name):
                    aliases[name] = preferred
    def _record_ordered_block(
        self, stmts: list[ast.stmt], candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        for stmt in stmts:
            candidates = self._record_ordered_stmt(stmt, candidates)
            self._record_external_redline_state(candidates)
        return candidates
    def _record_ordered_stmt(
        self, stmt: ast.stmt, candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            self._definition_redlines[id(stmt)] = (
                self._definition_redline_aliases(candidates))
            default_ids = {
                id(default) for _param, default in self._default_params(stmt)}
            defaults_recorded = False
            for expr in iter_def_site_nodes(stmt):
                if id(expr) in default_ids:
                    if not defaults_recorded:
                        self._record_default_params(stmt, candidates)
                        defaults_recorded = True
                    continue
                self._scan_expr_ordered(expr, candidates)
            candidates[stmt.name] = {""}
            return candidates
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            self._apply_ordered_import(stmt, candidates)
            return candidates
        if isinstance(stmt, ast.If):
            self._scan_expr_ordered(stmt.test, candidates)
            body = self._record_ordered_block(stmt.body, dict(candidates))
            other = self._record_ordered_block(stmt.orelse, dict(candidates))
            return self._merge_ordered_states(body, other)
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            before_loop = dict(candidates)
            self._record_loop(stmt, candidates)
            body = self._record_loop_body_fixed_point(stmt, candidates)
            else_entry = self._merge_ordered_states(before_loop, candidates, body)
            other = self._record_ordered_block(stmt.orelse, else_entry)
            return self._merge_ordered_states(before_loop, body, other)
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            for item in stmt.items:
                self._scan_expr_ordered(item.context_expr, candidates)
                self._shadow_store_names(item.optional_vars, candidates)
            return self._record_ordered_block(stmt.body, candidates)
        if isinstance(stmt, TRY_NODE_TYPES):
            return self._record_try(stmt, candidates)
        if isinstance(stmt, ast.Match):
            return self._record_match(stmt, candidates)
        self._scan_expr_ordered(stmt, candidates)
        assignment_aliases = self._assignment_aliases(stmt, candidates)
        for name in _scope_bound_names([stmt]):
            if isinstance(stmt, ast.Delete):
                candidates.pop(name, None)
            else:
                candidates[name] = {""}
        candidates.update(assignment_aliases)
        return candidates
    def _record_loop(self, stmt: ast.AST,
                     candidates: dict[str, set[str | None]]) -> None:
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            self._scan_expr_ordered(stmt.iter, candidates)
            if isinstance(stmt.target, ast.Name):
                targets = self._iteration_alias_names(stmt.iter, candidates)
                candidates[stmt.target.id] = targets or {""}
            else:
                self._shadow_store_names(stmt.target, candidates)
        else:
            self._scan_expr_ordered(stmt.test, candidates)
    def _record_loop_body_fixed_point(
        self, stmt: ast.AST, candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        entry = {name: set(targets) for name, targets in candidates.items()}
        while True:
            body_entry = {
                name: set(targets) for name, targets in entry.items()}
            if isinstance(stmt, ast.While):
                # while 条件会在每轮回边后重新求值，须使用合流后的别名状态。
                self._scan_expr_ordered(stmt.test, body_entry)
            body = self._record_ordered_block(stmt.body, body_entry)
            next_entry = self._merge_ordered_states(entry, candidates, body)
            if (self._redline_state_signature(next_entry)
                    == self._redline_state_signature(entry)):
                return body
            entry = next_entry
    def _record_try(self, stmt: ast.AST,
                    candidates: dict[str, set[str | None]],
                    ) -> dict[str, set[str | None]]:
        handler_states = [dict(candidates)]
        body = dict(candidates)
        for try_stmt in stmt.body:
            body = self._record_ordered_stmt(try_stmt, body)
            handler_states.append(dict(body))
        handler_entry = self._merge_ordered_states(*handler_states)
        states = [body]
        for handler in stmt.handlers:
            self._scan_expr_ordered(handler.type, handler_entry)
            branch = dict(handler_entry)
            if handler.name:
                branch[handler.name] = {""}
            states.append(self._record_ordered_block(handler.body, branch))
        states.append(self._record_ordered_block(stmt.orelse, dict(body)))
        merged = self._merge_ordered_states(*states)
        return self._record_ordered_block(stmt.finalbody, merged)
    def _record_match(self, stmt: ast.Match,
                      candidates: dict[str, set[str | None]],
                      ) -> dict[str, set[str | None]]:
        self._scan_expr_ordered(stmt.subject, candidates)
        states = [dict(candidates)]
        for case in stmt.cases:
            branch = dict(candidates)
            for node in walk_nodes(case.pattern):
                for attr in ("name", "rest"):
                    bound = getattr(node, attr, None)
                    if isinstance(bound, str):
                        branch[bound] = {""}
            pattern = case.pattern
            if (isinstance(pattern, ast.MatchAs)
                    and pattern.pattern is None and pattern.name
                    and pattern.name != "_"):
                self._bind_name_source(pattern.name, stmt.subject, branch)
            self._scan_expr_ordered(case.guard, branch)
            states.append(self._record_ordered_block(case.body, branch))
        return self._merge_ordered_states(*states)
    @staticmethod
    def _merge_ordered_states(
        *states: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        merged: dict[str, set[str | None]] = {}
        for state in states:
            for name, targets in state.items():
                merged.setdefault(name, set()).update(targets)
        for name in set(merged):
            for state in states:
                if name not in state:
                    merged[name].add(None)
        return merged
    def _apply_ordered_import(
        self, stmt: ast.stmt, candidates: dict[str, set[str | None]],
    ) -> None:
        own, shadowed = _scope_import_aliases([stmt])
        for name in shadowed:
            candidates[name] = {""}
        for name, target in own.items():
            candidates[name] = {target}
    @staticmethod
    def _shadow_store_names(
        node: ast.AST | None, candidates: dict[str, set[str | None]],
    ) -> None:
        if node is None:
            return
        for child in walk_nodes(node):
            if isinstance(child, ast.Name) and isinstance(
                    child.ctx, (ast.Store, ast.Del)):
                candidates[child.id] = {""}
    def _bind_name_source(
        self, name: str, source: ast.AST,
        candidates: dict[str, set[str | None]],
    ) -> None:
        candidates[name] = self._value_alias_names(source, candidates) or {""}
    def _record_comprehension(
        self, node: ast.AST, candidates: dict[str, set[str | None]],
    ) -> None:
        inner = {name: set(targets) for name, targets in candidates.items()}
        for generator in node.generators:
            self._scan_expr_ordered(generator.iter, inner)
            if isinstance(generator.target, ast.Name):
                targets = self._iteration_alias_names(generator.iter, inner)
                inner[generator.target.id] = targets or {""}
            else:
                self._shadow_store_names(generator.target, inner)
            for condition in generator.ifs:
                self._scan_expr_ordered(condition, inner)
        if isinstance(node, ast.DictComp):
            self._scan_expr_ordered(node.key, inner)
            self._scan_expr_ordered(node.value, inner)
        else:
            self._scan_expr_ordered(node.elt, inner)
        self._bind_walrus_aliases(node, inner, into=candidates)
    def _scan_expr_ordered(
        self, expr: ast.AST | None, candidates: dict[str, set[str | None]],
    ) -> None:
        if expr is None:
            return
        if isinstance(expr, _REDLINE_COMPREHENSION_NODES):
            self._record_comprehension(expr, candidates)
            return
        if isinstance(expr, ast.Assign):
            self._scan_expr_ordered(expr.value, candidates)
            for target in expr.targets:
                self._scan_expr_ordered(target, candidates)
            return
        if isinstance(expr, ast.IfExp):
            self._scan_expr_ordered(expr.test, candidates)
            body = {name: set(targets) for name, targets in candidates.items()}
            other = {name: set(targets) for name, targets in candidates.items()}
            self._scan_expr_ordered(expr.body, body)
            self._scan_expr_ordered(expr.orelse, other)
            merged = self._merge_ordered_states(body, other)
            candidates.clear()
            candidates.update(merged)
            return
        if isinstance(expr, ast.BoolOp):
            current = {name: set(targets) for name, targets in candidates.items()}
            states = []
            for value in expr.values:
                self._scan_expr_ordered(value, current)
                states.append({name: set(targets)
                               for name, targets in current.items()})
            merged = self._merge_ordered_states(*states)
            candidates.clear()
            candidates.update(merged)
            return
        if isinstance(expr, ast.Dict):
            for key, value in zip(expr.keys, expr.values, strict=True):
                self._scan_expr_ordered(key, candidates)
                self._scan_expr_ordered(value, candidates)
            return
        if isinstance(expr, ast.Lambda):
            self._definition_redlines[id(expr)] = (
                self._definition_redline_aliases(candidates))
            self._record_default_params(expr, candidates)
            child = {name: set(targets) for name, targets in candidates.items()}
            for param in collect_param_names(expr):
                child[param] = {""}
            for name, target in self._default_param_targets[id(expr)].items():
                child[name] = {target}
            self._scan_expr_ordered(expr.body, child)
            return
        if isinstance(expr, ast.Call):
            self._record_candidate_call(expr, candidates)
        for child in ast.iter_child_nodes(expr):
            self._scan_expr_ordered(child, candidates)
        if isinstance(expr, ast.NamedExpr):
            candidates.update(
                self._bind_target_aliases(expr.target, expr.value, candidates))
    def _assignment_aliases(
        self, stmt: ast.stmt, candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        aliases: dict[str, set[str | None]] = {}
        if isinstance(stmt, ast.Assign):
            targets, value = stmt.targets, stmt.value
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            targets, value = [stmt.target], stmt.value
        else:
            targets, value = [], None
        for target in targets:
            aliases.update(
                self._bind_target_aliases(target, value, candidates))
        self._bind_walrus_aliases(stmt, candidates, into=aliases)
        return aliases
    def _bind_walrus_aliases(
        self, node: ast.AST, candidates: dict[str, set[str | None]], *,
        into: dict[str, set[str | None]] | None = None,
    ) -> None:
        target_dict = candidates if into is None else into
        for child in iter_scope_nodes(node):
            if isinstance(child, ast.NamedExpr) and isinstance(
                    child.target, ast.Name):
                target_dict[child.target.id] = set(
                    candidates.get(child.target.id, {""}))
    @staticmethod
    def _clear_collection_aliases(
        candidates: dict[str, set[str | None]], name: str,
    ) -> None:
        prefix = f"{name}["
        for key in tuple(candidates):
            if key.startswith(prefix):
                candidates.pop(key, None)
    def _bind_collection_alias(
        self, name: str, value: ast.Tuple | ast.List,
        candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        element_targets = [
            self._value_alias_names(element, candidates)
            for element in value.elts
        ]
        resolved = set().union(*element_targets) if element_targets else set()
        self._clear_collection_aliases(candidates, name)
        aliases: dict[str, set[str | None]] = {name: {_REDLINE_COLLECTION}}
        if resolved:
            aliases[f"{name}[]"] = resolved
        if any(isinstance(element, ast.Starred) for element in value.elts):
            if resolved:
                aliases[f"{name}[*]"] = {_REDLINE_COLLECTION}
            return aliases
        for index, targets in enumerate(element_targets):
            if not targets:
                continue
            aliases[f"{name}[{index}]"] = targets
            aliases[f"{name}[{index - len(element_targets)}]"] = targets
        return aliases
    def _bind_target_aliases(
        self, target: ast.AST | None, value: ast.AST | None,
        candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        if target is None or value is None:
            return {}
        if isinstance(target, ast.Name):
            if isinstance(value, (ast.Tuple, ast.List)):
                return self._bind_collection_alias(
                    target.id, value, candidates)
            resolved = self._value_alias_names(value, candidates)
            # 改绑必须写回（包括空集）：返回 {} 会让旧别名残留，
            # 使 `(x := None)` / `a, os = 1, None` 这类改绑后仍按旧别名归因。
            return {target.id: resolved}
        if isinstance(target, (ast.Tuple, ast.List)):
            return self._bind_unpacked_aliases(target, value, candidates)
        return {}
    def _bind_unpacked_aliases(
        self, target: ast.Tuple | ast.List, value: ast.AST,
        candidates: dict[str, set[str | None]],
    ) -> dict[str, set[str | None]]:
        if not isinstance(value, (ast.Tuple, ast.List)):
            return {}
        targets = list(target.elts)
        values = list(value.elts)
        starred = [index for index, element in enumerate(targets)
                   if isinstance(element, ast.Starred)]
        if len(starred) > 1:
            return {}
        if starred:
            star = starred[0]
            trailing = len(targets) - star - 1
            if len(values) < len(targets) - 1:
                return {}
            targets = targets[:star] + targets[star + 1:]
            values = values[:star] + values[len(values) - trailing:]
        elif len(values) != len(targets):
            return {}
        aliases: dict[str, set[str | None]] = {}
        for element, source in zip(targets, values, strict=True):
            aliases.update(
                self._bind_target_aliases(element, source, candidates))
        return aliases
    def _iteration_alias_names(
        self, value: ast.AST,
        candidates: dict[str, set[str | None]],
    ) -> set[str]:
        targets = self._value_alias_names(value, candidates)
        if (isinstance(value, ast.Name)
                and _REDLINE_COLLECTION in candidates.get(value.id, ())):
            targets.discard(_REDLINE_COLLECTION)
            targets.update(candidates.get(f"{value.id}[]", ()))
        return targets
    @staticmethod
    def _literal_subscript_elements(node: ast.Subscript) -> list[ast.AST] | None:
        if not isinstance(node.value, (ast.Tuple, ast.List)):
            return None
        elements = list(node.value.elts)
        if isinstance(node.slice, ast.Slice):
            return []
        if isinstance(node.slice, ast.Constant):
            index = node.slice.value
            if not isinstance(index, int):
                return []
            if any(isinstance(element, ast.Starred) for element in elements):
                return elements
            try:
                return [elements[index]]
            except IndexError:
                return []
        return elements
    def _value_alias_names(
        self, value: ast.AST,
        candidates: dict[str, set[str | None]],
    ) -> set[str]:
        literal_elements = (
            self._literal_subscript_elements(value)
            if isinstance(value, ast.Subscript) else None)
        if literal_elements is not None:
            names: set[str] = set()
            for element in literal_elements:
                names |= self._value_alias_names(element, candidates)
            return names
        raw_name = self._expression_name(value)
        if raw_name:
            return set(self._resolved_names(raw_name, candidates))
        if isinstance(value, ast.NamedExpr):
            return self._value_alias_names(value.value, candidates)
        if isinstance(value, ast.Attribute):
            return {
                f"{base}.{value.attr}"
                for base in self._value_alias_names(value.value, candidates)
                if base
            }
        if isinstance(value, ast.IfExp):
            return (self._value_alias_names(value.body, candidates)
                    | self._value_alias_names(value.orelse, candidates))
        if isinstance(value, ast.BoolOp):
            names: set[str] = set()
            for element in value.values:
                names |= self._value_alias_names(element, candidates)
            return names
        if isinstance(value, (ast.Tuple, ast.List)):
            names: set[str] = set()
            for element in value.elts:
                names |= self._value_alias_names(element, candidates)
            return names
        return set()
    @staticmethod
    def _expression_name(node: ast.AST) -> str:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.NamedExpr):
            return _RedlineAliasResolver._expression_name(node.value)
        if isinstance(node, ast.Attribute):
            base = _RedlineAliasResolver._expression_name(node.value)
            return f"{base}.{node.attr}" if base else ""
        if isinstance(node, ast.Subscript):
            if isinstance(node.slice, ast.Slice):
                return ""
            base = _RedlineAliasResolver._expression_name(node.value)
            if not base:
                return ""
            if isinstance(node.slice, ast.Constant):
                index = node.slice.value
                if isinstance(index, int):
                    return f"{base}[{index}]"
                return f"{base}[{index!r}]"
            return f"{base}[]"
        return ""
    @staticmethod
    def _resolved_names(
        raw_name: str, candidates: dict[str, set[str | None]],
    ) -> list[str]:
        root, dot, rest = raw_name.partition(".")
        if "[" in root and root.endswith("]"):
            base = root.partition("[")[0]
            if _REDLINE_COLLECTION not in candidates.get(base, ()):
                return []
            targets = candidates.get(root)
            if (targets is None and root != f"{base}[]"
                    and f"{base}[*]" in candidates):
                targets = candidates.get(f"{base}[]")
            if targets is None:
                return []
        else:
            targets = candidates.get(root, {None})
        resolved = []
        for target in sorted(targets, key=lambda item: (item is not None, item or "")):
            if target is None:
                name = raw_name
            elif not target:
                continue
            else:
                name = f"{target}.{rest}" if dot else target
            resolved.append(_normalize_redline_call(name))
        return resolved
    def _record_candidate_call(
        self, node: ast.Call, candidates: dict[str, set[str | None]],
    ) -> None:
        raw_name = resolve_call_name(node)
        if not raw_name:
            raw_name = self._expression_name(getattr(node, "func", None) or node)
        resolved = self._resolved_names(raw_name, candidates) if raw_name else []
        for name in sorted(self._value_alias_names(node.func, candidates)):
            if name not in resolved:
                resolved.append(name)
        if not resolved:
            resolved = [""]
        dangerous = next(
            (name for name in resolved
             if name in _REDLINE_EXEC_CALLS or name in _REDLINE_SHELL_CALLS),
            None,
        )
        self.call_names[id(node)] = dangerous or resolved[0]
def _has_shell_true(call: ast.Call) -> bool:
    return any(is_shell_true_keyword(kw) for kw in call.keywords)
def _collect_pattern_flags(tree: ast.AST) -> tuple[bool, bool, bool, set[str]]:
    has_bare_except = False
    has_eval_exec = False
    has_shell_true = False
    hardcoded_secrets: set[str] = set()
    call_names = _RedlineAliasResolver().resolve(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.ExceptHandler) and node.type is None:
            has_bare_except = True
            continue
        if isinstance(node, ast.Call):
            resolved_name = call_names.get(id(node))
            name = (resolved_name if resolved_name is not None
                    else _normalize_redline_call(resolve_call_name(node)))
            if name in _REDLINE_EXEC_CALLS:
                has_eval_exec = True
            elif name in _REDLINE_SHELL_CALLS or _has_shell_true(node):
                has_shell_true = True
            continue
        hardcoded_secrets |= _secret_targets_of(node)
    return has_bare_except, has_eval_exec, has_shell_true, hardcoded_secrets
def _resolve_fix_labels(fix: dict, i: int) -> tuple[str, str]:
    rule_id = fix.get("rule_id") or f"FIX-{i}"
    return rule_id, fix.get("description") or f"修复 {rule_id}"
@dataclass(frozen=True)
class _StepSpec:
    index: int
    rule_id: str
    description: str
    @property
    def step_id(self) -> str:
        return f"step-{self.index}"
@dataclass(frozen=True)
class _StepOutcome:
    snapshot: VerifySnapshot
    after: str
    rolled_back: bool = False
    reason: str = ""
def _step_spec(fix: object, i: int) -> _StepSpec:
    if isinstance(fix, dict):
        rule_id, description = _resolve_fix_labels(fix, i)
        return _StepSpec(i, rule_id, description)
    kind = type(fix).__name__
    return _StepSpec(i, f"FIX-{i}", f"非法修复配置(非 dict: {kind})")
def _skipped_step(run: _FixRun, spec: _StepSpec, warning: str = "") -> None:
    run.steps.append(FixStep(
        step_id=spec.step_id, rule_id=spec.rule_id,
        before_code=run.code, after_code=run.code,
        fix_description=spec.description,
        verify_result=VerifySnapshot(
            status=VerifyStatus.SKIPPED,
            warnings=[warning] if warning else [],
        ),
    ))
def _new_redline_hits(base_hits: dict[tuple[str, str], list[int]],
                      cur_hits: dict[tuple[str, str], list[int]],
                      ) -> list[tuple[int, tuple[str, str], int]]:
    new_hits: list[tuple[int, tuple[str, str], int]] = []
    for key, lines in cur_hits.items():
        base_lines = base_hits.get(key, ())
        # “新增几处”按重数差计：行号整体平移（如修复在顶部插入 import）
        # 不构成新增；报告行号仍只取基线多重集之外的行。
        extra = len(lines) - len(base_lines)
        if extra <= 0:
            continue
        fresh_lines = sorted((Counter(lines) - Counter(base_lines)).elements())
        new_hits.append((fresh_lines[0], key, extra))
    return new_hits
def _redline_message(line: int, key: tuple[str, str], extra: int,
                     existed: bool) -> str:
    desc, _ident = key
    if existed:
        return f"{desc} 新增{extra}处 (行{line})"
    return f"{desc} (行{line})"
class VerifyStatus(Enum):
    PASSED = "passed"
    DEGRADED = "degraded"
    BLOCKED = "blocked"
    SKIPPED = "skipped"
@dataclass
class VerifySnapshot:
    status: VerifyStatus
    pre_score: float = 0.0
    post_score: float = 0.0
    warnings: list[str] = field(default_factory=list)
    redline_triggered: bool = False
    redline_detail: str = ""
@dataclass
class FixStep:
    step_id: str
    rule_id: str
    before_code: str
    after_code: str
    fix_description: str
    verify_result: VerifySnapshot
    rolled_back: bool = False
    rollback_reason: str = ""
@dataclass
class VerifiedFix:
    original_code: str
    fixed_code: str
    steps: list[FixStep]
    total_fixes: int
    successful_fixes: int
    rolled_back_fixes: int
    overall_improvement: float
    is_safe: bool
    def summary(self) -> dict[str, Any]:
        return {"total_fixes": self.total_fixes,
                "successful": self.successful_fixes,
                "rolled_back": self.rolled_back_fixes,
                "improvement": round(self.overall_improvement, 2),
                "is_safe": self.is_safe, "steps": len(self.steps)}
@dataclass
class _FixRun:
    code: str
    steps: list[FixStep] = field(default_factory=list)
    successful: int = 0
    rolled_back: int = 0
    all_safe: bool = True
class InlineVerifier:
    def __init__(self, score_tolerance: float = _DEFAULT_SCORE_TOLERANCE):
        self.score_tolerance = coerce_tolerance(score_tolerance)
    @staticmethod
    def _score(code: str, diag_fn: Callable) -> float | None:
        try:
            return finite_float_or_none(diag_fn(code))
        except Exception as scoring_error:
            logger.warning(
                "[InlineVerify] 诊断评分失败（按不可评分降级）: %s",
                scoring_error, exc_info=True)
            return None
    def verify_and_fix(
        self,
        original_code: str,
        fixes: list[dict],
        diag_fn: Callable | None = None,
    ) -> VerifiedFix:
        if diag_fn is None:
            diag_fn = self._builtin_diag
        _t0 = time.monotonic()
        fixes = list(fixes) if fixes is not None else []
        pre_score = self._score(original_code, diag_fn)
        run = _FixRun(code=original_code)
        current_score = pre_score
        for i, fix in enumerate(fixes):
            spec = _step_spec(fix, i)
            after = self._try_apply_fix(run, fix, spec)
            if after is None:
                continue
            snapshot = self._verify_step(
                run.code, current_score, after, diag_fn)
            if self._handle_step_outcome(run, snapshot, after, spec):
                self._record_abandoned(
                    run, fixes, i + 1, snapshot.redline_detail)
                break
            if run.code == after:
                current_score = snapshot.post_score
        result = self._finalize_result(
            run, original_code, len(fixes), pre_score, current_score)
        trace_module_run(
            _MODULE_TAG, "verify_and_fix", _t0, outcome="ok",
            total_fixes=result.total_fixes,
            successful=result.successful_fixes,
            rolled_back=result.rolled_back_fixes,
            steps=len(result.steps),
            safe=result.is_safe)
        return result
    def _try_apply_fix(self, run: _FixRun, fix: object,
                       spec: _StepSpec) -> str | None:
        if not isinstance(fix, dict):
            kind = type(fix).__name__
            logger.warning(
                "InlineVerifier: fixes 元素非 dict(跳过 #%d): %s",
                spec.index, kind)
            _skipped_step(run, spec, f"fixes 元素非 dict: {kind}")
            return None
        fix_fn = fix.get("fix_fn")
        if fix_fn is None:
            logger.warning("InlineVerifier: 修复配置缺 fix_fn(跳过 %s)",
                           spec.rule_id)
            _skipped_step(run, spec, "缺少 fix_fn（跳过）")
            return None
        try:
            after = fix_fn(run.code)
        except Exception as _e:
            logger.warning("InlineVerifier: fix_fn 执行异常(跳过 %s): %s",
                           spec.rule_id, _e, exc_info=True)
            _skipped_step(run, spec, f"fix_fn 异常: {_e}")
            return None
        if not isinstance(after, str):
            kind = type(after).__name__
            logger.warning(
                "InlineVerifier: fix_fn 返回非 str(跳过 %s): %s",
                spec.rule_id, kind)
            _skipped_step(run, spec, f"fix_fn 返回非 str: {kind}")
            return None
        if after == run.code:
            _skipped_step(run, spec)
            return None
        return after
    @staticmethod
    def _record_abandoned(run: _FixRun, fixes: list, start: int,
                          detail: str) -> None:
        for index in range(start, len(fixes)):
            _skipped_step(run, _step_spec(fixes[index], index),
                          f"前序安全红线中止，未执行: {detail}")
    @staticmethod
    def _record_step(run: _FixRun, spec: _StepSpec,
                     outcome: _StepOutcome) -> None:
        run.steps.append(FixStep(
            step_id=spec.step_id, rule_id=spec.rule_id,
            before_code=run.code, after_code=outcome.after,
            fix_description=spec.description,
            verify_result=outcome.snapshot,
            rolled_back=outcome.rolled_back,
            rollback_reason=outcome.reason,
        ))
    def _handle_step_outcome(
        self, run: _FixRun, snapshot: VerifySnapshot, after: str,
        spec: _StepSpec,
    ) -> bool:
        if snapshot.status == VerifyStatus.BLOCKED:
            logger.critical(
                "[InlineVerify] 安全红线触发: %s — %s",
                spec.rule_id, snapshot.redline_detail)
            self._record_step(run, spec, _StepOutcome(
                snapshot=snapshot, after=after, rolled_back=True,
                reason=f"安全红线: {snapshot.redline_detail}"))
            run.rolled_back += 1
            run.all_safe = False
            return True
        if snapshot.status == VerifyStatus.DEGRADED:
            logger.warning(
                "[InlineVerify] 修复 %s 导致质量退化 (%.1f → %.1f),已回滚",
                spec.rule_id, snapshot.pre_score, snapshot.post_score)
            self._record_step(run, spec, _StepOutcome(
                snapshot=snapshot, after=after, rolled_back=True,
                reason=(f"质量退化: {snapshot.pre_score:.1f} → "
                        f"{snapshot.post_score:.1f}")))
            run.rolled_back += 1
            run.all_safe = False
            return False
        self._record_step(
            run, spec, _StepOutcome(snapshot=snapshot, after=after))
        run.code = after
        run.successful += 1
        return False
    def _finalize_result(
        self, run: _FixRun, original_code: str, total_fixes: int,
        pre_score: float | None, post_score: float | None,
    ) -> VerifiedFix:
        improvement = (0.0 if post_score is None or pre_score is None
                       else post_score - pre_score)
        logger.info(
            "[InlineVerify] 完成: %d/%d 成功, %d 回滚, improvement=%.2f",
            run.successful, total_fixes, run.rolled_back, improvement
        )
        return VerifiedFix(
            original_code=original_code,
            fixed_code=run.code,
            steps=run.steps,
            total_fixes=total_fixes,
            successful_fixes=run.successful,
            rolled_back_fixes=run.rolled_back,
            overall_improvement=improvement,
            is_safe=run.all_safe,
        )
    def _verify_step(self, before: str, pre: float | None, after: str,
                     diag_fn: Callable) -> VerifySnapshot:
        redline_triggered, redline_detail = self.check_redlines(
            after, baseline=before)
        pre_report = 0.0 if pre is None else pre
        if redline_triggered:
            return VerifySnapshot(
                status=VerifyStatus.BLOCKED, pre_score=pre_report,
                post_score=pre_report,
                redline_triggered=True, redline_detail=redline_detail)
        post = self._score(after, diag_fn)
        post_report = 0.0 if post is None else post
        if pre is None or post is None:
            return VerifySnapshot(
                status=VerifyStatus.DEGRADED, pre_score=pre_report,
                post_score=post_report,
                warnings=["质量评分为非有限值或非数值，无法验证修复后质量"])
        score_drop_pct = (pre - post) / max(pre, 1) * 100
        if score_drop_pct > self.score_tolerance:
            return VerifySnapshot(
                status=VerifyStatus.DEGRADED, pre_score=pre, post_score=post,
                warnings=[f"质量退化 {score_drop_pct:.1f}% > 容忍 {self.score_tolerance}%"])
        return VerifySnapshot(
            status=VerifyStatus.PASSED, pre_score=pre, post_score=post)
    def check_redlines(self, code: str, baseline: str = "") -> tuple[bool, str]:
        try:
            tree = parse_cached(code)
        except PARSE_DEGRADE_EXC as e:
            logger.warning("%s: %s", MSG_SYNTAX_ERROR_SKIP, e)
            return True, f"语法错误: {e}"
        try:
            compile(tree, '<inline_verify>', 'exec')
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[InlineVerifier] Semantic check failed: %s", e)
            return True, f"语义错误: {e}"
        base_hits: dict[tuple[str, str], list[int]] = {}
        if baseline:
            try:
                base_hits = self._collect_redline_hits(baseline)
            except PARSE_DEGRADE_EXC as _e:
                log_swallowed(__name__, _e, context='InlineVerifier.check_redlines:SyntaxError')
                base_hits = {}
        cur_hits = self._collect_redline_hits(code, _tree=tree)
        new_hits = _new_redline_hits(base_hits, cur_hits)
        if new_hits:
            first_line, key, extra = min(new_hits)
            return True, _redline_message(first_line, key, extra, key in base_hits)
        return False, ""
    def _collect_redline_hits(
        self, code: str, _tree: ast.AST | None = None,
    ) -> dict[tuple[str, str], list[int]]:
        tree = _tree if _tree is not None else parse_cached(code)
        call_names = _RedlineAliasResolver().resolve(tree)
        seen: dict[tuple[str, str], list[int]] = {}
        for node in walk_nodes(tree):
            if isinstance(node, ast.Call):
                key = self._redline_key(node, call_names.get(id(node)))
            else:
                key = self._redline_key(node)
            if key is not None:
                seen.setdefault(key, []).append(node.lineno)
        return seen
    def _redline_key(self, node: ast.AST,
                     resolved_name: str | None = None,
                     ) -> tuple[str, str] | None:
        if isinstance(node, ast.Call):
            call_name = (resolved_name if resolved_name is not None
                         else _normalize_redline_call(
                             resolve_call_name(node)))
            if call_name in _REDLINE_EXEC_CALLS:
                return f"{call_name}() 任意代码执行风险", call_name
            if call_name in _REDLINE_SHELL_CALLS:
                return f"{call_name}() 命令注入风险", call_name
            if _has_shell_true(node):
                return "shell=True 命令注入风险", "shell=True"
            return None
        if isinstance(node, ast.ExceptHandler) and node.type is None:
            return "裸 except", "bare_except"
        return None
    @staticmethod
    def _builtin_diag(code: str) -> float:
        score = _DIAG_BASE_SCORE
        lines = count_lines(code)
        if lines < _DIAG_TINY_LINES:
            score -= _DIAG_TINY_PENALTY
        elif lines > _DIAG_HUGE_LINES:
            score -= _DIAG_HUGE_PENALTY
        try:
            tree = parse_cached(code)
        except PARSE_DEGRADE_EXC as _e:
            log_swallowed(__name__, _e, context='InlineVerifier._builtin_diag:SyntaxError')
            tree = None
        if tree is not None:
            has_bare_except, has_eval_exec, has_shell_true, secrets = (
                _collect_pattern_flags(tree))
            if has_bare_except:
                score -= _DIAG_BARE_EXCEPT_PENALTY
            if has_eval_exec:
                score -= _DIAG_EVAL_EXEC_PENALTY
            if has_shell_true:
                score -= _DIAG_SHELL_TRUE_PENALTY
            score -= _DIAG_SECRET_PENALTY * len(secrets)
        return max(_DIAG_SCORE_MIN, min(_DIAG_SCORE_MAX, score))
__all__ = [
    'VERIFY_LAYERS',
    'FixStep',
    'InlineVerifier',
    'LayerConfig',
    'VerifiedFix',
    'VerifySnapshot',
    'VerifyStatus',
    'post_write_import_check',
    'subprocess_import_module',
    'verify_regression',
]
logger.info("fix_safety_verify 验证阶梯与内联修复器已加载: %d 项导出", len(__all__))

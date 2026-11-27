from __future__ import annotations

import logging
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, NamedTuple

from jwsgj.diag_guard_io import SourceReadError, decode_source_strict
from jwsgj.diag_testing_coverage import (
    TEST_DIR_CANDIDATES,
    CoverageMap,
    locate_pytest_summary_line,
    parse_pytest_summary_counts,
)
from jwsgj.diag_types_normalize import coerce_timeout, elapsed_seconds
from jwsgj.log_config import get_module_logger, log_swallowed, write_module_run
from jwsgj.runtime_paths import (
    SOURCE_LAYOUT_ROOT_NAMES,
    get_backup_base,
    source_import_roots,
    subprocess_noartifact_env,
)
from jwsgj.runtime_scope import (
    canonical_path,
    is_test_source_basename,
    normalize_skill_dir,
)
from jwsgj.testsuite_registry import (
    TestRegistry,
    _paired_test_stems,
    test_asset_dirs,
)

__all__ = [
    "DEFAULT_REGRESSION_TIMEOUT",
    "DEFAULT_TEST_TIMEOUT",
    "MUTATION_TEST_TIMEOUT",
    "PYTEST_EXIT_NO_TESTS",
    "MutationTestResult",
    "SelectiveTestRunner",
    "TestRunResult",
    "bridge_covering_tests",
    "filename_matched_tests",
    "get_test_suite_bridge",
    "last_failure_line",
    "locate_targeted_tests",
    "regression_test_candidates",
    "run_post_write_regression",
    "run_pytest_files",
    "run_pytest_regression",
    "run_targeted_regression",
    "set_test_suite_bridge",
    "summarize_regression",
]
logger = get_module_logger(__name__, __file__)
logger.addHandler(logging.NullHandler())
_PYTEST_BASE_ARGS = ("-q", "--tb=short", "-p", "no:cacheprovider",
                     "-o", "addopts=")
def _pytest_env(cwd: str | Path) -> dict:
    env = subprocess_noartifact_env()
    try:
        root = os.path.abspath(os.fspath(cwd))
    except (OSError, TypeError, ValueError):
        return env
    entries = [root, *source_import_roots(root)]
    ambient = env.get("PYTHONPATH", "")
    if ambient:
        entries.extend(
            entry if os.path.isabs(entry)
            else os.path.abspath(os.path.join(root, entry))
            for entry in ambient.split(os.pathsep) if entry)
    env["PYTHONPATH"] = os.pathsep.join(
        dict.fromkeys(entry for entry in entries if entry))
    return env
PYTEST_EXIT_NO_TESTS = 5
def run_pytest_files(skill_dir: str | Path, extra_args: tuple[str, ...] = (),
                     *, timeout: float) -> subprocess.CompletedProcess:
    cmd = [sys.executable, "-m", "pytest", *_PYTEST_BASE_ARGS, *extra_args]
    return subprocess.run(  # jwsgj:suppress SYM-TAINT — 审计认可：cmd 由本函数内部构造（sys.executable 起始）
        cmd, cwd=str(skill_dir), capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=timeout,
        check=False, env=_pytest_env(skill_dir))
_RESTORE_RETRY_DELAY_S = 0.1
_PYTEST_INTERRUPT_BANNER_RE = re.compile(
    r"!{2,}\s*(?:Interrupt(?:ed)?:\s*)?stopping after \d+ failures?\s*!{2,}"
    r"|!{2,}\s*KeyboardInterrupt\s*!{2,}",
    re.IGNORECASE,
)
_VALID_MARKER_RE = re.compile(r"[a-zA-Z_][a-zA-Z0-9_]*")
_PYTEST_OUTCOME_NODEID_RE = re.compile(
    r"^\s*(?P<outcome>FAILED|ERROR|PASSED|XFAIL|XPASS)\s+(?:collecting\s+)?"
    r"(?P<body>.+?)\s*$")
_PYTEST_SKIPPED_FILE_RE = re.compile(
    r"^\s*SKIPPED\s+(?:\[\d+\]\s+)?(?P<file>.+?\.py)(?::|\s|$)")
def _counts_backed_by_failed_lines(counts: dict[str, int],
                                   failed_tests: list[str],
                                   returncode: int) -> dict[str, int]:
    if (returncode == 0 or not failed_tests
            or counts.get("failed", 0) + counts.get("errors", 0) > 0):
        return counts
    recovered = dict(counts)
    recovered["failed"] = len(failed_tests)
    logger.debug(
        "[SelectiveTestRunner] 摘要行无失败/错误计数（rc=%d），按 FAILED "
        "明细补齐 failed=%d", returncode, len(failed_tests))
    return recovered
DEFAULT_TEST_TIMEOUT = 60
MUTATION_TEST_TIMEOUT = 30
DEFAULT_REGRESSION_TIMEOUT = 300.0
@dataclass(frozen=True)
class _RunFacts:
    all_passed: bool
    no_tests_ran: bool
    pytest_not_found: bool
    collection_error: bool
    interrupted: bool
    total: int
    failed: int
    errors: int
    returncode: int
    skipped: int = 0
    deselected: int = 0
class _OutcomeFileMarkers(NamedTuple):
    files_norm: set[str]
    stems: set[str]
    exact_hits: set[str]
class _FailedFileMarkers(NamedTuple):
    files_norm: set[str]
    stems: set[str]
    exact_hits: set[str]
    error_files_norm: set[str] = frozenset()
    error_stems: set[str] = frozenset()
    error_hits: set[str] = frozenset()
def _merged_output(result: subprocess.CompletedProcess) -> str:
    stdout = result.stdout or ""
    stderr = result.stderr or ""
    separator = ("\n" if stdout and stderr
                 and not stdout.endswith(("\n", "\r")) else "")
    return stdout + separator + stderr
def _has_interrupt_banner(output: str) -> bool:
    return any(_PYTEST_INTERRUPT_BANNER_RE.fullmatch(line.strip())
               for line in output.splitlines())
def _build_run_facts(result: subprocess.CompletedProcess, output: str,
                     counts: dict[str, int]) -> _RunFacts:
    total = (counts["passed"] + counts["failed"] + counts["errors"]
             + counts["skipped"] + counts["xfailed"] + counts["xpassed"])
    executed = (counts["passed"] + counts["xfailed"] + counts["xpassed"])
    no_tests_ran = (
        (result.returncode == 5 and total == 0)
        or (result.returncode == 0 and executed == 0
            and (counts["skipped"] > 0 or counts["deselected"] > 0)))
    return _RunFacts(
        all_passed=result.returncode == 0 and executed > 0,
        no_tests_ran=no_tests_ran,
        pytest_not_found=(total == 0
                          and ("No module named pytest" in output
                               or "No module named __main__" in output)),
        collection_error=(result.returncode == 2 and executed == 0),
        interrupted=_has_interrupt_banner(output),
        total=total, failed=counts["failed"], errors=counts["errors"],
        returncode=result.returncode, skipped=counts["skipped"],
        deselected=counts["deselected"])
def _resolve_run_status(facts: _RunFacts) -> tuple[str, str]:
    if facts.all_passed:
        return "passed", ""
    if facts.no_tests_ran:
        return "skipped", "no tests executed in pytest"
    if facts.interrupted:
        message = (f"pytest interrupted (rc={facts.returncode}), "
                   "results incomplete")
        return "error", message
    if facts.returncode == 0 and facts.total == 0:
        return "error", "pytest exited 0 without test evidence"
    if facts.pytest_not_found:
        return "error", "pytest not installed or not accessible"
    if facts.collection_error:
        return "error", f"test collection error (rc={facts.returncode})"
    if facts.total == 0 and facts.returncode != 0:
        return "error", f"test execution failed (rc={facts.returncode}), no tests collected"
    parts = []
    if facts.failed:
        parts.append(f"{facts.failed} tests failed")
    if facts.errors:
        parts.append(f"{facts.errors} errors")
    return "failed", ", ".join(parts) or "test run failed"
def _file_has_failure_attribution(markers: _FailedFileMarkers,
                                  tf_normcase: str, tf_stem: str) -> bool:
    return (tf_normcase in markers.files_norm
            or (not markers.exact_hits and tf_stem in markers.stems))
def _file_has_error_attribution(markers: _FailedFileMarkers,
                               tf_normcase: str, tf_stem: str) -> bool:
    return (tf_normcase in markers.error_files_norm
            or (not markers.error_hits and tf_stem in markers.error_stems))
def _file_has_outcome_attribution(markers: _OutcomeFileMarkers,
                                  tf_normcase: str, tf_stem: str) -> bool:
    return (tf_normcase in markers.files_norm
            or (not markers.exact_hits and tf_stem in markers.stems))
def _resolve_file_status(facts: _RunFacts, final_status: str,
                         markers: _FailedFileMarkers,
                         successful_markers: _OutcomeFileMarkers,
                         skipped_markers: _OutcomeFileMarkers,
                         tf_normcase: str, tf_stem: str,
                         has_tests: bool, single_file: bool) -> str:
    has_success = _file_has_outcome_attribution(
        successful_markers, tf_normcase, tf_stem)
    has_skipped = _file_has_outcome_attribution(
        skipped_markers, tf_normcase, tf_stem)
    if facts.all_passed:
        if single_file or has_success:
            return "passed"
        if not has_tests or has_skipped:
            return "skipped"
        return "not_run"
    if facts.no_tests_ran:
        return "skipped"
    if _file_has_failure_attribution(markers, tf_normcase, tf_stem):
        return "failed"
    if _file_has_error_attribution(markers, tf_normcase, tf_stem):
        return "error"
    if has_success:
        return "passed"
    if has_skipped:
        return "skipped"
    if final_status == "error" or facts.interrupted:
        return "error"
    if not has_tests:
        return "skipped"
    return "error"
def _outcome_node_name(body: str) -> str:
    if "::" not in body:
        file_end = re.search(r"\.py(?=\s+-\s+)", body)
        if file_end is not None:
            return body[:file_end.end()].strip()
        name, separator, _message = body.rpartition(" - ")
        return (name if separator else body).strip()
    depth = 0
    start = body.find("::") + 2
    index = start
    while index < len(body):
        char = body[index]
        if char == "[":
            depth += 1
        elif char == "]":
            depth = max(0, depth - 1)
        elif depth == 0 and body.startswith(" - ", index):
            return body[:index].strip()
        index += 1
    return body.strip()
def _outcome_node_id(line: str) -> tuple[str, str] | None:
    match = _PYTEST_OUTCOME_NODEID_RE.match(line)
    if match is None:
        return None
    return match.group("outcome"), _outcome_node_name(match.group("body"))
def _named_failed_tests(lines: list[str]) -> list[str]:
    names: list[str] = []
    for line in lines:
        parsed = _outcome_node_id(line)
        if (parsed is not None and parsed[0] == "FAILED"
                and "::" in parsed[1]):
            names.append(parsed[1])
    return names
def _successful_node_ids(lines: list[str]) -> list[str]:
    return [
        parsed[1] for line in lines
        if (parsed := _outcome_node_id(line)) is not None
        and parsed[0] in {"PASSED", "XFAIL", "XPASS"}
        and "::" in parsed[1]
    ]
def _skipped_file_paths(lines: list[str]) -> list[str]:
    return [
        match.group("file") for line in lines
        if (match := _PYTEST_SKIPPED_FILE_RE.match(line)) is not None
    ]
_FAILED_BARE_PREFIX_RE = re.compile(r"^FAILED\b[:\s]*(?P<name>.+)$")
def _bare_failed_lines(lines: list[str]) -> list[str]:
    names: list[str] = []
    for line in lines:
        match = _FAILED_BARE_PREFIX_RE.match(line.strip())
        if match is None:
            continue
        name = match.group("name").strip()
        if name:
            names.append(name)
    return names
def _extract_failed_test_names(output_stripped: str, returncode: int) -> list[str]:
    lines = output_stripped.splitlines()
    failed_tests = _named_failed_tests(lines)
    if not failed_tests and returncode != 0:
        failed_tests = _bare_failed_lines(lines)
    return list(dict.fromkeys(failed_tests))
@dataclass
class TestRunResult:
    __test__ = False
    passed: bool = False
    total: int = 0
    failed: int = 0
    errors: int = 0
    skipped: int = 0
    duration: float = 0.0
    output: str = ""
    ran_tests: list[str] = field(default_factory=list)
    failed_tests: list[str] = field(default_factory=list)
    error_message: str = ""
    status: str = "not_run"
    def to_dict(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "total": self.total,
            "failed": self.failed,
            "errors": self.errors,
            "skipped": self.skipped,
            "duration": round(self.duration, 2),
            "status": self.status,
            "error_message": self.error_message[:200] if self.error_message else "",
        }
@dataclass
class MutationTestResult:
    killed: bool = False
    survived: bool = False
    tests_ran: int = 0
    tests_failed: int = 0
    duration: float = 0.0
    error: str = ""
    def to_dict(self) -> dict[str, Any]:
        return {
            "killed": self.killed,
            "survived": self.survived,
            "tests_ran": self.tests_ran,
            "tests_failed": self.tests_failed,
            "duration": round(self.duration, 2),
            "error": self.error[:200] if self.error else "",
        }
def _mutation_error_verdict(
    result: subprocess.CompletedProcess,
    tests_ran: int,
    failed_count: int,
    elapsed: float,
) -> MutationTestResult | None:
    if tests_ran == 0 and result.returncode != 0:
        mutation_error = (
            "no_tests_inconclusive" if result.returncode == 5
            else f"pytest execution failed (rc={result.returncode}), no tests reported"
        )
        return MutationTestResult(
            error=mutation_error,
            tests_ran=0,
            tests_failed=0,
            duration=elapsed,
        )
    if result.returncode != 0 and failed_count == 0:
        return MutationTestResult(
            error=(
                f"pytest exit rc={result.returncode} without failed count "
                f"in summary (tests_ran={tests_ran})"
            ),
            tests_ran=tests_ran,
            tests_failed=0,
            duration=elapsed,
        )
    return None
def _mutation_verdict(
    result: subprocess.CompletedProcess,
    elapsed: float,
) -> MutationTestResult:
    output = _merged_output(result)
    mutation_summary = locate_pytest_summary_line(output)
    failed_tests = _extract_failed_test_names(output.strip(), result.returncode)
    c = _counts_backed_by_failed_lines(
        parse_pytest_summary_counts(mutation_summary), failed_tests,
        result.returncode)
    tests_ran = (c["passed"] + c["failed"] + c["errors"] + c["skipped"]
                 + c["xfailed"] + c["xpassed"])
    failed_count = c["failed"] + c["errors"]
    error_result = _mutation_error_verdict(
        result, tests_ran, failed_count, elapsed)
    if error_result is not None:
        return error_result
    if c["errors"] and not c["failed"]:
        return MutationTestResult(
            error=(
                f"pytest_errors_inconclusive: {c['errors']} 个用例错误且"
                "无断言失败，无法区分突变效果"),
            tests_ran=tests_ran,
            tests_failed=0,
            duration=elapsed,
        )
    if result.returncode not in (0, 1):
        return MutationTestResult(
            error=f"pytest_exit_{result.returncode}_inconclusive",
            tests_ran=tests_ran,
            tests_failed=c["failed"],
            duration=elapsed,
        )
    if result.returncode == 0 and c["passed"] == 0:
        return MutationTestResult(
            error="no_successful_tests_inconclusive",
            tests_ran=tests_ran,
            tests_failed=0,
            duration=elapsed,
        )
    return MutationTestResult(
        killed=result.returncode == 1 and c["failed"] > 0,
        survived=result.returncode == 0 and c["passed"] > 0,
        tests_ran=tests_ran,
        tests_failed=c["failed"],
        duration=elapsed,
    )
def _validated_marker_args(markers: list[str] | None) -> list[str]:
    if not markers:
        return []
    valid_markers = [m for m in markers
                     if isinstance(m, str) and _VALID_MARKER_RE.fullmatch(m)]
    invalid = [m for m in markers if m not in valid_markers]
    if invalid:
        logger.warning("[SelectiveTestRunner] 跳过非法 marker: %s", invalid)
    if not valid_markers:
        return []
    return ["-m", " and ".join(valid_markers)]
@dataclass(frozen=True)
class _RunProfile:
    maxfail: int
    scope: str
_RUN_TESTS_PROFILE = _RunProfile(maxfail=5, scope="测试")
_RUN_ALL_PROFILE = _RunProfile(maxfail=10, scope="全量测试")
def _filter_str_items(items, label: str) -> list[str]:
    cleaned = [item for item in items if isinstance(item, str)]
    dropped = len(items) - len(cleaned)
    if dropped:
        logger.warning(
            "[SelectiveTestRunner] %s 含非 str 元素（%d 个），已过滤",
            label, dropped)
    return cleaned
class SelectiveTestRunner:
    __test__ = False
    def __init__(
        self,
        coverage_map: CoverageMap,
        test_registry: TestRegistry,
        project_root: str,
        test_timeout: int | None = None,
        mutation_timeout: int | None = None,
    ):
        self.coverage_map = coverage_map
        self.test_registry = test_registry
        self.project_root = os.path.abspath(project_root)
        self.test_timeout = coerce_timeout(test_timeout, DEFAULT_TEST_TIMEOUT)
        self.mutation_timeout = coerce_timeout(
            mutation_timeout, MUTATION_TEST_TIMEOUT)
    @staticmethod
    def _normalize_str_list(value, label: str, *,
                            none_passthrough: bool = False
                            ) -> list[str] | None:
        if value is None:
            return None if none_passthrough else []
        if isinstance(value, str):
            return [value]
        if isinstance(value, (bytes, bytearray)):
            return [bytes(value).decode("utf-8", "replace")]
        if hasattr(value, "__iter__"):
            return _filter_str_items(list(value), label)
        logger.warning(
            "[SelectiveTestRunner] %s 非可迭代类型（%s），%s", label,
            type(value).__name__,
            "忽略筛选" if none_passthrough else "按无源文件处理")
        return None if none_passthrough else []
    def _resolve_source_path(self, source_file: str) -> str:
        if os.path.isabs(source_file):
            return source_file
        candidate = os.path.join(self.project_root, source_file)
        return candidate if os.path.isfile(candidate) else source_file
    def _get_covering_tests(self, source_file: str) -> list[str]:
        resolved = self._resolve_source_path(source_file)
        for candidate in self._test_lookup_candidates(source_file, resolved):
            tests = self.coverage_map.get_tests_for(candidate)
            if tests:
                return tests
        return []
    def _test_lookup_candidates(self, source_file: str, resolved: str) -> Iterator[str]:
        yield resolved
        if os.path.normpath(source_file) != os.path.normpath(resolved):
            yield source_file
        if not os.path.isabs(source_file):
            return
        try:
            rel_form = os.path.relpath(resolved, self.project_root)
        except ValueError as e:
            log_swallowed(__name__, e,
                          context='SelectiveTestRunner._get_covering_tests:ValueError')
            return
        if rel_form and rel_form != os.curdir:
            yield rel_form
    def run_tests_for(
        self,
        source_files: list[str],
        timeout: int | None = None,
        markers: list[str] | None = None,
    ) -> TestRunResult:
        source_files = self._normalize_str_list(source_files, "source_files") or []
        covering: list[str] = []
        for sf in source_files:
            covering.extend(self._get_covering_tests(sf))
        return self._run_selected(
            covering, coerce_timeout(timeout, self.test_timeout), markers,
            _RUN_TESTS_PROFILE, "无覆盖测试文件，跳过测试验证")
    def _collect_existing_test_paths(
            self, test_keys: list[str]
    ) -> tuple[list[str], list[str]]:
        all_tests: list[str] = []
        writeback_paths: list[str] = []
        seen: set[str] = set()
        for key in test_keys:
            resolved = self._resolve_source_path(key)
            if not os.path.isabs(resolved) or not os.path.isfile(resolved):
                continue
            if not _target_within_skill(self.project_root, resolved):
                logger.warning(
                    "[SelectiveTestRunner] 忽略项目根外测试路径: %s", resolved)
                continue
            norm = os.path.normcase(os.path.normpath(resolved))
            if norm in seen:
                continue
            seen.add(norm)
            resolved_abs = os.path.abspath(resolved)
            all_tests.append(resolved_abs)
            writeback_paths.append(
                key if self.test_registry.get(key) is not None else resolved_abs)
        return all_tests, writeback_paths
    def _run_selected(
        self,
        test_keys: list[str],
        effective_timeout: int,
        markers: list[str] | None,
        profile: _RunProfile,
        skip_message: str,
    ) -> TestRunResult:
        markers = self._normalize_str_list(
            markers, "markers", none_passthrough=True)
        all_tests, writeback_paths = self._collect_existing_test_paths(test_keys)
        if not all_tests:
            return TestRunResult(
                passed=True, status="skipped", error_message=skip_message)
        return self._run_pytest(all_tests, effective_timeout, markers, profile,
                                writeback_paths=writeback_paths)
    @staticmethod
    def _error_result(start_time: float, test_paths: list[str],
                      message: str) -> TestRunResult:
        return TestRunResult(
            passed=False, status="error",
            duration=time.monotonic() - start_time,
            error_message=message,
            ran_tests=test_paths,
        )
    def _run_pytest(
        self,
        test_paths: list[str],
        timeout: int,
        markers: list[str] | None,
        profile: _RunProfile,
        writeback_paths: list[str] | None = None,
    ) -> TestRunResult:
        outcome_args = ("-rA",) if len(test_paths) > 1 else ()
        extra_args = (
            f"--maxfail={profile.maxfail}",
            *outcome_args,
            *_validated_marker_args(markers),
            *test_paths,
        )
        start_time = time.monotonic()
        try:
            result = run_pytest_files(
                self.project_root, extra_args, timeout=timeout)
            return self._parse_pytest_output(
                result, test_paths, time.monotonic() - start_time, writeback_paths)
        except subprocess.TimeoutExpired as e:
            logger.warning("pytest 子进程执行超时: %s", e, exc_info=True)
            return self._error_result(
                start_time, test_paths, f"{profile.scope}执行超时 ({timeout}s)")
        except (OSError, ValueError, subprocess.SubprocessError) as e:
            logger.debug("pytest 子进程执行异常: %s", e)
            return self._error_result(
                start_time, test_paths, f"{profile.scope}执行异常: {e}")
    def _parse_pytest_output(
        self,
        result: subprocess.CompletedProcess,
        ran_tests: list[str],
        elapsed: float,
        writeback_paths: list[str] | None = None,
    ) -> TestRunResult:
        output = _merged_output(result)
        output_stripped = output.strip()
        summary_line = locate_pytest_summary_line(output_stripped)
        failed_tests = _extract_failed_test_names(
            output_stripped, result.returncode)
        c = _counts_backed_by_failed_lines(
            parse_pytest_summary_counts(summary_line), failed_tests,
            result.returncode)
        facts = _build_run_facts(result, output, c)
        if c["deselected"] > 0:
            logger.debug("[SelectiveTestRunner] %d tests deselected",
                         c["deselected"])
        outcome_lines = output_stripped.splitlines()
        error_tests = _error_node_ids(outcome_lines)
        successful_tests = _successful_node_ids(outcome_lines)
        skipped_files = _skipped_file_paths(outcome_lines)
        markers = self._collect_failed_file_markers(
            failed_tests, ran_tests, error_tests)
        successful_markers = self._collect_outcome_file_markers(
            successful_tests, ran_tests)
        skipped_markers = self._collect_outcome_file_markers(
            skipped_files, ran_tests)
        final_status, final_msg = _resolve_run_status(facts)
        writeback = writeback_paths if writeback_paths is not None else ran_tests
        per_file_elapsed = elapsed / max(len(ran_tests), 1)
        for tf, tf_key in zip(ran_tests, writeback, strict=True):
            tf_normcase = os.path.normcase(os.path.normpath(tf))
            tf_stem = os.path.splitext(os.path.basename(tf))[0]
            meta = self.test_registry.get(tf_key)
            status = _resolve_file_status(
                facts, final_status, markers, successful_markers,
                skipped_markers, tf_normcase, tf_stem,
                has_tests=meta is None or meta.test_count > 0,
                single_file=len(ran_tests) == 1)
            self.test_registry.update_run_result(tf_key, status, per_file_elapsed)
        return TestRunResult(
            passed=facts.all_passed or facts.no_tests_ran,
            total=facts.total,
            failed=facts.failed,
            errors=facts.errors,
            skipped=c["skipped"],
            duration=elapsed,
            output=output[:2000],
            ran_tests=ran_tests,
            failed_tests=failed_tests,
            status=final_status,
            error_message=final_msg,
        )
    def _collect_failed_file_markers(
        self,
        failed_tests: list[str],
        ran_tests: list[str],
        error_tests: list[str] = (),
    ) -> _FailedFileMarkers:
        failed_files_norm, failed_stems = self._marker_file_sets(failed_tests)
        error_files_norm, error_stems = self._marker_file_sets(error_tests)
        ran_normcase = {
            os.path.normcase(os.path.normpath(tf)) for tf in ran_tests}
        return _FailedFileMarkers(
            failed_files_norm,
            failed_stems,
            failed_files_norm & ran_normcase,
            frozenset(error_files_norm),
            frozenset(error_stems),
            frozenset(error_files_norm & ran_normcase),
        )
    def _collect_outcome_file_markers(
        self,
        successful_tests: list[str],
        ran_tests: list[str],
    ) -> _OutcomeFileMarkers:
        files_norm, stems = self._marker_file_sets(successful_tests)
        ran_normcase = {
            os.path.normcase(os.path.normpath(tf)) for tf in ran_tests}
        return _OutcomeFileMarkers(
            files_norm, stems, files_norm & ran_normcase)
    def _marker_file_sets(
        self,
        node_ids: list[str],
    ) -> tuple[set[str], set[str]]:
        files_norm: set[str] = set()
        stems: set[str] = set()
        for ft_entry in node_ids:
            ft_file = ft_entry.split("::")[0].strip()
            if not ft_file:
                continue
            if not os.path.isabs(ft_file):
                ft_file = os.path.join(self.project_root, ft_file)
            files_norm.add(os.path.normcase(os.path.normpath(ft_file)))
            stems.add(os.path.splitext(os.path.basename(ft_file))[0])
        return files_norm, stems
    @staticmethod
    def _clear_pycache(source_file: str) -> None:
        pycache_dir = os.path.join(os.path.dirname(source_file), "__pycache__")
        if not os.path.isdir(pycache_dir):
            return
        try:
            shutil.rmtree(pycache_dir)
        except OSError as e:
            logger.warning(
                "[SelectiveTestRunner] __pycache__ 清理失败（旧 .pyc 可能掩盖源码）: %s, %s",
                pycache_dir, e)
    @staticmethod
    def _restore_source_file(
            source_file: str, original_source: str, source_encoding: str) -> str:
        for attempt in (1, 2):
            try:
                with open(
                        source_file, "w", encoding=source_encoding, newline="") as f:
                    f.write(original_source)
                SelectiveTestRunner._clear_pycache(source_file)
                return ""
            except OSError as e:
                logger.warning(
                    "[SelectiveTestRunner] 恢复原始文件失败(第%d次): %s, %s",
                    attempt, source_file, e,
                )
                if attempt == 1:
                    time.sleep(_RESTORE_RETRY_DELAY_S)
        backup_path = SelectiveTestRunner._write_restore_backup(
            source_file, original_source, source_encoding)
        if backup_path:
            return f"restore_failed_backup_created: {backup_path}"
        return "restore_failed_and_backup_failed"
    @staticmethod
    def _write_restore_backup(
            source_file: str, original_source: str, source_encoding: str) -> str:
        try:
            backup_dir = os.path.join(get_backup_base(), "mutation_restore")
            os.makedirs(backup_dir, exist_ok=True)
            ts = time.strftime("%Y%m%d%H%M%S")
            ident = re.sub(
                r"[^0-9A-Za-z_.-]+", "_",
                os.path.abspath(source_file))[-120:]
            backup_path = os.path.join(
                backup_dir, f"{ident}.mutation_backup_{ts}.bak")
            with open(backup_path, "w", encoding=source_encoding, newline="") as f:
                f.write(original_source)
            logger.error(
                "[SelectiveTestRunner] 无法恢复原始文件，已写入备份: %s (原文件: %s)",
                backup_path, source_file,
            )
            return backup_path
        except (OSError, RuntimeError) as e:
            logger.critical(
                "[SelectiveTestRunner] 无法恢复也无法备份原始文件: %s (%s)",
                source_file, e,
            )
            return ""
    def run_mutation_check(
        self,
        source_file: str,
        mutated_source: str,
        timeout: int | None = None,
    ) -> MutationTestResult:
        effective_timeout = coerce_timeout(timeout, self.mutation_timeout)
        source_file = os.path.abspath(self._resolve_source_path(source_file))
        if not _target_within_skill(self.project_root, source_file):
            logger.warning(
                "[SelectiveTestRunner] 突变检查拒绝越界目标: %s", source_file)
            return MutationTestResult(
                error=(f"path_escape_inconclusive: 目标文件越出项目根: "
                       f"{source_file}"))
        if not os.path.isfile(source_file):
            return MutationTestResult(error=f"source file not found: {source_file}")
        covering_tests = self._get_covering_tests(source_file)
        if not covering_tests:
            return MutationTestResult(error="no_tests_inconclusive")
        covering_tests, _ = self._collect_existing_test_paths(covering_tests)
        if not covering_tests:
            return MutationTestResult(error="no_tests_inconclusive")
        try:
            with open(source_file, "rb") as f:
                original_bytes = f.read()
            original_source, source_encoding = decode_source_strict(original_bytes)
        except (OSError, SourceReadError) as e:
            logger.warning("[SelectiveTestRunner] 源文件读取失败: %s", e, exc_info=True)
            return MutationTestResult(error=f"cannot read source: {e}")
        return self._execute_mutation(
            source_file, mutated_source, original_source, source_encoding,
            covering_tests, effective_timeout)
    def _execute_mutation(
        self,
        source_file: str,
        mutated_source: str,
        original_source: str,
        source_encoding: str,
        covering_tests: list[str],
        effective_timeout: int,
    ) -> MutationTestResult:
        start_time = time.monotonic()
        result = MutationTestResult(error="mutation_not_executed")
        try:
            with open(source_file, "w", encoding=source_encoding, newline="") as f:
                f.write(mutated_source)
            self._clear_pycache(source_file)
            completed = run_pytest_files(
                self.project_root, ("-x", *covering_tests),
                timeout=effective_timeout)
            result = _mutation_verdict(
                completed, time.monotonic() - start_time)
        except subprocess.TimeoutExpired as e:
            logger.warning("pytest 子进程执行超时: %s", e, exc_info=True)
            elapsed = time.monotonic() - start_time
            result = MutationTestResult(
                error=f"timeout ({effective_timeout}s)", duration=elapsed,
            )
        except (OSError, ValueError, subprocess.SubprocessError) as e:
            logger.debug("pytest 子进程执行异常: %s", e)
            elapsed = time.monotonic() - start_time
            result = MutationTestResult(error=str(e)[:200], duration=elapsed)
        finally:
            restore_error = self._restore_source_file(
                source_file, original_source, source_encoding)
        if not restore_error:
            return result
        error = (f"{result.error}; {restore_error}"
                 if result.error else restore_error)
        return MutationTestResult(
            tests_ran=result.tests_ran,
            tests_failed=result.tests_failed,
            duration=result.duration,
            error=error,
        )
    def run_all_tests(
        self,
        timeout: int | None = None,
        markers: list[str] | None = None,
    ) -> TestRunResult:
        return self._run_selected(
            [meta.path for meta in self.test_registry.entries.values()],
            coerce_timeout(timeout, self.test_timeout * 3), markers,
            _RUN_ALL_PROFILE, "无注册测试文件，跳过全量测试")
def _regression_output(proc) -> str:
    output = proc.stdout[-500:] if proc.stdout else ""
    if proc.stderr:
        output += "\n" + proc.stderr[-200:]
    return output
def _regression_verdict(proc, tag: str, skip_msg: str,
                        file_count: int) -> tuple:
    if proc.returncode == 5:
        logger.warning("%s 定向回归未执行: 未收集到测试", tag)
        return False, f"{skip_msg}: no tests collected"
    if proc.returncode == 0:
        output = _merged_output(proc)
        summary_line = locate_pytest_summary_line(output)
        counts = parse_pytest_summary_counts(summary_line)
        facts = _build_run_facts(proc, output, counts)
        status, verdict_message = _resolve_run_status(facts)
        if status == "passed":
            logger.info("%s 定向回归通过 (%d 个测试文件)", tag, file_count)
            return True, _regression_output(proc)
        if status == "skipped":
            logger.warning("%s 定向回归未执行: %s", tag, verdict_message)
            return False, f"{skip_msg}: {verdict_message}"
        logger.warning("%s 定向回归无有效通过证据: %s", tag, verdict_message)
        return False, verdict_message
    output = _regression_output(proc)
    logger.warning("%s 定向回归失败: %s",
                   tag, output.strip()[-300:] or f"pytest 退出码 {proc.returncode}")
    return False, output
def regression_test_candidates(target_file: str) -> list[str]:
    if not isinstance(target_file, str) or not target_file.strip():
        return []
    normalized = target_file.replace("\\", "/")
    rel_dir = os.path.dirname(normalized)
    stem = os.path.splitext(os.path.basename(normalized))[0]
    if not stem:
        return []
    candidate_stems = _paired_test_stems(stem)
    tests_dir = f"tests/{rel_dir}" if rel_dir else "tests"
    alt_tests_dir = f"test/{rel_dir}" if rel_dir else "test"
    candidates = []
    for candidate_stem in candidate_stems:
        candidates.extend([
            f"{tests_dir}/test_{candidate_stem}.py",
            f"{tests_dir}/{candidate_stem}_test.py",
            f"tests/test_{candidate_stem}.py",
            f"test_{candidate_stem}.py",
            f"{candidate_stem}_test.py",
            f"{alt_tests_dir}/test_{candidate_stem}.py",
            f"{alt_tests_dir}/{candidate_stem}_test.py",
            f"test/test_{candidate_stem}.py",
            f"test/{candidate_stem}_test.py",
        ])
        for layout_name in SOURCE_LAYOUT_ROOT_NAMES:
            if not (rel_dir == layout_name
                    or rel_dir.startswith(layout_name + "/")):
                continue
            package_dir = rel_dir[len(layout_name):].lstrip("/")
            package_tests_dir = (f"tests/{package_dir}"
                                 if package_dir else "tests")
            package_alt_tests_dir = (f"test/{package_dir}"
                                     if package_dir else "test")
            candidates[0:0] = [
                f"{package_tests_dir}/test_{candidate_stem}.py",
                f"{package_tests_dir}/{candidate_stem}_test.py",
                f"{package_alt_tests_dir}/test_{candidate_stem}.py",
                f"{package_alt_tests_dir}/{candidate_stem}_test.py",
            ]
            break
        if rel_dir:
            candidates.append(f"{rel_dir}/test_{candidate_stem}.py")
            candidates.append(f"{rel_dir}/{candidate_stem}_test.py")
    return list(dict.fromkeys(candidates))
def _existing_regression_modules(skill_dir: str, modules) -> list:
    module_list = modules if isinstance(modules, (list, tuple)) else ()
    base = canonical_path(skill_dir)
    existing = []
    for module in module_list:
        if not isinstance(module, str) or not module:
            continue
        try:
            full = canonical_path(os.path.join(base, module))
            rel = os.path.relpath(full, base)
        except (OSError, TypeError, ValueError) as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc, context='_existing_regression_modules:OSError')
            continue
        if rel == os.pardir or rel.startswith(os.pardir + os.sep):
            continue
        if os.path.isfile(full):
            existing.append(module)
    return existing
def _run_regression_safely(existing: list, skill_dir: str, tag: str,
                           skip_msg: str, timeout: float) -> tuple:
    try:
        proc = run_pytest_files(
            skill_dir, ("-x", *existing), timeout=timeout)
        return _regression_verdict(proc, tag, skip_msg, len(existing))
    except subprocess.TimeoutExpired as e:
        logger.warning("%s 回归测试超时(%gs): %s", tag, timeout, e)
        return False, f"{skip_msg}: timeout({timeout:g}s)"
    except (OSError, ValueError, subprocess.SubprocessError) as e:
        logger.warning("%s 回归测试无法运行: %s", tag, e)
        return False, f"{skip_msg}: {type(e).__name__}: {e}"
def run_pytest_regression(skill_dir: str, modules: list, tag: str,
                           skip_msg: str,
                           timeout: float | None = None) -> tuple:
    try:
        skill_dir = normalize_skill_dir(skill_dir)
    except (TypeError, ValueError, OSError) as exc:
        log_swallowed(
            __name__, exc, context='run_pytest_regression:normalize_skill_dir')
        skill_dir = ""
    if not skill_dir.strip():
        logger.warning("%s 定向回归无法判定: 技能目录非法或为空", tag)
        return False, f"{skip_msg}: invalid skill_dir"
    existing = _existing_regression_modules(skill_dir, modules)
    if not existing:
        logger.warning("%s 定向回归未执行: 目标无测试文件", tag)
        return False, f"{skip_msg}: no test files found"
    return _run_regression_safely(
        existing, skill_dir, tag, skip_msg,
        coerce_timeout(timeout, DEFAULT_REGRESSION_TIMEOUT))
def last_failure_line(stdout: str | None, stderr: str | None) -> str:
    lines = (stdout or "").strip().splitlines()
    failed_lines = [ln for ln in lines if _is_failure_line(ln)]
    if failed_lines:
        return failed_lines[-1].strip()
    if lines:
        return lines[-1].strip()
    err_lines = (stderr or "").strip().splitlines()
    if err_lines:
        return err_lines[-1].strip()
    return "test failed"
def _is_failure_line(line: str) -> bool:
    return "FAILED" in line or " failed" in line.lower()
def _summary_count(lines: list[str], outcome: str) -> int | None:
    summary_line = locate_pytest_summary_line("\n".join(lines))
    if not summary_line:
        return None
    count = parse_pytest_summary_counts(summary_line).get(outcome, 0)
    return count if count > 0 else None
def _error_node_ids(lines: list[str]) -> list[str]:
    names: list[str] = []
    for line in lines:
        parsed = _outcome_node_id(line)
        if parsed is not None and parsed[0] == "ERROR":
            names.append(parsed[1])
    return names
def _extract_failed_stats(lines: list[str]) -> tuple[int, list[str]]:
    node_ids = list(dict.fromkeys(_named_failed_tests(lines)))
    if node_ids:
        return len(node_ids), node_ids
    summary_n = _summary_count(lines, "failed")
    if summary_n is not None:
        return summary_n, []
    return _failure_fallback_count(lines), []
def _failure_fallback_count(lines: list[str]) -> int:
    return sum(1 for ln in lines if _is_failure_line(ln))
def _extract_error_stats(lines: list[str]) -> int:
    error_nodes = list(dict.fromkeys(_error_node_ids(lines)))
    if error_nodes:
        return len(error_nodes)
    return _summary_count(lines, "errors") or 0
def bridge_covering_tests(file_path: str,
                          skill_dir: str | None = None) -> list[str]:
    try:
        bridge = get_test_suite_bridge()
    except Exception as bridge_err:
        logger.warning("[TargetedReg] bridge 实例获取异常，降级文件名匹配: %s", bridge_err)
        return []
    if bridge is None:
        return []
    try:
        covering = bridge.coverage_map.get_tests_for(file_path)
        raw_paths = list(covering or [])
    except Exception:
        logger.debug("[TargetedReg] bridge 覆盖映射查询失败，降级文件名匹配",
                     exc_info=True)
        return []
    tests: list[str] = []
    for raw_test_path in raw_paths:
        try:
            test_path = os.fspath(raw_test_path)
        except TypeError:
            continue
        if not isinstance(test_path, str):
            continue
        resolved = (test_path
                    if skill_dir is None or os.path.isabs(test_path)
                    else os.path.join(skill_dir, test_path))
        if (skill_dir is not None
                and not _target_within_skill(skill_dir, resolved)):
            logger.warning("[TargetedReg] 忽略项目根外的桥接测试路径: %s",
                           resolved)
            continue
        if os.path.isfile(resolved):
            tests.append(resolved)
    return tests
def _stem_occurs_on_boundary(stem: str, name: str) -> bool:
    start = 0
    while True:
        idx = name.find(stem, start)
        if idx < 0:
            return False
        end = idx + len(stem)
        left_ok = idx == 0 or not name[idx - 1].isalnum()
        right_ok = end >= len(name) or not name[end].isalnum()
        if left_ok and right_ok:
            return True
        start = idx + 1
def _disk_test_dir_paths(skill_dir: str) -> list[str]:
    try:
        entries = sorted(os.listdir(skill_dir))
    except OSError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return []
    actual: dict[str, str] = {}
    for entry in entries:
        actual.setdefault(entry.lower(), entry)
    paths = [os.path.join(skill_dir, actual[name])
             for name in reversed(TEST_DIR_CANDIDATES) if name in actual]
    seen = {os.path.normcase(os.path.abspath(p)) for p in paths}
    try:
        asset_dirs = test_asset_dirs(skill_dir)
    except OSError:
        logger.warning("[TargetedReg] 测试目录面枚举失败: %s", skill_dir,
                       exc_info=True)
        asset_dirs = []
    for entry in asset_dirs:
        if not os.path.isdir(entry):
            continue
        key = os.path.normcase(os.path.abspath(entry))
        if key in seen:
            continue
        seen.add(key)
        paths.append(entry)
    return paths
def _iter_test_search_dirs(skill_dir: str, file_path: str) -> list[str]:
    root = canonical_path(skill_dir)
    dirs: list[str] = []
    seen: set[str] = set()
    candidates = [os.path.dirname(os.path.abspath(file_path))]
    candidates.extend(_disk_test_dir_paths(skill_dir))
    for candidate in candidates:
        if not os.path.isdir(candidate):
            continue
        try:
            real = canonical_path(candidate)
            if os.path.commonpath([real, root]) != root:
                continue
        except (OSError, ValueError):
            continue
        key = os.path.normcase(real)
        if key in seen:
            continue
        seen.add(key)
        dirs.append(candidate)
    return dirs
def _resolve_skill_file_path(skill_dir: str, file_path: str) -> str:
    if not os.path.isabs(file_path):
        file_path = os.path.join(skill_dir, file_path)
    return os.path.abspath(file_path)
def filename_matched_tests(skill_dir: str, file_path: str) -> list[str]:
    skill_dir = normalize_skill_dir(skill_dir)
    file_path = _resolve_skill_file_path(skill_dir, file_path)
    stem = os.path.splitext(os.path.basename(file_path))[0]
    if not stem:
        return []
    search_dirs = _iter_test_search_dirs(skill_dir, file_path)
    direct_matches: list[str] = []
    for test_dir in search_dirs:
        direct_matches.extend(
            path for path in _direct_test_match(test_dir, stem)
            if _target_within_skill(skill_dir, path))
    if direct_matches:
        return list(dict.fromkeys(direct_matches))
    if _target_within_skill(skill_dir, file_path):
        rel_path = os.path.relpath(file_path, skill_dir)
        mirrored = _existing_regression_modules(
            skill_dir, regression_test_candidates(rel_path))
        if mirrored:
            return [os.path.normpath(os.path.join(skill_dir, path))
                    for path in mirrored]
    fuzzy: list[str] = []
    for test_dir in search_dirs:
        fuzzy.extend(_fuzzy_test_matches(test_dir, stem))
    return sorted({path for path in fuzzy
                   if _target_within_skill(skill_dir, path)})
_DIRECT_TEST_TEMPLATES = ("test_{}.py", "_test_{}.py", "{}_test.py")
def _direct_test_names(stem: str) -> tuple[str, ...]:
    return tuple(
        template.format(candidate_stem)
        for candidate_stem in _paired_test_stems(stem)
        for template in _DIRECT_TEST_TEMPLATES
    )
def _direct_test_match(test_dir: str, stem: str) -> list[str]:
    return [candidate
            for name in _direct_test_names(stem)
            if os.path.isfile(candidate := os.path.join(test_dir, name))]
def _fuzzy_test_matches(test_dir: str, stem: str) -> list[str]:
    try:
        entries = os.listdir(test_dir)
    except OSError:
        logger.warning("[TargetedReg] 测试目录列举失败: %s", test_dir, exc_info=True)
        return []
    normalized_stem = os.path.normcase(stem).lower()
    fuzzy = [os.path.join(test_dir, tf)
             for tf in entries
             if tf.lower().endswith(".py")
             and is_test_source_basename(tf)
             and _stem_occurs_on_boundary(normalized_stem, tf.lower())]
    return sorted(fuzzy)
def locate_targeted_tests(skill_dir: str, file_path: str) -> tuple[list[str], str]:
    skill_dir = normalize_skill_dir(skill_dir)
    file_path = _resolve_skill_file_path(skill_dir, file_path)
    bridge_tests = bridge_covering_tests(file_path, skill_dir=skill_dir)
    if bridge_tests:
        return sorted(set(bridge_tests)), "bridge"
    matched = filename_matched_tests(skill_dir, file_path)
    if not matched:
        return [], "none"
    stem = os.path.splitext(os.path.basename(file_path))[0]
    if os.path.basename(matched[0]) in _direct_test_names(stem):
        return matched, "filename"
    return matched, "fuzzy"
def _interpret_pytest_outcome(result, tests: list[str], mode: str,
                              file_path: str) -> dict:
    if result.returncode == PYTEST_EXIT_NO_TESTS:
        logger.info("[TargetedReg] 定向回归跳过: %s 定位到 %d 个测试文件但无用例可收集 (%s 定位)",
                    file_path, len(tests), mode)
        return {"status": "skipped", "mode": mode, "tests": [],
                "summary": f"定位到 {len(tests)} 个测试文件但无测试用例可收集"
                           f"（{mode} 定位），定向回归跳过"}
    if result.returncode == 0:
        output = _merged_output(result)
        summary_line = locate_pytest_summary_line(output)
        counts = parse_pytest_summary_counts(summary_line)
        facts = _build_run_facts(result, output, counts)
        status, verdict_message = _resolve_run_status(facts)
        if status == "passed":
            total = len(tests)
            logger.info("[TargetedReg] 定向回归通过: %s (%d 个测试文件, %s 定位)",
                        file_path, total, mode)
            return {"status": status, "mode": mode, "tests": tests,
                    "total": total, "skipped": counts["skipped"],
                    "summary": f"定向回归通过: {len(tests)} 个测试文件 "
                               f"({mode} 定位)"}
        logger.warning("[TargetedReg] 定向回归无有效通过证据: %s | %s",
                       file_path, verdict_message)
        return {"status": status, "mode": mode, "tests": tests,
                "total": len(tests), "skipped": counts["skipped"],
                "summary": (f"定向回归{status}: {verdict_message} "
                            f"({mode} 定位)")}
    summary = last_failure_line(result.stdout, result.stderr)
    if result.returncode != 1:
        logger.warning(
            "[TargetedReg] 定向回归无法判定(rc=%d, %s 定位): %s | %s",
            result.returncode, mode, file_path, str(summary)[:200])
        return {"status": "error", "mode": mode, "tests": tests,
                "total": len(tests), "failed": 0, "errors": 0,
                "failed_tests": [],
                "summary": (f"定向回归无法判定(rc={result.returncode}, "
                            f"{mode} 定位): {str(summary)[:200]}")}
    lines = _merged_output(result).strip().splitlines()
    failed_count, failed_node_ids = _extract_failed_stats(lines)
    error_count = _extract_error_stats(lines)
    if (error_count and not failed_node_ids
            and _summary_count(lines, "failed") is None):
        failed_count = 0
    if failed_count == 0 and error_count == 0:
        logger.warning(
            "[TargetedReg] 定向回归无法判定(rc=1且无失败明细, %s 定位): %s | %s",
            mode, file_path, str(summary)[:200])
        return {"status": "error", "mode": mode, "tests": tests,
                "total": len(tests), "failed": 0, "errors": 0,
                "failed_tests": [],
                "summary": (f"定向回归无法判定(rc=1且无失败明细, "
                            f"{mode} 定位): {str(summary)[:200]}")}
    logger.warning("[TargetedReg] 定向回归失败(%s 定位): %s | failed=%d | errors=%d | %s",
                   mode, file_path, failed_count, error_count, str(summary)[:200])
    return {"status": "failed", "mode": mode, "tests": tests, "total": len(tests),
            "failed": failed_count,
            "errors": error_count,
            "skipped": _summary_count(lines, "skipped") or 0,
            "failed_tests": failed_node_ids[:5],
            "summary": f"定向回归失败({mode} 定位): "
                       f"{str(summary)[:200]}"}
def _execute_targeted_pytest(
        skill_dir: str, file_path: str, tests: list[str],
        timeout: float) -> tuple[subprocess.CompletedProcess | None, str | None]:
    try:
        result = run_pytest_files(skill_dir, tuple(tests), timeout=timeout)
    except subprocess.TimeoutExpired:
        logger.warning("[TargetedReg] 定向回归超时(%ss)，无法判定，交 AI 决策: %s",
                       timeout, file_path)
        return None, f"定向回归超时({timeout}s)，无法判定，交 AI 决策"
    except (OSError, ValueError, subprocess.SubprocessError) as e:
        logger.warning("[TargetedReg] 定向回归执行异常(交 AI 决策): %s: %s",
                       file_path, e)
        return None, f"定向回归执行异常: {e}"
    return result, None
def _display_target_path(file_path: str, skill_dir: str) -> str:
    try:
        rel = os.path.relpath(file_path, skill_dir)
    except ValueError as _e:
        log_swallowed(__name__, _e,
                      context='run_targeted_regression._display_path:ValueError')
        return file_path
    if rel == ".." or rel.startswith(".." + os.sep):
        return file_path
    return rel
class _RegressionRun(NamedTuple):
    started: float
    started_mono: float
    file_path: str
    skill_dir: str
_INVALID_SKILL_DIR_SUMMARY = "技能目录非法或为空，定向回归跳过"
def _regression_result(
    status: str,
    mode: str,
    tests: list[str],
    run: _RegressionRun,
    **extra: Any,
) -> dict:
    write_module_run(
        "testsuite_runner", "run_targeted_regression", outcome=status,
        duration_ms=(time.monotonic() - run.started_mono) * 1000.0,
        mode=mode, tests=len(tests),
        failed=extra.get("failed", 0),
        errors=extra.get("errors", 0))
    return {
        "status": status,
        "mode": mode,
        "file": _display_target_path(run.file_path, run.skill_dir),
        "tests": tests,
        "total": extra.get("total", 0),
        "failed": extra.get("failed", 0),
        "errors": extra.get("errors", 0),
        "skipped": extra.get("skipped", 0),
        "failed_tests": extra.get("failed_tests", []),
        "summary": extra.get("summary", ""),
        "duration": elapsed_seconds(run.started),
    }
def _target_skip_summary(file_path: str) -> str | None:
    if os.path.splitext(file_path)[1].lower() != ".py":
        return (f"非 Python 文件，定向回归跳过: "
                f"{os.path.basename(file_path)}")
    if not os.path.isfile(file_path):
        logger.warning("[TargetedReg] 目标文件不存在，定向回归跳过: %s", file_path)
        return "目标文件不存在，定向回归跳过"
    return None
def _target_within_skill(skill_dir: str, file_path: str) -> bool:
    try:
        root = canonical_path(skill_dir)
        target = canonical_path(file_path)
        common = os.path.commonpath([root, target])
    except (OSError, ValueError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return False
    return os.path.normcase(common) == os.path.normcase(root)
def run_targeted_regression(skill_dir: str, file_path: str,
                             timeout: float | None = None) -> dict:
    started = time.time()
    _t0m = time.monotonic()
    if not isinstance(skill_dir, str) or not skill_dir.strip():
        run = _RegressionRun(started, _t0m, str(file_path or ""), "")
        return _regression_result(
            "skipped", "none", [], run,
            summary=_INVALID_SKILL_DIR_SUMMARY)
    if not isinstance(file_path, (str, os.PathLike)):
        run = _RegressionRun(started, _t0m, str(file_path), skill_dir)
        return _regression_result(
            "skipped", "none", [], run,
            summary="目标路径类型非法，定向回归跳过")
    file_path = os.fsdecode(file_path)
    skill_dir = normalize_skill_dir(skill_dir)
    file_path = _resolve_skill_file_path(skill_dir, file_path)
    timeout = coerce_timeout(timeout, DEFAULT_REGRESSION_TIMEOUT)
    run = _RegressionRun(started, _t0m, file_path, skill_dir)
    skip_summary = _target_skip_summary(file_path)
    if skip_summary is not None:
        return _regression_result(
            "skipped", "none", [], run, summary=skip_summary)
    if not _target_within_skill(skill_dir, file_path):
        return _regression_result(
            "skipped", "none", [], run,
            summary="目标文件越出项目根，定向回归跳过")
    tests, mode = locate_targeted_tests(skill_dir, file_path)
    if not tests:
        return _regression_result(
            "skipped", "none", [], run,
            summary=f"无对应测试文件（{os.path.basename(file_path)}），"
                    f"定向回归跳过——不跑全量")
    result, run_error = _execute_targeted_pytest(
        skill_dir, file_path, tests, timeout)
    if run_error is not None:
        return _regression_result(
            "error", mode, tests, run,
            total=len(tests), summary=run_error)
    return _regression_result(
        run=run,
        **_interpret_pytest_outcome(result, tests, mode, file_path))
_VALID_REGRESSION_STATUSES = frozenset({"passed", "skipped", "failed", "error"})
def run_post_write_regression(skill_dir: str, file_path: str) -> dict:
    try:
        regression = run_targeted_regression(skill_dir, file_path)
        if isinstance(regression, dict):
            status = regression.get("status")
            if isinstance(status, str) and status in _VALID_REGRESSION_STATUSES:
                return regression
            error: BaseException = ValueError(f"返回状态异常({status!r})")
        else:
            error = TypeError(f"返回形态异常({type(regression).__name__})")
    except Exception as exc:
        logger.debug("[AIManualFix] 定向回归链路抛错，按 error 收口: %s: %s",
                     type(exc).__name__, exc)
        error = exc
    logger.warning("[AIManualFix] 定向回归链路异常(按error状态收口): %s: %s",
                   type(error).__name__, error,
                   exc_info=(type(error), error, error.__traceback__))
    return {"status": "error", "mode": "none", "file": file_path,
            "tests": [], "total": 0, "failed": 0, "errors": 0,
            "skipped": 0, "failed_tests": [],
            "summary": f"定向回归执行异常: {error}", "duration": 0.0}
def summarize_regression(result: dict | None) -> str:
    if not isinstance(result, dict) or not result:
        return ""
    parts: list[str] = []
    if result.get("status"):
        parts.append(f"status={result['status']}")
    if result.get("mode"):
        parts.append(f"mode={result['mode']}")
    tests = result.get("tests")
    if isinstance(tests, (list, tuple)) and tests:
        parts.append(f"tests={len(tests)}")
    for key in ("failed", "errors"):
        count = result.get(key)
        if isinstance(count, int) and not isinstance(count, bool) and count:
            parts.append(f"{key}={count}")
    if result.get("summary"):
        parts.append(str(result["summary"])[:160])
    return " | ".join(parts)
_test_suite_bridge_instance = None
_test_suite_bridge_lock = threading.Lock()
def get_test_suite_bridge() -> Any:
    with _test_suite_bridge_lock:
        return _test_suite_bridge_instance
def set_test_suite_bridge(bridge: Any) -> None:
    global _test_suite_bridge_instance
    with _test_suite_bridge_lock:
        _test_suite_bridge_instance = bridge

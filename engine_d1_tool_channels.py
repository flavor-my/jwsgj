from __future__ import annotations

import ast
import hashlib
import json
import logging
import math
import os
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import Any, NamedTuple

if __package__ in (None, ""):
    import sys as _sys
    _pkg_parent = os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))
    if _pkg_parent not in _sys.path:
        _sys.path.insert(0, _pkg_parent)
from jwsgj.diag_security_diagnoser import (
    DiagOptions,
    _sink_record_file,
    get_diagnoser,
    taint_traversal_exemption,
)
from jwsgj.diag_self_check import (
    ensure_tool,
    resolve_tool_path,
    run_tool_process,
)
from jwsgj.diag_shared_ast_nodes import (
    attr_chain_key,
    call_tail_name,
    is_none_literal,
    iter_arg_defaults,
    iter_arg_nodes,
)
from jwsgj.diag_shared_source_core import (
    assign_target_of,
    code_part,
    join_balanced_stmt,
    parse_cached,
    read_source,
    read_source_cached,
    src_lines,
)
from jwsgj.diag_shared_source_scan import (
    has_inline_suppression,
    line_has_applicable_nosec,
    line_has_taint_suppression,
)
from jwsgj.diag_taint_interproc import (
    check_vulnerability,
)
from jwsgj.diag_taint_model import BUILTIN_SINKS
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    SEVERITY_RANK,
    TAINT_SOURCE_CATEGORY_BY_NAME,
    normalize_filepath,
)
from jwsgj.fp_rules_judge import (
    _UNRESOLVED_FILE_MARKERS,
    TAINT_PATH_TRAVERSAL_RULES,
    apply_fp_downgrade,
    enhance_taint_with_confidence,
    equiv_dedup_key,
    fp_rule_registered,
    get_fp_rule_ids,
    is_static_fp_rule,
    is_test_scoped_fp_rule,
    map_bandit_severity,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import subprocess_noartifact_env
from jwsgj.runtime_scope import (
    adaptive_workers,
    coerce_skill_dir,
    collect_scan_py_files,
    is_scan_scope_path,
    is_test_file_path,
    safe_relpath,
)

__all__ = [
    "DEFAULT_INCLUDE_TESTS",
    "BanditRunner",
    "RuffRunner",
    "VulnerabilityScanner",
    "as_int",
    "elapsed_ms",
    "generate_source_exploit_report",
    "normalize_abs_path",
    "postprocess_findings",
    "quick_vulnerability_check",
    "release_bandit_fp_caches",
    "release_ruff_fp_caches",
    "resolve_scan_targets",
    "security_scan_plan",
]
logger = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
DEFAULT_INCLUDE_TESTS = False
_VULN_CONFIDENCE_DEFAULT = 0.70
_VULN_SCORE_MAX = 100.0
logger.info("engine_d1_tool_channels 已加载：%d 项导出", len(__all__))
def _abs_skill_root(skill_dir) -> str:
    root = coerce_skill_dir(skill_dir)
    return os.path.abspath(root) if root.strip() else ""
def _swallow(function_name: str, exc: BaseException) -> None:
    log_swallowed(__name__, exc,
                  context=f"{function_name}:{type(exc).__name__}")
def normalize_abs_path(filename: str, abs_skill_dir: str) -> str:
    if not isinstance(filename, str) or not filename:
        return ""
    path = (filename if os.path.isabs(filename) else os.path.join(
        abs_skill_dir, filename.replace("/", os.sep).replace("\\", os.sep)))
    return os.path.abspath(path)
def _chunk_files(py_files: list[str], budget: int = 8000) -> list[list[str]]:
    if not py_files:
        return []
    chunks: list[list[str]] = []
    cur: list[str] = []
    cur_len = 0
    for pf in py_files:
        if cur and cur_len + len(pf) + 3 > budget:
            chunks.append(cur)
            cur, cur_len = [], 0
        cur.append(pf)
        cur_len += len(pf) + 3
    if cur:
        chunks.append(cur)
    return chunks
def as_int(v) -> int:
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, int):
        return v
    if v is None or (isinstance(v, str) and not v.strip()):
        return 0
    try:
        f = float(v)
    except (TypeError, ValueError, OverflowError) as _e:
        _swallow('as_int', _e)
        return 0
    return int(f) if math.isfinite(f) else 0
def elapsed_ms(start: float) -> float:
    return round((time.perf_counter() - start) * 1000, 1)
def _scan_result_skeleton(tool: str) -> dict:
    return {
        "findings": [], "findings_count": 0,
        "status": "pass", "summary": "",
        "elapsed_ms": 0, "tool": tool, "tool_version": "",
        "rules_checked": [], "files_scanned": 0,
    }
def _tool_gate_blocked(tool: str, result: dict, start: float) -> bool:
    ensure = ensure_tool(tool)
    if ensure["status"] == "error":
        _fill_channel_error(result, start,
                            f"{tool} 不可用（自动安装失败）: {ensure.get('error', '')}")
        logger.error("[%s] %s", tool.capitalize(), result["summary"])
        return True
    result["tool_version"] = ensure.get("version", "").split("\n")[0]
    return False
def _scan_target_paths(py_files) -> list[str] | None:
    if py_files is None:
        return None
    if isinstance(py_files, (str, bytes, os.PathLike)):
        items = [py_files]
    else:
        try:
            items = list(py_files)
        except TypeError as _e:
            _swallow("_scan_target_paths", _e)
            return []
    paths: list[str] = []
    for item in items:
        try:
            paths.append(os.fsdecode(item))
        except TypeError as _e:
            _swallow("_scan_target_paths", _e)
    return paths
def resolve_scan_targets(py_files, skill_dir: str,
                          include_tests: bool) -> list[str]:
    abs_skill_dir = _abs_skill_root(skill_dir)
    if not abs_skill_dir:
        return []
    files = _scan_target_paths(py_files)
    if files is None:
        files = collect_scan_py_files(
            abs_skill_dir, include_tests=include_tests)
    resolved: dict[str, str] = {}
    for path in (normalize_abs_path(fp, abs_skill_dir) for fp in files):
        if not path:
            continue
        if not is_scan_scope_path(
                path, include_tests, root_dir=abs_skill_dir):
            continue
        resolved.setdefault(os.path.normcase(path), path)
    return list(resolved.values())
def security_scan_plan(skill_dir: str, include_tests: bool,
                       active_count: int) -> tuple[list[str], int]:
    if not _abs_skill_root(skill_dir):
        return [], adaptive_workers(active_count)
    py_files = collect_scan_py_files(
        skill_dir, include_tests=include_tests)
    workers = adaptive_workers(active_count)
    return py_files, workers
def _fill_channel_error(result: dict, start: float, summary: str) -> dict:
    result["status"] = "error"
    result["summary"] = summary
    result["elapsed_ms"] = elapsed_ms(start)
    return result
class _SiteSpec(NamedTuple):
    channel: str
    id_key: str
    default_id: str
    line_key: str
    col_key: str
    group_key: str = ""
_BANDIT_SITE_SPEC = _SiteSpec(
    "Bandit", "test_id", "UNKNOWN", "line_number", "col_offset")
_RUFF_SITE_SPEC = _SiteSpec(
    "Ruff", "code", "unknown", "row", "column", "location")
class _FindingSite(NamedTuple):
    rule_id: str
    abs_path: str
    rel_path: str
    line: int
    col: int
    col_known: bool
def _finding_site(entry: Any, abs_skill_dir: str,
                  spec: _SiteSpec) -> _FindingSite | None:
    if not isinstance(entry, dict):
        logger.debug("[%s] 跳过非 dict finding 元素: %r",
                     spec.channel, type(entry).__name__)
        return None
    group = _entry_group(entry, spec)
    raw_col = group.get(spec.col_key)
    abs_path, rel_path = _site_paths(entry, abs_skill_dir)
    return _FindingSite(
        rule_id=str(entry.get(spec.id_key) or spec.default_id),
        abs_path=abs_path,
        rel_path=rel_path,
        line=as_int(group.get(spec.line_key)),
        col=as_int(raw_col),
        col_known=raw_col is not None,
    )
def _entry_group(entry: dict, spec: _SiteSpec) -> dict:
    if not spec.group_key:
        return entry
    group = entry.get(spec.group_key)
    return group if isinstance(group, dict) else {}
def _site_paths(entry: dict, abs_skill_dir: str) -> tuple[str, str]:
    abs_path = normalize_abs_path(entry.get("filename") or "", abs_skill_dir)
    rel_path = (safe_relpath(abs_path, abs_skill_dir, normalize=False)
                if abs_path else "")
    return abs_path, rel_path
def _make_bandit_finding(bf: dict, site: _FindingSite) -> dict:
    issue_text = str(bf.get("issue_text") or "")
    severity = str(bf.get("issue_severity") or "MEDIUM")
    confidence = str(bf.get("issue_confidence") or "MEDIUM")
    return {
        "rule_id": site.rule_id,
        "severity": map_bandit_severity(severity),
        "confidence": _map_bandit_confidence(confidence),
        "message": issue_text,
        "file": site.rel_path,
        "line": site.line,
        "col": site.col,
        "source": "E1-bandit",
        "fix_suggestion": issue_text,
        "family": "danger_pattern",
        "test_id": site.rule_id,
    }
def _convert_bandit_findings(raw_findings: list[dict],
                             abs_skill_dir: str
                             ) -> tuple[list[dict], list[str], int, int]:
    findings: list[dict] = []
    rules_seen: set[str] = set()
    skipped_b101 = 0
    skipped_fp = 0
    for bf in raw_findings:
        site = _finding_site(bf, abs_skill_dir, _BANDIT_SITE_SPEC)
        if site is None:
            continue
        rules_seen.add(site.rule_id)
        is_test_file = is_test_file_path(site.rel_path)
        skip_tag = bandit_finding_fp(
            site.rule_id, site.abs_path, site.line,
            site.col if site.col_known else None, is_test_file)
        if skip_tag == "b101":
            skipped_b101 += 1
            continue
        if skip_tag == "fp":
            skipped_fp += 1
            continue
        findings.append(_make_bandit_finding(bf, site))
    return findings, sorted(rules_seen), skipped_b101, skipped_fp
_BANDIT_CONFIDENCE_MAP: dict[str, float] = {
    "HIGH": 0.90, "MEDIUM": 0.70, "LOW": 0.50}
_BANDIT_CONFIDENCE_DEFAULT = 0.50
def _map_bandit_confidence(confidence: str) -> float:
    return _BANDIT_CONFIDENCE_MAP.get(str(confidence or "").upper(),
                                      _BANDIT_CONFIDENCE_DEFAULT)
def _loads_tool_json(stdout: str, who: str) -> tuple[str | None, Any]:
    try:
        return None, json.loads(stdout)
    except (json.JSONDecodeError, RecursionError) as e:
        log_swallowed(__name__, e, context=f"{who}:{type(e).__name__}")
        return (f"JSON parse error: {e}", None)
def _bandit_incomplete_reason(scan_errors: list) -> str:
    first = scan_errors[0]
    reason = (str(first.get("reason") or first.get("filename") or first)
              if isinstance(first, dict) else str(first))
    return (f"bandit scan incomplete: {len(scan_errors)} file(s) "
            f"not covered, e.g. {reason[:140]}")
def _parse_bandit_stdout(stdout: str) -> tuple[str | None, list]:
    if not stdout.strip():
        return ("bandit error: empty JSON output", [])
    err, data = _loads_tool_json(stdout, "_parse_bandit_stdout")
    if err:
        return (err, [])
    if not isinstance(data, dict):
        return (f"bandit error: unexpected JSON shape {type(data).__name__}", [])
    return _bandit_results(data)
def _bandit_results(data: dict) -> tuple[str | None, list]:
    scan_errors = data.get("errors")
    if scan_errors is not None and not isinstance(scan_errors, list):
        shape = type(scan_errors).__name__
        return f"bandit error: unexpected errors shape {shape}", []
    results = data.get("results")
    if not isinstance(results, list):
        return (f"bandit error: unexpected results shape {type(results).__name__}", [])
    for index, item in enumerate(results):
        if not isinstance(item, dict):
            return ((f"bandit error: unexpected results[{index}] shape "
                     f"{type(item).__name__}"), [])
    if scan_errors:
        return (_bandit_incomplete_reason(scan_errors), results)
    return (None, results)
def _collect_raw_findings(run_chunk, chunks: list[list[str]],
                          parallel: bool) -> tuple[str | None, list]:
    raw: list = []
    first_err: str | None = None
    if not parallel:
        for chunk in chunks:
            err, res = run_chunk(chunk)
            if err and first_err is None:
                first_err = err
            raw.extend(res or [])
        return first_err, raw
    with ThreadPoolExecutor(max_workers=adaptive_workers(len(chunks))) as ex:
        for err, res in ex.map(run_chunk, chunks):
            if err and first_err is None:
                first_err = err
            raw.extend(res or [])
    return first_err, raw
def _tool_exit_error(tool: str, proc) -> str | None:
    if proc.returncode in (0, 1):
        return None
    return f"{tool} error: exit {proc.returncode}: {(proc.stderr or '')[:200]}"
_CHANNEL_TIMEOUT_SECONDS = 120
class _ToolChannelRunner:
    tool: str = ""
    label: str = ""
    parallel: bool = False
    def __init__(self, skill_dir: str,
                 include_tests: bool = DEFAULT_INCLUDE_TESTS):
        self.skill_dir = _abs_skill_root(skill_dir)
        self._include_tests = include_tests
    def _run_chunk(self, chunk: list[str]):
        raise NotImplementedError
    def _convert(self, raw_findings: list) -> tuple[list[dict], list[str], dict]:
        raise NotImplementedError
    def _summary(self, n_findings: int, n_files: int, n_rules: int,
                 _details: dict) -> str:
        raise NotImplementedError
    def run(self, py_files: list[str] | None = None) -> dict:
        start = time.perf_counter()
        result: dict[str, Any] = _scan_result_skeleton(self.tool)
        explicit_files = py_files is not None
        py_files = resolve_scan_targets(
            py_files, self.skill_dir, self._include_tests)
        if not py_files:
            summary = ("no scannable Python files in explicit targets"
                       if explicit_files else "no Python files found")
            logger.warning("[%s] %s (include_tests=%s)",
                           self.label, summary, self._include_tests)
            return _fill_channel_error(result, start, summary)
        if _tool_gate_blocked(self.tool, result, start):
            return result
        try:
            err, raw_findings = _collect_raw_findings(
                self._run_chunk, _chunk_files(py_files), self.parallel)
            findings, rules_seen, details = self._convert(raw_findings)
            result["findings"] = findings
            result["findings_count"] = len(findings)
            result["rules_checked"] = rules_seen
            if err:
                logger.error("[%s] %s", self.label, err)
                return _fill_channel_error(result, start, err)
            result["files_scanned"] = len(py_files)
            result["summary"] = self._summary(
                len(findings), len(py_files), len(rules_seen), details)
            result["elapsed_ms"] = elapsed_ms(start)
            logger.info(
                "[%s] %s", self.label, result["summary"],
                extra={"event": "e1_scan_done",
                       "duration_ms": result["elapsed_ms"]})
        except subprocess.TimeoutExpired:
            logger.warning("[%s] 通道超时(%ss)，本次扫描中断",
                           self.label, _CHANNEL_TIMEOUT_SECONDS)
            _fill_channel_error(
                result, start,
                f"{self.tool} timeout ({_CHANNEL_TIMEOUT_SECONDS}s)")
        except Exception as e:
            _fill_channel_error(result, start,
                                f"unexpected error: {type(e).__name__}: {e}")
            logger.warning("[%s] 通道意外异常: %s: %s", self.label,
                           type(e).__name__, e, exc_info=True)
        return result
class BanditRunner(_ToolChannelRunner):
    tool = "bandit"
    label = "Bandit"
    parallel = True
    def _run_chunk(self, _chunk: list[str]):
        proc = run_tool_process(
            [resolve_tool_path("bandit") or "bandit", "-f", "json", "-q", "-r"] + _chunk,
            cwd=self.skill_dir, timeout=_CHANNEL_TIMEOUT_SECONDS)
        err = _tool_exit_error("bandit", proc)
        if err is not None:
            return (err, [])
        return _parse_bandit_stdout(proc.stdout)
    def _convert(self, raw_findings: list) -> tuple[list[dict], list[str], dict]:
        findings, rules_seen, skipped_b101, skipped_fp = _convert_bandit_findings(
            raw_findings, self.skill_dir)
        return findings, rules_seen, {
            "skipped_b101": skipped_b101, "skipped_fp": skipped_fp}
    def _summary(self, n_findings: int, n_files: int, n_rules: int,
                 details: dict) -> str:
        return (f"bandit: {n_findings} findings in {n_files} files "
                f"({n_rules} rules, {details['skipped_b101']} B101 skipped, "
                f"{details['skipped_fp']} FP skipped)")
_RUFF_SECURITY_PREFIX_RE = re.compile(r"^(?:S|B|F|E|A|G|PLW|PLE)\d")
_DEFAULT_RUFF_FAMILY = "code_smell"
RUFF_FAMILY_MAP: dict[str, str] = {
    "F401": "unused_import",
    "F402": "shadowing_builtin",
    "F811": "dead_code",
    "F841": "dead_code",
    "F821": "undefined_name",
    "F822": "undefined_name",
    "F823": "undefined_name",
}
_RUFF_EXACT_SEVERITY: dict[str, str] = {
    "S110": "P2", "S112": "P2",
    "S602": "P0", "S605": "P0",
    "S603": "P2", "S604": "P2", "S606": "P2", "S607": "P2", "S609": "P2",
    "S608": "P1",
}
_RUFF_PREFIX_SEVERITY: tuple[tuple[tuple[str, ...], str], ...] = (
    (("B3", "B4", "B5"), "P1"),
    (("B6", "B7"), "P2"),
    (("SIM", "UP", "PIE", "C", "I", "N", "D", "T", "PERF", "NPY",
      "ASYNC", "RUF"), "P3"),
    (("F", "E", "W"), "P2"),
    (("S", "A", "R"), "P1"),
)
_RUFF_DEFAULT_SEVERITY = "P2"
def _map_ruff_severity(code: str) -> str:
    exact = _RUFF_EXACT_SEVERITY.get(code)
    if exact is not None:
        return exact
    for prefixes, severity in _RUFF_PREFIX_SEVERITY:
        if code.startswith(prefixes):
            return severity
    return _RUFF_DEFAULT_SEVERITY
def _ruff_fix_text(fix: Any) -> str:
    if not fix:
        return ""
    if isinstance(fix, str):
        return fix
    if isinstance(fix, dict):
        return str(fix.get("message") or "")
    return json.dumps(fix, ensure_ascii=False, default=str)
def _ruff_skip_reason(code: str, abs_path: str, row: int, column: int,
                      fp_rule_ids: set[str], include_tests: bool,
                      skill_dir: str) -> bool:
    if not _RUFF_SECURITY_PREFIX_RE.match(code):
        return True
    if not is_scan_scope_path(abs_path, include_tests, root_dir=skill_dir):
        return True
    if ruff_finding_fp(code, abs_path, row, column):
        return True
    return bool(code in fp_rule_ids
                or is_static_fp_rule(code, file_path=abs_path))
def _make_ruff_finding(rf: dict, site: _FindingSite) -> dict:
    sev = apply_fp_downgrade(
        site.rule_id, _map_ruff_severity(site.rule_id),
        file_path=site.abs_path)
    return {
        "rule_id": site.rule_id,
        "severity": sev,
        "confidence": 0.85,
        "message": str(rf.get("message") or ""),
        "file": site.rel_path,
        "line": site.line,
        "col": site.col,
        "source": "E1-ruff",
        "fix_suggestion": _ruff_fix_text(rf.get("fix")),
        "family": RUFF_FAMILY_MAP.get(site.rule_id, _DEFAULT_RUFF_FAMILY),
    }
def _load_fp_rule_ids(abs_skill_dir: str) -> set[str]:
    try:
        return get_fp_rule_ids(abs_skill_dir)
    except Exception as e:  # noqa: BLE001
        logger.warning("加载FP规则库失败(非阻断，仅静态规则生效): %s", e)
        return set()
def _convert_ruff_findings(raw_findings: list[dict], abs_skill_dir: str,
                           include_tests: bool) -> tuple[list[dict], list[str]]:
    findings: list[dict] = []
    rules_seen: set[str] = set()
    fp_rule_ids = _load_fp_rule_ids(abs_skill_dir)
    for rf in raw_findings:
        site = _finding_site(rf, abs_skill_dir, _RUFF_SITE_SPEC)
        if site is None:
            continue
        rules_seen.add(site.rule_id)
        if _ruff_skip_reason(site.rule_id, site.abs_path, site.line, site.col,
                             fp_rule_ids, include_tests, abs_skill_dir):
            continue
        findings.append(_make_ruff_finding(rf, site))
    return findings, sorted(rules_seen)
def _parse_ruff_stdout(stdout: str) -> tuple[str | None, list | None]:
    if not stdout.strip():
        return ("ruff error: empty JSON output", None)
    err, data = _loads_tool_json(stdout, "_parse_ruff_stdout")
    if err:
        return (err, None)
    if not isinstance(data, list):
        return (f"ruff error: unexpected JSON shape {type(data).__name__}", None)
    for index, item in enumerate(data):
        if not isinstance(item, dict):
            return ((f"ruff error: unexpected finding[{index}] shape "
                     f"{type(item).__name__}"), None)
    return (None, data)
_RUFF_CHANNEL_SELECT = "F"
class RuffRunner(_ToolChannelRunner):
    tool = "ruff"
    label = "Ruff"
    def _run_chunk(self, _chunk: list[str]):
        ruff_env = dict(subprocess_noartifact_env())
        ruff_env.setdefault(
            "RAYON_NUM_THREADS", str(min(4, os.cpu_count() or 1)))
        proc = run_tool_process(
            [resolve_tool_path("ruff") or "ruff", "check", "--no-cache",
             "--output-format", "json", "--no-fix",
             "--select", _RUFF_CHANNEL_SELECT] + _chunk,
            env=ruff_env, cwd=self.skill_dir,
            timeout=_CHANNEL_TIMEOUT_SECONDS)
        err = _tool_exit_error("ruff", proc)
        if err is not None:
            return (err, None)
        return _parse_ruff_stdout(proc.stdout)
    def _convert(self, raw_findings: list) -> tuple[list[dict], list[str], dict]:
        findings, rules_seen = _convert_ruff_findings(
            raw_findings, self.skill_dir, include_tests=self._include_tests)
        return findings, rules_seen, {}
    def _summary(self, n_findings: int, n_files: int, n_rules: int,
                 _details: dict) -> str:
        return (f"ruff: {n_findings} findings in {n_files} files "
                f"({n_rules} rules)")
def _single_none_comparison(node: ast.AST, op_type: type) -> bool:
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 1 or len(node.comparators) != 1:
        return False
    if not isinstance(node.ops[0], op_type):
        return False
    return (is_none_literal(node.left)
            != is_none_literal(node.comparators[0]))
def _none_comparison_name(node: ast.AST, op_type: type) -> str | None:
    if not _single_none_comparison(node, op_type):
        return None
    other = node.comparators[0] if is_none_literal(node.left) else node.left
    return attr_chain_key(other)
def _find_b101_assert(tree: ast.AST, lineno: int,
                      col: int | None = None) -> ast.Assert | None:
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Assert) and node.lineno == lineno
                and (col is None or node.col_offset == col)
                and _none_comparison_name(node.test, ast.IsNot) is not None):
            return node
    return None
def _find_b101_target(tree: ast.AST, lineno: int,
                      col: int | None = None) -> str | None:
    node = _find_b101_assert(tree, lineno, col)
    return (_none_comparison_name(node.test, ast.IsNot)
            if node is not None else None)
def _direct_stmt_exits(stmt: ast.stmt) -> bool:
    if isinstance(stmt, (ast.Raise, ast.Return)):
        return True
    return (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Attribute)
            and stmt.value.func.attr == "exit"
            and isinstance(stmt.value.func.value, ast.Name)
            and stmt.value.func.value.id == "sys")
def _definitely_non_none_value(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return node.value is not None
    return isinstance(node, (
        ast.List, ast.Tuple, ast.Set, ast.Dict,
        ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
        ast.JoinedStr, ast.Lambda,
    ))
def _stmt_rebinds_target(stmt: ast.stmt, target: str) -> bool:
    if isinstance(stmt, ast.Assign):
        targets, value = stmt.targets, stmt.value
    elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        targets, value = [stmt.target], stmt.value
    else:
        return False
    return (_definitely_non_none_value(value)
            and any(attr_chain_key(candidate) == target
                    for candidate in targets))
def _binding_overwrites_target(bound: str | None, target: str) -> bool:
    return bool(bound) and (
        bound == target or target.startswith(bound + "."))
def _stmt_may_rebind_target(stmt: ast.stmt, target: str) -> bool:
    pending: list[ast.AST] = [stmt]
    while pending:
        node = pending.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if _binding_overwrites_target(node.name, target):
                return True
            pending.extend(node.decorator_list)
            pending.extend(
                decorator.body for decorator in node.decorator_list
                if isinstance(decorator, ast.Lambda))
            if isinstance(node, ast.ClassDef):
                pending.extend(node.bases)
                pending.extend(keyword.value for keyword in node.keywords)
            else:
                pending.extend(iter_arg_defaults(node.args))
                pending.extend(
                    arg.annotation for arg in iter_arg_nodes(node.args)
                    if arg.annotation is not None)
                if node.returns is not None:
                    pending.append(node.returns)
            continue
        if isinstance(node, ast.Lambda):
            pending.extend(iter_arg_defaults(node.args))
            continue
        if isinstance(node, ast.comprehension):
            pending.append(node.iter)
            pending.extend(node.ifs)
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            pending.append(node.annotation)
            continue
        if (isinstance(node, (ast.Name, ast.Attribute, ast.Subscript))
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and _binding_overwrites_target(attr_chain_key(node), target)):
            return True
        if (isinstance(node, ast.ExceptHandler)
                and _binding_overwrites_target(node.name, target)):
            return True
        if (isinstance(node, (ast.MatchAs, ast.MatchStar))
                and _binding_overwrites_target(node.name, target)):
            return True
        if (isinstance(node, ast.MatchMapping)
                and _binding_overwrites_target(node.rest, target)):
            return True
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                bound = (alias.asname or alias.name.partition('.')[0]
                         if isinstance(node, ast.Import)
                         else alias.asname or alias.name)
                if _binding_overwrites_target(bound, target):
                    return True
            continue
        pending.extend(ast.iter_child_nodes(node))
    return False
def _branch_exits_or_rebinds_non_none(body: list[ast.stmt],
                                      target: str) -> bool:
    if any(_direct_stmt_exits(stmt) for stmt in body):
        return True
    last_binding = next(
        (stmt for stmt in reversed(body)
         if _stmt_may_rebind_target(stmt, target)), None)
    return (last_binding is not None
            and _stmt_rebinds_target(last_binding, target))
def _none_guard_narrows(node: ast.If, target: str, *,
                        check_alternative: bool = True) -> bool:
    if not _branch_exits_or_rebinds_non_none(node.body, target):
        return False
    return not (check_alternative and any(
        _stmt_undoes_non_none_narrowing(stmt, target)
        for stmt in node.orelse))
def _leading_if_branches_narrow(root: ast.If, guard: ast.If,
                                target: str) -> bool:
    current = root
    while current is not guard:
        if not _branch_exits_or_rebinds_non_none(current.body, target):
            return False
        if (len(current.orelse) != 1
                or not isinstance(current.orelse[0], ast.If)):
            return False
        current = current.orelse[0]
    return True
def _statement_context(tree: ast.AST) -> tuple[dict, dict]:
    parents: dict = {}
    locations: dict = {}
    for parent in walk_nodes(tree):
        for field, value in ast.iter_fields(parent):
            if isinstance(value, ast.AST):
                parents[value] = parent
                continue
            if not isinstance(value, list):
                continue
            for item in value:
                if isinstance(item, ast.AST):
                    parents[item] = parent
            if value and all(isinstance(item, ast.stmt) for item in value):
                for index, stmt in enumerate(value):
                    locations[stmt] = (parent, field, index)
    return parents, locations
def _if_chain_root(node: ast.If, locations: dict) -> ast.If:
    root = node
    while True:
        location = locations.get(root)
        if location is None:
            return root
        parent, field, _index = location
        if not (isinstance(parent, ast.If) and field == "orelse"
                and len(parent.orelse) == 1
                and parent.col_offset == root.col_offset):
            return root
        root = parent
def _stmt_undoes_non_none_narrowing(stmt: ast.stmt, target: str) -> bool:
    return (_stmt_may_rebind_target(stmt, target)
            and not _stmt_rebinds_target(stmt, target))
def _preceding_stmts_undo_narrowing(location: tuple, target: str,
                                    start: int = 0) -> bool:
    parent, field, stop = location
    statements = getattr(parent, field, ())
    return any(_stmt_undoes_non_none_narrowing(stmt, target)
               for stmt in statements[start:stop])
def _nested_scope_rebinds_or_shadows(scope: ast.AST, target: str) -> bool:
    if any(_binding_overwrites_target(arg.arg, target)
           for arg in iter_arg_nodes(scope.args)):
        return True
    pending: list[ast.AST] = list(scope.body)
    while pending:
        node = pending.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        if (isinstance(node, ast.Global)
                and any(_binding_overwrites_target(name, target)
                        for name in node.names)):
            return True
        if (isinstance(node, ast.stmt)
                and _stmt_may_rebind_target(node, target)):
            return True
        pending.extend(ast.iter_child_nodes(node))
    return False
def _lexical_function_or_class(node, parents):
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            return current
    return None
def _outer_scope_undoes_guard_after(scope, guard, target, parents):
    guard_nodes = {id(item) for item in walk_nodes(guard)}
    for node in walk_nodes(scope):
        if not isinstance(node, ast.stmt) or node is scope or id(node) in guard_nodes:
            continue
        if getattr(node, 'lineno', 0) <= guard.lineno:
            continue
        if _lexical_function_or_class(node, parents) is not scope:
            continue
        if _stmt_undoes_non_none_narrowing(node, target):
            return True
    return False
def _guard_dominates_assert(guard: ast.If, assertion: ast.Assert,
                            guard_scope, assert_scope,
                            parents: dict, locations: dict,
                            target: str = "") -> bool:
    if guard_scope is assert_scope:
        candidate: ast.AST = assertion
    elif guard_scope is not None and _scope_covers(guard_scope, assert_scope):
        if target and _nested_scope_rebinds_or_shadows(assert_scope, target):
            return False
        if target and _outer_scope_undoes_guard_after(
                guard_scope, guard, target, parents):
            return False
        candidate = assertion
        while candidate in parents and parents[candidate] is not guard_scope:
            candidate = parents[candidate]
        if parents.get(candidate) is not guard_scope:
            return False
    else:
        return False
    root = _if_chain_root(guard, locations)
    guard_location = locations.get(root)
    if guard_location is None:
        return False
    guard_parent, guard_field, guard_index = guard_location
    while candidate is not root:
        location = locations.get(candidate)
        if (location is not None and location[0] is guard
                and location[1] == "orelse"):
            return not (target and _preceding_stmts_undo_narrowing(
                location, target))
        if (location is not None and location[0] is guard_parent
                and location[1] == guard_field):
            if location[2] <= guard_index:
                return False
            if (root is not guard and not _leading_if_branches_narrow(
                    root, guard, target)):
                return False
            return not (target and _preceding_stmts_undo_narrowing(
                location, target, start=guard_index + 1))
        if (target and location is not None
                and _preceding_stmts_undo_narrowing(location, target)):
            return False
        parent = parents.get(candidate)
        if parent is None:
            return False
        candidate = parent
    return False
def _assertion_in_else_branch(guard: ast.If, assertion: ast.Assert,
                               locations: dict) -> bool:
    candidate: ast.AST = assertion
    while candidate is not guard:
        location = locations.get(candidate)
        if location is None:
            return False
        parent, field, _index = location
        if parent is guard:
            return field == "orelse"
        candidate = parent
    return False
def _has_none_guard(tree: ast.AST, target: str, lineno: int,
                   col: int | None = None) -> bool:
    assertion = _find_b101_assert(tree, lineno, col)
    if assertion is None:
        return False
    assert_scope = _enclosing_function(tree, lineno)
    parents, locations = _statement_context(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        if not (lineno - 6 <= node.lineno < lineno):
            continue
        if _none_comparison_name(node.test, ast.Is) != target:
            continue
        in_else = _assertion_in_else_branch(node, assertion, locations)
        if not (in_else
                or _none_guard_narrows(
                    node, target, check_alternative=not in_else)):
            continue
        guard_scope = _enclosing_function(tree, node.lineno)
        if _guard_dominates_assert(node, assertion, guard_scope, assert_scope,
                                   parents, locations, target=target):
            return True
    return False
def _b101_type_narrowing_fp(filepath: str, lineno: int,
                             col: int | None = None) -> bool:
    if lineno <= 0:
        return False
    tree = _ast_tree_cached(os.path.abspath(filepath))
    if tree is None:
        return False
    target = _find_b101_target(tree, lineno, col)
    if target is None:
        return False
    return _has_none_guard(tree, target, lineno, col)
_B1X_AST_CACHE_MAX = 256
_FpCacheKey = tuple[int, int, bytes | None]
_B1X_AST_CACHE: dict[str, tuple[_FpCacheKey, ast.AST | None]] = {}
def _fp_key(abs_path: str, who: str, source: str | None):
    try:
        st = os.stat(abs_path)
    except OSError as _e:
        _swallow(who, _e)
        return None
    digest = (None if source is None else hashlib.sha256(
        source.encode("utf-8", errors="surrogatepass")).digest())
    return (st.st_mtime_ns, st.st_size, digest)
def _fp_cache_get(abs_path: str, cache: dict, cache_max: int,
                  who: str, build=None):
    source = read_source(abs_path)
    fp_key = _fp_key(abs_path, who, source)
    if fp_key is None:
        return None
    hit = cache.get(abs_path)
    if hit is not None and hit[0] == fp_key:
        return hit[1]
    payload = _build_payload(source, build, who)
    _store_payload(cache, abs_path, fp_key, payload, cache_max)
    return payload
def _build_payload(source: str | None, build, who: str) -> ast.AST | None:
    if source is None:
        return None
    try:
        tree = ast.parse(source)
    except Exception as _e:  # noqa: BLE001
        _swallow(who, _e)
        return None
    return tree if build is None else build(tree)
def _store_payload(cache: dict, abs_path: str, fp_key, payload,
                   cache_max: int) -> None:
    if len(cache) >= cache_max:
        cache.clear()
    cache[abs_path] = (fp_key, payload)
def _ast_tree_cached(abs_path: str) -> ast.AST | None:
    return _fp_cache_get(abs_path, _B1X_AST_CACHE, _B1X_AST_CACHE_MAX,
                         '_ast_tree_cached')
_B101_TEST_FN_RE = re.compile(
    r"_*self_?test(?:_[a-z0-9_]+)?", re.IGNORECASE)
def _b101_test_semantic_fp(filepath: str, lineno: int) -> bool:
    if lineno <= 0:
        return False
    tree = _ast_tree_cached(os.path.abspath(filepath))
    if tree is None:
        return False
    innermost = _enclosing_function(tree, lineno)
    if innermost is None:
        return False
    return bool(_B101_TEST_FN_RE.fullmatch(innermost.name))
def _node_end_lineno(node: ast.AST) -> int:
    return getattr(node, "end_lineno", None) or node.lineno
def _enclosing_function(tree: ast.AST, lineno: int):
    enclosing = [
        node for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.lineno <= lineno <= _node_end_lineno(node)
    ]
    if not enclosing:
        return None
    return max(enclosing, key=lambda fn: fn.lineno)
def _scope_covers(outer, inner) -> bool:
    if outer is None or inner is None:
        return outer is inner
    if outer is inner:
        return True
    return (outer.lineno <= inner.lineno
            and _node_end_lineno(inner) <= _node_end_lineno(outer))
_B607_AST_CACHE: dict[str, tuple[_FpCacheKey, dict[int, bool] | None]] = {}
_B607_AST_CACHE_MAX = 64
def _b607_cmd_first_is_literal(arg: ast.expr) -> bool | None:
    node = arg
    while isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        node = node.left
    if not isinstance(node, (ast.List, ast.Tuple)):
        return None
    if not node.elts:
        return False
    first = node.elts[0]
    return isinstance(first, ast.Constant) and isinstance(first.value, str)
_B607_PROCESS_CALL_NAMES = frozenset({
    "Popen", "call", "check_call", "check_output", "run", "getoutput",
    "getstatusoutput", "system", "popen", "startfile",
})
def _b607_is_process_call(node: ast.Call) -> bool:
    return call_tail_name(node) in _B607_PROCESS_CALL_NAMES
def _b607_collect_verdicts(tree: ast.AST) -> dict[int, bool]:
    verdicts: dict[int, bool] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call) or not node.args:
            continue
        if not _b607_is_process_call(node):
            continue
        lit = _b607_cmd_first_is_literal(node.args[0])
        verdicts[node.lineno] = verdicts.get(node.lineno, True) and bool(lit)
    return verdicts
def _b607_test_fixture(filepath: str, lineno: int) -> bool:
    if lineno <= 0:
        return False
    verdicts = _fp_cache_get(
        os.path.abspath(filepath), _B607_AST_CACHE, _B607_AST_CACHE_MAX,
        '_b607_test_fixture', _b607_collect_verdicts)
    if not verdicts:
        return False
    return verdicts.get(lineno, False)
_B102_TAINT_SOURCE_RE = re.compile(
    r"\binput\s*\(|request\.|sys\.stdin|os\.environ|environ\[|\bargv\b|"
    r"urlopen|urllib|requests\.|socket\.|subprocess|\beval\s*\("
)
def _is_exec_call_at(node: ast.AST, lineno: int) -> bool:
    return (isinstance(node, ast.Call) and node.lineno == lineno
            and isinstance(node.func, ast.Name) and node.func.id == "exec")
def _exec_source_node(node: ast.Call) -> ast.AST | None:
    source = node.args[0] if node.args else None
    if source is None:
        source = next(
            (kw.value for kw in node.keywords if kw.arg == "source"), None)
    return source
def _b102_exec_source_is_literal(tree: ast.AST, lineno: int) -> bool:
    seen = False
    for node in walk_nodes(tree):
        if not _is_exec_call_at(node, lineno):
            continue
        seen = True
        source = _exec_source_node(node)
        if not (isinstance(source, ast.Constant)
                and isinstance(source.value, str)):
            return False
    return seen
def _b102_test_fixture(filepath: str, lineno: int) -> bool:
    lines = src_lines(filepath)
    if not lines or not (1 <= lineno <= len(lines)):
        return False
    line = code_part(lines[lineno - 1])
    if not re.search(r"\bexec\s*\(", line):
        return False
    tree = _ast_tree_cached(os.path.abspath(filepath))
    if tree is None:
        return False
    if not _b102_exec_source_is_literal(tree, lineno):
        return False
    return not _B102_TAINT_SOURCE_RE.search(_taint_window(lines, lineno))
def _taint_window(lines: list[str], lineno: int) -> str:
    return "\n".join(
        code_part(l) for l in lines[max(0, lineno - 11):lineno + 4])
_B108_AST_CACHE: dict[str, tuple[
    _FpCacheKey, set[tuple[int, int, int, int]] | None]] = {}
_B108_AST_CACHE_MAX = 64
_CONTAINER_CTOR_NAMES = frozenset({
    "set", "frozenset", "list", "tuple", "dict"})
_PURE_LITERAL_MAX_DEPTH = 12
def _is_pure_literal_container(node: ast.AST, _depth: int = 0) -> bool:
    if _depth > _PURE_LITERAL_MAX_DEPTH:
        return False
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return all(_is_pure_literal_container(e, _depth + 1)
                   for e in node.elts)
    if isinstance(node, ast.Dict):
        return all(key is not None
                   and _is_pure_literal_container(key, _depth + 1)
                   and _is_pure_literal_container(value, _depth + 1)
                   for key, value in zip(node.keys, node.values, strict=True))
    return False
def _b108_collect_spans(tree: ast.AST) -> set[tuple[int, int, int, int]]:
    spans: set[tuple[int, int, int, int]] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            spans.update(_b108_arg_spans(node))
    return spans
def _b108_arg_spans(node: ast.Call) -> set[tuple[int, int, int, int]]:
    is_ctor = _is_container_ctor(node)
    spans = set()
    for arg in list(node.args) + [kw.value for kw in node.keywords]:
        if is_ctor and _is_pure_literal_container(arg):
            continue
        spans.add(_node_span(arg))
    return spans
def _is_container_ctor(node: ast.Call) -> bool:
    return (isinstance(node.func, ast.Name)
            and node.func.id in _CONTAINER_CTOR_NAMES)
def _b108_call_arg_spans(abs_path: str) -> set[tuple[int, int, int, int]] | None:
    return _fp_cache_get(abs_path, _B108_AST_CACHE, _B108_AST_CACHE_MAX,
                         '_b108_call_arg_spans', _b108_collect_spans)
def _node_span(node: ast.AST) -> tuple[int, int, int, int]:
    return (node.lineno, node.col_offset,
            _node_end_lineno(node), getattr(node, "end_col_offset", 0) or 0)
def _point_in_span(lineno: int, col: int | None,
                   span: tuple[int, int, int, int],
                   col_valid: bool) -> bool:
    if not col_valid:
        return span[0] <= lineno <= span[2]
    return (span[0], span[1]) <= (lineno, col) < (span[2], span[3])
def _in_call_arg_span(spans: list[tuple[int, int, int, int]],
                      lineno: int,
                      col: int | None,
                      col_valid: bool) -> bool:
    return any(_point_in_span(lineno, col, span, col_valid)
               for span in spans)
def _b108_is_non_call_position_fp(abs_path: str, lineno: int,
                                  col: int | None = None) -> bool:
    if lineno <= 0:
        return False
    spans = _b108_call_arg_spans(abs_path)
    if spans is None:
        return False
    return not _in_call_arg_span(spans, lineno, col,
                                 col is not None and col >= 0)
_B104_LOOPBACK_SIBLINGS = frozenset({
    "localhost", "127.0.0.1", "[::1]", "::1"})
def _container_has_loopback_sibling(node) -> bool:
    siblings = [e.value for e in node.elts
                if isinstance(e, ast.Constant)]
    return any(isinstance(v, str) and v in _B104_LOOPBACK_SIBLINGS
               for v in siblings)
def _b104_has_loopback_sibling(tree: ast.AST,
                                lineno: int,
                                col: int | None,
                                col_valid: bool) -> bool:
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Tuple, ast.List, ast.Set)):
            continue
        if not _point_in_span(lineno, col, _node_span(node), col_valid):
            continue
        if _container_has_loopback_sibling(node):
            return True
    return False
def _b104_is_non_bind_position_fp(abs_path: str, lineno: int,
                                  col: int | None = None) -> bool:
    if lineno <= 0:
        return False
    spans = _b108_call_arg_spans(abs_path)
    if spans is None:
        return False
    _col_valid = col is not None and col >= 0
    if _in_call_arg_span(spans, lineno, col, _col_valid):
        return False
    tree = _ast_tree_cached(abs_path)
    if tree is None:
        return False
    return _b104_has_loopback_sibling(tree, lineno, col, _col_valid)
_BANDIT_STRUCTURAL_FP_IDS = frozenset({"B603", "B404", "B403"})
_BANDIT_TEST_FILE_FP_IDS = frozenset({"B108", "B110", "B112", "B311"})
def _bandit_b101_skip(rule_id: str, abs_path: str, line: int,
                      is_test_file: bool, col: int | None = None) -> str | None:
    if rule_id != "B101":
        return None
    if is_test_file:
        return "b101"
    if _b101_type_narrowing_fp(abs_path, line, col):
        return "b101"
    if _b101_test_semantic_fp(abs_path, line):
        return "b101"
    return None
def _bandit_ast_position_skip(rule_id: str, abs_path: str, line: int,
                              col: int | None) -> bool:
    if rule_id == "B108" and _b108_is_non_call_position_fp(
            abs_path, line, col):
        return True
    return bool(rule_id == "B104" and _b104_is_non_bind_position_fp(
        abs_path, line, col))
def _bandit_test_fixture_skip(rule_id: str, abs_path: str, line: int,
                              is_test_file: bool) -> bool:
    if not is_test_file:
        return False
    if rule_id == "B607" and _b607_test_fixture(abs_path, line):
        return True
    return bool(rule_id == "B102" and _b102_test_fixture(abs_path, line))
def _bandit_rule_id_skip(rule_id: str, is_test_file: bool) -> bool:
    if is_test_file and rule_id in _BANDIT_TEST_FILE_FP_IDS:
        return True
    return rule_id in _BANDIT_STRUCTURAL_FP_IDS
def bandit_finding_fp(rule_id: str, abs_path: str, line: int,
                      col: int | None, is_test_file: bool) -> str | None:
    b101_tag = _bandit_b101_skip(
        rule_id, abs_path, line, is_test_file, col=col)
    if b101_tag is not None:
        return b101_tag
    if _bandit_rule_id_skip(rule_id, is_test_file):
        return "fp"
    if _bandit_ast_position_skip(rule_id, abs_path, line, col):
        return "fp"
    if has_inline_suppression(abs_path, line, rule_id):
        return "fp"
    if _bandit_test_fixture_skip(rule_id, abs_path, line, is_test_file):
        return "fp"
    return None
def ruff_finding_fp(code: str, abs_path: str, row: int, column: int) -> bool:
    return (_is_ruff_code_specific_fp(code, abs_path, row, column)
            or has_inline_suppression(abs_path, row, code))
_PLW1510_WINDOW = 6
def _mentions_returncode(expr: ast.AST, target: str) -> bool:
    return any(
        isinstance(node, ast.Attribute) and node.attr == "returncode"
        and attr_chain_key(node.value) == target
        for node in walk_nodes(expr))
def _branch_exits(body: list) -> bool:
    for stmt in body:
        if _direct_stmt_exits(stmt):
            return True
        if (isinstance(stmt, ast.If) and stmt.orelse
                and _branch_exits(stmt.body)
                and _branch_exits(stmt.orelse)):
            return True
    return False
def _node_proves_returncode_checked(node: ast.AST, target: str) -> bool:
    if isinstance(node, ast.Assert):
        return _mentions_returncode(node.test, target)
    if isinstance(node, ast.If):
        return (_mentions_returncode(node.test, target)
                and _branch_exits(node.body))
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        func = node.value.func
        return (isinstance(func, ast.Attribute)
                and func.attr == "check_returncode"
                and attr_chain_key(func.value) == target)
    return False
def _target_rebound_before_check(tree: ast.AST, target: str, call_lineno: int,
                                 check: ast.AST, call_scope,
                                 parents: dict) -> bool:
    check_pos = (check.lineno, getattr(check, "col_offset", 0))
    check_ancestors: set[ast.AST] = set()
    current: ast.AST | None = check
    while current is not None:
        check_ancestors.add(current)
        current = parents.get(current)
    for stmt in walk_nodes(tree):
        if not isinstance(stmt, ast.stmt) or stmt in check_ancestors:
            continue
        stmt_lineno = getattr(stmt, "lineno", None)
        if stmt_lineno is None or stmt_lineno <= call_lineno:
            continue
        if (stmt_lineno, getattr(stmt, "col_offset", 0)) >= check_pos:
            continue
        if _enclosing_function(tree, stmt_lineno) is not call_scope:
            continue
        if _stmt_may_rebind_target(stmt, target):
            return True
    return False
def _returncode_post_check(target: str, abs_path: str, lineno: int) -> bool:
    tree = _ast_tree_cached(abs_path)
    if tree is None:
        return False
    call_scope = _enclosing_function(tree, lineno)
    parents, _locations = _statement_context(tree)
    lo, hi = lineno + 1, lineno + _PLW1510_WINDOW
    for node in walk_nodes(tree):
        node_lineno = getattr(node, "lineno", None)
        if node_lineno is None or not lo <= node_lineno <= hi:
            continue
        if _enclosing_function(tree, node_lineno) is not call_scope:
            continue
        if not _node_proves_returncode_checked(node, target):
            continue
        if not _target_rebound_before_check(
                tree, target, lineno, node, call_scope, parents):
            return True
    return False
def _plw1510_has_explicit_check(filepath: str, lineno: int) -> bool:
    lines = src_lines(filepath)
    if not lines or not (1 <= lineno <= len(lines)):
        return False
    stmt = join_balanced_stmt([code_part(l) for l in lines], lineno)
    target = assign_target_of(stmt)
    if target is None:
        return False
    return _returncode_post_check(target, os.path.abspath(filepath), lineno)
_RUFF_FP_CACHE_MAX_FILES = 256
_F541_CACHE: dict[str, tuple[_FpCacheKey, ast.AST | None]] = {}
def _ruff_col_to_byte_col(filepath: str, lineno: int, col: int) -> int:
    if col <= 0:
        return col - 1
    lines = src_lines(filepath)
    if not lines or not (1 <= lineno <= len(lines)):
        return col - 1
    return len(lines[lineno - 1][:col - 1].encode("utf-8", errors="replace"))
def _f821_span_covers(node: ast.expr, ln: int, cl: int) -> bool:
    if (getattr(node, "lineno", None) is None
            or getattr(node, "end_lineno", None) is None):  # pragma: no cover
        return False
    return _point_in_span(ln, cl, _node_span(node), True)
def _node_covers_line(node: ast.AST, lineno: int) -> bool:
    sl = getattr(node, "lineno", None)
    el = getattr(node, "end_lineno", None)
    if sl is None or el is None:
        return False
    return sl <= lineno <= el
def _constant_has_brace(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and ("{" in node.value or "}" in node.value))
def _f541_joined_str_has_brace_at_line(node: ast.JoinedStr,
                                       lineno: int,
                                       byte_col: int | None) -> bool:
    if not _node_covers_line(node, lineno):
        return False
    if byte_col is not None and not _f821_span_covers(node, lineno, byte_col):
        return False
    return any(_constant_has_brace(v) for v in node.values)
def _f541_has_escaped_braces(abs_path: str, lineno: int,
                             column: int | None = None) -> bool:
    if lineno <= 0:
        return False
    tree = _fp_cache_get(abs_path, _F541_CACHE, _RUFF_FP_CACHE_MAX_FILES,
                         '_f541_has_escaped_braces')
    if tree is None:
        return False
    byte_col = None
    if column is not None:
        byte_col = _ruff_col_to_byte_col(abs_path, lineno, column)
    return _has_escaped_brace_joined_str(tree, lineno, byte_col)
def _has_escaped_brace_joined_str(tree: ast.AST, lineno: int,
                                  byte_col: int | None) -> bool:
    return any(
        isinstance(node, ast.JoinedStr)
        and _f541_joined_str_has_brace_at_line(node, lineno, byte_col)
        for node in walk_nodes(tree))
def _is_ruff_code_specific_fp(code: str, abs_path: str, row: int,
                              column: int) -> bool:
    if code == "F541" and _f541_has_escaped_braces(abs_path, row, column):
        return True
    return bool(code == "PLW1510" and _plw1510_has_explicit_check(abs_path, row))
def release_bandit_fp_caches() -> int:
    n = len(_B1X_AST_CACHE) + len(_B607_AST_CACHE) + len(_B108_AST_CACHE)
    _B1X_AST_CACHE.clear()
    _B607_AST_CACHE.clear()
    _B108_AST_CACHE.clear()
    return n
def release_ruff_fp_caches() -> int:
    n = len(_F541_CACHE)
    _F541_CACHE.clear()
    return n
def _starts_with_sep(path: str) -> bool:
    return path.startswith(os.sep) or (
        os.altsep is not None and path.startswith(os.altsep))
def _resolve_finding_file(skill_dir: str, file_val: str) -> str:
    if not file_val:
        return file_val
    if os.path.splitdrive(file_val)[0]:
        return file_val
    if not _starts_with_sep(file_val):
        return os.path.join(skill_dir, file_val)
    if os.name != "nt":
        return file_val
    return os.path.join(skill_dir, file_val.lstrip("/\\"))
def _fp_trace_entry(finding: dict, reason: str, **extra: Any) -> dict:
    entry = {"rule_id": finding.get("rule_id") or "",
             "file": finding.get("file", ""),
             "line": finding.get("line", 0),
             "reason": reason}
    entry.update(extra)
    return entry
def _is_user_input_sql_taint(finding: dict, rule_id: str) -> bool:
    return (rule_id == "E1-sql_injection"
            and finding.get("source_fragment") == "user_input")
def _fp_downgrade_exempt(finding: dict, rule_id: str) -> bool:
    return (is_test_scoped_fp_rule(rule_id)
            or _is_user_input_sql_taint(finding, rule_id))
def _fp_triage(f: dict, skill_dir: str) -> tuple:
    _rule_id = f.get("rule_id") or ""
    if _rule_id in TAINT_PATH_TRAVERSAL_RULES:
        return _fp_triage_taint(f)
    if _static_fp_hit(f, _rule_id, skill_dir):
        return "drop", _fp_trace_entry(
            f, "static_or_fixed_fp_rule",
            test_scoped=is_test_scoped_fp_rule(_rule_id))
    if not _fp_downgrade_exempt(f, _rule_id):
        f["severity"] = apply_fp_downgrade(
            _rule_id, f.get("severity") or "P2",
            skill_dir=skill_dir,
            file_path=str(f.get("file") or f.get("file_path") or ""))
    return "keep", None
def _fp_triage_taint(f: dict) -> tuple:
    _exempt = taint_traversal_exemption(f)
    if _exempt is True:
        return "drop", _fp_trace_entry(
            f, "trusted_origin", source_name=f.get("source_name", ""))
    if _exempt is False:
        return "keep", None
    f["severity"] = "INFO"
    return "keep", _fp_trace_entry(f, "origin_missing_downgraded_info")
def _static_fp_hit(f: dict, rule_id: str, skill_dir: str) -> bool:
    if f.get("source") == "E1-ruff":
        return False
    if not fp_rule_registered(skill_dir, rule_id):
        return False
    if _is_user_input_sql_taint(f, rule_id):
        return False
    if is_test_scoped_fp_rule(rule_id):
        return bool(is_test_file_path(f.get("file", "")))
    return True
def _filter_fp_findings(all_findings: list, skill_dir: str) -> tuple:
    _fp_removed = 0
    _kept_findings = []
    _fp_trace: list[dict] = []
    for f in all_findings:
        _action, _trace = _fp_triage(f, skill_dir)
        if _trace is not None:
            _fp_trace.append(_trace)
        if _action == "drop":
            _fp_removed += 1
        else:
            _kept_findings.append(f)
    return _kept_findings, _fp_removed, _fp_trace
def _dedup_equiv_findings(all_findings: list) -> tuple:
    seen: set[tuple] = set()
    deduped = []
    _dedup_trace: list[dict] = []
    for f in all_findings:
        key = equiv_dedup_key(f)
        if key is not None and key in seen:
            _dedup_trace.append(_fp_trace_entry(
                f, "equiv_rule_merged", source=f.get("source", "")))
            continue
        if key is not None:
            seen.add(key)
        deduped.append(f)
    return deduped, _dedup_trace
def _drop_stale_findings(deduped: list, dedup_trace: list,
                         skill_dir: str) -> tuple:
    _stale_removed = 0
    _fresh: list[dict] = []
    if not skill_dir:
        if deduped:
            logger.warning(
                "[engine_d1_tool_channels] 缺少技能根，跳过陈旧 finding 剔除"
                "（保留 %d 条）", len(deduped))
        return list(deduped), _stale_removed
    for f in deduped:
        _fp = str(f.get("file") or "")
        # "?"/"n/a" 是工具未定位到文件的占位标记（与 fp_rules_judge 同一契约），
        # 无法核实文件存在性，不得按“文件已不存在”剔除。
        if (_fp and _fp.strip().casefold()
                not in _UNRESOLVED_FILE_MARKERS):
            _abs = _resolve_finding_file(skill_dir, _fp)
            if not os.path.isfile(_abs):
                _stale_removed += 1
                logger.warning(
                    "[engine_d1_tool_channels] 陈旧 finding 剔除"
                    "(文件已不存在): %s:%s %s",
                    _fp, f.get("line"), f.get("rule_id"))
                dedup_trace.append(_fp_trace_entry(
                    f, "stale_file_removed", source=f.get("source", "")))
                continue
        _fresh.append(f)
    return _fresh, _stale_removed
class _PostProcessed(NamedTuple):
    findings: list[dict]
    fp_removed: int
    fp_trace: list[dict]
    dedup_trace: list[dict]
    stale_removed: int
def _finding_items(value) -> list:
    if isinstance(value, dict):
        return [value]
    if value is None or isinstance(value, (str, bytes)):
        return []
    try:
        return list(value)
    except TypeError as _e:
        _swallow("_finding_items", _e)
        return []
def _skill_dir_arg(skill_dir) -> str:
    if not skill_dir:
        return ""
    try:
        return os.fsdecode(os.fspath(skill_dir))
    except TypeError as _e:
        _swallow("_skill_dir_arg", _e)
        return ""
def postprocess_findings(skill_dir: str,
                         findings: list[dict]) -> _PostProcessed:
    skill_dir = _skill_dir_arg(skill_dir)
    _raw = _finding_items(findings)
    findings = [f for f in _raw if isinstance(f, dict)]
    if len(findings) != len(_raw):
        logger.warning(
            "[engine_d1_tool_channels] 后处理跳过 %d 个非映射 finding",
            len(_raw) - len(findings))
    kept, fp_removed, fp_trace = _filter_fp_findings(findings, skill_dir)
    deduped, dedup_trace = _dedup_equiv_findings(kept)
    fresh, stale_removed = _drop_stale_findings(
        deduped, dedup_trace, skill_dir)
    return _PostProcessed(fresh, fp_removed, fp_trace, dedup_trace,
                          stale_removed)
@dataclass(frozen=True)
class _FileScan:
    fp: str
    rel_path: str
    source: str
    tree: Any
def _vget_or(v, *keys, default=""):
    for k in keys:
        val = v.get(k)
        if val:
            return val
    return default
def _as_dict_items(value: Any) -> list[dict]:
    if value is None:
        return []
    if isinstance(value, dict):
        return [value]
    if not isinstance(value, (list, tuple, set, frozenset)):
        raise TypeError(f"expected mapping items, got {type(value).__name__}")
    items = list(value)
    for item in items:
        if not isinstance(item, dict):
            raise TypeError(
                "expected every item to be a mapping, "
                f"got {type(item).__name__}")
    return items
def _as_list(value: Any) -> list:
    return (list(value) if isinstance(value, (list, tuple, set, frozenset))
            else [])
def _origin_is_user_controlled(rule: str, v: dict) -> bool:
    if rule in TAINT_PATH_TRAVERSAL_RULES:
        return taint_traversal_exemption(v) is False
    return _is_user_input_sql_taint(v, rule)
def _fp_downgrade_applies(rule: str, v: dict) -> bool:
    return (not is_test_scoped_fp_rule(rule)
            or is_test_file_path(v.get("file") or ""))
def _downgrade_vuln_severity(
        v: dict, rule: str, sev: str, *, skill_dir: str) -> str:
    if (_origin_is_user_controlled(rule, v)
            or not _fp_downgrade_applies(rule, v)):
        return sev
    return apply_fp_downgrade(
        rule, sev, skill_dir=skill_dir,
        file_path=str(v.get("file") or v.get("file_path") or "")) or sev
def _vuln_confidence_normalize(v: dict) -> float:
    conf = v.get("confidence")
    if not isinstance(conf, (int, float)) or isinstance(conf, bool):
        return _VULN_CONFIDENCE_DEFAULT
    if isinstance(conf, float) and not math.isfinite(conf):
        return _VULN_CONFIDENCE_DEFAULT
    return float(min(1, max(0, conf)))
def _format_vuln_finding(v, *, skill_dir: str) -> dict | None:
    if not isinstance(v, dict):
        return None
    rule = _vget_or(v, "rule_id", default="E1-VULN")
    sev = _downgrade_vuln_severity(
        v, rule, _vget_or(v, "severity", default="P2"),
        skill_dir=skill_dir)
    entry = {
        "rule_id": rule, "severity": sev,
        "confidence": _vuln_confidence_normalize(v),
        "message": _vget_or(v, "message", "suggestion", default=""),
        "file": _vget_or(v, "file", default=""),
        "line": _vget_or(v, "line", default=0), "source": "E1-vuln",
        "family": v.get("family") or "security",
        "category": _vget_or(v, "category", default=""),
        "cwe_id": _vget_or(v, "cwe_id", default=""),
        "sink": _vget_or(v, "sink", default=""),
        "fix_suggestion": _vget_or(
            v, "fix_suggestion", "suggestion", default=""),
        "source_name": _vget_or(v, "source_name", default=""),
        "source_category": _vget_or(v, "source_category", default=""),
        "source_fragment": _vget_or(v, "source_fragment", default="")}
    if isinstance(v.get("fp_evidence"), dict):
        entry["fp_evidence"] = v["fp_evidence"]
    if v.get("trusted_origin") is True:
        entry["trusted_origin"] = True
    return entry
_ENHANCED_OR_FIELDS: tuple = (
    ("message", "suggestion", ""), ("line", "line", 0),
    ("category", "category", ""), ("cwe_id", "cwe_id", ""),
    ("sink", "sink", ""),
    ("source_fragment", "source", ""),
    ("fix_suggestion", "suggestion", ""),
    ("source_name", "taint_origin", ""))
def _enhanced_finding_payload(issue: dict, rel_path: str) -> dict:
    payload = {
        "rule_id": f"E1-{_vget_or(issue, 'category', default='VULN')}",
        "severity": map_bandit_severity(
            _vget_or(issue, "severity", default="MEDIUM")),
        "confidence": _vuln_confidence_normalize(issue),
        "file": _vget_or(issue, "file", default=rel_path),
        "source": "E1-vuln",
        "family": "security",
        "source_category": TAINT_SOURCE_CATEGORY_BY_NAME.get(
            _vget_or(issue, "taint_origin", default=""), ""),
    }
    for dst, src_f, fb in _ENHANCED_OR_FIELDS:
        payload[dst] = _vget_or(issue, src_f, default=fb)
    if issue.get("trusted_origin") is True:
        payload["trusted_origin"] = True
    return payload
def _vulnerability_suppressed(item: dict, source: str) -> bool:
    line = item.get("line") or 0
    return (
        line_has_applicable_nosec(
            source, line, item.get("category") or "")
        or line_has_taint_suppression(
            source, line, item.get("sink") or "")
    )
def _parse_tree_or_none(source: str, fp: str):
    try:
        return parse_cached(source, fp)
    except PARSE_DEGRADE_EXC as _e:
        _swallow('_parse_tree_or_none', _e)
        return None
def _cached_source_and_tree(cache, fp: str) -> tuple | None:
    if cache is None:
        return None
    try:
        source, tree = cache.get_source_and_ast(fp)
    except Exception as e:
        logger.warning(
            "[VulnerabilityScanner] 缓存复合读取失败,回退分离路径 %s: %s",
            fp, e, exc_info=True)
        return None
    if source is None:
        return None
    return source, tree
def _taint_item_file(item: dict, fp: str, rel_path: str, skill_dir: str) -> str:
    raw_file = normalize_filepath(item.get("file"))
    if item.get("cross_module") and raw_file:
        callee = os.path.join(os.path.dirname(fp), raw_file)
        item["file"] = safe_relpath(callee, skill_dir, normalize=False)
    else:
        item["file"] = raw_file or rel_path
    return item["file"] or ""
def _taint_entry_file(item: dict, rel_path: str) -> str:
    if not item.get("cross_module"):
        return rel_path
    return normalize_filepath(item.get("file")) or rel_path
_VULN_SEVERITY_DEFAULT = 'LOW'
_VULN_SEVERITY_WEIGHTS: dict[str, int] = {
    'CRITICAL': 25, 'HIGH': 15, 'MEDIUM': 8, 'LOW': 3}
def _run_diag(source_code: str, filepath: str, options: DiagOptions, *,
              tree: Any = None) -> tuple[str | None, dict]:
    result = get_diagnoser().diag(source_code, filepath=filepath, tree=tree,
                                  options=options)
    if result.get('ok') is False:
        return str(result.get('error') or '诊断失败'), result
    return None, result
def _category_value(category: Any) -> str:
    return category.value if hasattr(category, 'value') else str(category)
_VULN_ROW_FIELDS: tuple[str, ...] = (
    'category', 'severity', 'file', 'line', 'sink', 'source',
    'confidence', 'suggestion', 'cwe_id')
def _vuln_row(f: Any) -> dict | None:
    if not all(hasattr(f, name) for name in _VULN_ROW_FIELDS):
        logger.warning("[VulnerabilityScanner] 跳过缺字段 finding: %r",
                       type(f).__name__)
        return None
    row = {name: getattr(f, name) for name in _VULN_ROW_FIELDS}
    row['category'] = _category_value(row['category'])
    row['taint_origin'] = getattr(f, 'taint_origin', '')
    return row
def _vuln_issue_rows(result: dict) -> list[dict]:
    rows = (_vuln_row(f) for f in _as_list(result.get('findings')))
    return [row for row in rows if row is not None]
def _finding_file_key(file_value: Any, filepath: str) -> str:
    file_value = _sink_record_file(file_value, filepath)
    return os.path.normcase(os.path.abspath(file_value or filepath))
def _trace_has_direct_finding(direct_findings: list, filepath: str,
                              sink_file: str, sink_line: int,
                              sink_name: str) -> bool:
    trace_file_key = _finding_file_key(sink_file, filepath)
    for finding in direct_findings:
        if as_int(getattr(finding, 'line', 0)) != sink_line:
            continue
        finding_file = getattr(finding, 'file', '')
        if _finding_file_key(finding_file, filepath) != trace_file_key:
            continue
        if get_diagnoser()._sink_names_match(
                getattr(finding, 'sink', ''), sink_name):
            return True
    return False
def _taint_issue_rows(result: dict, filepath: str) -> list[dict]:
    filepath = normalize_filepath(filepath)
    direct_findings = _as_list(result.get('findings'))
    rows: list[dict] = []
    for trace in _as_list(result.get('taint_traces')):
        sink_name = getattr(trace, 'sink_expr', '')
        sink_line = as_int(getattr(trace, 'sink_line', 0))
        if not isinstance(sink_name, str) or not sink_name or sink_line <= 0:
            continue
        sink_file = _sink_record_file(
            getattr(trace, 'sink_file', ''), filepath)
        if _trace_has_direct_finding(
                direct_findings, filepath, sink_file, sink_line, sink_name):
            continue
        sink_spec = next(
            (spec for spec in BUILTIN_SINKS if spec.name == sink_name), None)
        source_name = (getattr(trace, 'source_expr', '')
                       or getattr(trace, 'variable', ''))
        rows.append({
            'category': sink_spec.category if sink_spec else 'taint',
            'severity': sink_spec.severity if sink_spec else 'P0',
            'file': sink_file,
            'line': sink_line,
            'sink': sink_name,
            'source': source_name,
            'confidence': _VULN_CONFIDENCE_DEFAULT,
            'suggestion': (sink_spec.description if sink_spec
                           else '污点传播到危险 sink'),
            'cwe_id': sink_spec.cwe_id if sink_spec else '',
            'taint_origin': source_name,
        })
    return rows
_VULN_SEVERITY_WEIGHT_BY_RANK = {
    SEVERITY_RANK[severity]: weight
    for severity, weight in _VULN_SEVERITY_WEIGHTS.items()}
def _vuln_issue_weight(issue: dict) -> int:
    severity = str(
        issue.get('severity') or _VULN_SEVERITY_DEFAULT).upper()
    weight = _VULN_SEVERITY_WEIGHTS.get(severity)
    if weight is not None:
        return weight
    return _VULN_SEVERITY_WEIGHT_BY_RANK.get(
        SEVERITY_RANK.get(severity),
        _VULN_SEVERITY_WEIGHTS[_VULN_SEVERITY_DEFAULT])
def _vuln_score(issues: list[dict]) -> float:
    penalty = sum(_vuln_issue_weight(issue) for issue in issues)
    return max(0.0, _VULN_SCORE_MAX - penalty)
def _quick_vulnerability_error(error: str) -> dict:
    return {'vulnerable': False, 'issues': [], 'score': 0.0,
            'error': error}
def quick_vulnerability_check(
        source_code: Any, filepath: str = _DEFAULT_FILEPATH,
        tree: Any = None, *, include_taint: bool = True) -> dict:
    if not isinstance(source_code, str):
        return _quick_vulnerability_error('source_code is not a string')
    try:
        err, result = _run_diag(
            source_code, filepath,
            DiagOptions(enable_symbolic=False, enable_cfg_du=False,
                        include_extras=include_taint),
            tree=tree)
        if err:
            return _quick_vulnerability_error(err)
        issues = _vuln_issue_rows(result)
        if include_taint:
            issues.extend(_taint_issue_rows(result, filepath))
        return {'vulnerable': len(issues) > 0, 'issues': issues,
                'score': _vuln_score(issues),
                'framework': result.get('framework', 'unknown')}
    except Exception as e:  # noqa: BLE001
        logger.warning('quick_vulnerability_check failed: %s', e)
        return _quick_vulnerability_error(str(e))
_EXPLOIT_ROW_FIELDS: tuple[str, ...] = (
    'category', 'severity', 'line', 'sink', 'source', 'cwe_id')
def _exploit_vuln_rows(findings: list) -> list[dict]:
    rows: list[dict] = []
    for f in _as_list(findings):
        if not all(hasattr(f, name) for name in _EXPLOIT_ROW_FIELDS):
            logger.warning("[Exploit] 跳过缺字段 finding: %r",
                           type(f).__name__)
            continue
        row = {name: getattr(f, name) for name in _EXPLOIT_ROW_FIELDS}
        row['category'] = _category_value(row['category'])
        rows.append(row)
    return rows
_EXPLOIT_REPORT_FIELDS: tuple[str, ...] = (
    'severity_score', 'source_info', 'sink_info', 'propagation_steps',
    'trigger_input', 'fix_suggestion', 'vulnerability')
def _exploit_sections(reports: list) -> tuple[list[dict], list[dict]]:
    exploits: list[dict] = []
    fixes: list[dict] = []
    for report in _as_list(reports):
        if not all(hasattr(report, name) for name in _EXPLOIT_REPORT_FIELDS):
            logger.warning("[Exploit] 跳过缺字段报告: %r",
                           type(report).__name__)
            continue
        exploits.append({
            'severity_score': report.severity_score,
            'source_info': report.source_info,
            'sink_info': report.sink_info,
            'propagation_steps': report.propagation_steps,
            'trigger_input': report.trigger_input})
        fixes.append({
            'suggestion': report.fix_suggestion,
            'severity': getattr(report.vulnerability, 'severity', '')})
    return exploits, fixes
def generate_source_exploit_report(
        source_code: Any, filepath: str = _DEFAULT_FILEPATH) -> dict:
    if not isinstance(source_code, str):
        return {'status': 'error', 'vulnerabilities': [], 'exploits': [],
                'fixes': [], 'error': 'source_code is not a string'}
    try:
        err, result = _run_diag(
            source_code, filepath, DiagOptions(enable_symbolic=False))
        if err:
            return {'status': 'error', 'vulnerabilities': [], 'exploits': [],
                    'fixes': [], 'error': err}
        vulnerabilities = _exploit_vuln_rows(result.get('findings', []))
        exploits, fixes = _exploit_sections(result.get('exploit_reports', []))
        return {'status': 'ok', 'vulnerabilities': vulnerabilities,
                'exploits': exploits, 'fixes': fixes}
    except Exception as e:  # noqa: BLE001
        logger.warning('generate_source_exploit_report failed: %s', e)
        return {'status': 'error', 'vulnerabilities': [], 'exploits': [],
                'fixes': [], 'error': str(e)}
def _direct_taint_dedup_key(finding: dict) -> tuple | None:
    rule_id = str(finding.get("rule_id") or "")
    category = finding.get("category")
    if (finding.get("source") != "E1-vuln" or not category
            or not rule_id.startswith(("E1-", "TAINT-"))):
        return None
    return equiv_dedup_key({**finding, "rule_id": f"E1-{category}"})
def _dedup_direct_taint_findings(findings: list[dict]) -> list[dict]:
    unique: list[dict] = []
    seen: set[tuple] = set()
    for finding in findings:
        key = _direct_taint_dedup_key(finding)
        if key is not None and key in seen:
            continue
        if key is not None:
            seen.add(key)
        unique.append(finding)
    return unique
class VulnerabilityScanner:
    def __init__(self, skill_dir: str, cache=None,
                 include_tests: bool = DEFAULT_INCLUDE_TESTS):
        self.skill_dir = _abs_skill_root(skill_dir)
        self._cache = cache
        self._include_tests = include_tests
    def _load_source_and_tree(self, fp: str) -> tuple:
        hit = _cached_source_and_tree(self._cache, fp)
        if hit is not None:
            source, tree = hit
            if tree is None:
                tree = _parse_tree_or_none(source, fp)
            return source, tree
        source = read_source_cached(fp)
        if source is None:
            return None, None
        return source, _parse_tree_or_none(source, fp)
    def _collect_vulnerability_vulns(
            self, py_files: list[str] | None,
            use_enhanced: bool) -> tuple[list[dict], set[str], int]:
        enhanced_vulns: list[dict] = []
        taint_vulns: list[dict] = []
        failed_files: set[str] = set()
        scanned_total = 0
        py_files = resolve_scan_targets(
            py_files, self.skill_dir, self._include_tests)
        for fp in py_files:
            if self._scan_one_file(fp, use_enhanced, enhanced_vulns,
                                   taint_vulns, failed_files):
                scanned_total += 1
        vulns = enhanced_vulns + taint_vulns
        return vulns, failed_files, scanned_total
    def _scan_one_file(self, fp: str, use_enhanced: bool,
                       enhanced_vulns: list[dict], taint_vulns: list[dict],
                       failed_files: set[str]) -> bool:
        rel_path = safe_relpath(fp, self.skill_dir, normalize=False)
        if not self._include_tests and is_test_file_path(rel_path):
            logger.debug(
                "[VulnerabilityScanner] 测试基建文件不参与生产扫描: %s",
                rel_path)
            return False
        source, tree = self._load_source_and_tree(fp)
        if source is None:
            failed_files.add(fp)
            if os.path.isfile(fp):
                logger.warning(
                    "[VulnerabilityScanner] 源文件不可读,扫描覆盖不完整 %s",
                    fp)
            else:
                logger.warning(
                    "[VulnerabilityScanner] 目标不是可读常规文件,"
                    "扫描覆盖不完整 %s", fp)
            return True
        if tree is None:
            failed_files.add(fp)
            logger.warning(
                "[VulnerabilityScanner] 源码解析失败,扫描覆盖不完整 %s",
                fp)
            return True
        view = _FileScan(fp=fp, rel_path=rel_path,
                         source=source, tree=tree)
        if use_enhanced:
            self._scan_file_enhanced(view, enhanced_vulns, failed_files)
        self._scan_file_taint(view, taint_vulns, failed_files)
        return True
    def run(self, use_enhanced: bool = True, py_files: list[str] | None = None) -> dict:
        start = time.perf_counter()
        vulns, failed_files, total_files = self._collect_vulnerability_vulns(
            py_files, use_enhanced)
        findings = []
        for v in vulns:
            entry = _format_vuln_finding(v, skill_dir=self.skill_dir)
            if entry is not None:
                findings.append(entry)
        findings = _dedup_direct_taint_findings(findings)
        all_failed = total_files > 0 and len(failed_files) == total_files
        no_targets = total_files == 0
        summary = f"安全漏洞: {len(findings)} 个"
        if no_targets:
            summary += "；没有可扫描的 Python 文件，扫描未执行"
        if failed_files:
            summary += (f"（检测失败{len(failed_files)}文件,"
                        f"扫描覆盖不完整!）")
        if all_failed:
            summary += "；所有目标文件均未能完成扫描"
        return {
            "findings": findings,
            "findings_count": len(findings),
            "status": "error" if no_targets or all_failed else "pass",
            "summary": summary,
            "elapsed_ms": elapsed_ms(start),
            "vulnerabilities": findings,
            "detect_failed": len(failed_files),
            "files_scanned": total_files - len(failed_files),
        }
    def _scan_file_enhanced(self, view: _FileScan, vulns_out: list[dict], failed_files: set[str]) -> None:
        try:
            result = quick_vulnerability_check(
                view.source, filepath=view.rel_path, tree=view.tree,
                include_taint=False)
            if result.get("error"):
                failed_files.add(view.fp)
                logger.warning(
                    "[VulnerabilityScanner] 增强检测失败,扫描覆盖不完整 %s: %s",
                    view.fp, result["error"])
            self._append_enhanced_issues(result, view, vulns_out)
        except Exception as e:  # noqa: BLE001
            failed_files.add(view.fp)
            logger.warning(
                "[VulnerabilityScanner] 增强检测执行失败 %s: %s", view.fp, e)
    def _append_enhanced_issues(self, result: dict, view: _FileScan, vulns_out: list[dict]) -> None:
        issues = _as_dict_items(result.get("issues"))
        if not (result.get("vulnerable") and issues):
            return
        for issue in issues:
            self._append_enhanced_issue(
                issue, view.rel_path, view.source, vulns_out)
    def _append_enhanced_issue(self, issue: dict, rel_path: str, source: str, vulns_out: list[dict]) -> None:
        if _vulnerability_suppressed(issue, source):
            return
        vulns_out.append(_enhanced_finding_payload(issue, rel_path))
    def _scan_file_taint(self, view: _FileScan, taint_vulns: list[dict], failed_files: set[str]) -> None:
        try:
            taint_result = check_vulnerability(
                view.source, tree=view.tree, filepath=view.fp)
            if not isinstance(taint_result, (dict, list)):
                failed_files.add(view.fp)
                logger.warning(
                    "[VulnerabilityScanner] 污点分析返回非法类型 %s: %s",
                    type(taint_result).__name__, view.fp)
                return
            self._expand_taint_result(taint_result, view, taint_vulns)
        except Exception as e:  # noqa: BLE001
            logger.warning(
                "[VulnerabilityScanner] 污点分析失败 %s: %s", view.fp, e)
            failed_files.add(view.fp)
    def _taint_entry(self, item: dict, file_value: str, source_text: str) -> dict | None:
        entry = dict(item)
        entry["file"] = normalize_filepath(file_value)
        entry["source"] = "E1-vuln"
        entry["family"] = "taint"
        if _vulnerability_suppressed(entry, source_text):
            return None
        return entry
    @staticmethod
    def _taint_items_of(taint_result: Any) -> list[dict]:
        if isinstance(taint_result, dict):
            return _as_dict_items(taint_result.get("vulnerabilities"))
        return _as_dict_items(taint_result)
    def _collect_taint_items(self, raw_items: list[dict], fp: str,
                             rel_path: str) -> tuple[list[dict], set[str]]:
        taint_items = []
        item_files: set[str] = set()
        for raw_item in raw_items:
            i = dict(raw_item)
            item_file = _taint_item_file(i, fp, rel_path, self.skill_dir)
            if item_file:
                item_files.add(item_file)
            taint_items.append(i)
        return taint_items, item_files
    def _build_taint_source_map(self, item_files: set[str], rel_path: str, source: str) -> dict[str, str]:
        sm: dict[str, str] = {rel_path: source}
        for cf in sorted(item_files):
            if not cf or cf in sm:
                continue
            cf_src = read_source_cached(os.path.join(self.skill_dir, cf))
            sm[cf] = cf_src if cf_src is not None else ""
        return sm
    def _expand_taint_result(self, taint_result: Any, view: _FileScan,
                             taint_vulns: list) -> None:
        taint_items, item_files = self._collect_taint_items(
            self._taint_items_of(taint_result), view.fp, view.rel_path)
        sm = self._build_taint_source_map(
            item_files, view.rel_path, view.source)
        for enh in enhance_taint_with_confidence(
                taint_items, source_map=sm):
            if not isinstance(enh, dict):
                continue
            item = enh.get("flow")
            if not isinstance(item, dict):
                continue
            entry_file = _taint_entry_file(item, view.rel_path)
            entry = self._taint_entry(
                item, entry_file,
                sm.get(entry_file or view.rel_path, ""))
            if entry is None:
                continue
            entry["fp_evidence"] = (enh["fp_evidence"]
                                    if isinstance(enh.get("fp_evidence"), dict)
                                    else {})
            taint_vulns.append(entry)

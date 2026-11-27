from __future__ import annotations

import ast
import copy
import io
import logging
import os
import re
import subprocess
import sys
import time
import tokenize
from collections import deque
from dataclasses import dataclass, field
from importlib.util import find_spec
from typing import Any

from jwsgj.diag_callgraph_channels import (
    FallbackCallGraph,
    build_fallback_call_graph,
    fallback_resolve_function_name,
)
from jwsgj.diag_callgraph_source import EntryPointDiscoverer
from jwsgj.diag_shared_ast_bindings import (
    ScopeNameResolver,
    build_module_symbol_table,
    exec_scope_declarations,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    _irrefutable_case,
    first_symbol_field,
    innermost_span,
    is_mutable_default,
    iter_pattern_capture_names,
    module_postpones_annotations,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_surface import module_export_names
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    parse_cached,
    read_source,
    read_source_strict,
)
from jwsgj.diag_shared_source_scan import (
    IDENTIFIER_SOURCE,
    is_silent_handler,
)
from jwsgj.diag_types_defs import dict_findings
from jwsgj.diag_types_normalize import (
    adjust_finding_confidence,
    anchor_to_skill,
    channel_locator,
    env_number,
    finding_file_path,
    finding_rule_family,
    is_real_number,
    make_locator_fast,
    normalize_severity_rank,
    safe_finding_line,
)
from jwsgj.fix_guide_rule_identity import (
    is_dead_code_finding,
    is_family_member,
    normalize_rule,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import is_test_dir_name, normalize_skill_dir
from jwsgj.xv_evidence_strength import (
    DEPTH_CONFIDENCE_BOOST_CAP,
    DEPTH_PRIORITY_BOOST_CAP,
    ISOLATED_CONFIDENCE_PENALTY,
    bizflow_signal_payload,
    business_flow_confidence_boost,
    counter_evidence_confidence_penalty,
    refdepth_boosts,
    refdepth_signal_payload,
    test_triage_confidence_boost,
    vcs_recency_confidence_boost,
)

logger = logging.getLogger(__name__)
__all__ = [
    "DEPTH_CONFIDENCE_BOOST_CAP",
    "DEPTH_PRIORITY_BOOST_CAP",
    "FALSIFY_MAX_ITEMS",
    "FALSIFY_PATTERN_FAMILIES",
    "ISOLATED_CONFIDENCE_PENALTY",
    "BusinessFlowResult",
    "BusinessFlowValidator",
    "CounterEvidenceAnalyzer",
    "FalsificationAnalyzer",
    "ReachabilityReport",
    "RefDepthAnalyzer",
    "RefDepthResult",
    "TestTriageVerifier",
    "VCSRecencyAnalyzer",
    "annotate_findings_with_bizflow",
    "annotate_findings_with_counter_evidence",
    "annotate_findings_with_falsification",
    "annotate_findings_with_ref_depth",
    "annotate_findings_with_test_triage",
    "annotate_findings_with_vcs",
    "build_callers_map",
    "classify_flow_result",
    "is_usable_call_graph",
    "package_init_symbols",
    "resolve_function_for_finding",
]
def _normalize_annotate_input(findings, results):
    if isinstance(findings, list):
        findings_n = findings
    elif isinstance(findings, tuple):
        findings_n = list(findings)
    else:
        findings_n = []
        if findings:
            logger.warning("[XV] findings 非清单形态,跳过整段: %r",
                           type(findings).__name__)
    results_n = results if isinstance(results, dict) else {}
    return findings_n, results_n
def _iter_finding_views(findings):
    if isinstance(findings, str) or not isinstance(findings, (list, tuple)):
        if findings:
            logger.warning("[XV] findings 非清单形态,跳过整段: %r",
                           type(findings).__name__)
        return
    for f in findings:
        if not isinstance(f, dict):
            continue
        yield f, finding_file_path(f), channel_locator(f)
def _iter_signal_pairs(findings, results):
    for f, _fp, loc in _iter_finding_views(findings):
        r = results.get(loc)
        if not isinstance(r, dict):
            continue
        yield f, r
def _signal_str(v) -> str:
    return v if isinstance(v, str) else ""
_QUOTED_IDENTIFIER_RE = re.compile(
    rf"['\"]({IDENTIFIER_SOURCE})['\"]", re.UNICODE)
_BARE_IDENTIFIER_RE = re.compile(
    rf"(?<!\w)({IDENTIFIER_SOURCE})(?!\w)", re.UNICODE)
def _first_regex_identifier(pattern, text: str) -> str | None:
    for match in pattern.finditer(text):
        candidate = match.group(1)
        if candidate.isidentifier() and candidate.isascii():
            return candidate
    return None
def _quoted_identifier_in_message(message: str) -> str | None:
    return _first_regex_identifier(_QUOTED_IDENTIFIER_RE, message)
def _first_identifier_in_message(message: str) -> str | None:
    return (_quoted_identifier_in_message(message)
            or _first_regex_identifier(_BARE_IDENTIFIER_RE, message))
def _coerce_skill_dir(skill_dir) -> str:
    if isinstance(skill_dir, os.PathLike):
        try:
            skill_dir = os.fspath(skill_dir)
        except TypeError as _e:
            log_swallowed(__name__, _e, context='_coerce_skill_dir:fspath')
            return ""
    if not isinstance(skill_dir, str) or not skill_dir:
        return ""
    return normalize_skill_dir(skill_dir)
class VCSRecencyAnalyzer:
    def __init__(self, skill_dir: str):
        self.skill_dir = _coerce_skill_dir(skill_dir)
        self._git_repo_root: str | None = None
        self.recent_days = env_number("JWSGJ_VCS_RECENCY_DAYS", 7, int)
        self.recent_commits = env_number("JWSGJ_VCS_RECENT_COMMITS", 5, int)
        self.is_git, self.recent_files = self._detect_git()
    def _detect_git(self):
        if not self.skill_dir:
            return False, None
        d = os.path.abspath(self.skill_dir)
        while True:
            if os.path.exists(os.path.join(d, ".git")):
                self._git_repo_root = d
                return True, self._git_recent_changed_files(d)
            parent = os.path.dirname(d)
            if parent == d:
                break
            d = parent
        return False, None
    def _git_recent_changed_files(self, repo: str):
        try:
            out = subprocess.run( # nosec B607
                ["git", "log", f"-{self.recent_commits}", "--name-only",
                 "--pretty=format:", "--diff-filter=ACMR"],
                cwd=repo, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
                check=False,
            )
            files = {ln.strip() for ln in out.stdout.splitlines() if ln.strip()}
            return files or None
        except Exception as e: # noqa: BLE001
            logger.debug("[VCS] git 变更文件获取失败（忽略，无VCS信号）: %s", e)
            return None
    def _repo_relative(self, fp: str) -> str | None:
        _base = self._git_repo_root or self.skill_dir
        if not _base:
            return fp.replace("\\", "/")
        try:
            return os.path.relpath(fp, _base).replace("\\", "/")
        except ValueError as e:
            logger.debug("[VCSRecency] relpath 跨盘符（%s），跳过仓库内路径匹配: %s", e, fp)
            return None
    def _vcs_signal(self, fp: str) -> tuple:
        boost, method, detail = False, "", ""
        if self.is_git and self.recent_files is not None:
            rel = self._repo_relative(fp)
            _hit = rel is not None and rel in self.recent_files
            if _hit:
                boost, method, detail = True, "git", f"recent<={self.recent_commits} commits"
        if not boost:
            try:
                age_days = max(0.0, (time.time() - os.path.getmtime(fp)) / 86400.0)
                if age_days <= self.recent_days:
                    boost, method, detail = True, "mtime", f"{age_days:.1f}d"
            except (OSError, ValueError) as e:
                logger.debug("文件状态探测失败（跳过）: %s: %s", fp, e)
        return boost, method, detail
    def analyze(self, findings: list[dict]) -> dict:
        results: dict = {}
        for _f, raw_fp, loc in _iter_finding_views(findings):
            if not raw_fp:
                continue
            fp = anchor_to_skill(raw_fp, self.skill_dir)
            boost, method, detail = self._vcs_signal(fp)
            results[loc] = {"boost": boost, "method": method, "detail": detail}
        return results
def _load_ast(fp: str, context: str, mark_generator_calls: bool = False) -> tuple:
    try:
        src = read_source_strict(fp)
        tree = parse_cached(src, filename=fp)
        if mark_generator_calls:
            _mark_eager_generator_calls(tree, src, fp)
        return tree, None
    except SyntaxError as e:
        log_swallowed(__name__, e, context=f"{context}:SyntaxError")
        return None, {"smoke": None,
                      "detail": f"syntax_error:{getattr(e, 'msg', '')}"}
    except (OSError, ValueError, RecursionError, MemoryError) as e:
        log_swallowed(__name__, e,
                      context=f"{context}:{type(e).__name__}")
        return None, {"smoke": None, "detail": type(e).__name__}
def _scope_parameter_names(node) -> set[str]:
    args = node.args
    parameters = [
        *args.posonlyargs, *args.args, *args.kwonlyargs,
    ]
    if args.vararg is not None:
        parameters.append(args.vararg)
    if args.kwarg is not None:
        parameters.append(args.kwarg)
    return {arg.arg for arg in parameters}
def _nonlocal_names(node) -> set[str]:
    names: set[str] = set()
    body = getattr(node, "body", [])
    stack = list(body) if isinstance(body, list) else []
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(current, ast.Nonlocal):
            names.update(current.names)
        stack.extend(ast.iter_child_nodes(current))
    return names
def _covering_function_scopes(tree: ast.Module, line: int) -> list:
    return _covering_nodes(
        tree, line, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
_STATEMENT_LIST_FIELDS = ("body", "orelse", "finalbody", "handlers", "cases")
def _statement_prefix_before(node, line: int):
    node_line = getattr(node, "lineno", None)
    if node_line is None:
        node_line = getattr(getattr(node, "pattern", None), "lineno", line)
    if node_line > line:
        return None
    cloned = copy.copy(node)
    for field_name in _STATEMENT_LIST_FIELDS:
        items = getattr(node, field_name, None)
        if not isinstance(items, list):
            continue
        prefix = []
        for item in items:
            cloned_item = _statement_prefix_before(item, line)
            if cloned_item is not None:
                prefix.append(cloned_item)
        setattr(cloned, field_name, prefix)
    return cloned
def _iter_expression_name_events(node):
    if node is None:
        return
    if isinstance(node, ast.NamedExpr):
        yield from _iter_expression_name_events(node.value)
        yield from _iter_expression_name_events(node.target)
        return
    if isinstance(node, ast.BoolOp):
        yield from _iter_boolop_name_events(node)
        return
    if isinstance(node, ast.IfExp):
        yield from _iter_expression_name_events(node.test)
        branch = _constant_truth_value(node.test)
        if branch is not None:
            yield from _iter_expression_name_events(
                node.body if branch else node.orelse)
            return
        yield from _iter_exclusive_name_events([
            list(_iter_expression_name_events(node.body)),
            list(_iter_expression_name_events(node.orelse)),
        ])
        return
    if isinstance(node, ast.Call):
        yield from _iter_expression_name_events(node.func)
        eager_generator = getattr(node, "_jwsgj_eager_generator", False)
        for arg in node.args:
            if eager_generator and isinstance(arg, ast.GeneratorExp):
                yield from _iter_comprehension_name_events(arg, force_eager=True)
            else:
                yield from _iter_expression_name_events(arg)
        for keyword in node.keywords:
            yield from _iter_expression_name_events(keyword.value)
        return
    if isinstance(node, ast.Dict):
        for key, value in zip(node.keys, node.values, strict=True):
            yield from _iter_expression_name_events(key)
            yield from _iter_expression_name_events(value)
        return
    if isinstance(node, ast.Lambda):
        for default in (
                *node.args.defaults,
                *(value for value in node.args.kw_defaults
                  if value is not None)):
            yield from _iter_expression_name_events(default)
        return
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp,
                         ast.DictComp)):
        yield from _iter_comprehension_name_events(node)
        return
    if isinstance(node, ast.Name):
        if isinstance(node.ctx, ast.Load):
            kind = "load"
        elif isinstance(node.ctx, ast.Store):
            kind = "bind"
        else:
            kind = "unbind"
        yield kind, node.id, node.lineno
        return
    for child in ast.iter_child_nodes(node):
        yield from _iter_expression_name_events(child)
def _iter_definition_name_events(node):
    for decorator in node.decorator_list:
        yield from _iter_expression_name_events(decorator)
    if isinstance(node, ast.ClassDef):
        for base in node.bases:
            yield from _iter_expression_name_events(base)
        for keyword in node.keywords:
            yield from _iter_expression_name_events(keyword.value)
    else:
        args = node.args
        for default in (
                *args.defaults,
                *(value for value in args.kw_defaults if value is not None)):
            yield from _iter_expression_name_events(default)
        parameters = [
            *args.posonlyargs, *args.args, *args.kwonlyargs,
        ]
        if args.vararg is not None:
            parameters.append(args.vararg)
        if args.kwarg is not None:
            parameters.append(args.kwarg)
        for parameter in parameters:
            yield from _iter_expression_name_events(parameter.annotation)
        yield from _iter_expression_name_events(node.returns)
def _constant_truth_value(node) -> bool | None:
    return bool(node.value) if isinstance(node, ast.Constant) else None
def _is_literal_empty_iterable(node) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and not node.value)
def _is_literal_nonempty_iterable(node) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return bool(node.elts) and not any(
            isinstance(elt, ast.Starred) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return bool(node.keys) and all(key is not None for key in node.keys)
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))
def _merge_exclusive_binding_events(branch_events: list[list]) -> list:
    final_by_branch = []
    for events in branch_events:
        final_events = {}
        for event in events:
            if event[0] in {"bind", "unbind"} and event[1]:
                final_events[event[1]] = event
        final_by_branch.append(final_events)
    names = sorted({name for final in final_by_branch for name in final})
    merged = {}
    for name in names:
        events = [final.get(name) for final in final_by_branch]
        if any(event is not None and event[0] == "unbind" for event in events):
            merged[name] = next(
                event for event in reversed(events)
                if event is not None and event[0] == "unbind")
        elif all(event is not None and event[0] == "bind" for event in events):
            merged[name] = events[-1]
    return [merged[name] for name in sorted(merged)]
def _iter_exclusive_name_events(branch_events):
    branches = [list(events) for events in branch_events]
    affected_names = sorted({
        event[1] for events in branches for event in events
        if event[0] in {"bind", "unbind"} and event[1]})
    for events in branches:
        for name in affected_names:
            yield "checkpoint", name, 0
        yield from events
        for name in affected_names:
            yield "restore", name, 0
    yield from _merge_exclusive_binding_events(branches)
def _iter_boolop_name_events(node: ast.BoolOp):
    paths = []
    prefix = []
    stopped = False
    stop_truth = isinstance(node.op, ast.Or)
    for index, value in enumerate(node.values):
        prefix.extend(_iter_expression_name_events(value))
        truth = _constant_truth_value(value)
        if truth is not None and truth == stop_truth:
            paths.append(prefix)
            stopped = True
            break
        if truth is None and index < len(node.values) - 1:
            paths.append(list(prefix))
    if not stopped:
        paths.append(prefix)
    yield from _iter_exclusive_name_events(paths)
_EAGER_GENERATOR_CONSUMERS = frozenset({
    "all", "any", "frozenset", "list", "max", "min", "set",
    "sorted", "sum", "tuple",
})
def _mark_eager_generator_calls(tree: ast.Module, src: str, fp: str) -> None:
    resolver = ScopeNameResolver(src, fp, tree, set())
    consumers = tuple(_EAGER_GENERATOR_CONSUMERS)
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            node._jwsgj_eager_generator = _call_matches_keywords(
                node, consumers, resolver)
def _iter_comprehension_name_events(node, force_eager: bool = False):
    first = node.generators[0]
    yield from _iter_expression_name_events(first.iter)
    if _is_literal_empty_iterable(first.iter):
        return
    certain = (_is_literal_nonempty_iterable(first.iter)
               and (not isinstance(node, ast.GeneratorExp) or force_eager))
    optional = []
    stopped = False
    for index, generator in enumerate(node.generators):
        if index:
            events = list(_iter_expression_name_events(generator.iter))
            if certain:
                yield from events
            else:
                optional.extend(events)
            if _is_literal_empty_iterable(generator.iter):
                stopped = True
                break
            certain = certain and _is_literal_nonempty_iterable(generator.iter)
        for condition in generator.ifs:
            events = list(_iter_expression_name_events(condition))
            if certain:
                yield from events
            else:
                optional.extend(events)
            truth = _constant_truth_value(condition)
            if truth is False:
                stopped = True
                break
            certain = certain and truth is True
        if stopped:
            break
    if not stopped:
        outputs = ((node.key, node.value) if isinstance(node, ast.DictComp)
                   else (node.elt,))
        for output in outputs:
            events = list(_iter_expression_name_events(output))
            if certain:
                yield from events
            else:
                optional.extend(events)
    if optional:
        yield from _iter_exclusive_name_events([optional, []])
def _iter_assign_name_events(stmt: ast.Assign):
    yield from _iter_expression_name_events(stmt.value)
    for target in stmt.targets:
        yield from _iter_expression_name_events(target)


def _iter_annassign_name_events(stmt: ast.AnnAssign):
    if stmt.value is not None:
        yield from _iter_expression_name_events(stmt.value)
        yield from _iter_expression_name_events(stmt.target)
    yield from _iter_expression_name_events(stmt.annotation)


def _iter_augassign_name_events(stmt: ast.AugAssign):
    if isinstance(stmt.target, ast.Name):
        yield "load", stmt.target.id, stmt.target.lineno
    else:
        yield from _iter_expression_name_events(stmt.target)
    yield from _iter_expression_name_events(stmt.value)
    if isinstance(stmt.target, ast.Name):
        yield "bind", stmt.target.id, stmt.target.lineno


def _iter_import_name_events(stmt):
    for alias in stmt.names:
        if alias.name == "*":
            continue
        name = alias.asname or (
            alias.name.split(".")[0] if isinstance(stmt, ast.Import)
            else alias.name)
        yield "bind", name, stmt.lineno


def _iter_def_name_events(stmt):
    """函数 / 类定义：先发装饰器与定义位表达式，再绑定自身名字。

    类作用域特殊：类体内只有 ``load`` 与 ``global`` 声明名会外泄到模块作用域。
    """
    yield from _iter_definition_name_events(stmt)
    if isinstance(stmt, ast.ClassDef):
        class_global_names = exec_scope_declarations(stmt)[1]
        for class_stmt in stmt.body:
            for kind, name, line in _iter_statement_name_events(class_stmt):
                if kind == "load" or name in class_global_names:
                    yield kind, name, line
    yield "bind", stmt.name, stmt.lineno


def _loop_break_lines(body: list) -> list[int]:
    lines: set[int] = set()
    stack = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Break):
            lines.add(node.lineno)
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef,
                             ast.For, ast.AsyncFor, ast.While)):
            continue
        stack.extend(ast.iter_child_nodes(node))
    return sorted(lines)
def _statement_name_events_before(body: list, line: int) -> list:
    events = []
    for child in body:
        cloned = _statement_prefix_before(child, line)
        if cloned is not None:
            events.extend(_iter_statement_name_events(cloned))
    return events
def _loop_break_finally_name_events(stmt, break_line: int) -> list:
    finalbies = []
    for node in ast.walk(stmt):
        if not isinstance(node, TRY_TYPES) or not node.finalbody:
            continue
        end_line = getattr(node, "end_lineno", node.lineno) or node.lineno
        if not node.lineno <= break_line <= end_line:
            continue
        in_finalbody = any(
            child.lineno <= break_line <= (
                getattr(child, "end_lineno", child.lineno) or child.lineno)
            for child in node.finalbody)
        if not in_finalbody:
            finalbies.append(node)
    finalbies.sort(key=lambda node: (
        (getattr(node, "end_lineno", node.lineno) or node.lineno)
        - node.lineno, -node.lineno))
    events = []
    for node in finalbies:
        final_breaks = _loop_break_lines(node.finalbody)
        if final_breaks:
            events.extend(_statement_name_events_before(
                node.finalbody, final_breaks[0]))
        else:
            for child in node.finalbody:
                events.extend(_iter_statement_name_events(child))
    return events
def _loop_break_name_events(stmt) -> list[list]:
    """break 路径的名字事件流。

    ``break`` 能执行说明循环体至少进入过一次, 因此 ``for`` / ``async for``
    的循环目标在 break 路径上必然已经绑定; 缺失这条绑定会把
    ``for x in [1]: break`` 之后的合法使用误判为未定义。
    """
    target_events = (
        list(_iter_expression_name_events(stmt.target))
        if isinstance(stmt, (ast.For, ast.AsyncFor)) else [])
    paths = []
    for break_line in _loop_break_lines(stmt.body):
        events = [*target_events,
                  *_statement_name_events_before(stmt.body, break_line)]
        events.extend(_loop_break_finally_name_events(stmt, break_line))
        paths.append(events)
    return paths
def _iter_loop_completion_name_events(
        stmt, body_events: list, else_events: list, certain: bool):
    break_paths = _loop_break_name_events(stmt)
    if certain and not break_paths:
        yield from (*body_events, *else_events)
        return
    paths = [[*body_events, *else_events]]
    if not certain:
        paths.append(else_events)
    paths.extend(break_paths)
    yield from _iter_exclusive_name_events(paths)
def _iter_for_name_events(stmt):
    yield from _iter_expression_name_events(stmt.iter)
    if _is_literal_empty_iterable(stmt.iter):
        for child in stmt.orelse:
            yield from _iter_statement_name_events(child)
        return
    body_events = [
        *_iter_expression_name_events(stmt.target),
        *(event for child in stmt.body
          for event in _iter_statement_name_events(child)),
    ]
    else_events = [event for child in stmt.orelse
                   for event in _iter_statement_name_events(child)]
    yield from _iter_loop_completion_name_events(
        stmt, body_events, else_events,
        _is_literal_nonempty_iterable(stmt.iter))


def _iter_with_name_events(stmt):
    for item in stmt.items:
        yield from _iter_expression_name_events(item.context_expr)
        yield from _iter_expression_name_events(item.optional_vars)
    for child in stmt.body:
        yield from _iter_statement_name_events(child)


def _collect_binding_events(nodes) -> list:
    return [
        event for child in nodes
        for event in _iter_statement_name_events(child)
        if event[0] in {"bind", "unbind"} and event[1]
    ]


def _iter_if_name_events(stmt: ast.If):
    yield from _iter_expression_name_events(stmt.test)
    branch = _constant_truth_value(stmt.test)
    if branch is not None:
        for child in (stmt.body if branch else stmt.orelse):
            yield from _iter_statement_name_events(child)
        return
    yield from _iter_exclusive_name_events([
        [event for child in stmt.body
         for event in _iter_statement_name_events(child)],
        [event for child in stmt.orelse
         for event in _iter_statement_name_events(child)],
    ])


def _iter_while_name_events(stmt: ast.While):
    yield from _iter_expression_name_events(stmt.test)
    branch = _constant_truth_value(stmt.test)
    if branch is False:
        for child in stmt.orelse:
            yield from _iter_statement_name_events(child)
        return
    body_events = [event for child in stmt.body
                   for event in _iter_statement_name_events(child)]
    else_events = [event for child in stmt.orelse
                   for event in _iter_statement_name_events(child)]
    yield from _iter_loop_completion_name_events(
        stmt, body_events, else_events, branch is True)


def _iter_match_name_events(stmt: ast.Match):
    yield from _iter_expression_name_events(stmt.subject)
    capture_names = sorted({
        name for case in stmt.cases
        for name in iter_pattern_capture_names(case.pattern)})

    def _case_name_events(case):
        for name in iter_pattern_capture_names(case.pattern):
            yield "bind", name, case.pattern.lineno
        if case.guard is not None:
            yield from _iter_expression_name_events(case.guard)
        for child in case.body:
            yield from _iter_statement_name_events(child)

    def _case_binding_events(case):
        bindings = [
            ("bind", name, case.pattern.lineno)
            for name in iter_pattern_capture_names(case.pattern)
        ]
        if case.guard is not None:
            bindings.extend(
                event for event in _iter_expression_name_events(case.guard)
                if event[0] in {"bind", "unbind"} and event[1])
        for child in case.body:
            bindings.extend(
                event for event in _iter_statement_name_events(child)
                if event[0] in {"bind", "unbind"} and event[1])
        return bindings

    case_bindings = [(case, _case_binding_events(case))
                     for case in stmt.cases]
    affected_names = sorted(set(capture_names) | {
        event[1] for _case, bindings in case_bindings
        for event in bindings})
    for case, _bindings in case_bindings:
        for name in affected_names:
            yield "checkpoint", name, case.pattern.lineno
        yield from _case_name_events(case)
        for name in affected_names:
            yield "restore", name, case.pattern.lineno
    guaranteed_index = next(
        (index for index, case in enumerate(stmt.cases)
         if _irrefutable_case(case)), None)
    if guaranteed_index is not None:
        reachable = case_bindings[:guaranteed_index + 1]
        yield from _merge_exclusive_binding_events(
            [bindings for _case, bindings in reachable])


def _iter_try_name_events(stmt):
    """``try`` 家族：``ast.Try`` 的处理器互斥；``TryStar`` 处理器按并集处理，再与 ``else`` 互斥合并。"""
    if not _strip_noop_statements(stmt.body):
        for child in (*stmt.orelse, *stmt.finalbody):
            yield from _iter_statement_name_events(child)
        return
    for child in stmt.body:
        yield from _iter_statement_name_events(child)
    handler_names = sorted({
        handler.name for handler in stmt.handlers if handler.name})
    handler_branch_bindings = []
    for handler in stmt.handlers:
        branch_bindings = [
            event for event in _iter_expression_name_events(handler.type)
            if event[0] in {"bind", "unbind"} and event[1]
        ]
        if handler.name:
            branch_bindings.append(("bind", handler.name, handler.lineno))
        for child in handler.body:
            branch_bindings.extend(
                event for event in _iter_statement_name_events(child)
                if event[0] in {"bind", "unbind"} and event[1])
        handler_branch_bindings.append(branch_bindings)
    handler_bindings = [
        event for branch in handler_branch_bindings for event in branch]
    affected_names = sorted(set(handler_names) | {
        event[1] for event in handler_bindings})
    exclusive_handlers = isinstance(stmt, ast.Try)
    if not exclusive_handlers:
        for name in affected_names:
            yield "checkpoint", name, stmt.lineno
    for handler in stmt.handlers:
        if exclusive_handlers:
            for name in affected_names:
                yield "checkpoint", name, handler.lineno
        yield from _iter_expression_name_events(handler.type)
        if handler.name:
            yield "bind", handler.name, handler.lineno
        for child in handler.body:
            yield from _iter_statement_name_events(child)
        if exclusive_handlers:
            for name in affected_names:
                yield "restore", name, handler.lineno
    if not exclusive_handlers:
        for name in affected_names:
            yield "restore", name, stmt.lineno
    else_bindings = _collect_binding_events(stmt.orelse)
    merge_names = sorted(set(affected_names) | {
        event[1] for event in else_bindings})
    for name in merge_names:
        yield "checkpoint", name, stmt.lineno
    for child in stmt.orelse:
        yield from _iter_statement_name_events(child)
    for name in merge_names:
        yield "restore", name, stmt.lineno
    if exclusive_handlers:
        yield from _merge_exclusive_binding_events(
            [*handler_branch_bindings, else_bindings])
    else:
        # except* 的各处理器可同时执行（上方按并集处理），但 else 仅在无处理器
        # 执行时运行、且处理器可能一个都不执行：后置状态须把处理器并集与
        # else（缺省即空分支）按互斥路径合并，不能把处理器内绑定直接沿用。
        yield from _merge_exclusive_binding_events(
            [handler_bindings, else_bindings])
    for name in handler_names:
        yield "unbind", name, stmt.lineno
    for child in stmt.finalbody:
        yield from _iter_statement_name_events(child)


def _iter_statement_name_events(stmt):
    """语句 → 名字事件流（``bind`` / ``unbind`` / ``load`` / 检查点）。

    各语句族下沉到独立生成器，本函数只做分发；未命中的语句按子节点
    递归兜底。拆分前后事件流逐条等价。
    """
    if isinstance(stmt, ast.Assign):
        yield from _iter_assign_name_events(stmt)
        return
    if isinstance(stmt, ast.AnnAssign):
        yield from _iter_annassign_name_events(stmt)
        return
    if isinstance(stmt, ast.AugAssign):
        yield from _iter_augassign_name_events(stmt)
        return
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        yield from _iter_import_name_events(stmt)
        return
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        yield from _iter_def_name_events(stmt)
        return
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        yield from _iter_for_name_events(stmt)
        return
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        yield from _iter_with_name_events(stmt)
        return
    if isinstance(stmt, ast.If):
        yield from _iter_if_name_events(stmt)
        return
    if isinstance(stmt, ast.While):
        yield from _iter_while_name_events(stmt)
        return
    if isinstance(stmt, ast.Match):
        yield from _iter_match_name_events(stmt)
        return
    if isinstance(stmt, TRY_TYPES):
        yield from _iter_try_name_events(stmt)
        return
    for child in ast.iter_child_nodes(stmt):
        if isinstance(child, ast.stmt):
            yield from _iter_statement_name_events(child)
        elif isinstance(child, ast.expr):
            yield from _iter_expression_name_events(child)

def _load_binding_status(
        body: list, line: int, name: str, initial: bool = False,
) -> bool | None:
    bound = initial
    checkpoints: list[bool] = []
    bound_load = False
    for stmt in body:
        for kind, event_name, event_line in _iter_statement_name_events(stmt):
            if event_name != name:
                continue
            if kind == "bind":
                bound = True
            elif kind == "unbind":
                bound = False
            elif kind == "checkpoint":
                checkpoints.append(bound)
            elif kind == "restore":
                bound = checkpoints.pop()
            elif event_line == line:
                if not bound:
                    return True
                bound_load = True
    return False if bound_load else None
def _symbols_declared_before(
        body: list, line: int, name: str | None = None) -> set[str]:
    prefix = []
    for stmt in body:
        cloned = _statement_prefix_before(stmt, line)
        if cloned is not None:
            prefix.append(cloned)
    declared = build_module_symbol_table(ast.Module(
        body=prefix, type_ignores=[]))
    if name is not None:
        binding_status = _load_binding_status(body, line, name)
        if binding_status is True:
            declared.discard(name)
        elif binding_status is False:
            declared.add(name)
    return declared
def _node_span_len(node) -> int:
    return ((getattr(node, "end_lineno", node.lineno) or node.lineno)
            - node.lineno)
def _innermost_node(nodes: list):
    return min(nodes, key=lambda node: (_node_span_len(node), -node.lineno))
def _innermost_execution_class(
    tree: ast.Module, line: int, function_scopes: list,
) -> ast.ClassDef | None:
    classes = _covering_nodes(tree, line, (ast.ClassDef,))
    if not classes:
        return None
    innermost = _innermost_node(classes)
    if (function_scopes and _node_span_len(function_scopes[-1])
            <= _node_span_len(innermost)):
        return None
    return innermost
def _name_binding_state(
    body: list, name: str, line: int | None = None, initial: bool = False,
) -> bool:
    bound = initial
    checkpoints: list[bool] = []
    for original in body:
        stmt = (original if line is None
                else _statement_prefix_before(original, line))
        if stmt is None:
            continue
        for kind, event_name, _event_line in _iter_statement_name_events(stmt):
            if event_name != name:
                continue
            if kind == "bind":
                bound = True
            elif kind == "unbind":
                bound = False
            elif kind == "checkpoint":
                checkpoints.append(bound)
            elif kind == "restore":
                bound = checkpoints.pop()
    return bound
def _name_has_later_binding(body: list, name: str, line: int) -> bool:
    for stmt in body:
        for kind, event_name, event_line in _iter_statement_name_events(stmt):
            if kind == "bind" and event_name == name and event_line > line:
                return True
    return False
def _covering_exception_handlers(tree: ast.Module, line: int) -> list:
    return [
        node for node in walk_nodes(tree)
        if isinstance(node, ast.ExceptHandler)
        and node.lineno <= line <= (
            getattr(node, "end_lineno", node.lineno) or node.lineno)
    ]
def _active_exception_handler_names(tree: ast.Module, line: int) -> set[str]:
    names: set[str] = set()
    for node in _covering_exception_handlers(tree, line):
        if not node.name:
            continue
        load_status = _load_binding_status(
            node.body, line, node.name, initial=True)
        if load_status is True:
            continue
        if (load_status is False or _name_binding_state(
                node.body, node.name, line=line, initial=True)):
            names.add(node.name)
    return names
def _unevaluated_annotation_name(
    tree: ast.Module, name: str, line: int,
) -> bool:
    postpone_all = module_postpones_annotations(tree)
    candidates = []
    unevaluated: set[int] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and node.id == name and node.lineno == line):
            candidates.append(node)
        annotation = None
        skip_annotation = postpone_all
        if isinstance(node, ast.arg):
            annotation = node.annotation
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            annotation = node.returns
        elif isinstance(node, ast.AnnAssign):
            annotation = node.annotation
            if not skip_annotation and any(
                    isinstance(child, ast.Name) and child.id == name
                    and child.lineno == line
                    for child in walk_nodes(annotation)):
                owners = _covering_nodes(
                    tree, node.lineno,
                    (ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.Lambda, ast.ClassDef))
                skip_annotation = bool(owners) and isinstance(
                    _innermost_node(owners),
                    (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
        if annotation is not None and skip_annotation:
            unevaluated.update(
                id(child) for child in walk_nodes(annotation)
                if isinstance(child, ast.Name))
    return bool(candidates) and all(
        id(node) in unevaluated for node in candidates)
def _function_header_owner(scopes: list, name: str, line: int):
    for node in reversed(scopes):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if any(kind == "load" and event_name == name and event_line == line
               for kind, event_name, event_line
               in _iter_definition_name_events(node)):
            return node
    return None
def _function_scope_symbols(
    tree: ast.Module, line: int, name: str,
    active_handler_names: set[str], scopes: list | None = None,
    inactive_handler_names: set[str] | None = None,
) -> set[str] | None:
    if scopes is None:
        scopes = _covering_function_scopes(tree, line)
    if not scopes:
        return set(active_handler_names)
    symbols: set[str] = set(active_handler_names)
    for node in scopes:
        symbols.update(_scope_parameter_names(node))
    innermost = scopes[-1]
    inner_before = _symbols_declared_before(innermost.body, line, name) \
        if isinstance(innermost.body, list) else set()
    if isinstance(innermost.body, list):
        inner_tree = ast.Module(body=innermost.body, type_ignores=[])
        inner_all = build_module_symbol_table(inner_tree)
        inner_local, inner_globals = exec_scope_declarations(inner_tree)
        if name in inner_globals:
            return set()
        inner_all.update(inner_local)
        inner_visible = (
            _scope_parameter_names(innermost) | inner_before
            | active_handler_names | _nonlocal_names(innermost))
        if name in inner_all and name not in inner_visible:
            return None
    symbols.update(inner_before)
    for node in scopes[:-1]:
        if isinstance(node.body, list):
            outer_symbols = build_module_symbol_table(ast.Module(
                body=node.body, type_ignores=[]))
            for inactive_name in inactive_handler_names or ():
                if _name_has_later_binding(node.body, inactive_name, line):
                    outer_symbols.add(inactive_name)
                else:
                    outer_symbols.discard(inactive_name)
            symbols.update(outer_symbols)
    return symbols
_LEXICAL_SCOPE_BOUNDARIES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
)
def _bare_annotation_names(body: list) -> set[str]:
    names: set[str] = set()
    stack = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, _LEXICAL_SCOPE_BOUNDARIES):
            continue
        if (isinstance(node, ast.AnnAssign) and node.value is None
                and isinstance(node.target, ast.Name)):
            names.add(node.target.id)
        stack.extend(ast.iter_child_nodes(node))
    return names
def _scope_binding_names(body: list) -> set[str]:
    return {
        event_name for stmt in body
        for kind, event_name, _event_line in _iter_statement_name_events(stmt)
        if kind == "bind"
    }
def _scope_global_names(node) -> set[str]:
    scope = ast.Module(body=node.body, type_ignores=[])
    return exec_scope_declarations(scope)[1]
def _delegated_binding_map(
    tree: ast.Module, parents: dict,
) -> dict[int, set[str]]:
    delegated: dict[int, set[str]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        writes = _scope_binding_names(node.body)
        for name in writes & _scope_global_names(node):
            delegated.setdefault(id(tree), set()).add(name)
        for name in writes & _nonlocal_names(node):
            current = parents.get(node)
            while current is not None:
                if isinstance(current,
                              (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if (name in _scope_global_names(current)
                            or name in _nonlocal_names(current)):
                        current = parents.get(current)
                        continue
                    declarations = (
                        _scope_parameter_names(current)
                        | _scope_binding_names(current.body)
                        | _bare_annotation_names(current.body)
                    )
                    if name in declarations:
                        delegated.setdefault(id(current), set()).add(name)
                        break
                current = parents.get(current)
    return delegated
def _module_delegated_binding_names(tree: ast.Module) -> set[str]:
    parents = {
        child: parent for parent in walk_nodes(tree)
        for child in ast.iter_child_nodes(parent)
    }
    return _delegated_binding_map(tree, parents).get(id(tree), set())
def _has_annotation_only_binding(
    tree: ast.Module, name: str, line: int,
) -> bool:
    parents = {
        child: parent for parent in walk_nodes(tree)
        for child in ast.iter_child_nodes(parent)
    }
    owners = [
        node for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef))
        and node.lineno <= line <= (
            getattr(node, "end_lineno", node.lineno) or node.lineno)
    ]
    function_scopes = [
        node for node in owners
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    header_owner = _function_header_owner(function_scopes, name, line)
    owners = [node for node in owners if node is not header_owner]
    if any(name in _scope_global_names(node) for node in owners):
        owners = []
    delegated = _delegated_binding_map(tree, parents)
    for owner in [tree, *owners]:
        bindings = (
            _scope_binding_names(owner.body)
            | delegated.get(id(owner), set())
        )
        if isinstance(owner, ast.ClassDef):
            bindings |= delegated.get(id(tree), set())
        if (name in _bare_annotation_names(owner.body)
                and name not in bindings):
            return True
    return False
def _lexical_name_status(
    fp: str, tree: ast.Module, name: str, line: int,
    fallback_names: set[str],
) -> bool | None:
    nodes = [
        node for node in walk_nodes(tree)
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
            and node.id == name and node.lineno == line)
    ]
    if not nodes:
        return None
    if _has_annotation_only_binding(tree, name, line):
        return False
    try:
        src = read_source_strict(fp)
    except (OSError, ValueError, RecursionError, MemoryError) as exc:
        log_swallowed(
            __name__, exc,
            context=f'_lexical_name_status:{type(exc).__name__}')
        return None
    resolver = ScopeNameResolver(src, fp, tree, fallback_names)
    return all(resolver.is_bound(node) for node in nodes)
_IMPORT_SYMBOL_UNKNOWN = object()
class TestTriageVerifier:
    __test__ = False
    _EXEC_FAMILIES = ("import_error", "syntax_error", "broken_call",
                      "resource_leak", "unhandled_exception", "broken_import",
                      "undefined_name")
    _IMPORT_FAMILIES = ("import_error", "broken_import")
    _SYMBOL_FAMILIES = ("undefined_name", "broken_call")
    _COMPILE_FAMILIES = ("syntax_error",)
    def __init__(self, skill_dir: str):
        self.skill_dir = _coerce_skill_dir(skill_dir)
    def analyze(self, findings: list[dict]) -> dict:
        results: dict = {}
        _compile_cache: dict = {}
        _import_cache: dict = {}
        _symbol_cache: dict = {}
        for f, loc in _iter_test_triage_located(findings):
            raw_fp = finding_file_path(f)
            rf = finding_rule_family(f)
            fp = anchor_to_skill(raw_fp, self.skill_dir)
            if not is_family_member(rf, self._EXEC_FAMILIES) or not fp or not os.path.isfile(fp):
                results[loc] = {"smoke": None, "detail": "not_exec_family"}
                continue
            if is_family_member(rf, self._IMPORT_FAMILIES):
                results[loc] = self._verify_import(fp, f, _import_cache)
            elif is_family_member(rf, self._SYMBOL_FAMILIES):
                results[loc] = self._verify_symbol(fp, f, _symbol_cache)
            elif is_family_member(rf, self._COMPILE_FAMILIES):
                results[loc] = self._verify_compile(fp, _compile_cache)
            else:
                results[loc] = {
                    "smoke": None,
                    "detail": "runtime_verification_required",
                }
        return results
    def _verify_compile(self, fp: str, cache: dict) -> dict:
        if fp not in cache:
            try:
                src_text = read_source_strict(fp)
                compile(src_text, fp, "exec")
                cache[fp] = {"smoke": "pass", "detail": "compile_ok"}
            except SyntaxError as e:
                log_swallowed(__name__, e, context='TestTriageVerifier._verify_compile:SyntaxError')
                cache[fp] = {"smoke": "fail", "detail": f"syntax:{getattr(e, 'msg', '')}"}
            except (OSError, ValueError, RecursionError, MemoryError) as e:
                log_swallowed(__name__, e, context=(
                    f'TestTriageVerifier._verify_compile:{type(e).__name__}'))
                cache[fp] = {"smoke": None, "detail": type(e).__name__}
        return cache[fp]
    def _verify_import(self, fp: str, finding: dict, cache: dict) -> dict:
        _key = (fp, safe_finding_line(finding))
        if _key in cache:
            return cache[_key]
        result = self._do_import_verify(fp, finding)
        cache[_key] = result
        return result
    @staticmethod
    def _line_imports(tree, target_line: int) -> list:
        line_imports = []
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            _in_range = (node.lineno <= target_line
                         <= getattr(node, "end_lineno", node.lineno))
            if _in_range:
                if isinstance(node, ast.Import):
                    line_imports.extend((node, alias.name)
                                        for alias in node.names)
                else:
                    line_imports.append((node, node.module or ""))
        return line_imports
    def _verify_single_import(self, fp: str, node, mod: str) -> Any:
        _level = getattr(node, "level", 0) or 0
        if _level > 0:
            _names = [a.name for a in node.names]
            _status = self._relative_target_exists(fp, _level, mod, _names)
            if _status is _IMPORT_SYMBOL_UNKNOWN:
                return _IMPORT_SYMBOL_UNKNOWN
            if not _status:
                _label = mod or ("." * _level)
                return f"module_not_found:{_label}"
            return None
        _broken = self._first_missing_prefix(fp, mod)
        if _broken:
            return f"module_not_found:{_broken}"
        if isinstance(node, ast.ImportFrom):
            _names = [alias.name for alias in node.names]
            _missing = self._absolute_missing_name(fp, mod, _names)
            if _missing is _IMPORT_SYMBOL_UNKNOWN:
                return _IMPORT_SYMBOL_UNKNOWN
            if _missing:
                return f"symbol_not_found:{mod}.{_missing}"
        return None
    def _do_import_verify(self, fp: str, finding: dict) -> dict:
        tree, _failure = _load_ast(fp, "TestTriageVerifier._do_import_verify")
        if _failure is not None:
            return _failure
        target_line = safe_finding_line(finding)
        if target_line <= 0:
            return {"smoke": None, "detail": "no_line_context"}
        line_imports = self._line_imports(tree, target_line)
        if not line_imports:
            return {"smoke": None, "detail": "no_import_at_line"}
        unresolved = False
        for node, mod in line_imports:
            _fail = self._verify_single_import(fp, node, mod)
            if _fail is _IMPORT_SYMBOL_UNKNOWN:
                unresolved = True
                continue
            if _fail is not None:
                return {"smoke": "fail", "detail": _fail}
        if unresolved:
            return {"smoke": None, "detail": "import_symbol_unresolved"}
        return {"smoke": "pass", "detail": "all_imports_resolvable"}
    @staticmethod
    def _module_exists(module_name: str) -> bool:
        try:
            return find_spec(module_name) is not None
        except Exception as e: # noqa: BLE001
            logger.debug("[TestTriage] find_spec 异常归模块不可用（%s: %s）: %s",
                         type(e).__name__, e, module_name)
            return False
    @staticmethod
    def _local_module_bases(
        fp: str, skill_dir: str, top_package: str,
    ) -> list[str]:
        if not isinstance(fp, str) or not fp or not top_package:
            return []
        bases: list[str] = [os.path.dirname(os.path.abspath(fp))]
        current = bases[0]
        while True:
            if os.path.basename(current) == top_package:
                bases.append(os.path.dirname(current))
                break
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent
        if isinstance(skill_dir, str) and skill_dir:
            bases.append(os.path.abspath(skill_dir))
        seen: set[str] = set()
        unique: list[str] = []
        for base in bases:
            key = os.path.normcase(base)
            if key not in seen:
                seen.add(key)
                unique.append(base)
        return unique
    def _local_module_exists(self, fp: str, dotted: str) -> bool:
        parts = dotted.split(".")
        if not parts or any(not part for part in parts):
            return False
        for base in self._local_module_bases(fp, self.skill_dir, parts[0]):
            target = os.path.join(base, *parts)
            if os.path.isdir(target) or os.path.isfile(target + ".py"):
                return True
        return False
    def _resolved_top_module_is_local(
            self, fp: str, top_package: str) -> bool:
        try:
            spec = find_spec(top_package)
        except Exception as e: # noqa: BLE001
            logger.debug(
                "[TestTriage] 顶层模块解析异常（%s: %s）: %s",
                type(e).__name__, e, top_package)
            return False
        if spec is None:
            return False
        locations = list(
            getattr(spec, "submodule_search_locations", None) or [])
        origin = getattr(spec, "origin", None)
        if origin and origin not in {"built-in", "frozen"}:
            locations.append(origin)
        bases = [
            os.path.normcase(os.path.abspath(base))
            for base in self._local_module_bases(
                fp, self.skill_dir, top_package)
        ]
        for location in locations:
            if not isinstance(location, (str, os.PathLike)):
                continue
            resolved = os.path.normcase(os.path.abspath(location))
            if any(resolved == base
                   or resolved.startswith(base.rstrip(os.sep) + os.sep)
                   for base in bases):
                return True
        return False
    def _first_missing_prefix(self, fp: str, dotted: str) -> str:
        parts = dotted.split(".")
        if not parts:
            return ""
        top_resolvable = self._module_exists(parts[0])
        allow_local_fallback = (
            not top_resolvable
            or self._resolved_top_module_is_local(fp, parts[0]))
        for i in range(1, len(parts) + 1):
            prefix = ".".join(parts[:i])
            if self._module_exists(prefix):
                continue
            if (allow_local_fallback
                    and self._local_module_exists(fp, prefix)):
                continue
            return prefix
        return ""
    @staticmethod
    def _names_status(symbols, names: list) -> bool | None:
        if symbols is None or "*" in symbols or "__getattr__" in symbols:
            return None
        return all(name == "*" or name in symbols for name in names)
    @classmethod
    def _package_dir_missing_name(cls, base: str, names: list) -> Any:
        pkg_syms = package_init_symbols(base)
        if (pkg_syms is None
                and os.path.isfile(os.path.join(base, "__init__.py"))):
            return _IMPORT_SYMBOL_UNKNOWN
        status = cls._names_status(pkg_syms, names)
        if status is True:
            return None
        for name in names:
            if name == "*":
                continue
            if cls._relative_import_symbol_exists(base, name, pkg_syms):
                continue
            if status is None:
                return _IMPORT_SYMBOL_UNKNOWN
            return name
        return None
    @classmethod
    def _module_file_missing_name(cls, module_file: str,
                                  names: list) -> Any:
        syms = cls._module_file_symbols(module_file)
        status = cls._names_status(syms, names)
        if status is None:
            return _IMPORT_SYMBOL_UNKNOWN
        if status is True:
            return None
        for name in names:
            if name != "*" and name not in syms:
                return name
        return None
    def _local_missing_name(self, fp: str, module: str,
                            names: list) -> tuple[bool, Any]:
        for base in self._local_module_bases(
                fp, self.skill_dir, module.split(".")[0]):
            target = os.path.join(base, *module.split("."))
            if os.path.isdir(target):
                return True, self._package_dir_missing_name(target, names)
            module_file = target + ".py"
            if os.path.isfile(module_file):
                return True, self._module_file_missing_name(module_file, names)
        return False, None
    def _spec_missing_name(self, module: str, names: list) -> Any:
        try:
            spec = find_spec(module)
        except Exception as e: # noqa: BLE001
            logger.debug("[TestTriage] find_spec 失败，导入名不判定: %s: %s",
                         type(e).__name__, module)
            return _IMPORT_SYMBOL_UNKNOWN
        if spec is None:
            return _IMPORT_SYMBOL_UNKNOWN
        locations = getattr(spec, "submodule_search_locations", None)
        if locations:
            return self._locations_missing_name(locations, names)
        origin = getattr(spec, "origin", None)
        if not (isinstance(origin, str) and origin.endswith(".py")
                and os.path.isfile(origin)):
            _loaded = sys.modules.get(module)
            origin = getattr(_loaded, "__file__", None)
        if (isinstance(origin, str) and origin.endswith(".py")
                and os.path.isfile(origin)):
            return self._module_file_missing_name(origin, names)
        return _IMPORT_SYMBOL_UNKNOWN
    def _locations_missing_name(self, locations, names: list) -> Any:
        missing_names: list[str] = []
        unresolved = False
        for location in locations:
            if not isinstance(location, str) or not os.path.isdir(location):
                continue
            missing = self._package_dir_missing_name(location, names)
            if missing is None:
                return None
            if missing is _IMPORT_SYMBOL_UNKNOWN:
                unresolved = True
            else:
                missing_names.append(missing)
        if unresolved:
            return _IMPORT_SYMBOL_UNKNOWN
        return missing_names[0] if missing_names else _IMPORT_SYMBOL_UNKNOWN
    def _absolute_missing_name(self, fp: str, module: str,
                               names: list) -> Any:
        top_package = module.split(".", 1)[0]
        allow_local = (
            not self._module_exists(top_package)
            or self._resolved_top_module_is_local(fp, top_package))
        if allow_local:
            found_local, local_missing = self._local_missing_name(
                fp, module, names)
            if found_local:
                return local_missing
        return self._spec_missing_name(module, names)
    @staticmethod
    def _relative_import_symbol_exists(base: str, name: str, pkg_syms) -> bool:
        if name == "*":
            return True
        candidate = os.path.join(base, name)
        return any((
            os.path.isdir(candidate),
            os.path.isfile(candidate + ".py"),
            pkg_syms is not None and name in pkg_syms,
        ))
    @classmethod
    def _relative_package_symbols_exist(cls, base: str, names: list) -> Any:
        pkg_syms = package_init_symbols(base)
        status = cls._names_status(pkg_syms, names)
        if status is True:
            return True
        if status is None and (
                pkg_syms is not None
                or os.path.isfile(os.path.join(base, "__init__.py"))):
            return _IMPORT_SYMBOL_UNKNOWN
        return all(
            cls._relative_import_symbol_exists(base, name, pkg_syms)
            for name in names
        )
    @staticmethod
    def _module_file_symbols(module_file: str) -> frozenset[str] | None:
        try:
            src = read_source_strict(module_file)
            tree = parse_cached(src, filename=module_file)
        except (SyntaxError, ValueError, OSError, RecursionError,
                MemoryError) as exc:
            log_swallowed(
                __name__, exc,
                context=f'TestTriageVerifier._module_file_symbols:{type(exc).__name__}')
            return None
        return frozenset(build_module_symbol_table(tree))
    @staticmethod
    def _relative_target_exists(fp: str, level: int, module: str, names: list) -> Any:
        base = os.path.dirname(os.path.abspath(fp))
        for _ in range(max(level - 1, 0)):
            base = os.path.dirname(base)
        if module:
            target = os.path.join(base, *module.split("."))
            if os.path.isdir(target):
                return TestTriageVerifier._relative_package_symbols_exist(
                    target, names)
            module_file = target + ".py"
            if not os.path.isfile(module_file):
                return False
            missing = TestTriageVerifier._module_file_missing_name(
                module_file, names)
            if missing is _IMPORT_SYMBOL_UNKNOWN:
                return _IMPORT_SYMBOL_UNKNOWN
            return missing is None
        return TestTriageVerifier._relative_package_symbols_exist(
            base, names)
    @staticmethod
    def _symbol_verify_mode(finding: dict) -> str:
        """验证通道：broken_call 需按 ``模块.符号`` 核对被调模块。"""
        return ("broken_call"
                if is_family_member(finding_rule_family(finding),
                                    ("broken_call",))
                else "symbol")
    def _verify_symbol(self, fp: str, finding: dict, cache: dict) -> dict:
        _key = (fp, self._extract_claimed_name(finding),
                safe_finding_line(finding), self._symbol_verify_mode(finding))
        if _key in cache:
            return cache[_key]
        result = self._do_symbol_verify(fp, finding)
        cache[_key] = result
        return result
    def _do_symbol_verify(self, fp: str, finding: dict) -> dict:
        name = self._extract_claimed_name(finding)
        if not name:
            return {"smoke": None, "detail": "no_name_in_finding"}
        tree, _failure = _load_ast(
            fp, "TestTriageVerifier._do_symbol_verify",
            mark_generator_calls=True)
        if _failure is not None:
            return _failure
        target_line = safe_finding_line(finding)
        if target_line <= 0:
            return {"smoke": None, "detail": "no_line_context"}
        if self._symbol_verify_mode(finding) == "broken_call":
            return self._verify_broken_call_target(fp, name)
        if _unevaluated_annotation_name(tree, name, target_line):
            return {"smoke": "pass",
                    "detail": f"name_annotation_not_evaluated:{name}"}
        symbols = build_module_symbol_table(tree)
        covering_handlers = _covering_exception_handlers(tree, target_line)
        active_handler_names = _active_exception_handler_names(tree, target_line)
        inactive_handler_names = {
            node.name for node in covering_handlers if node.name
        } - active_handler_names
        for inactive_name in inactive_handler_names:
            if _name_has_later_binding(
                    tree.body, inactive_name, target_line):
                symbols.add(inactive_name)
            else:
                symbols.discard(inactive_name)
        scopes = _covering_function_scopes(tree, target_line)
        header_owner = _function_header_owner(scopes, name, target_line)
        if header_owner is not None:
            scopes = [node for node in scopes if node is not header_owner]
        class_scope = _innermost_execution_class(tree, target_line, scopes)
        class_before: set[str] = set()
        class_all: set[str] = set()
        if class_scope is not None:
            class_before = _symbols_declared_before(
                class_scope.body, target_line, name)
            class_tree = ast.Module(body=class_scope.body, type_ignores=[])
            class_all = build_module_symbol_table(class_tree)
            class_all.update(exec_scope_declarations(class_tree)[0])
            class_all.update(_bare_annotation_names(class_scope.body))
        class_local_unbound = (
            class_scope is not None and name in class_all
            and name not in class_before)
        module_delegated = (
            _module_delegated_binding_names(tree)
            if class_local_unbound else set())
        if not scopes:
            declared_before = _symbols_declared_before(
                tree.body, target_line, name)
            declared_before |= class_before | module_delegated
            execution_names = (
                symbols | class_all | exec_scope_declarations(tree)[0])
            if (name in execution_names and name not in declared_before
                    and name not in active_handler_names
                    and name not in BUILTIN_NAMES):
                return {"smoke": "fail", "detail": f"name_undefined:{name}",
                        "symbol_level": True}
            symbols = declared_before
        function_symbols = _function_scope_symbols(
            tree, target_line, name, active_handler_names, scopes=scopes,
            inactive_handler_names=inactive_handler_names)
        if function_symbols is None:
            return {"smoke": "fail", "detail": f"name_undefined:{name}",
                    "symbol_level": True}
        if class_local_unbound:
            function_symbols = set()
            symbols |= module_delegated
        symbols |= function_symbols
        symbols |= class_before
        symbols |= BUILTIN_NAMES
        if class_scope is not None and name in class_all and name not in symbols:
            return {"smoke": "fail", "detail": f"name_undefined:{name}",
                    "symbol_level": True}
        if name in inactive_handler_names and name not in symbols:
            return {"smoke": "fail", "detail": f"name_undefined:{name}",
                    "symbol_level": True}
        if name in symbols:
            return {"smoke": "pass", "detail": f"name_defined:{name}"}
        lexical_status = _lexical_name_status(
            fp, tree, name, target_line, symbols)
        if lexical_status is True:
            return {"smoke": "pass", "detail": f"name_defined:{name}"}
        return {"smoke": "fail", "detail": f"name_undefined:{name}",
                "symbol_level": True}
    def _verify_broken_call_target(self, fp: str, name: str) -> dict:
        """跨模块调用断裂：按 ``模块.符号`` 复核**被调模块**的定义面。

        调用方文件自身的符号表不包含 ``模块.符号`` 这种点号名, 直接拿调用方
        符号表核对必然得出 ``name_undefined``, 会把真实缺失与误报一并抬高
        置信度; 这里改为先定位目标模块, 只核对末段符号。定位不到目标模块
        时返回 ``smoke=None``, 不调整置信度。
        """
        module, _sep, symbol = name.rpartition(".")
        if not (module and symbol):
            return {"smoke": None, "detail": "broken_call_target_unresolved"}
        if module == "__init__":
            init_file = os.path.join(self.skill_dir, "__init__.py")
            if not os.path.isfile(init_file):
                return {"smoke": None,
                        "detail": "broken_call_target_unresolved"}
            missing = self._module_file_missing_name(init_file, [symbol])
        else:
            found_local, missing = self._local_missing_name(
                fp, module, [symbol])
            if not found_local:
                return {"smoke": None,
                        "detail": "broken_call_target_unresolved"}
        if missing is _IMPORT_SYMBOL_UNKNOWN:
            return {"smoke": None, "detail": "broken_call_target_unresolved"}
        if missing is None:
            return {"smoke": "pass", "detail": f"name_defined:{name}"}
        return {"smoke": "fail", "detail": f"name_undefined:{name}",
                "symbol_level": True}
    @staticmethod
    def _extract_claimed_name(finding: dict) -> str:
        _detail = finding.get("detail")
        if isinstance(_detail, dict):
            _v = _detail.get("name")
            if isinstance(_v, str) and _v.strip():
                return _v.strip()
        name = first_symbol_field(
            finding, ("name", "symbol", "identifier", "var_name"))
        if name:
            return name
        return _quoted_identifier_in_message(
            str(finding.get("message", ""))) or ""
def _iter_test_triage_located(findings):
    if isinstance(findings, str) or not isinstance(findings, (list, tuple)):
        if findings:
            logger.warning("[XV] findings 非清单形态,跳过整段: %r",
                           type(findings).__name__)
        return
    items = [f for f in findings if isinstance(f, dict)]
    names_by_loc = {}
    for f in items:
        if is_family_member(
                finding_rule_family(f), TestTriageVerifier._SYMBOL_FAMILIES):
            loc = channel_locator(f)
            names_by_loc.setdefault(loc, set()).add(
                TestTriageVerifier._extract_claimed_name(f))
    for f in items:
        loc = channel_locator(f)
        if len(names_by_loc.get(loc, ())) > 1:
            name = TestTriageVerifier._extract_claimed_name(f)
            loc = f"{loc}::symbol={name}"
        yield f, loc
def annotate_findings_with_vcs(findings: list[dict], results: dict) -> list[dict]:
    findings, results = _normalize_annotate_input(findings, results)
    for f, r in _iter_signal_pairs(findings, results):
        if r.get("boost"):
            f["_vcs_recency_boost"] = True
            f["_vcs_recency_method"] = _signal_str(r.get("method"))
            f["_vcs_recency_detail"] = _signal_str(r.get("detail"))
            _boost = vcs_recency_confidence_boost()
            adjust_finding_confidence(f, _boost, increasing=True)
    return findings
def _apply_test_triage_smoke(f: dict, r: dict) -> None:
    smoke = r.get("smoke")
    if smoke is None:
        return
    f["_test_triage_detail"] = _signal_str(r.get("detail"))
    if smoke == "pass":
        f["_test_triage_smoke_pass"] = True
        adjust_finding_confidence(
            f, -test_triage_confidence_boost("pass"), increasing=False)
    elif smoke == "fail":
        f["_test_triage_smoke_fail"] = True
        if r.get("symbol_level"):
            f["_test_triage_symbol_level_fail"] = True
        adjust_finding_confidence(
            f, test_triage_confidence_boost("fail"), increasing=True)
def annotate_findings_with_test_triage(findings: list[dict], results: dict) -> list[dict]:
    findings, results = _normalize_annotate_input(findings, results)
    for f, loc in _iter_test_triage_located(findings):
        r = results.get(loc)
        if isinstance(r, dict):
            _apply_test_triage_smoke(f, r)
    return findings
def package_init_symbols(pkg_dir: str) -> frozenset[str] | None:
    init = os.path.join(pkg_dir, "__init__.py")
    if not os.path.isfile(init):
        return None
    try:
        _src = read_source_strict(init)
        _tree = parse_cached(_src, filename=init)
    except (SyntaxError, ValueError, OSError, RecursionError,
            MemoryError) as _e:
        log_swallowed(__name__, _e,
                      context=f'package_init_symbols:{type(_e).__name__}')
        return None
    return frozenset(build_module_symbol_table(_tree))
_FN_INDEX_SNAPSHOT: list = []
_FN_BUCKETS_SNAPSHOT: list = []
_OUT_DEGREE_SNAPSHOT: list = []
_CALLER_CONTAINER_TYPES = (list, tuple, set, frozenset)
def _norm_path_key(path: str) -> str:
    return os.path.normcase(os.path.normpath(path))
def _callgraph_channel(call_graph: Any, attr: str, expected: type):
    if not hasattr(call_graph, attr):
        return None
    value = getattr(call_graph, attr)
    return value if isinstance(value, expected) else None
def is_usable_call_graph(call_graph: Any) -> bool:
    return isinstance(getattr(call_graph, "functions", None), dict)
def _cached_graph_value(call_graph: Any, snapshot: list, build,
                        version: Any) -> Any:
    cached = snapshot[0] if snapshot else None
    if cached is not None:
        cached_graph, cached_version, cached_value = cached
        if cached_graph is call_graph and cached_version == version:
            return cached_value
    value = build()
    snapshot[:] = [(call_graph, version, value)]
    return value
def _build_fn_entries(functions: dict) -> list[tuple[str, int, int, str]]:
    entries: list[tuple[str, int, int, str]] = []
    try:
        for fname, fnode in functions.items():
            if not isinstance(fname, str) or not fname:
                continue
            span = _normalized_node_span(fnode)
            if span is None:
                continue
            entries.append((*span, fname))
    except (AttributeError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_build_fn_entries:{type(_e).__name__}')
    return entries
def _normalized_node_span(fnode) -> tuple[str, int, int] | None:
    fp = getattr(fnode, "filepath", "")
    if not isinstance(fp, str):
        fp = ""
    sl = getattr(fnode, "start_line", 0)
    el = getattr(fnode, "end_line", 0)
    if isinstance(sl, bool) or not isinstance(sl, int):
        sl = 0
    if isinstance(el, bool) or not isinstance(el, int):
        el = 0
    if not fp or sl < 1 or el < sl:
        return None
    return _norm_path_key(fp), sl, el
def _fn_index_version(call_graph: Any) -> tuple:
    functions = _callgraph_channel(call_graph, "functions", dict)
    if functions is None:
        return ()
    entries = [
        (fname, _normalized_node_span(fnode))
        for fname, fnode in functions.items()
        if isinstance(fname, str) and fname
    ]
    return tuple(sorted(entries, key=lambda item: item[0]))
def _callgraph_fn_entries(call_graph: Any) -> list[tuple[str, int, int, str]]:
    return _cached_graph_value(
        call_graph, _FN_INDEX_SNAPSHOT,
        lambda: _build_fn_entries(call_graph.functions),
        _fn_index_version(call_graph))
def _callgraph_fn_buckets(call_graph: Any) -> dict[str, list[tuple[str, int, int, str]]]:
    entries = _callgraph_fn_entries(call_graph)
    snapshot = _FN_BUCKETS_SNAPSHOT
    cached = snapshot[0] if snapshot else None
    if cached is not None and cached[0] is entries:
        return cached[1]
    buckets: dict[str, list[tuple[str, int, int, str]]] = {}
    for entry in entries:
        buckets.setdefault(os.path.basename(entry[0]), []).append(entry)
    _FN_BUCKETS_SNAPSHOT[:] = [(entries, buckets)]
    return buckets
def _candidate_entries(call_graph: Any, norm_query: str,
                       fn_buckets: dict) -> list:
    buckets = (fn_buckets if fn_buckets is not None
               else _callgraph_fn_buckets(call_graph))
    base = os.path.basename(norm_query)
    return buckets.get(base, []) if base else []
def _path_matches(norm_fp: str, norm_query: str) -> bool:
    if os.path.isabs(norm_fp) == os.path.isabs(norm_query):
        return norm_fp == norm_query
    return any((
        norm_fp == norm_query,
        norm_fp.endswith(os.sep + norm_query),
        norm_query.endswith(os.sep + norm_fp),
    ))
def _innermost_match(candidates: list, norm_query: str, line: int) -> str:
    matches = [entry for entry in candidates
               if _path_matches(entry[0], norm_query)]
    if len({entry[0] for entry in matches}) > 1:
        return ""
    return innermost_span(
        [(sl, el, name) for _norm_fp, sl, el, name in matches], line)
def _resolve_function_name(
    filepath: str, line: int, call_graph: Any,
    fn_buckets: dict | None = None,
) -> str:
    if not call_graph or not hasattr(call_graph, "functions"):
        return ""
    if not isinstance(call_graph.functions, dict):
        return ""
    if not isinstance(filepath, str) or not filepath:
        return ""
    norm_fp_path = _norm_path_key(filepath)
    return _innermost_match(
        _candidate_entries(call_graph, norm_fp_path, fn_buckets),
        norm_fp_path, line)
def resolve_function_for_finding(
    findings: list[dict],
    call_graph: Any,
) -> dict[str, str]:
    buckets = (_callgraph_fn_buckets(call_graph)
               if is_usable_call_graph(call_graph) else {})
    result: dict[str, str] = {}
    for f in findings:
        if not isinstance(f, dict):
            continue
        locator = make_locator_fast(f)
        result[locator] = _resolve_function_name(
            finding_file_path(f), safe_finding_line(f), call_graph, buckets)
    return result
_DFS_MAX_DEPTH = 400
_GENERIC_ENTRY_NAMES: tuple[str, ...] = (
    "main", "run", "start", "cli", "app", "serve", "entrypoint",
)
@dataclass
class RefDepthResult:
    locator: str
    function_name: str = ""
    in_degree: int = 0
    call_chain_depth: int = 0
    is_isolated: bool = False
    is_entry_point: bool = False
    priority_boost: int = 0
    confidence_boost: float = 0.0
    def to_dict(self) -> dict:
        try:
            return {
                "locator": self.locator,
                "function_name": self.function_name,
                "in_degree": self.in_degree,
                "call_chain_depth": self.call_chain_depth,
                "is_isolated": self.is_isolated,
                "is_entry_point": self.is_entry_point,
                "priority_boost": self.priority_boost,
                "confidence_boost": self.confidence_boost,
            }
        except Exception:
            logger.exception("[to_dict] 异常降级")
            return {"_error": True, "_partial": True}
def _caller_identity(member) -> str:
    return member.split(":", 1)[0] if isinstance(member, str) else ""
def _caller_pairs_from_index(call_graph: Any) -> dict[str, set[str]] | None:
    callers = _callgraph_channel(call_graph, "callers", dict)
    if callers is None:
        return None
    pairs: dict[str, set[str]] = {}
    for callee, peers in callers.items():
        if not isinstance(callee, str) or not callee:
            continue
        if not isinstance(peers, _CALLER_CONTAINER_TYPES):
            continue
        identities = {_caller_identity(member) for member in peers}
        identities.discard("")
        if identities:
            pairs[callee] = identities
    return pairs
def _callee_pairs_from_edges(call_graph: Any) -> dict[str, set[str]] | None:
    edges = _callgraph_channel(call_graph, "calls", list)
    if edges is None:
        return None
    pairs: dict[str, set[str]] = {}
    for edge in edges:
        caller = getattr(edge, "caller_func", "")
        callee = getattr(edge, "callee_func", "")
        if (isinstance(caller, str) and isinstance(callee, str)
                and caller and callee):
            pairs.setdefault(caller, set()).add(callee)
    return pairs
def _has_call_edge_evidence(call_graph: Any) -> bool:
    return (isinstance(getattr(call_graph, "callers", None), dict)
            or isinstance(getattr(call_graph, "calls", None), list))
def _out_degree_pairs(call_graph: Any) -> dict[str, set[str]]:
    mapped: dict[str, set[str]] = {}
    for caller, callees in (_callee_pairs_from_edges(call_graph) or {}).items():
        mapped.setdefault(caller, set()).update(callees)
    for callee, callers in (_caller_pairs_from_index(call_graph) or {}).items():
        for caller in callers:
            mapped.setdefault(caller, set()).add(callee)
    return mapped
def _out_degree_version(call_graph: Any) -> tuple:
    edges = _callee_pairs_from_edges(call_graph)
    index = _caller_pairs_from_index(call_graph)
    if edges is None and index is None:
        return ("unavailable",)
    return (
        "edges", tuple(sorted(
            (caller, tuple(sorted(callees)))
            for caller, callees in (edges or {}).items())),
        "index", tuple(sorted(
            (callee, tuple(sorted(callers)))
            for callee, callers in (index or {}).items())),
    )
def _out_degree_map(call_graph: Any) -> dict[str, int]:
    return _cached_graph_value(
        call_graph, _OUT_DEGREE_SNAPSHOT,
        lambda: {name: len(targets)
                 for name, targets in _out_degree_pairs(call_graph).items()},
        _out_degree_version(call_graph))
def _build_depth_context(
    call_graph: Any, entry_points: set[str],
) -> dict[str, int]:
    all_funcs = _func_names(call_graph)
    callees_map = _out_degree_pairs(call_graph)
    entries = _depth_root_entries(all_funcs, callees_map, entry_points)
    if not entries:
        return {}
    return _solve_chain_depths(entries, callees_map)
def _depth_root_entries(
    all_funcs: set[str], callees_map: dict[str, set[str]],
    entry_points: set[str],
) -> set[str]:
    entries = set(entry_points)
    all_callees: set[str] = set()
    for callees in callees_map.values():
        all_callees.update(callees)
    entries.update(
        fn for fn in all_funcs
        if fn not in all_callees and callees_map.get(fn)
    )
    return entries
def _invert_callers_map(callees_map: dict[str, set[str]]) -> dict[str, set[str]]:
    callers_map: dict[str, set[str]] = {}
    for caller, callees in callees_map.items():
        for callee in callees:
            callers_map.setdefault(callee, set()).add(caller)
    return callers_map
def _solve_chain_depths(
    entries: set[str], callees_map: dict[str, set[str]],
) -> dict[str, int]:
    callers_map = _invert_callers_map(callees_map)
    depth: dict[str, int] = {}
    visited: set[str] = set()
    topo_order: list[str] = []
    def _dfs(n: str, _depth: int = 0):
        if n in visited:
            return
        visited.add(n)
        if _depth >= _DFS_MAX_DEPTH:
            topo_order.append(n)
            return
        for callee in sorted(callees_map.get(n, set())):
            _dfs(callee, _depth + 1)
        topo_order.append(n)
    for entry in sorted(entries):
        _dfs(entry)
    for n in reversed(topo_order):
        if n in entries:
            depth[n] = 0
        else:
            max_pred = 0
            for caller in callers_map.get(n, set()):
                max_pred = max(max_pred, depth.get(caller, 0))
            depth[n] = max_pred + 1
    return depth
def _func_names(call_graph: Any) -> set:
    functions = _callgraph_channel(call_graph, "functions", dict)
    if functions is None:
        return set()
    return {fn for fn in functions if isinstance(fn, str)}
def build_callers_map(call_graph: Any) -> dict[str, set[str]]:
    merged: dict[str, set[str]] = {
        callee: set(callers)
        for callee, callers in (
            _caller_pairs_from_index(call_graph) or {}).items()
    }
    for caller, callees in (
            _callee_pairs_from_edges(call_graph) or {}).items():
        for callee in callees:
            merged.setdefault(callee, set()).add(caller)
    return merged
@dataclass
class BusinessFlowResult:
    locator: str
    finding_rule_id: str
    finding_file: str
    finding_line: int
    function_name: str = ""
    reachable: bool = False
    impacted_entry_points: list[str] = field(default_factory=list)
    entry_count: int = 0
    confidence_boost: float = 0.0
    is_false_positive_candidate: bool = False
    bfs_truncated: bool = False
    def to_dict(self) -> dict:
        return {
            "locator": self.locator,
            "finding_rule_id": self.finding_rule_id,
            "finding_file": self.finding_file,
            "finding_line": self.finding_line,
            "function_name": self.function_name,
            "reachable": self.reachable,
            "reachable_from_entry": self.reachable,
            "impacted_entry_points": self.impacted_entry_points,
            "entry_count": self.entry_count,
            "confidence_boost": self.confidence_boost,
            "is_false_positive_candidate": self.is_false_positive_candidate,
            "bfs_truncated": self.bfs_truncated,
        }
@dataclass
class ReachabilityReport:
    total_findings: int = 0
    reachable_findings: int = 0
    unreachable_findings: int = 0
    unresolved_findings: int = 0
    call_graph_available: bool = True
    false_positive_candidates: int = 0
    results: dict[str, BusinessFlowResult] = field(default_factory=dict)
    def to_dict(self) -> dict:
        return {
            "total_findings": self.total_findings,
            "reachable_findings": self.reachable_findings,
            "unreachable_findings": self.unreachable_findings,
            "unresolved_findings": self.unresolved_findings,
            "false_positive_candidates": self.false_positive_candidates,
            "call_graph_available": self.call_graph_available,
            "results": {loc: r.to_dict() for loc, r in self.results.items()},
        }
def _is_unresolved_result(result: BusinessFlowResult,
                          report: ReachabilityReport) -> bool:
    if result.reachable:
        return False
    return (not result.function_name
            or not report.call_graph_available
            or result.bfs_truncated)
def classify_flow_result(
    result: BusinessFlowResult,
    f: dict,
    report: ReachabilityReport,
    entries: list[str],
) -> None:
    if result.reachable:
        if is_dead_code_finding(result.finding_rule_id, f):
            result.is_false_positive_candidate = True
            result.confidence_boost = business_flow_confidence_boost(True, True, len(entries))
        else:
            result.confidence_boost = business_flow_confidence_boost(
            True, False, len(entries))
        report.reachable_findings += 1
        if result.is_false_positive_candidate:
            report.false_positive_candidates += 1
    elif _is_unresolved_result(result, report):
        report.unresolved_findings += 1
    else:
        report.unreachable_findings += 1
        if is_dead_code_finding(result.finding_rule_id, f):
            result.confidence_boost = business_flow_confidence_boost(False, True, 0)
def _get_entry_points(skill_dir: str) -> list[str]:
    if not skill_dir:
        return []
    try:
        discoverer = EntryPointDiscoverer(skill_dir)
        entries = discoverer.discover()
        return [e.callable_name for e in entries if e.callable_name]
    except Exception as e: # noqa: BLE001
        logger.warning("[BizFlow] 入口点发现失败: %s", e)
        return []
def _ensure_call_graph(
    call_graph: Any, skill_dir: str,
) -> tuple[Any, dict[str, set[str]] | None]:
    if is_usable_call_graph(call_graph) and _has_call_edge_evidence(call_graph):
        return call_graph, None
    logger.info("[BizFlow] call_graph不可用（缺调用边证据），启用AST回退分析")
    _fallback_graph = build_fallback_call_graph(skill_dir)
    if not _fallback_graph:
        return call_graph, _fallback_graph
    return (FallbackCallGraph(_fallback_graph, _invert_callers_map(_fallback_graph)),
            _fallback_graph)
def _resolve_via_fallback_ast(
    f: dict, fallback_graph: dict[str, set[str]], skill_dir: str,
) -> str:
    _fp = finding_file_path(f)
    if _fp and not os.path.isabs(_fp):
        _fp = os.path.join(skill_dir, _fp)
    _resolved = fallback_resolve_function_name(
        _fp, safe_finding_line(f), skill_dir)
    if _resolved and _resolved in fallback_graph:
        return _resolved
    return ""
def _resolve_finding_function(
    f: dict, locator: str, func_map: dict[str, str],
    fallback_graph: dict[str, set[str]] | None, skill_dir: str,
) -> str:
    func_name = func_map.get(locator, "")
    if func_name or not fallback_graph:
        return func_name
    resolved = _resolve_via_fallback_ast(f, fallback_graph, skill_dir)
    if resolved:
        func_map[locator] = resolved
    return resolved
_BFS_MAX_VISITED_NODES = 500
def _collect_entry_hits(
    current: str,
    entry_index: dict[str, list[str]],
    found_entries: list[str],
) -> None:
    _last = current.rsplit(".", 1)[-1]
    for ep in entry_index.get(_last, ()):
        if ep in found_entries:
            continue
        if (current == ep
                or current.startswith(".")
                or ep.startswith(".")
                or ("." in ep and current.endswith("." + ep))
                or ("." in current and ep.endswith("." + current))):
            found_entries.append(ep)
def _index_entry_points(entry_points: list[str]) -> dict[str, list[str]]:
    index: dict[str, list[str]] = {}
    if not isinstance(entry_points, (list, tuple, set, frozenset)):
        return index
    for ep in entry_points:
        if isinstance(ep, str) and ep:
            index.setdefault(ep.rsplit(".", 1)[-1], []).append(ep)
    return index
def _iter_caller_names(callers_map: dict, current: str):
    _raw = callers_map.get(current)
    if not isinstance(_raw, _CALLER_CONTAINER_TYPES):
        if _raw is not None:
            logger.warning('[BizFlow] callers[%s] 形态非法(%s),已跳过',
                           current, type(_raw).__name__)
        return
    for caller in _raw:
        caller_name = _caller_identity(caller)
        if caller_name:
            yield caller_name
def _walk_reachability(function_name: str, callers_map: dict,
                       entry_index: dict[str, list[str]],
                       ) -> tuple[list[str], bool]:
    if not isinstance(function_name, str) or not function_name:
        return [], True
    visited: set[str] = set()
    queue = deque([function_name])
    found_entries: list[str] = []
    truncated = False
    while queue:
        current = queue.popleft()
        if current in visited:
            continue
        visited.add(current)
        _collect_entry_hits(current, entry_index, found_entries)
        _pending = sorted(
            caller for caller in _iter_caller_names(callers_map, current)
            if caller not in visited)
        if not _pending:
            continue
        if len(visited) > _BFS_MAX_VISITED_NODES:
            truncated = True
            continue
        queue.extend(_pending)
    return found_entries, not truncated
def _compute_reachability(
    function_name: str,
    callers_map: dict[str, set[str]],
    entry_index: dict[str, list[str]],
) -> tuple[bool, list[str], bool]:
    if not isinstance(function_name, str) or not function_name:
        return False, [], True
    found_entries, fully_explored = _walk_reachability(
        function_name, callers_map, entry_index)
    return bool(found_entries), found_entries, fully_explored
def _flow_rule_identity(f: dict) -> str:
    return str(f.get("rule_id") or f.get("type") or "unknown")
def _iter_bizflow_views(findings):
    items = [f for f in findings if isinstance(f, dict)]
    rules_by_loc: dict[str, set[str]] = {}
    for f in items:
        rules_by_loc.setdefault(make_locator_fast(f), set()).add(
            _flow_rule_identity(f))
    for f in findings:
        if not isinstance(f, dict):
            yield f, ""
            continue
        locator = make_locator_fast(f)
        if len(rules_by_loc.get(locator, ())) > 1:
            locator = f"{locator}::rule={_flow_rule_identity(f)}"
        yield f, locator
def _build_flow_result(
    f: dict, locator: str, func_name: str, reachable: bool,
    entries: list[str], fully_explored: bool,
) -> BusinessFlowResult:
    return BusinessFlowResult(
        locator=locator,
        finding_rule_id=_flow_rule_identity(f),
        finding_file=finding_file_path(f),
        finding_line=safe_finding_line(f),
        function_name=func_name,
        reachable=reachable,
        impacted_entry_points=entries,
        entry_count=len(entries),
        bfs_truncated=not fully_explored,
    )
def _analyze_reachability(
    findings: Any,
    call_graph: Any,
    entry_points: list[str],
    func_map: dict[str, str] | None = None,
) -> ReachabilityReport:
    valid_findings = dict_findings(findings)
    report = ReachabilityReport(total_findings=len(valid_findings))
    report.call_graph_available = (is_usable_call_graph(call_graph)
                                   and _has_call_edge_evidence(call_graph))
    if not valid_findings:
        return report
    if not entry_points:
        report.unresolved_findings = len(valid_findings)
        report.call_graph_available = False
        return report
    if func_map is None:
        func_map = resolve_function_for_finding(valid_findings, call_graph)
    callers_map = build_callers_map(call_graph)
    entry_index = _index_entry_points(entry_points)
    for f, locator in _iter_bizflow_views(valid_findings):
        func_name = (func_map.get(locator)
                     or func_map.get(make_locator_fast(f), ""))
        reachable, entries, fully_explored = _compute_reachability(
            func_name, callers_map, entry_index)
        result = _build_flow_result(
            f, locator, func_name, reachable, entries, fully_explored)
        classify_flow_result(result, f, report, entries)
        report.results[locator] = result
    logger.info(
        "[BizFlow] 业务流追踪: %d findings, %d reachable, "
        "%d unreachable, %d FP candidates",
        report.total_findings, report.reachable_findings,
        report.unreachable_findings, report.false_positive_candidates)
    return report
class BusinessFlowValidator:
    def __init__(self, skill_dir: str):
        self.skill_dir = _coerce_skill_dir(skill_dir)
        self._entry_points: list[str] = []
        self._entry_points_loaded = False
    def _entry_points_cached(self) -> list[str]:
        if not self._entry_points_loaded:
            self._entry_points = _get_entry_points(self.skill_dir)
            self._entry_points_loaded = True
        return list(self._entry_points)
    def validate(
        self,
        findings: list[dict],
        call_graph: Any = None,
    ) -> ReachabilityReport:
        try:
            valid_findings = dict_findings(findings)
            if not valid_findings:
                return _analyze_reachability(valid_findings, call_graph, [])
            entry_points = self._entry_points_cached()
            if not entry_points:
                logger.warning("[BizFlow] 入口点列表为空，跳过业务流验证（避免全局正向偏置）")
                return _analyze_reachability(valid_findings, call_graph, [])
            call_graph, fallback_graph = _ensure_call_graph(
                call_graph, self.skill_dir)
            func_map = resolve_function_for_finding(valid_findings, call_graph)
            for f in valid_findings:
                locator = make_locator_fast(f)
                func_map[locator] = _resolve_finding_function(
                    f, locator, func_map, fallback_graph, self.skill_dir)
            return _analyze_reachability(
                valid_findings, call_graph, entry_points, func_map)
        except Exception:
            logger.exception("[validate] 异常降级")
            return ReachabilityReport(call_graph_available=False)
def annotate_findings_with_bizflow(
    findings: list[dict],
    report: ReachabilityReport,
) -> list[dict]:
    findings, _results = _normalize_annotate_input(findings, None)
    try:
        if not isinstance(report, ReachabilityReport):
            logger.warning("[annotate_findings_with_bizflow] 非 ReachabilityReport 输入(%s)，跳过注解",
                           type(report).__name__)
            return findings
        annotated = []
        for f, locator in _iter_bizflow_views(findings):
            if isinstance(f, dict):
                result = report.results.get(locator)
                unresolved = (_is_unresolved_result(result, report)
                              if result is not None else True)
                f.update(bizflow_signal_payload(result, unresolved))
            annotated.append(f)
        return annotated
    except Exception:
        logger.exception("[annotate_findings_with_bizflow] 异常降级")
        return findings
_ENTRY_DECORATOR_NAMES: tuple[str, ...] = (
    "command", "group", "route", "app.route", "flask.route",
    "register", "entry_point", "main", "click.command",
    "click.group", "api_view", "action", "task",
)
_ENTRY_PREFIX_PATTERNS: tuple[str, ...] = (
    "cmd_", "cli_", "main_", "entry_", "launch_", "serve_",
)
def _function_node_of(function_name: str, call_graph: Any):
    functions = _callgraph_channel(call_graph, "functions", dict)
    if functions is None:
        return None
    return functions.get(function_name)
def _decorator_marks_entry(decorators) -> bool:
    for decorator in decorators:
        if not isinstance(decorator, str):
            continue
        for entry_name in _ENTRY_DECORATOR_NAMES:
            if decorator == entry_name or decorator.endswith("." + entry_name):
                return True
    return False
def _has_entry_decorator(function_name: str, call_graph: Any) -> bool:
    fnode = _function_node_of(function_name, call_graph)
    if fnode is None:
        return False
    return _decorator_marks_entry(getattr(fnode, "decorators", []))
def _has_no_caller_evidence(
    function_name: str, simple: str,
    callers_map: dict[str, set[str]], has_edge_evidence: bool,
) -> bool:
    if simple.startswith("_"):
        return False
    if not has_edge_evidence:
        return False
    return not callers_map.get(function_name)
def _is_entry_point_func(
    function_name: str,
    call_graph: Any,
    callers_map: dict[str, set[str]],
    has_edge_evidence: bool,
) -> bool:
    if not isinstance(function_name, str) or not function_name:
        return False
    simple = function_name.rsplit(".", maxsplit=1)[-1]
    if simple in _GENERIC_ENTRY_NAMES:
        return True
    if _has_entry_decorator(function_name, call_graph):
        return True
    if any(simple.startswith(p) for p in _ENTRY_PREFIX_PATTERNS):
        return True
    return _has_no_caller_evidence(
        function_name, simple, callers_map, has_edge_evidence)
def _neutral_result(locator: str) -> RefDepthResult:
    return RefDepthResult(locator=locator)
def _neutral_refdepth_results(findings: list[dict]) -> dict[str, RefDepthResult]:
    results: dict[str, RefDepthResult] = {}
    for f in findings:
        if not isinstance(f, dict):
            continue
        locator = make_locator_fast(f)
        results[locator] = _neutral_result(locator)
    return results
def _measure_ref_depth(
    locator: str,
    func_name: str,
    ctx: _BatchContext,
) -> RefDepthResult:
    in_degree = len(ctx.callers_map.get(func_name, ()))
    out_degree = ctx.out_degree_map.get(func_name, 0)
    chain_depth = ctx.depth_map.get(func_name, 0)
    is_entry = func_name in ctx.entry_points
    is_isolated = (ctx.has_edge_evidence
                   and in_degree == 0
                   and out_degree == 0
                   and not is_entry and chain_depth == 0)
    priority_boost, confidence_boost = refdepth_boosts(
        in_degree, chain_depth, is_entry, is_isolated,
    )
    return RefDepthResult(
        locator=locator,
        function_name=func_name,
        in_degree=in_degree,
        call_chain_depth=chain_depth,
        is_isolated=is_isolated,
        is_entry_point=is_entry,
        priority_boost=priority_boost,
        confidence_boost=confidence_boost,
    )
class _BatchContext:
    __slots__ = ("callers_map", "depth_map", "entry_points", "fn_buckets",
                 "has_edge_evidence", "out_degree_map")
    def __init__(self, call_graph: Any) -> None:
        self.has_edge_evidence = _has_call_edge_evidence(call_graph)
        self.callers_map = build_callers_map(call_graph)
        self.entry_points = _collect_entry_points(
            call_graph, self.callers_map, self.has_edge_evidence)
        self.depth_map = _build_depth_context(call_graph, self.entry_points)
        self.out_degree_map = _out_degree_map(call_graph)
        self.fn_buckets = _callgraph_fn_buckets(call_graph)
class RefDepthAnalyzer:
    def __init__(self, skill_dir: str):
        self.skill_dir = _coerce_skill_dir(skill_dir)
    def analyze(
        self,
        findings: list[dict],
        call_graph: Any = None,
    ) -> dict[str, RefDepthResult]:
        results: dict[str, RefDepthResult] = {}
        try:
            if not call_graph or not hasattr(call_graph, "functions"):
                logger.info("[RefDepth] call_graph 不可用，跳过引用深度分析")
                return _neutral_refdepth_results(findings)
            ctx = _BatchContext(call_graph)
            for f in findings:
                if not isinstance(f, dict):
                    continue
                locator, result = _analyze_one(f, call_graph, ctx)
                results[locator] = result
            return results
        except Exception:
            logger.exception("[analyze] 异常降级")
            return results
def _collect_entry_points(
    call_graph: Any,
    callers_map: dict[str, set[str]],
    has_edge_evidence: bool,
) -> set[str]:
    functions = _callgraph_channel(call_graph, "functions", dict)
    if functions is None:
        return set()
    return {
        fn for fn in functions
        if _is_entry_point_func(fn, call_graph, callers_map, has_edge_evidence)
    }
def _analyze_one(f: dict, call_graph: Any,
                 ctx: _BatchContext) -> tuple[str, RefDepthResult]:
    locator = make_locator_fast(f)
    func_name = _resolve_function_name(
        finding_file_path(f), safe_finding_line(f), call_graph, ctx.fn_buckets)
    if not func_name:
        return locator, _neutral_result(locator)
    return locator, _measure_ref_depth(locator, func_name, ctx)
def annotate_findings_with_ref_depth(
    findings: list[dict],
    ref_depth_results: dict[str, RefDepthResult],
) -> list[dict]:
    try:
        annotated = []
        for f in findings:
            if not isinstance(f, dict):
                annotated.append(f)
                continue
            locator = make_locator_fast(f)
            result = ref_depth_results.get(locator) or _neutral_result(locator)
            f.update(refdepth_signal_payload(result))
            annotated.append(f)
        return annotated
    except Exception:
        logger.exception("[annotate_findings_with_ref_depth] 异常降级")
        return findings
FALSIFY_PATTERN_FAMILIES = {
    "mutable_default", "silent_swallow", "empty_except",
    "danger_pattern", "dead_code", "diag_general",
}
FALSIFY_MAX_ITEMS = 50
def _is_notimplemented_raise(stmt: ast.stmt) -> bool:
    if not isinstance(stmt, ast.Raise):
        return False
    exc = stmt.exc
    if isinstance(exc, ast.Call):
        exc = exc.func
    if isinstance(exc, ast.Name):
        return exc.id == 'NotImplementedError'
    return (
        isinstance(exc, ast.Attribute)
        and exc.attr == 'NotImplementedError'
        and isinstance(exc.value, ast.Name)
        and exc.value.id == 'builtins'
    )
def _covering_nodes(tree: ast.Module, line: int, types) -> list:
    return [node for node in walk_nodes(tree)
            if isinstance(node, types) and _node_span_covers(node, line)]
def _node_span_covers(node: ast.AST, line: int) -> bool:
    return node.lineno <= line <= (
        getattr(node, "end_lineno", node.lineno) or node.lineno)
def _covering_any(tree: ast.Module, line: int, types, predicate) -> bool | None:
    nodes = _covering_nodes(tree, line, types)
    if not nodes:
        return None
    return predicate(_innermost_node(nodes))
def _has_mutable_default(node) -> bool:
    return any(
        is_mutable_default(default)
        for default in (
            *node.args.defaults,
            *(d for d in node.args.kw_defaults if d is not None),
        )
    )
def _strip_noop_statements(body: list) -> list:
    return [s for s in body if not (
        isinstance(s, ast.Pass)
        or (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)))]
def _is_stub_node(node) -> bool:
    body = node.body
    if not body:
        return False
    stripped = _strip_noop_statements(body)
    if not stripped:
        return True
    return all(_is_notimplemented_raise(stmt) for stmt in stripped)
_FALSIFY_IDENTITY_CLAIMS: tuple[tuple[str, tuple[frozenset[str], ...]], ...] = (
    ("mutable_default", (
        frozenset({"mutable", "default"}),
        frozenset({"mda", "01"}),
        frozenset({"rb", "01"}),
    )),
    ("silent_swallow", (
        frozenset({"silent", "swallow"}),
        frozenset({"except", "pass"}),
        frozenset({"except", "exception", "pass"}),
        frozenset({"empty", "except"}),
        frozenset({"bare", "except"}),
        frozenset({"b110"}),
        frozenset({"be", "01"}),
        frozenset({"sn", "01"}),
    )),
    ("stub", (
        frozenset({"stub"}),
        frozenset({"empty", "body"}),
        frozenset({"empty", "function"}),
    )),
    ("eval", (
        frozenset({"eval"}),
        frozenset({"b307"}),
    )),
    ("exec", (
        frozenset({"exec"}),
        frozenset({"b102"}),
    )),
)
_CLAIM_TEXT_KEYWORDS: dict[str, tuple[str, ...]] = {
    "mutable_default": ("mutable default", "可变默认", "可变对象默认"),
    "silent_swallow": ("swallow", "吞错", "吞没", "吞掉",
                       "空 except", "裸 except"),
    "stub": ("stub", "empty body", "空壳", "空函数", "pass 语句"),
}
_CLAIM_TOKEN_SPLIT_RE = re.compile(r"[^a-z0-9]+")
def _claim_identity_tokens(text: str) -> frozenset[str]:
    return frozenset(
        token for token in _CLAIM_TOKEN_SPLIT_RE.split(text.lower()) if token)
def _identity_claim_kinds(haystack: str) -> frozenset[str]:
    tokens = _claim_identity_tokens(haystack)
    return frozenset(
        kind for kind, patterns in _FALSIFY_IDENTITY_CLAIMS
        if any(pattern <= tokens for pattern in patterns))
def _claims_text(message: str, kind: str) -> bool:
    return any(keyword in message for keyword in _CLAIM_TEXT_KEYWORDS[kind])
_CLAIM_PASS_RE = re.compile(r"(?<![A-Za-z0-9])pass(?![A-Za-z0-9])")
_CLAIM_BUILTIN_CALL_RE: dict[str, re.Pattern] = {
    "eval": re.compile(r"(?<![A-Za-z0-9_])eval\s*\("),
    "exec": re.compile(r"(?<![A-Za-z0-9_])exec\s*\("),
}
def _claims_mutable_default(haystack: str, message: str) -> bool:
    return ("mutable_default" in _identity_claim_kinds(haystack)
            or _claims_text(message, "mutable_default"))
def _claims_silent_swallow(haystack: str, message: str) -> bool:
    if "silent_swallow" in _identity_claim_kinds(haystack):
        return True
    if "except" in haystack and _CLAIM_PASS_RE.search(haystack):
        return True
    return _claims_text(message, "silent_swallow")
def _claims_stub(haystack: str) -> bool:
    return ("stub" in _identity_claim_kinds(haystack)
            or any(k in haystack for k in _CLAIM_TEXT_KEYWORDS["stub"]))
def _claims_builtin_call(haystack: str, message: str, kind: str) -> bool:
    return (kind in _identity_claim_kinds(haystack)
            or bool(_CLAIM_BUILTIN_CALL_RE[kind].search(message)))
def _falsify_verification_kind(f: dict) -> str:
    rule_id = str(f.get("rule_id", "")).lower()
    rule_family = str(f.get("rule_family", "")).lower()
    message = str(f.get("message", "")).lower()
    identity = f"{rule_id} {rule_family}"
    haystack = f"{identity} {message}"
    if _claims_mutable_default(identity, message):
        return "mutable_default"
    if _claims_silent_swallow(haystack, message):
        return "silent_swallow"
    if _claims_stub(haystack):
        return "stub"
    if _claims_builtin_call(identity, message, "eval"):
        return "eval"
    if _claims_builtin_call(identity, message, "exec"):
        return "exec"
    return "unknown"
def _falsify_result_locator(f: dict) -> str:
    return f"{channel_locator(f)}::pattern={_falsify_verification_kind(f)}"
def _has_valid_candidate_location(f: dict) -> bool:
    return bool(finding_file_path(f)) and safe_finding_line(f) > 0
def _in_falsify_family(f: dict) -> bool:
    rf_raw = f.get("rule_family", "")
    rf = rf_raw if isinstance(rf_raw, str) else ""
    if rf in FALSIFY_PATTERN_FAMILIES:
        return True
    return normalize_rule(rf or str(f.get("rule_id", "") or "")) in FALSIFY_PATTERN_FAMILIES
def _falsify_candidate_loc(f: dict) -> str | None:
    if not isinstance(f, dict):
        return None
    if normalize_severity_rank(f.get("severity")) > 1:
        return None
    if not _has_valid_candidate_location(f):
        return None
    if not _in_falsify_family(f):
        return None
    return channel_locator(f)
def _call_matches_keywords(
    node: ast.Call, keywords: tuple,
    resolver: ScopeNameResolver | None = None,
) -> bool:
    func = node.func
    builtin_targets = {f"builtins.{keyword}" for keyword in keywords}
    if resolver is not None:
        if isinstance(func, ast.Name):
            if resolver.import_path(func) in builtin_targets:
                return True
            return func.id in keywords and not resolver.is_bound(func)
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)):
            return (func.attr in keywords
                    and resolver.import_path(func.value) == "builtins")
        return False
    name = resolve_call_name(node)
    return name in keywords or name in builtin_targets
class FalsificationAnalyzer:
    def __init__(self, skill_dir: str):
        self.skill_dir = _coerce_skill_dir(skill_dir)
        self._src_cache: dict = {}
    def _read_source(self, filepath: str) -> str | None:
        if not isinstance(filepath, str) or not filepath:
            return None
        fp = filepath if os.path.isabs(filepath) else os.path.join(self.skill_dir, filepath)
        if fp in self._src_cache:
            return self._src_cache[fp]
        if not os.path.isfile(fp):
            src = None
        else:
            src = read_source(fp)
            if src is None:
                logger.warning("[Falsify] 源码读取失败(该文件复查降级为不可判定): %s", fp)
        self._src_cache[fp] = src
        return src
    def _check_mutable_default(self, tree: ast.Module, line: int) -> bool | None:
        return _covering_any(
            tree, line, (ast.FunctionDef, ast.AsyncFunctionDef),
            _has_mutable_default)
    def _check_silent_swallow(self, tree: ast.Module, line: int,
                              src_lines: list[str] | None = None) -> bool | None:
        def _verify(node) -> bool:
            covering_handlers = [
                handler for handler in node.handlers
                if _node_span_covers(handler, line)]
            handlers = covering_handlers or node.handlers
            return any(
                is_silent_handler(handler, src_lines)[0]
                for handler in handlers)
        return _covering_any(tree, line, TRY_TYPES, _verify)
    def _check_stub(self, tree: ast.Module, line: int) -> bool | None:
        return _covering_any(
            tree, line, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef),
            _is_stub_node)
    def _check_dangerous_call(
        self, tree: ast.Module, line: int, keywords: tuple,
        src: str | None = None,
    ) -> bool | None:
        resolver = (ScopeNameResolver(src, "<falsify>", tree, set())
                    if isinstance(src, str) else None)
        hit = False
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Call) or not _node_span_covers(node, line):
                continue
            hit = True
            if _call_matches_keywords(node, keywords, resolver):
                return True
        return False if hit else None
    def verify_finding(self, f: dict, tree: ast.Module | None,
                       src: str | None = None) -> bool | None:
        if tree is None:
            return None
        kind = _falsify_verification_kind(f)
        line = safe_finding_line(f)
        if kind == "mutable_default":
            return self._check_mutable_default(tree, line)
        if kind == "silent_swallow":
            return self._check_silent_swallow(
                tree, line, src.splitlines() if isinstance(src, str) else None)
        if kind == "stub":
            return self._check_stub(tree, line)
        if kind == "eval":
            return self._check_dangerous_call(tree, line, ("eval",), src=src)
        if kind == "exec":
            return self._check_dangerous_call(tree, line, ("exec",), src=src)
        return None
    def analyze(self, findings: list[dict]) -> dict:
        results: dict = {}
        try:
            candidates = self._collect_falsify_candidates(findings)
            self._verify_falsify_candidates(candidates, results)
        except Exception as e: # noqa: BLE001
            logger.warning("[XV] falsify 分析失败 in FalsificationAnalyzer.analyze(): %s", e)
        return results
    def _collect_falsify_candidates(self, findings: list[dict]) -> list:
        candidates: list = []
        try:
            seen_keys: set = set()
            for f in findings:
                if _falsify_candidate_loc(f) is None:
                    continue
                key = _falsify_result_locator(f)
                if key in seen_keys:
                    continue
                seen_keys.add(key)
                candidates.append((key, f))
                if len(candidates) >= FALSIFY_MAX_ITEMS:
                    break
            return candidates
        except Exception as e: # noqa: BLE001
            logger.warning("[XV] falsify 候选收集失败 in _collect_falsify_candidates(): %s", e)
            return candidates
    def _source_tree_cached(self, fp: str, cache: dict) -> tuple:
        if fp not in cache:
            src = self._read_source(fp)
            tree = None
            if src is not None:
                try:
                    tree = parse_cached(src, filename=fp)
                except (SyntaxError, ValueError, RecursionError,
                        MemoryError) as e:
                    logger.warning("[Falsify] 目标源码解析失败(该文件复查降级为不可判定): %s: %s", fp, e)
                    tree = None
            cache[fp] = (src, tree)
        return cache[fp]
    @staticmethod
    def _outcome(verified: bool | None) -> dict:
        if verified is True:
            return {"verified": True, "detail": "pattern_reproduced"}
        if verified is False:
            return {"verified": False, "detail": "pattern_absent"}
        return {"verified": None, "detail": "no_verifier"}
    def _verify_falsify_candidates(self, candidates: list, results: dict) -> None:
        try:
            _file_trees: dict = {}
            for loc, f in candidates:
                fp = finding_file_path(f)
                src, tree = self._source_tree_cached(fp, _file_trees)
                if src is None:
                    results[loc] = {"verified": None, "detail": "file_unreadable_or_missing"}
                    continue
                if tree is None:
                    results[loc] = {"verified": None, "detail": "syntax_error_in_target"}
                    continue
                try:
                    verified = self.verify_finding(f, tree, src)
                except Exception as e: # noqa: BLE001
                    logger.debug("[Falsify] %s 复查异常: %s", loc, e)
                    verified = None
                results[loc] = self._outcome(verified)
        except Exception as e: # noqa: BLE001
            logger.warning("[XV] falsify 复查失败 in _verify_falsify_candidates(): %s", e)
def _clamp_unit_interval(v: float, default: float) -> float:
    if not is_real_number(v):
        return default
    return float(v) if (0.0 <= v <= 1.0) else default
def _apply_falsify_annotation(f: dict, r: dict, boost: float, penalty: float) -> None:
    if r.get("verified") is True:
        f["_falsify_verified"] = True
        f["_falsify_detail"] = _signal_str(r.get("detail"))
        adjust_finding_confidence(f, boost, increasing=True)
    elif r.get("verified") is False:
        f["_falsify_failed"] = True
        f["_falsify_detail"] = _signal_str(r.get("detail"))
        adjust_finding_confidence(f, -penalty, increasing=False)
_FALSIFY_VERIFIED_BOOST = 0.05
_FALSIFY_FAILED_PENALTY = 0.30
def annotate_findings_with_falsification(
        findings: list[dict], results: dict,
        boost: float = _FALSIFY_VERIFIED_BOOST,
        penalty: float = _FALSIFY_FAILED_PENALTY) -> list[dict]:
    findings, results = _normalize_annotate_input(findings, results)
    boost = _clamp_unit_interval(boost, _FALSIFY_VERIFIED_BOOST)
    penalty = _clamp_unit_interval(penalty, _FALSIFY_FAILED_PENALTY)
    for f in findings:
        if not isinstance(f, dict):
            continue
        r = results.get(_falsify_result_locator(f))
        if not isinstance(r, dict):
            continue
        _apply_falsify_annotation(f, r, boost, penalty)
    return findings
class CounterEvidenceAnalyzer:
    _SUPPRESS_PATTERNS = (
        "#noqa", "#pragma: no cover", "#pragma nocover",
        "#suppress", "#ignore:", "#lint:ignore", "#type: ignore",
        "#pylint: disable",
        "# noqa", "# type: ignore", "# pylint: disable",
        "# pragma: no cover", "# ignore:",
    )
    _CURRENT_LINE_ONLY_SUPPRESS_PATTERNS = frozenset({
        "#noqa", "# noqa",
        "#type: ignore", "# type: ignore",
        "#pragma: no cover", "#pragma nocover", "# pragma: no cover",
    })
    _FIXTURE_DIRS = frozenset({"fixtures"})
    _DEAD_FAMILIES = ("dead_code", "unused_import", "unused_variable", "orphan",
                      "unused", "deadcode")
    def __init__(self, skill_dir: str):
        self.skill_dir = _coerce_skill_dir(skill_dir)
        self._all_exports_cache: dict[str, frozenset[str]] = {}
        self._src_lines_cache: dict[str, list[str] | None] = {}
        self._source_comments_cache: dict[str, dict[int, list[str]]] = {}
    def _source_lines(self, anchored: str):
        if anchored in self._src_lines_cache:
            return self._src_lines_cache[anchored]
        try:
            lines = read_source_strict(anchored).splitlines(keepends=True)
        except (OSError, TypeError, ValueError) as e:
            logger.debug("文件读取失败（跳过）: %s: %s", anchored, e)
            lines = None
        self._src_lines_cache[anchored] = lines
        return lines
    def _source_comments(self, anchored: str, lines: list[str]) -> dict[int, list[str]]:
        if anchored in self._source_comments_cache:
            return self._source_comments_cache[anchored]
        comments: dict[int, list[str]] = {}
        try:
            tokens = tokenize.generate_tokens(io.StringIO("".join(lines)).readline)
            for token in tokens:
                if token.type == tokenize.COMMENT:
                    comments.setdefault(token.start[0], []).append(token.string)
        except (tokenize.TokenError, SyntaxError, ValueError) as exc:
            logger.debug("[CounterEvidence] 注释词法分析部分降级: %s: %s",
                         anchored, exc)
        self._source_comments_cache[anchored] = comments
        return comments
    def _suppress_reasons(self, anchored: str, line: int) -> list:
        reasons: list = []
        lines = self._source_lines(anchored)
        if lines is None:
            return reasons
        targets = []
        if 0 < line <= len(lines):
            targets.append((line - 1, "line"))
        if line > 1 and line - 2 < len(lines):
            targets.append((line - 2, "prev_line"))
        comments = self._source_comments(anchored, lines)
        for idx, where in targets:
            for comment in comments.get(idx + 1, ()):
                for p in self._SUPPRESS_PATTERNS:
                    if (where == "prev_line"
                            and p in self._CURRENT_LINE_ONLY_SUPPRESS_PATTERNS):
                        continue
                    if p in comment.lower():
                        reasons.append(f"{where}_suppress:{p.strip()}")
                        break
        return reasons
    def _project_relative(self, fp: str) -> str | None:
        anchored = anchor_to_skill(fp, self.skill_dir)
        if not isinstance(anchored, str) or not anchored:
            return None
        try:
            rel = os.path.relpath(
                os.path.abspath(anchored), os.path.abspath(self.skill_dir))
        except (OSError, ValueError) as _swallowed_exc:
            log_swallowed(__name__, _swallowed_exc,
                          context=f'_project_relative:{type(_swallowed_exc).__name__}')
            return None
        if rel == os.pardir or rel.startswith(os.pardir + os.sep):
            return None
        return rel
    def _test_dir_reason(self, fp: str) -> str | None:
        rel = self._project_relative(fp)
        if rel is None:
            return None
        parts = rel.replace("\\", "/").split("/")
        return "test_dir" if any(
            seg.lower() in self._FIXTURE_DIRS or is_test_dir_name(seg)
            for seg in parts[:-1]
        ) else None
    def _all_export_reason(self, anchored: str, f: dict) -> str | None:
        rf = finding_rule_family(f)
        if not is_family_member(rf, self._DEAD_FAMILIES):
            return None
        symbol = _counter_evidence_symbol(f)
        if symbol and symbol in self._all_exports_cached(anchored):
            return "exported_in_all"
        return None
    def analyze(self, findings: list[dict]) -> dict:
        results: dict = {}
        for f, fp, loc in _iter_counter_evidence_views(findings):
            line = safe_finding_line(f)
            if not fp:
                continue
            anchored = anchor_to_skill(fp, self.skill_dir)
            reasons: list = []
            reasons.extend(self._suppress_reasons(anchored, line))
            _r2 = self._test_dir_reason(fp)
            if _r2 is not None:
                reasons.append(_r2)
            _r3 = self._all_export_reason(anchored, f)
            if _r3 is not None:
                reasons.append(_r3)
            results[loc] = {"counter_evidence": bool(reasons), "reasons": reasons}
        return results
    def _all_exports_cached(self, fp: str) -> frozenset[str]:
        _cached = self._all_exports_cache.get(fp)
        if _cached is None:
            _cached = self._parse_all_exports(fp)
            self._all_exports_cache[fp] = _cached
        return _cached
    @staticmethod
    def _parse_all_exports(fp: str) -> frozenset[str]:
        try:
            src_text = read_source_strict(fp)
            tree = parse_cached(src_text, filename=fp)
        except (SyntaxError, ValueError, OSError, RecursionError,
                MemoryError) as _e:
            log_swallowed(__name__, _e, context=(
                f'CounterEvidenceAnalyzer._parse_all_exports:{type(_e).__name__}'))
            return frozenset()
        return frozenset(module_export_names(tree))
def _counter_evidence_symbol(f: dict) -> str | None:
    if not is_family_member(
            finding_rule_family(f), CounterEvidenceAnalyzer._DEAD_FAMILIES):
        return None
    detail = f.get("detail")
    if isinstance(detail, dict):
        value = detail.get("name")
        if isinstance(value, str) and value.strip():
            return value.strip()
    name = first_symbol_field(
        f, ("name", "symbol", "identifier", "var_name"))
    if name:
        return name
    return _first_identifier_in_message(str(f.get("message", ""))) or ""
def _iter_counter_evidence_views(findings):
    views = list(_iter_finding_views(findings))
    symbols_by_loc: dict[str, set[str]] = {}
    for f, _fp, loc in views:
        symbol = _counter_evidence_symbol(f)
        if symbol is not None:
            symbols_by_loc.setdefault(loc, set()).add(symbol)
    for f, fp, loc in views:
        symbol = _counter_evidence_symbol(f)
        result_loc = loc
        if symbol is not None and len(symbols_by_loc.get(loc, ())) > 1:
            result_loc = f"{loc}::symbol={symbol}"
        yield f, fp, result_loc
def annotate_findings_with_counter_evidence(
        findings: list[dict], results: dict) -> list[dict]:
    findings, results = _normalize_annotate_input(findings, results)
    for f, _fp, loc in _iter_counter_evidence_views(findings):
        r = results.get(loc)
        if not isinstance(r, dict) or not r.get("counter_evidence"):
            continue
        f["_counter_evidence"] = True
        _reasons = r.get("reasons")
        if not isinstance(_reasons, list):
            _reasons = []
        f["_counter_evidence_reasons"] = _reasons
        f["_review_required"] = True
        f["_review_reason"] = (
            f"counter_evidence:{','.join(str(x) for x in _reasons)}")
        _pen = counter_evidence_confidence_penalty()
        adjust_finding_confidence(f, -_pen, increasing=False)
    return findings

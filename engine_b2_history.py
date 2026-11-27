from __future__ import annotations

__all__ = [
    "HistoryAnalyzer",
    "HistoryPatternMatch",
    "HistoryPatternScanner",
    "HistoryTrendAggregator",
    "HistoryTrendEntry",
    "HistoryTrendReport",
    "UnifiedAstEngine",
    "run_b1_unified_ast_analysis",
    "run_engine_B",
    "run_history_analysis",
]
import ast
import math
import os
import re
import time
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime
from functools import partial
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_antipattern_flow_detect import (
    collect_scope_filtered_findings,
    run_density_post_processor,
    run_extended_detectors,
    run_file_detectors,
)
from jwsgj.diag_antipattern_flow_govern import (
    run_antipattern_detector,
)
from jwsgj.diag_detector_findings import (
    RETIRED_RULE_IDS,
    consolidate_findings,
    detector_entry,
    finding_file,
    finding_line,
    finding_rule_id,
    group_envelope,
    is_retired_rule,
    normalize_severity,
    split_malformed_issues,
    verdict_from_severity_counts,
    worst_sub_status,
)
from jwsgj.diag_exception_verdict import (
    run_exception_detector,
)
from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    is_broad_except,
    is_docstring_stmt,
    is_mutable_default,
    is_placeholder_stmt,
    iter_arg_nodes,
    iter_unpack_target_names,
)
from jwsgj.diag_types_vocab import SEVERITY_RANK
from jwsgj.engine_b1_cohesion import (
    COHESION_RULE_IDS,
    CohesionAnalyzer,
    result_to_b1_findings,
)
from jwsgj.hallucination_ledger import (
    run_hallucination_detector,
)
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
    write_module_run,
)
from jwsgj.runtime_paths import (
    read_evolution_section,
)
from jwsgj.runtime_scope import (
    is_diagnosis_out_of_scope,
    read_diagnostic_source_strict,
)
from jwsgj.shared_cache import (
    as_diag_ctx,
    coerce_dimension_issues,
    collect_scan_py_files,
    ensure_entry_warmed,
    fingerprint_freeze_window,
    gate_scan_files_cached,
    require_warmed,
    run_dimension_channels,
)

_DEFAULT_CACHE: Any = None
_DEFAULT_HISTORY_DATA: dict | None = None
logger = get_module_logger(__name__, __file__)
class _SkillScopedEngine:
    def __init__(self, skill_dir: str, cache: Any = _DEFAULT_CACHE):
        root = os.fspath(skill_dir)
        if not root or not root.strip() or not os.path.isdir(root):
            raise ValueError(f"skill_dir 必须是已存在的目录: {skill_dir!r}")
        self.skill_dir = os.path.abspath(root)
        self._cache = cache
        self._post_init()
    def _post_init(self) -> None:
        pass
    @property
    def cache(self) -> Any:
        return self._cache
@dataclass
class HistoryPatternMatch:
    pattern_id: str
    pattern_name: str
    severity: str
    confidence: float
    message: str
    file: str
    line: int
    fix_suggestion: str = ""
    extra: dict = field(default_factory=dict)
_NESTING_NODES: tuple = (ast.If, ast.For, ast.While, ast.Try,
                          ast.AsyncFor, TRY_STAR)
_MAX_BRANCH_NESTING = 5
_SLEEP_SECONDS_KW: frozenset[str] = frozenset(
    {"delay", "seconds", "secs", "duration"})
def _sleep_seconds_arg(node: ast.Call) -> ast.expr | None:
    if node.args:
        return node.args[0]
    _kw = next((k for k in node.keywords if k.arg in _SLEEP_SECONDS_KW),
               None)
    return _kw.value if _kw is not None else None
_HP005_MIN_REPORT_SECONDS = 0.2
def _is_wait_duration(arg: ast.expr | None) -> bool:
    while (isinstance(arg, ast.UnaryOp)
           and isinstance(arg.op, (ast.UAdd, ast.USub))):
        arg = arg.operand
    return (isinstance(arg, ast.Constant)
            and isinstance(arg.value, (int, float))
            and not isinstance(arg.value, bool)
            and abs(arg.value) >= _HP005_MIN_REPORT_SECONDS)
_PATH_CONCAT_RE = re.compile(
    r"\+\s*(?:[rRbBuUfF]{1,2})?(['\"])(/[^'\"]*|\\+[^'\"]*)\1")
_PATH_CONCAT_LEFT_RE = re.compile(
    r"(?:[rRbBuUfF]{1,2})?(['\"])(/[^'\"]*|\\+[^'\"]*)\1\s*\+")
_HP004_COMPARE_RE = re.compile(r"\.(?:startswith|endswith)\s*\(")
_HP004_SEP_LITERALS = frozenset(("/", chr(92) + chr(92)))
_HP004_PKG_MARKERS = frozenset(("/__init__.py", "/__init__"))
def _iter_bound_names(target: ast.AST):
    pending: list[ast.AST] = [target]
    while pending:
        cur = pending.pop()
        if isinstance(cur, ast.Name):
            yield cur
        elif isinstance(cur, (ast.Tuple, ast.List)):
            pending.extend(reversed(cur.elts))
        elif isinstance(cur, ast.Starred):
            pending.append(cur.value)
def _count_module_assigns(tree: ast.Module) -> dict[str, int]:
    counts: dict[str, int] = {}
    for node in iter_module_scope_statements(tree):
        for _name in _assign_name_targets(node):
            counts[_name] = counts.get(_name, 0) + 1
    return counts
def _assign_name_targets(node: ast.stmt) -> list[str]:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif (isinstance(node, ast.AugAssign)
            or (isinstance(node, ast.AnnAssign) and node.value is not None)):
        targets = [node.target]
    else:
        targets = []
    return [nm for target in targets for nm in iter_unpack_target_names(target)]
def _unique_path_hits(hits: list) -> list:
    seen: set[int] = set()
    unique: list = []
    for hit, probe_pos in hits:
        # 去重键必须是 ``+`` 运算符位置：右侧模式与左侧模式会匹配同一个
        # 运算符，但两者的 group(2) 分别落在右/左路径字面量上，起点不同，
        # 用 group(2) 起点去重会让同一运算符被保留两次（HP-004 重复上报）。
        key = probe_pos
        if key in seen:
            continue
        seen.add(key)
        unique.append((hit, probe_pos))
    return unique
def _path_concat_hits(line: str) -> list:
    if not _path_concat_candidate_line(line) or line.lstrip().startswith("#"):
        return []
    hits = [(m, m.start()) for m in _PATH_CONCAT_RE.finditer(line)
            if not _path_concat_compare_hit(line, m.start())]
    # 左侧模式以 ``\+`` 结尾，探针必须落在 ``+`` 本身（m.end()-1）：
    # 若用 m.end()（+ 后一字符），"/a"+"b" 这种无空格写法的探针正好落在
    # 右侧字符串的起始引号上，被 _in_str_span 误判为字符串内而漏检。
    hits.extend((m, m.end() - 1) for m in _PATH_CONCAT_LEFT_RE.finditer(line)
                if not _path_concat_compare_hit(line, m.start()))
    return _unique_path_hits(hits)
def _path_concat_candidate_line(line: str) -> bool:
    return ("+" in line
            and any(f"{quote}{separator}" in line
                    for quote in ("'", '"')
                    for separator in ("/", chr(92))))
_QUOTED_TEXT_RE = re.compile(
    r"'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\"")
def _path_concat_compare_hit(line: str, hit_start: int) -> bool:
    masked = _QUOTED_TEXT_RE.sub(lambda m: " " * len(m.group()), line)
    opener = max(
        (match.start()
         for match in _HP004_COMPARE_RE.finditer(masked, 0, hit_start)),
        default=-1)
    if opener < 0:
        return False
    depth = 0
    for char in masked[opener:hit_start]:
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth <= 0:
                return False
    return depth > 0
def _is_swallowed_except(handler: ast.ExceptHandler, lines: list[str],
                         str_spans: list) -> bool:
    return (is_broad_except(handler)
            and all(is_placeholder_stmt(stmt) for stmt in handler.body)
            and not _has_rationale_comment(handler, handler.body, lines,
                                           str_spans))
def _has_rationale_comment(handler: ast.ExceptHandler,
                           body: list[ast.stmt], lines: list[str],
                           str_spans: list) -> bool:
    _end = max([handler.lineno]
               + [getattr(s, "end_lineno", None) or s.lineno for s in body])
    return any(_line_has_comment(lines, ln, str_spans)
               for ln in range(handler.lineno, _end + 1))
def _line_has_comment(lines: list[str], lineno: int,
                      str_spans: list) -> bool:
    if not 0 < lineno <= len(lines):
        return False
    return _first_real_comment_col(lines[lineno - 1], lineno,
                                   str_spans) is not None
def _paired_sequence_names(target, value) -> list[ast.Name] | None:
    if not isinstance(value, (ast.Tuple, ast.List)):
        return None
    if len(target.elts) != len(value.elts):
        return None
    names: list[ast.Name] = []
    for sub_target, sub_value in zip(target.elts, value.elts, strict=True):
        sub_names = _paired_mutable_names(sub_target, sub_value)
        if sub_names is None:
            return None
        names.extend(sub_names)
    return names
def _paired_mutable_names(target, value) -> list[ast.Name] | None:
    if isinstance(target, (ast.Tuple, ast.List)):
        return _paired_sequence_names(target, value)
    if isinstance(target, ast.Starred):
        inner = target.value
        return [inner] if isinstance(inner, ast.Name) else []
    if isinstance(target, ast.Name):
        return [target] if is_mutable_default(value) else []
    return []
def _starred_bound_names(target) -> list[ast.Name]:
    if isinstance(target, ast.Starred):
        return [target.value] if isinstance(target.value, ast.Name) else []
    if isinstance(target, (ast.Tuple, ast.List)):
        return [nm for elt in target.elts
                for nm in _starred_bound_names(elt)]
    return []
def _unique_bound_names(names: list[ast.Name]) -> list[ast.Name]:
    seen: set[str] = set()
    unique: list[ast.Name] = []
    for name in names:
        if name.id in seen:
            continue
        seen.add(name.id)
        unique.append(name)
    return unique
def _mutable_bound_names(node) -> list[ast.Name]:
    if not isinstance(node, ast.Assign):
        if not is_mutable_default(node.value):
            return []
        return _unique_bound_names(list(_iter_bound_names(node.target)))
    names: list[ast.Name] = []
    for target in node.targets:
        paired = _paired_mutable_names(target, node.value)
        if paired is None:
            paired = _starred_bound_names(target)
        names.extend(paired)
    return _unique_bound_names(names)
def _first_real_comment_col(line: str, lineno: int,
                            str_spans: list) -> int | None:
    return next((len(line[:col].encode("utf-8"))
                 for col, ch in enumerate(line)
                 if ch == "#"
                 and not _in_str_span(lineno,
                                      len(line[:col].encode("utf-8")),
                                      str_spans)), None)
def _hp004_hit_excluded(line: str, lineno: int, m,
                        cmt_col, str_spans: list,
                        probe_pos: int) -> bool:
    _hit_byte = len(line[:probe_pos].encode("utf-8"))
    if _in_str_span(lineno, _hit_byte, str_spans):
        return True
    if cmt_col is not None and _hit_byte > cmt_col:
        return True
    literal = m.group(2)
    if _hp004_is_text_literal(literal):
        return True
    marker = _hp004_marker_form(literal)
    return (literal in _HP004_SEP_LITERALS
            or marker in _HP004_PKG_MARKERS)
def _hp004_is_text_literal(literal: str) -> bool:
    return (literal.lstrip("/").lstrip(chr(92))[:1].isspace())
def _hp004_marker_form(literal: str) -> str:
    text = literal.replace(chr(92) * 2, chr(92)).replace(chr(92), "/")
    return "/" + text.lstrip("/")
def _in_str_span(lineno: int, byte_col: int, str_spans) -> bool:
    return bool(str_spans) and any(
        (s_line, s_col) <= (lineno, byte_col) < (e_line, e_col)
        for s_line, s_col, e_line, e_col in str_spans)
def _is_elif_child(parent: ast.AST, child: ast.AST) -> bool:
    return (isinstance(parent, ast.If)
            and isinstance(child, ast.If)
            and getattr(parent, "orelse", None) == [child]
            and child.col_offset == parent.col_offset)
def _is_pass_through_body(body: list, nesting_nodes) -> bool:
    is_ctrl = [isinstance(stmt, nesting_nodes) for stmt in body]
    if sum(is_ctrl) > 1:
        return False
    siblings = [(idx, stmt) for idx, (stmt, ctrl)
                in enumerate(zip(body, is_ctrl, strict=True)) if not ctrl]
    if not siblings:
        return True
    index, stmt = siblings[0]
    return index == 0 and len(siblings) == 1 and is_docstring_stmt(stmt)
def _is_structural_guard(node: ast.AST) -> bool:
    body = getattr(node, "body", None)
    if body is None:
        return False
    if not _is_pass_through_body(body, _NESTING_NODES):
        return False
    if isinstance(node, (ast.For, ast.AsyncFor, ast.Try, TRY_STAR)):
        return True
    return isinstance(node, ast.If) and _is_isinstance_test(node.test)
def _shape_profile(v: ast.AST) -> tuple[bool, bool]:
    if isinstance(v, ast.Call):
        func = v.func
        name = getattr(func, "id", None) or getattr(func, "attr", None)
        is_isinstance = name == "isinstance"
        return is_isinstance, is_isinstance
    if isinstance(v, ast.UnaryOp) and isinstance(v.op, ast.Not):
        return _shape_profile(v.operand)
    if isinstance(v, ast.BoolOp):
        profiles = [_shape_profile(w) for w in v.values]
        return (all(atom for atom, _has in profiles),
                any(has for _atom, has in profiles))
    return isinstance(v, (ast.Name, ast.Attribute)), False
def _is_isinstance_test(test: ast.AST) -> bool:
    atom, has_isinstance = _shape_profile(test)
    return atom and has_isinstance
@dataclass
class _SleepScope:
    parent: _SleepScope | None = None
    kind: str = "module"
    deferred: bool = False
    comprehension: bool = False
    events: dict[str, list[tuple[int, int, str]]] = field(default_factory=dict)
    local_names: set[str] = field(default_factory=set)
    global_names: set[str] = field(default_factory=set)
    nonlocal_names: set[str] = field(default_factory=set)
    type_param_names: set[str] = field(default_factory=set)
    def bind(self, name: str, node: ast.AST, kind: str,
             *, at_end: bool = False) -> None:
        lineno = getattr(node, "lineno", 0)
        col_offset = getattr(node, "col_offset", 0)
        if at_end:
            lineno = getattr(node, "end_lineno", None) or lineno
            end_col = getattr(node, "end_col_offset", None)
            col_offset = col_offset if end_col is None else end_col
        self.local_names.add(name)
        self.events.setdefault(name, []).append((lineno, col_offset, kind))
class _SleepScopeIndex(ast.NodeVisitor):
    def __init__(self):
        self.root = _SleepScope()
        self.scope = self.root
        self.candidate_scopes: dict[int, _SleepScope] = {}
        self.postponed_annotations = False
    def visit_Module(self, node: ast.Module) -> None:
        self.postponed_annotations = any(
            isinstance(stmt, ast.ImportFrom)
            and not stmt.level and stmt.module == "__future__"
            and any(alias.name == "annotations" for alias in stmt.names)
            for stmt in node.body)
        self.generic_visit(node)
    def _binding_scope(self, name: str,
                       scope: _SleepScope | None = None) -> _SleepScope:
        current = self.scope if scope is None else scope
        while current.kind != "module":
            if name in current.global_names:
                return self.root
            if name not in current.nonlocal_names:
                break
            parent = _nonlocal_sleep_parent(current)
            if parent is None:
                break
            current = parent
        return current
    def _bind(self, name: str, node: ast.AST, kind: str,
              *, scope: _SleepScope | None = None,
              at_end: bool = False) -> None:
        owner = self._binding_scope(name, scope)
        owner.bind(name, node, kind, at_end=at_end)
    def _bind_args(self, args: ast.arguments) -> None:
        for arg in iter_arg_nodes(args):
            self._bind(arg.arg, arg, "shadow")
    def _visit_assignment_target(self, target: ast.AST,
                                 position_node: ast.AST) -> None:
        if isinstance(target, ast.Name):
            self._bind(target.id, position_node, "shadow", at_end=True)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._visit_assignment_target(element, position_node)
        elif isinstance(target, ast.Starred):
            self._visit_assignment_target(target.value, position_node)
        else:
            self.visit(target)
    def _push_type_param_scope(self, node, *, deferred: bool):
        outer = self.scope
        self.scope = _SleepScope(
            parent=outer, kind="annotation", deferred=deferred)
        self._bind_type_params(node)
        return outer
    def _visit_type_param_values(self, node) -> None:
        for type_param in getattr(node, "type_params", None) or ():
            for attr in ("bound", "default_value"):
                value = getattr(type_param, attr, None)
                if value is not None:
                    self.visit(value)
    def _visit_type_params(self, node) -> None:
        if not getattr(node, "type_params", None):
            return
        outer = self._push_type_param_scope(node, deferred=True)
        self._visit_type_param_values(node)
        self.scope = outer
    def _bind_type_params(self, node) -> None:
        for type_param in getattr(node, "type_params", None) or ():
            name = getattr(type_param, "name", None)
            if isinstance(name, str) and name:
                self._bind(name, type_param, "shadow")
                self.scope.type_param_names.add(name)
    def _visit_arg_annotations(self, args: ast.arguments) -> None:
        if self.postponed_annotations:
            return
        for arg in iter_arg_nodes(args):
            if arg.annotation is not None:
                self.visit(arg.annotation)
    def _visit_function(self, node) -> None:
        self._bind(node.name, node, "shadow", at_end=True)
        for decorator in node.decorator_list:
            self.visit(decorator)
        type_params = getattr(node, "type_params", None) or ()
        if type_params:
            outer = self._push_type_param_scope(node, deferred=False)
            self._visit_arg_annotations(node.args)
            self.scope = outer
        else:
            self._visit_arg_annotations(node.args)
        for default in (*node.args.defaults, *node.args.kw_defaults):
            if default is not None:
                self.visit(default)
        if node.returns is not None and not self.postponed_annotations:
            if type_params:
                outer = self._push_type_param_scope(node, deferred=False)
                self.visit(node.returns)
                self.scope = outer
            else:
                self.visit(node.returns)
        self._visit_type_params(node)
        outer = self.scope
        self.scope = _SleepScope(parent=outer, kind="function",
                                 deferred=True)
        self._bind_args(node.args)
        self._bind_type_params(node)
        for stmt in node.body:
            self.visit(stmt)
        self.scope = outer
    def visit_FunctionDef(self, node) -> None:
        self._visit_function(node)
    def visit_AsyncFunctionDef(self, node) -> None:
        self._visit_function(node)
    def visit_Lambda(self, node) -> None:
        for default in (*node.args.defaults, *node.args.kw_defaults):
            if default is not None:
                self.visit(default)
        outer = self.scope
        self.scope = _SleepScope(parent=outer, kind="function",
                                 deferred=True)
        self._bind_args(node.args)
        self.visit(node.body)
        self.scope = outer
    def _visit_comprehension(self, node) -> None:
        first, *remaining = node.generators
        self.visit(first.iter)
        outer = self.scope
        self.scope = _SleepScope(
            parent=outer, kind="function",
            deferred=isinstance(node, ast.GeneratorExp), comprehension=True)
        for generator in (first, *remaining):
            if generator is not first:
                self.visit(generator.iter)
            self.visit(generator.target)
            for condition in generator.ifs:
                self.visit(condition)
        if isinstance(node, ast.DictComp):
            self.visit(node.key)
            self.visit(node.value)
        else:
            self.visit(node.elt)
        self.scope = outer
    visit_ListComp = _visit_comprehension
    visit_SetComp = _visit_comprehension
    visit_DictComp = _visit_comprehension
    visit_GeneratorExp = _visit_comprehension
    def visit_ClassDef(self, node) -> None:
        self._bind(node.name, node, "shadow", at_end=True)
        for decorator in node.decorator_list:
            self.visit(decorator)
        if getattr(node, "type_params", None):
            outer = self._push_type_param_scope(node, deferred=False)
            for base in node.bases:
                self.visit(base)
            for keyword in node.keywords:
                self.visit(keyword.value)
            self.scope = outer
        else:
            for base in node.bases:
                self.visit(base)
            for keyword in node.keywords:
                self.visit(keyword.value)
        self._visit_type_params(node)
        outer = self.scope
        self.scope = _SleepScope(parent=outer, kind="class")
        self._bind_type_params(node)
        for stmt in node.body:
            self.visit(stmt)
        self.scope = outer
    def visit_TypeAlias(self, node) -> None:
        self._bind(node.name.id, node, "shadow", at_end=True)
        outer = self._push_type_param_scope(node, deferred=True)
        self._visit_type_param_values(node)
        self.visit(node.value)
        self.scope = outer
    def visit_Import(self, node) -> None:
        for alias in node.names:
            root = alias.name.split(".")[0]
            bound = alias.asname or root
            module_name = alias.name if alias.asname else root
            kind = ("module" if module_name in ("time", "asyncio")
                    else "shadow")
            self._bind(bound, node, kind)
    def visit_ImportFrom(self, node) -> None:
        sleep_module = not node.level and node.module in ("time", "asyncio")
        for alias in node.names:
            if alias.name == "*":
                if sleep_module:
                    self._bind("sleep", node, "direct")
                continue
            bound = alias.asname or alias.name
            kind = "direct" if sleep_module and alias.name == "sleep" else "shadow"
            self._bind(bound, node, kind)
    def visit_Assign(self, node) -> None:
        self.visit(node.value)
        for target in node.targets:
            self._visit_assignment_target(target, node)
    def visit_AugAssign(self, node) -> None:
        if not isinstance(node.target, ast.Name):
            self.visit(node.target)
        self.visit(node.value)
        if isinstance(node.target, ast.Name):
            self._bind(node.target.id, node, "shadow", at_end=True)
    def visit_NamedExpr(self, node) -> None:
        self.visit(node.value)
        owner = self.scope
        while owner.comprehension and owner.parent is not None:
            owner = owner.parent
        self._bind(node.target.id, node, "shadow", scope=owner, at_end=True)
    def _visit_for(self, node) -> None:
        self.visit(node.iter)
        self._visit_assignment_target(node.target, node.iter)
        for stmt in (*node.body, *node.orelse):
            self.visit(stmt)
    visit_For = _visit_for
    visit_AsyncFor = _visit_for
    def visit_Name(self, node) -> None:
        if isinstance(node.ctx, (ast.Store, ast.Del)):
            self._bind(node.id, node, "shadow")
    def visit_Global(self, node) -> None:
        self.scope.global_names.update(node.names)
    def visit_Nonlocal(self, node) -> None:
        self.scope.nonlocal_names.update(node.names)
    def visit_ExceptHandler(self, node) -> None:
        if isinstance(node.name, str):
            self._bind(node.name, node.type or node, "shadow", at_end=True)
        self.generic_visit(node)
    def visit_AnnAssign(self, node) -> None:
        evaluate_annotation = not (
            self.postponed_annotations or self.scope.kind == "function")
        if node.value is None:
            if not isinstance(node.target, ast.Name):
                self.visit(node.target)
            if evaluate_annotation:
                self.visit(node.annotation)
            return
        if evaluate_annotation:
            self.visit(node.annotation)
        self.visit(node.value)
        self._visit_assignment_target(node.target, node)
    def visit_MatchAs(self, node) -> None:
        if node.name is not None:
            self._bind(node.name, node, "shadow")
        self.generic_visit(node)
    def visit_MatchStar(self, node) -> None:
        if node.name is not None:
            self._bind(node.name, node, "shadow")
        self.generic_visit(node)
    def visit_MatchMapping(self, node) -> None:
        if node.rest is not None:
            self._bind(node.rest, node, "shadow")
        self.generic_visit(node)
    def visit_Call(self, node) -> None:
        candidates = []
        _bfs_call_candidate(node, candidates)
        if candidates:
            self.candidate_scopes[id(node)] = self.scope
        self.generic_visit(node)
def _nonlocal_sleep_parent(scope: _SleepScope) -> _SleepScope | None:
    parent = scope.parent
    while parent is not None and parent.kind != "function":
        parent = parent.parent
    return parent
def _sleep_events_at(current: _SleepScope, name: str, node: ast.Call,
                     deferred: bool) -> list:
    events = list(current.events.get(name, ()))
    if deferred:
        return events
    return [event for event in events
            if event[:2] <= (node.lineno, node.col_offset)]
def _sleep_parent_kind(current: _SleepScope,
                       name: str) -> tuple[_SleepScope | None, str | None]:
    parent = current.parent
    if current.kind in ("function", "annotation") and parent is not None \
            and parent.kind == "class":
        if current.kind == "function" and name in parent.type_param_names:
            return None, "shadow"
        return parent.parent, None
    return parent, None
def _sleep_binding_kind(scope: _SleepScope, root: _SleepScope,
                        name: str, node: ast.Call,
                        is_attr: bool) -> str | None:
    current = scope
    deferred = False
    while current is not None:
        if (current.kind == "annotation" and current.parent is not None
                and current.parent.kind == "class"):
            events = _sleep_events_at(
                current.parent, name, node, deferred or current.deferred)
            if events:
                return max(events)[2]
        if current.kind != "module" and name in current.global_names:
            deferred = deferred or current.deferred
            current = root
            continue
        if name in current.nonlocal_names:
            deferred = True
            current = _nonlocal_sleep_parent(current)
            continue
        if name in current.local_names:
            events = _sleep_events_at(current, name, node, deferred)
            if events:
                return max(events)[2]
            if current.kind != "class":
                return None
        if current.deferred:
            deferred = True
        current, verdict = _sleep_parent_kind(current, name)
        if verdict is not None:
            return verdict
    return "module" if is_attr and name in ("time", "asyncio") else None
def _resolve_sleep_calls(tree: ast.Module, sleep_candidates: list) -> list:
    index = _SleepScopeIndex()
    index.visit(tree)
    resolved = []
    for name, is_attr, node in sleep_candidates:
        scope = index.candidate_scopes.get(id(node))
        if scope is None:
            continue
        expected = "module" if is_attr else "direct"
        if _sleep_binding_kind(
                scope, index.root, name, node, is_attr) == expected:
            resolved.append(node)
    return resolved
_NESTING_SKIP_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                       ast.ClassDef)
def _child_nesting_depth(parent: ast.AST, child: ast.AST,
                         depth: int) -> int | None:
    if isinstance(child, _NESTING_SKIP_NODES):
        return None
    if (isinstance(child, _NESTING_NODES)
            and not _is_elif_child(parent, child)
            and not _is_structural_guard(child)):
        return depth + 1
    return depth
def _max_nesting(node: ast.AST, current: int) -> int:
    max_d = current
    stack = [(node, current)]
    while stack:
        cur, depth = stack.pop()
        for fname in STMT_FIELDS.get(cur.__class__, ()):
            for child in getattr(cur, fname, None) or ():
                child_depth = _child_nesting_depth(cur, child, depth)
                if child_depth is None:
                    continue
                max_d = max(max_d, child_depth)
                stack.append((child, child_depth))
    return max_d
def _cached_source_pair(cache, filepath: str, rel_path: str):
    if cache is None:
        return None, None
    try:
        _pair = getattr(cache, "get_source_and_ast", None)
        if _pair is not None:
            return _pair(filepath)
        return cache.get_source(filepath), cache.get_ast(filepath)
    except Exception as _e:
        logger.debug("[HistoryPatternScanner] cache read failed for %s: %s",
                     rel_path, _e)
        return None, None
class HistoryPatternScanner(_SkillScopedEngine):
    PATTERNS: ClassVar[dict[str, dict]] = {
        "HP-001": {
            "name": "裸except捕获",
            "severity": "P2",
            "confidence": 0.7,
            "description": "裸 except（bare except，无异常类型）捕获所有异常；宽泛 except Exception 不在此报（有处理逻辑的宽泛捕获属正常防御式写法，空体吞没场景由 HP-002 报）",
            "suggestion": "指定具体的异常类型，如 ValueError, TypeError 等",
        },
        "HP-002": {
            "name": "异常吞没",
            "severity": "P2",
            "confidence": 0.6,
            "description": "裸/宽泛 except 且块内仅有 pass 或 …（省略号）占位且无注释阐明降级理由（窄类型异常的刻意降级属误报）",
            "suggestion": "收窄异常类型；至少记录异常信息：logging.warning(str(e))",
        },
        "HP-003": {
            "name": "全局可变状态",
            "severity": "P2",
            "confidence": 0.5,
            "description": "模块级可变对象（含带类型注解形态 x: dict = {}、裸内建构造调用 list()/dict()/set()/bytearray()、推导式、含可变元素元组与 [x] * n 复制——与字面量同语义共享可变绑定，仅收字面量会使这些形态整体漏检）且非全大写常量或存在二次赋值（全大写且仅定义一次的常量表属误报；下划线前缀名（含 __all__ 等双下划线 dunder）属单模块私有状态/导出声明，不计入）",
            "suggestion": "使用工厂函数封装，或添加锁保护",
        },
        "HP-004": {
            "name": "字符串拼接路径",
            "severity": "P3",
            "confidence": 0.8,
            "description": "用 + 拼接以分隔符开头的路径字面量（误报豁免：后缀拼接 path + '.bak'；startswith/endswith 比较前缀；裸分隔符 a + '/' + b 逻辑 rel-path 拼接；'/__init__.py' 包标记映射；分隔符后紧跟空白的人类可读文案）",
            "suggestion": "使用 os.path.join() 或 pathlib.Path",
        },
        "HP-005": {
            "name": "硬编码等待",
            "severity": "P3",
            "confidence": 0.6,
            "description": "sleep(常量) 式硬编码等待，含 time.sleep(n)/asyncio.sleep(n) 属性调用与 from time/asyncio import sleep 后的直接调用，位置与等待时长关键字形态（asyncio.sleep(delay=0.5)）同口径（仅上报 |值|≥0.2s 的显著等待，亚秒级渲染/轮询节流不报；显式 timeout=N 传参是最佳实践不报；本地自定义 sleep 函数不报）",
            "suggestion": "提取为可配置常量或环境变量",
        },
        "HP-006": {
            "name": "过深嵌套",
            "severity": "P3",
            "confidence": 0.5,
            "description": "函数体分支有效嵌套深度超过5层（对齐 pylint max-nested-blocks=5 基线；口径=If/For/While/Try，结构遍历型 pass-through 守卫（for 迭代下降/try 容错包装/纯形状匹配链）不计层——BoolOp 组合须全部子条件为形状原子（isinstance 调用/裸存在性真值/not 组合/嵌套 BoolOp）且至少含一个 isinstance 成分才豁免——裸真值仅作辅助成分，独立裸名条件链不豁免；比较/方法调用/in 成员判定等实质逻辑照常计层；elif/with 不计层）",
            "suggestion": "提取子函数降低嵌套",
        },
    }
    def _post_init(self) -> None:
        self.py_files: list[str] = []
        self.skipped_files: list[dict] = []
    def analyze(self) -> list[HistoryPatternMatch]:
        self.skipped_files = []
        self._collect_py_files()
        matches: list[HistoryPatternMatch] = []
        for fp in self.py_files:
            matches.extend(self._scan_file_guarded(fp))
        logger.info("[B2] HistoryPatternScanner 扫描完成: %d 文件, %d 模式命中, %d 跳过",
                    len(self.py_files), len(matches), len(self.skipped_files))
        return matches
    def _scan_file_guarded(self, filepath: str) -> list[HistoryPatternMatch]:
        try:
            return self._scan_file(filepath)
        except Exception as exc:
            rel_path = os.path.relpath(
                filepath, self.skill_dir).replace("\\", "/")
            logger.warning(
                "[HistoryPatternScanner] 单文件扫描意外失败跳过 %s: %s",
                rel_path, exc, exc_info=True)
            self.skipped_files.append({
                "file": rel_path, "reason": "scan_error",
                "error": type(exc).__name__})
            return []
    def _collect_py_files(self):
        walk_errors: list = []
        self.py_files = gate_scan_files_cached(
            self._cache, self.skill_dir, walk_errors)
        for exc in walk_errors:
            logger.warning("[HistoryPatternScanner] 目录遍历失败 %s: %s",
                           self.skill_dir, type(exc).__name__)
            self.skipped_files.append({
                "file": "<walk>", "reason": "walk_error",
                "error": type(exc).__name__})
    def _scan_file(self, filepath: str):
        rel_path = os.path.relpath(filepath, self.skill_dir).replace("\\", "/")
        source, tree = self._load_source_tree(filepath, rel_path)
        if source is None or tree is None:
            return []
        matches: list[HistoryPatternMatch] = []
        lines = source.split("\n")
        handlers, sleep_candidates, func_nodes, str_spans = \
            collect_scan_nodes(tree)
        sleep_calls = _resolve_sleep_calls(tree, sleep_candidates)
        self._check_except_patterns(handlers, lines, rel_path, matches,
                                    str_spans)
        self._check_global_mutables(tree, rel_path, matches)
        self._check_path_concat(lines, rel_path, matches, str_spans)
        self._check_hardcoded_sleeps(sleep_calls, rel_path, matches)
        self._check_nesting_depth(func_nodes, rel_path, matches)
        return matches
    def _load_source_tree(self, filepath: str, rel_path: str):
        source, tree = _cached_source_pair(self._cache, filepath, rel_path)
        if source is None:
            source = self._read_source_or_skip(filepath, rel_path)
            if source is None:
                return None, None
        if tree is None:
            tree = self._parse_source(source, rel_path)
        return (source, tree) if tree is not None else (None, None)
    def _read_source_or_skip(self, filepath: str, rel_path: str):
        try:
            return read_diagnostic_source_strict(filepath)
        except (OSError, UnicodeDecodeError) as _e:
            logger.warning("[HistoryPatternScanner] 读取失败跳过 %s: %s",
                           rel_path, type(_e).__name__)
            self.skipped_files.append(
                {"file": rel_path, "reason": "read_error",
                 "error": type(_e).__name__})
            return None
    def _parse_source(self, source: str, rel_path: str):
        try:
            return ast.parse(source)
        except (SyntaxError, ValueError, RecursionError, MemoryError) as _se:
            logger.warning("[HistoryPatternScanner] 跳过 %s (syntax_error: %s)",
                           rel_path, _se.__class__.__name__)
            self.skipped_files.append(
                {"file": rel_path, "reason": "syntax_error", "error": str(_se)})
            return None
    def _emit(self, pattern_id: str, message: str, rel_path: str, line: int,
              extra: dict | None = None) -> HistoryPatternMatch:
        rule = self.PATTERNS[pattern_id]
        return HistoryPatternMatch(
            pattern_id=pattern_id, pattern_name=rule["name"],
            severity=rule["severity"], confidence=rule["confidence"],
            message=message, file=rel_path, line=line,
            fix_suggestion=rule["suggestion"], extra=extra or {})
    def _check_except_patterns(self, handlers: list, lines: list[str],
                               rel_path: str, targets: list,
                               str_spans: list):
        for node in handlers:
            if node.type is None:
                targets.append(self._emit(
                    "HP-001", "裸 except 捕获所有异常",
                    rel_path, node.lineno))
            if _is_swallowed_except(node, lines, str_spans):
                exc_type = ast.dump(node.type) if node.type else "bare"
                targets.append(self._emit(
                    "HP-002", "宽泛异常被吞没（except块仅有 pass/… 且无降级理由）",
                    rel_path, node.lineno, {"exception_type": exc_type}))
    def _check_global_mutables(self, tree: ast.Module,
                               rel_path: str, targets: list):
        assign_counts = _count_module_assigns(tree)
        for node in iter_module_scope_statements(tree):
            if isinstance(node, ast.Assign) or (
                    isinstance(node, ast.AnnAssign) and node.value is not None):
                self._flag_mutable_assign(node, assign_counts, rel_path, targets)
    def _flag_mutable_assign(self, node, assign_counts: dict[str, int],
                             rel_path: str, targets: list):
        for target in _mutable_bound_names(node):
            if target.id.startswith("_"):
                continue
            if target.id.isupper() and assign_counts.get(target.id, 0) <= 1:
                continue
            targets.append(self._emit(
                "HP-003", f"模块级可变变量 '{target.id}'",
                rel_path, node.lineno, {"var_name": target.id}))
    def _check_path_concat(self, lines: list[str], rel_path: str, targets: list,
                           str_spans: list):
        for i, line in enumerate(lines, 1):
            hits = _path_concat_hits(line)
            if not hits:
                continue
            _cmt_col = _first_real_comment_col(line, i, str_spans)
            for m, probe_pos in hits:
                if _hp004_hit_excluded(
                        line, i, m, _cmt_col, str_spans, probe_pos):
                    continue
                targets.append(self._emit(
                    "HP-004", "使用字符串拼接构造含分隔符的路径", rel_path, i))
    def _check_hardcoded_sleeps(self, calls: list, rel_path: str, targets: list):
        for node in calls:
            arg = _sleep_seconds_arg(node)
            if not _is_wait_duration(arg):
                continue
            targets.append(self._emit(
                "HP-005", f"硬编码等待 sleep({ast.unparse(arg)})",
                rel_path, node.lineno))
    def _check_nesting_depth(self, func_nodes: list, rel_path: str, targets: list):
        for node in func_nodes:
            max_depth = _max_nesting(node, 0)
            if max_depth > _MAX_BRANCH_NESTING:
                targets.append(self._emit(
                    "HP-006",
                    f"函数 '{node.name}' 分支有效嵌套深度 {max_depth}"
                    f"（超过 {_MAX_BRANCH_NESTING}）",
                    rel_path, node.lineno,
                    {"func_name": node.name, "depth": max_depth}))
class HistoryAnalyzer(_SkillScopedEngine):
    def analyze(self) -> dict:
        findings: list[dict] = []
        payload: dict = {}
        files_scanned, pattern_count = self._scan_patterns(findings, payload)
        session_count = self._aggregate_trend(findings, payload)
        return {
            "status": "warn" if findings else "pass",
            "findings_count": len(findings),
            "files_scanned": files_scanned,
            "summary": f"历史分析: {pattern_count}个模式匹配, {session_count}轮趋势",
            "findings": findings,
            "payload": payload,
        }
    def _scan_patterns(self, findings: list, payload: dict) -> tuple[int, int]:
        scanner = HistoryPatternScanner(self.skill_dir, self._cache)
        raw_matches = scanner.analyze()
        for rm in raw_matches:
            findings.append({
                "rule_id": rm.pattern_id,
                "severity": rm.severity,
                "confidence": rm.confidence,
                "message": rm.message,
                "file": rm.file,
                "line": rm.line,
                "source": "B2-pattern",
                "pattern_name": rm.pattern_name,
                "fix_suggestion": rm.fix_suggestion,
            })
        payload["pattern_catalog"] = {k: dict(v) for k, v in HistoryPatternScanner.PATTERNS.items()}
        payload["pattern_matches"] = [{
            "pattern_id": m.pattern_id, "pattern_name": m.pattern_name,
            "severity": m.severity, "file": m.file, "line": m.line,
        } for m in raw_matches]
        if scanner.skipped_files:
            payload["skipped_files"] = scanner.skipped_files
            findings.extend(_skip_file_findings(scanner.skipped_files))
        return len(scanner.py_files), len(raw_matches)
    def _aggregate_trend(self, findings: list, payload: dict) -> int:
        try:
            aggregator = HistoryTrendAggregator(skill_dir=self.skill_dir)
            report = aggregator.aggregate()
            payload["trend_report"] = report.to_dict()
            payload["session_count"] = report.session_count
            if report.session_count > 0 or _has_trend_data(report):
                findings.extend(report.gate_findings())
                payload["method_confidence_multipliers"] = {
                    mid: report.get_method_adjustment(mid)
                    for mid in report.method_trends
                }
            if report.load_error:
                findings.append(_trend_finding(
                    "B2-TREND-LOAD-ERROR", "P3", 0.9,
                    report.load_error, "load_error"))
                payload["trend_error"] = report.load_error
        except Exception as e:
            logger.warning("[HistoryAnalyzer] 趋势聚合异常: %s", e, exc_info=True)
            payload["trend_error"] = str(e)
            findings.append({
                "rule_id": "B2-TREND-ERROR", "severity": "P2",
                "confidence": 0.85, "source": "B2-trend",
                "message": f"趋势聚合异常，本轮趋势通道失效: {str(e)[:120]}",
                "trend_type": "aggregate_error",
            })
        return payload.get("session_count", 0)
def _skip_file_findings(skipped_files: list) -> list[dict]:
    return [{
        "rule_id": "B2-SKIP-FILE", "severity": "P2", "confidence": 0.9,
        "message": (f"文件因 {_sk.get('reason')} 被跳过扫描: "
                    f"{_sk.get('file')} ({str(_sk.get('error', ''))[:80]})"
                    f" —— 该文件 HP 检测全部漏检；"
                    f"若为并行写入暂态，待稳定后复扫确认"),
        "file": _sk.get("file"), "line": 0, "source": "B2-pattern",
    } for _sk in skipped_files]
def run_history_analysis(skill_dir: str, cache: Any = _DEFAULT_CACHE) -> dict:
    require_warmed(cache, "B2 历史模式分析")
    logger.info("[B2] run_history_analysis 开始: %s", skill_dir)
    try:
        return HistoryAnalyzer(skill_dir, cache).analyze()
    except Exception as e:
        logger.warning("[history_analyzer] Exception: %s", e, exc_info=True)
        return {"status": "error", "findings_count": 0,
                "summary": f"历史分析异常: {e}", "findings": [],
                "payload": {}, "files_scanned": 0}
HIGH_FP_RATE_THRESHOLD: float = 0.5
FIXER_GAP_RATE_THRESHOLD: float = 0.7
_ENTRY_OK = "ok"
_ENTRY_EMPTY = "empty"
_ENTRY_DIRTY = "dirty"
@dataclass
class HistoryTrendEntry:
    key: str
    trend_type: str
    total_sessions: int = 0
    recent_fp_rate: float = 0.0
    overall_fp_rate: float = 0.0
    trend_direction: str = "stable"
    confidence_adjustment: float = 1.0
    sample_count: int = 0
    _scores: list[float] = field(default_factory=list, repr=False, compare=False)
    def to_dict(self) -> dict:
        return {
            "key": self.key,
            "trend_type": self.trend_type,
            "total_sessions": self.total_sessions,
            "recent_fp_rate": round(self.recent_fp_rate, 4),
            "overall_fp_rate": round(self.overall_fp_rate, 4),
            "trend_direction": self.trend_direction,
            "confidence_adjustment": round(self.confidence_adjustment, 4),
            "sample_count": self.sample_count,
        }
@dataclass
class HistoryTrendReport:
    generated_at: str = ""
    session_count: int = 0
    method_trends: dict[str, HistoryTrendEntry] = field(default_factory=dict)
    cv_rule_trends: dict[str, HistoryTrendEntry] = field(default_factory=dict)
    fixer_trends: dict[str, HistoryTrendEntry] = field(default_factory=dict)
    global_insights: list[str] = field(default_factory=list)
    unattributed_fp_count: int = 0
    fixer_coverage_gaps: dict[str, int] = field(default_factory=dict)
    load_error: str = ""
    def get_high_fp_methods(self, threshold: float = HIGH_FP_RATE_THRESHOLD) -> list[str]:
        return _threshold_keys(self.method_trends, threshold)
    def get_degrading_methods(self) -> list[str]:
        return sorted(k for k, v in self.method_trends.items()
                      if v.trend_direction == "degrading")
    def get_method_adjustment(self, method_id: str) -> float:
        entry = self.method_trends.get(method_id)
        if entry is None:
            return 1.0
        return entry.confidence_adjustment
    def to_dict(self) -> dict:
        return {
            "generated_at": self.generated_at,
            "session_count": self.session_count,
            "method_trends": {k: v.to_dict() for k, v in self.method_trends.items()},
            "cv_rule_trends": {k: v.to_dict() for k, v in self.cv_rule_trends.items()},
            "fixer_trends": {k: v.to_dict() for k, v in self.fixer_trends.items()},
            "global_insights": self.global_insights,
            "unattributed_fp_count": self.unattributed_fp_count,
            "fixer_coverage_gaps": self.fixer_coverage_gaps,
            "load_error": self.load_error,
        }
    def gate_findings(self) -> list[dict]:
        return [
            *self._method_gate(),
            *self._coverage_gap_gate(),
            *self._cv_rule_gate(),
            *self._unattributed_fp_gate(),
            *self._fixer_gate(),
        ]
    def mark_no_sessions(self) -> None:
        self.session_count = 0
        self.global_insights.append("无历史session数据，方法级置信度调整默认为1.0")
    def clamp_session_count(self, fallback: int) -> None:
        self.session_count = _clean_count(self.session_count, fallback)
    def note_treatment_skips(self, dirty_signals: int,
                             rate_less_signals: int = 0) -> None:
        if self.unattributed_fp_count:
            self.global_insights.append(
                f"治疗确认误报中 {self.unattributed_fp_count} 条 rule_id 缺失无法归因规则，"
                "已跳过规则级统计（需修复上游 evidence 字段或清理历史脏数据）")
        if rate_less_signals:
            self.global_insights.append(
                f"治疗确认误报分布中 {rate_less_signals} 条规则记录（按 session 计）"
                "缺少规则级分母，未折算误报率；"
                "仅采用 high_fp_rate_rule 的 fp_rate/sample_size 信号")
        if dirty_signals:
            self.global_insights.append(
                f"high_fp_rate_rule 误报率信号中 {dirty_signals} 条 rule_id 缺失，"
                "已跳过规则级统计（与确认误报计数分列，不折算条数）")
    def _method_gate(self) -> list:
        gates: list = []
        for key, entry in sorted(self.method_trends.items()):
            if entry.recent_fp_rate > HIGH_FP_RATE_THRESHOLD:
                gates.append(_trend_finding(
                    "B2-HIGH-FP", "P2", 0.80,
                    f"修复器类型 '{key}' 近期修复失败率 {entry.recent_fp_rate:.1%}（失败源于误报或修复器能力不足），建议核查其失败模式",
                    "method", key=key,
                    recent_fp_rate=round(entry.recent_fp_rate, 4),
                    trend_direction=entry.trend_direction,
                    confidence_adjustment=round(entry.confidence_adjustment, 4)))
            if entry.trend_direction == "degrading":
                gates.append(_trend_finding(
                    "B2-DEGRADING", "P2", 0.75,
                    f"修复器类型 '{key}' 修复失败率上升趋势中 (fp_rate: {entry.overall_fp_rate:.1%} -> {entry.recent_fp_rate:.1%})",
                    "method", key=key,
                    overall_fp_rate=round(entry.overall_fp_rate, 4),
                    recent_fp_rate=round(entry.recent_fp_rate, 4)))
        return gates
    def _coverage_gap_gate(self) -> list:
        gates: list = []
        for rule_id, gap_sessions in sorted(self.fixer_coverage_gaps.items()):
            gates.append(_trend_finding(
                "B2-FIXER-COVERAGE-GAP", "P3", 0.75,
                (f"规则 '{rule_id}' 在 {gap_sessions} 轮 session 中存在 "
                 f"confirmed finding 无对应修复器，诊断产出无法转化为修复行动，"
                 f"建议补充修复器（feedback_target=fixer_registry）"),
                "coverage_gap", key=rule_id, gap_sessions=gap_sessions))
        return gates
    def _cv_rule_gate(self) -> list:
        gates: list = []
        for key, entry in sorted(self.cv_rule_trends.items()):
            if entry.recent_fp_rate > HIGH_FP_RATE_THRESHOLD:
                gates.append(_trend_finding(
                    "B2-RULE-FP", "P1", 0.85,
                    f"CV规则 '{key}' 近期误报率 {entry.recent_fp_rate:.1%}，建议调整规则权重",
                    "cv_rule", key=key,
                    recent_fp_rate=round(entry.recent_fp_rate, 4),
                    confidence_adjustment=round(entry.confidence_adjustment, 4)))
        return gates
    def _unattributed_fp_gate(self) -> list:
        if self.unattributed_fp_count <= 0:
            return []
        return [_trend_finding(
            "B2-FP-UNATTRIBUTED", "P3", 0.7,
            (f"治疗阶段确认 {self.unattributed_fp_count} 个误报但证据 rule_id 缺失，"
             f"无法归因规则降权；建议核验历史 session 数据的 evidence 字段"),
            "treatment_fp", unattributed_fp_count=self.unattributed_fp_count)]
    def _fixer_gate(self) -> list:
        gates: list = []
        for key, entry in sorted(self.fixer_trends.items()):
            if entry.recent_fp_rate > FIXER_GAP_RATE_THRESHOLD:
                gates.append(_trend_finding(
                    "B2-FIXER-GAP", "P2", 0.70,
                    f"修复器 '{key}' 能力薄弱 (误报代理率 {entry.recent_fp_rate:.1%})，建议增强修复能力",
                    "fixer", key=key,
                    recent_fp_rate=round(entry.recent_fp_rate, 4)))
        return gates
_CV_RULE_KEY_PREFIXES = ("CV-CONFIDENCE-", "CONFIDENCE_")
def _canonical_rule_key(rule_key: Any) -> str:
    if not isinstance(rule_key, str):
        return ""
    text = rule_key.strip()
    folded = text.casefold()
    for prefix in _CV_RULE_KEY_PREFIXES:
        if folded.startswith(prefix.casefold()):
            return text[len(prefix):].strip()
    return text
def _normalize_history(value: Any) -> dict:
    if isinstance(value, dict):
        return value
    if value is None:
        return {}
    return {"_load_error": f"非对象历史数据: {type(value).__name__}"}
def _clean_trend_table(history: dict, key: str,
                       report: HistoryTrendReport) -> dict:
    table = history.get(key) or {}
    if not isinstance(table, dict):
        report.global_insights.append(
            f"{key} 非对象({type(table).__name__})，已跳过趋势聚合")
        return {}
    return table
def _clean_list(value) -> list:
    if isinstance(value, (list, tuple)):
        return list(value)
    return []
def _clean_count(value, default: int = 0) -> int:
    if isinstance(value, bool):
        return default
    number = _clean_number(value, float(default))
    if number <= 0 or not number.is_integer():
        return default
    return int(number)
def _is_zero_count(value) -> bool:
    if isinstance(value, bool):
        return False
    number = _clean_number(value, float("nan"))
    if not math.isfinite(number) or not number.is_integer():
        return False
    return number == 0
def _valid_sample_size(value) -> bool:
    if isinstance(value, bool):
        return False
    number = _clean_number(value, float("nan"))
    return (math.isfinite(number)
            and number >= 1 and number.is_integer())
def _clean_number(value, default: float) -> float:
    if isinstance(value, bool):
        return default
    if isinstance(value, str):
        text = value.strip()
        if not text:
            return default
        try:
            result = float(text)
        except ValueError as _e:
            logger.debug("非数值字符串归一失败降级: %r (%s)",
                         value, type(_e).__name__)
            return default
        except OverflowError as _e:
            log_swallowed(__name__, _e, context='_clean_number:OverflowError')
            return default
        return result if math.isfinite(result) else default
    if not isinstance(value, (int, float)):
        return default
    try:
        result = float(value)
    except OverflowError as _e:
        log_swallowed(__name__, _e, context='_clean_number:OverflowError')
        return default
    return result if math.isfinite(result) else default
def _percentage_or_none(value) -> float | None:
    number = _clean_number(value, -1.0)
    return number if 0.0 <= number <= 100.0 else None
def _confidence_value(value) -> float | None:
    if isinstance(value, bool):
        return None
    number = _clean_number(value, float("nan"))
    if not math.isfinite(number):
        return None
    return max(0.0, min(1.0, number))
def _confidence_fp_proxies(items: list) -> list:
    scores = []
    for item in items:
        if not isinstance(item, dict):
            logger.debug(
                "反馈条目非对象，按无证据跳过（不影响其余样本）: %s",
                type(item).__name__)
            continue
        conf = _confidence_value(item.get("confidence"))
        if conf is None:
            logger.debug(
                "反馈置信度非有限数值，按无证据跳过: %r",
                item.get("confidence"))
            continue
        scores.append(conf)
    return scores
_TREND_RECENT_WINDOW = 5
_TREND_SLOPE_IMPROVING = -0.05
_TREND_SLOPE_DEGRADING = 0.05
_TREND_ADJUSTMENT_MIN = 0.50
_TREND_ADJUSTMENT_MAX = 1.00
def _finalize_entry_scores(entry: HistoryTrendEntry, scores: list) -> None:
    entry._scores = list(scores)
    if not scores:
        return
    entry.overall_fp_rate = sum(scores) / len(scores)
    recent = scores[-_TREND_RECENT_WINDOW:]
    entry.recent_fp_rate = sum(recent) / len(recent)
    entry.trend_direction = _compute_trend_direction(scores)
    entry.confidence_adjustment = _compute_adjustment(entry)
    entry.sample_count = len(scores)
def _entry_scores(entry: HistoryTrendEntry) -> list[float]:
    if entry._scores:
        return list(entry._scores)
    return [entry.overall_fp_rate] * entry.sample_count
def _merge_trend_entry(target: dict, entry: HistoryTrendEntry) -> None:
    current = target.get(entry.key)
    if current is None:
        target[entry.key] = entry
        return
    scores = _entry_scores(current) + _entry_scores(entry)
    current.total_sessions += entry.total_sessions
    _finalize_entry_scores(current, scores)
def _compute_trend_direction(scores: list[float]) -> str:
    if len(scores) < 3:
        return "stable"
    slope = _least_squares_slope(scores)
    if slope < _TREND_SLOPE_IMPROVING:
        return "improving"
    if slope > _TREND_SLOPE_DEGRADING:
        return "degrading"
    return "stable"
def _least_squares_slope(scores: list[float]) -> float:
    n = len(scores)
    x_mean = (n - 1) / 2.0
    y_mean = sum(scores) / n
    numerator = sum((i - x_mean) * (y - y_mean)
                    for i, y in enumerate(scores))
    denominator = sum((i - x_mean) ** 2 for i in range(n))
    return numerator / denominator
def _compute_adjustment(entry: HistoryTrendEntry) -> float:
    base = 1.0 - entry.recent_fp_rate * 0.5
    if entry.trend_direction == "improving":
        base += 0.05
    elif entry.trend_direction == "degrading":
        base -= 0.10
    return max(_TREND_ADJUSTMENT_MIN,
               min(_TREND_ADJUSTMENT_MAX, round(base, 4)))
def _record_load_error(report: HistoryTrendReport, message: str) -> None:
    report.global_insights.append(message)
    if not report.load_error:
        report.load_error = message
def _clean_sessions(sessions, report: HistoryTrendReport) -> list:
    if isinstance(sessions, tuple):
        sessions = list(sessions)
    if sessions is not None and not isinstance(sessions, list):
        _record_load_error(
            report,
            f"历史 sessions 字段非列表({type(sessions).__name__})，"
            f"趋势数据加载失败，趋势分析本轮不可用")
        return []
    if not sessions:
        return []
    clean = [item for item in sessions if isinstance(item, dict)]
    dirty = [item for item in sessions if not isinstance(item, dict)]
    if not dirty:
        return clean
    _example = type(dirty[0]).__name__
    if clean:
        report.global_insights.append(
            f"历史 sessions 中 {len(dirty)} 个元素非对象"
            f"（如 {_example}）已剔除，"
            f"干净数据照常统计（历史数据损坏，建议检查反馈历史文件）")
        return clean
    _record_load_error(
        report,
        f"历史 sessions 全部 {len(dirty)} 个元素非对象"
        f"（如 {_example}），趋势数据加载失败，"
        f"趋势分析本轮不可用（历史数据损坏，建议检查反馈历史文件）")
    return []
def _format_insight_signal(items: list, label: str, advice: str = "",
                           total: int | None = None) -> str:
    if not items:
        return ""
    count = len(items) if total is None else total
    message = f"{label}({count}个): {items[:5]}"
    return f"{message} -- {advice}" if advice else message
def _threshold_keys(entries: dict, threshold: float) -> list:
    return sorted(k for k, v in entries.items()
                  if v.recent_fp_rate > threshold)
def _has_trend_data(report: HistoryTrendReport) -> bool:
    return bool(report.method_trends or report.cv_rule_trends
                or report.fixer_trends or report.fixer_coverage_gaps
                or report.unattributed_fp_count)
def _insight_high_fp_methods(report: HistoryTrendReport) -> str:
    return _format_insight_signal(
        report.get_high_fp_methods(),
        "高失败率修复器类型", "建议核查其失败模式（误报或能力不足）")
def _insight_degrading_methods(report: HistoryTrendReport) -> str:
    return _format_insight_signal(
        report.get_degrading_methods(),
        "失败率恶化修复器类型", "修复失败率上升中")
def _insight_coverage_gaps(report: HistoryTrendReport) -> str:
    gaps = report.fixer_coverage_gaps
    top_gaps = [k for k, _ in sorted(
        gaps.items(), key=lambda kv: (-kv[1], kv[0]))[:5]]
    return _format_insight_signal(
        top_gaps, "修复器覆盖缺口规则", "建议补充修复器", total=len(gaps))
def _insight_high_fp_rules(report: HistoryTrendReport) -> str:
    return _format_insight_signal(
        _threshold_keys(report.cv_rule_trends, HIGH_FP_RATE_THRESHOLD),
        "高误报CV规则")
def _insight_weak_fixers(report: HistoryTrendReport) -> str:
    return _format_insight_signal(
        _threshold_keys(report.fixer_trends, FIXER_GAP_RATE_THRESHOLD),
        "修复器能力薄弱", "建议增强修复能力")
_INSIGHT_GENERATORS = (
    _insight_high_fp_methods,
    _insight_degrading_methods,
    _insight_coverage_gaps,
    _insight_high_fp_rules,
    _insight_weak_fixers,
)
def _generate_insights(report: HistoryTrendReport) -> None:
    _baseline = len(report.global_insights)
    if report.session_count < 2:
        report.global_insights.append(
            f"历史数据不足({report.session_count}轮session)，趋势分析可靠性有限")
    for make_insight in _INSIGHT_GENERATORS:
        insight = make_insight(report)
        if insight:
            report.global_insights.append(insight)
    if len(report.global_insights) == _baseline:
        report.global_insights.append("历史趋势整体稳定，无需特殊调整")
def _count_unattributed_fp(value, report: HistoryTrendReport) -> None:
    count = _clean_number(value, 0.0)
    if count > 0:
        report.unattributed_fp_count += math.ceil(count)
def _collect_rule_distribution(dist: dict,
                               report: HistoryTrendReport) -> tuple[int, float]:
    attributable = 0
    accounted = 0.0
    for raw_rule_id, n in dist.items():
        count = _clean_number(n, 0.0)
        if count <= 0:
            continue
        accounted += count
        rule_id = _canonical_rule_key(raw_rule_id)
        if not rule_id:
            _count_unattributed_fp(count, report)
            continue
        attributable += 1
    return attributable, accounted
def _collect_fp_confirmed_signals(outcome: dict,
                                  report: HistoryTrendReport) -> int:
    rate_less_signals = 0
    for issue in _clean_list(outcome.get("issues_discovered")):
        dist = _treatment_fp_dist(issue)
        if dist is not None:
            attributable, accounted = _collect_rule_distribution(dist, report)
            rate_less_signals += attributable
            declared = _clean_count(issue.get("fp_confirmed_count"), 0)
            missing = declared - accounted
            if missing > 0:
                _count_unattributed_fp(missing, report)
    return rate_less_signals
def _treatment_fp_dist(issue) -> dict | None:
    if not isinstance(issue, dict):
        return None
    if issue.get("issue_type") != "treatment_fp_confirmed":
        return None
    dist = issue.get("rule_distribution") or {}
    return dist if isinstance(dist, dict) else None
def _collect_high_fp_rule_rates(outcome: dict, session_idx: int,
                                rule_sessions: dict[str, list[float]],
                                session_rules: set) -> int:
    return sum(
        _record_high_fp_rule_rate(
            pattern, session_idx, rule_sessions, session_rules)
        for pattern in _clean_list(outcome.get("failure_patterns"))
        if isinstance(pattern, dict)
        and pattern.get("type") == "high_fp_rate_rule"
    )
def _record_high_fp_rule_rate(pattern: dict, session_idx: int,
                              rule_sessions: dict[str, list[float]],
                              session_rules: set) -> int:
    rule_id = _canonical_rule_key(pattern.get("rule_id"))
    if not rule_id:
        return 1
    session_key = (session_idx, rule_id)
    if session_key in session_rules:
        return 0
    if _append_rule_rate(pattern, rule_id, rule_sessions):
        session_rules.add(session_key)
    return 0
def _append_rule_rate(pattern: dict, rule_id: str,
                      rule_sessions: dict[str, list[float]]) -> bool:
    if not _valid_sample_size(pattern.get("sample_size")):
        return False
    fp_rate = _percentage_or_none(pattern.get("fp_rate"))
    if fp_rate is None:
        return False
    rule_sessions.setdefault(rule_id, []).append(fp_rate / 100.0)
    return True
def _merge_rule_sessions(rule_sessions: dict[str, list[float]],
                         report: HistoryTrendReport) -> None:
    for rule_id, scores in rule_sessions.items():
        entry = report.cv_rule_trends.get(rule_id)
        if entry is None:
            entry = HistoryTrendEntry(key=rule_id, trend_type="cv_rule")
            report.cv_rule_trends[rule_id] = entry
        merged_scores = _entry_scores(entry) + scores
        entry.total_sessions += len(scores)
        _finalize_entry_scores(entry, merged_scores)
def _collect_fixer_weakness(pattern: dict,
                            method_data: dict[str, dict]) -> None:
    if pattern.get("type") != "fixer_type_weakness":
        return
    if not _valid_sample_size(pattern.get("sample_size")):
        return
    fixer_type = _fixer_type_of(pattern)
    percentage = _percentage_or_none(pattern.get("success_rate"))
    if percentage is None:
        return
    method_data.setdefault(fixer_type, {"scores": []})["scores"].append(
        1.0 - percentage / 100.0)
def _fixer_type_of(pattern: dict) -> str:
    fixer_type = pattern.get("fixer_type", "unknown")
    if isinstance(fixer_type, str) and fixer_type.strip():
        return fixer_type.strip()
    return "unknown"
def _collect_coverage_gap(issue: dict, session_idx: int,
                          coverage_gaps: dict[str, int],
                          session_gap_rules: set) -> None:
    if issue.get("issue_type") != "fixer_coverage_gap":
        return
    for raw_rule in _clean_list(issue.get("unfixable_rules")):
        rule = _canonical_rule_key(raw_rule)
        if not rule:
            continue
        if (session_idx, rule) in session_gap_rules:
            continue
        session_gap_rules.add((session_idx, rule))
        coverage_gaps[rule] = coverage_gaps.get(rule, 0) + 1
def _collect_method_signals(outcome: dict, session_idx: int,
                            method_data: dict[str, dict],
                            coverage_gaps: dict[str, int],
                            session_gap_rules: set) -> None:
    for pattern in _clean_list(outcome.get("failure_patterns")):
        if isinstance(pattern, dict):
            _collect_fixer_weakness(pattern, method_data)
    for issue in _clean_list(outcome.get("issues_discovered")):
        if isinstance(issue, dict):
            _collect_coverage_gap(
                issue, session_idx, coverage_gaps, session_gap_rules)
def _iter_session_outcomes(sessions: list):
    for session in sessions:
        outcome = session.get("outcome_summary", {}) or {}
        yield outcome if isinstance(outcome, dict) else {}
def _cv_rule_entry(rule_key: Any, rule_data: Any) -> tuple[HistoryTrendEntry | None, str]:
    key = _canonical_rule_key(rule_key)
    if not key or not isinstance(rule_data, dict):
        return None, _ENTRY_DIRTY
    raw_adjustments = rule_data.get("adjustments")
    if raw_adjustments is not None and not isinstance(raw_adjustments, (list, tuple)):
        return None, _ENTRY_DIRTY
    adjustments = _clean_list(raw_adjustments)
    raw_count = rule_data.get("trigger_count", 0)
    trigger_count = _clean_count(raw_count)
    if not adjustments and trigger_count <= 0:
        if _is_zero_count(raw_count):
            return None, _ENTRY_EMPTY
        return None, _ENTRY_DIRTY
    scores = _confidence_fp_proxies(adjustments)
    if adjustments and not scores:
        return None, _ENTRY_DIRTY
    entry = HistoryTrendEntry(
        key=key, trend_type="cv_rule",
        total_sessions=max(trigger_count, len(adjustments)),
    )
    _finalize_entry_scores(entry, scores)
    return entry, _ENTRY_OK
def _fixer_entry(fixer_key: Any, fixer_data: Any) -> tuple[HistoryTrendEntry | None, str]:
    key = _canonical_rule_key(fixer_key)
    if not key or not isinstance(fixer_data, dict):
        return None, _ENTRY_DIRTY
    raw_feedbacks = fixer_data.get("feedbacks")
    if raw_feedbacks is not None and not isinstance(raw_feedbacks, (list, tuple)):
        return None, _ENTRY_DIRTY
    feedbacks = _clean_list(raw_feedbacks)
    raw_count = fixer_data.get("request_count", 0)
    request_count = _clean_count(raw_count)
    if not feedbacks and request_count <= 0:
        if _is_zero_count(raw_count):
            return None, _ENTRY_EMPTY
        return None, _ENTRY_DIRTY
    scores = _confidence_fp_proxies(feedbacks)
    if feedbacks and not scores:
        return None, _ENTRY_DIRTY
    entry = HistoryTrendEntry(
        key=key, trend_type="fixer",
        total_sessions=max(request_count, len(feedbacks)),
    )
    _finalize_entry_scores(entry, scores)
    return entry, _ENTRY_OK
def _aggregate_entry_table(history: dict, key: str, entry_factory,
                           target: dict, report: HistoryTrendReport,
                           dirty_reason: str) -> None:
    table = _clean_trend_table(history, key, report)
    empty = 0
    skipped = 0
    for entry_key, entry_data in table.items():
        entry, verdict = entry_factory(entry_key, entry_data)
        if verdict == _ENTRY_EMPTY:
            empty += 1
            continue
        if verdict != _ENTRY_OK or entry is None:
            skipped += 1
            continue
        _merge_trend_entry(target, entry)
    if empty:
        report.global_insights.append(
            f"{key} 含 {empty} 条无信号条目，已跳过趋势聚合")
    if skipped:
        report.global_insights.append(
            f"{key} 含 {skipped} 条{dirty_reason}，已跳过趋势聚合")
def _trend_finding(rule_id: str, severity: str, confidence: float,
                   message: str, trend_type: str, **fields) -> dict:
    finding = {
        "rule_id": rule_id, "severity": severity,
        "confidence": confidence, "source": "B2-trend",
        "message": message, "trend_type": trend_type,
    }
    finding.update(fields)
    return finding
class HistoryTrendAggregator:
    def __init__(self, history_data: dict | None = _DEFAULT_HISTORY_DATA,
                 skill_dir: str = ""):
        self._history = history_data
        self._skill_dir = os.fspath(skill_dir) if skill_dir else ""
    def _resolve_history(self, history_data: dict | None) -> dict:
        if history_data is not None:
            return history_data
        if self._history is not None:
            return self._history
        return self._load_history()
    def _load_history(self) -> dict:
        if not self._skill_dir:
            return _normalize_history(self._history)
        try:
            data = read_evolution_section(self._skill_dir, "feedback_history")
        except (OSError, ValueError, TypeError) as e:
            logger.warning("HistoryTrendAggregator: 读取反馈历史失败: %s", e)
            return {"_load_error": f"{type(e).__name__}: {e}"}
        if data is None:
            return {}
        if not isinstance(data, dict):
            return {"_load_error": f"非对象JSON: {type(data).__name__}"}
        return data
    def aggregate(
            self, history_data: dict | None = _DEFAULT_HISTORY_DATA,
    ) -> HistoryTrendReport:
        history = _normalize_history(self._resolve_history(history_data))
        report = HistoryTrendReport(
            generated_at=datetime.now().isoformat(),
            session_count=history.get("session_count", 0),
        )
        if history.get("_load_error"):
            _record_load_error(
                report,
                f"历史数据加载失败({history['_load_error']})，趋势分析本轮不可用")
        sessions = self._prepare_sessions(history, report)
        if sessions is not None:
            self._aggregate_method_trends(sessions, report)
        _aggregate_entry_table(
            history, "cv_rule_weights", _cv_rule_entry,
            report.cv_rule_trends, report, "脏键/建议值条目")
        _aggregate_entry_table(
            history, "fixer_needs", _fixer_entry,
            report.fixer_trends, report, "空键/脏值条目")
        if sessions is not None:
            self._aggregate_treatment_fp_trends(sessions, report)
        _generate_insights(report)
        return report
    def _prepare_sessions(self, history: dict,
                          report: HistoryTrendReport) -> list | None:
        sessions = _clean_sessions(history.get("sessions"), report)
        if not sessions:
            report.mark_no_sessions()
            return None
        report.clamp_session_count(len(sessions))
        return sessions
    def _aggregate_treatment_fp_trends(self, sessions: list,
                                       report: HistoryTrendReport):
        rule_sessions: dict[str, list[float]] = {}
        _dirty_rate_signals = 0
        _rate_less_signals = 0
        _session_rules: set[tuple[int, str]] = set()
        for _si, outcome in enumerate(_iter_session_outcomes(sessions)):
            _dirty_rate_signals += _collect_high_fp_rule_rates(
                outcome, _si, rule_sessions, _session_rules)
            _rate_less_signals += _collect_fp_confirmed_signals(outcome, report)
        _merge_rule_sessions(rule_sessions, report)
        report.note_treatment_skips(_dirty_rate_signals, _rate_less_signals)
    def _aggregate_method_trends(self, sessions: list, report: HistoryTrendReport):
        method_data: dict[str, dict] = {}
        coverage_gaps: dict[str, int] = {}
        _session_gap_rules: set[tuple[int, str]] = set()
        for _si, outcome in enumerate(_iter_session_outcomes(sessions)):
            _collect_method_signals(
                outcome, _si, method_data, coverage_gaps, _session_gap_rules)
        report.fixer_coverage_gaps = coverage_gaps
        for key, data in method_data.items():
            scores = data["scores"]
            entry = HistoryTrendEntry(
                key=key, trend_type="method", total_sessions=len(scores))
            _finalize_entry_scores(entry, scores)
            report.method_trends[key] = entry
def iter_module_scope_statements(tree: ast.Module):
    stack = list(reversed(getattr(tree, "body", None) or []))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        yield node
        _push_scope_children(stack, node)
def _push_match_case_bodies(stack: list, node: ast.AST) -> None:
    for _case in reversed(getattr(node, "cases", None) or []):
        stack.extend(reversed(getattr(_case, "body", None) or []))
def _push_scope_children(stack: list, node: ast.AST) -> None:
    fields = STMT_FIELDS.get(node.__class__, ())
    if "cases" in fields:
        _push_match_case_bodies(stack, node)
        return
    for attr in reversed(fields):
        stack.extend(reversed(getattr(node, attr, None) or []))
_CHILD_FIELDS: dict[type, tuple[str, ...]] = {}
def _bfs_call_candidate(node: ast.Call, sleep_candidates: list) -> None:
    if not (node.args or node.keywords):
        return
    _fn = node.func
    if _fn.__class__ is ast.Attribute and _fn.attr == "sleep":
        _owner = _fn.value.id if _fn.value.__class__ is ast.Name else None
        sleep_candidates.append((_owner, True, node))
    elif _fn.__class__ is ast.Name:
        sleep_candidates.append((_fn.id, False, node))
def _learn_child_fields(node: ast.AST) -> tuple[str, ...]:
    _keep = []
    for _fname in node._fields:
        _v = getattr(node, _fname, None)
        if _v is None or _v.__class__ is list or isinstance(_v, ast.AST):
            _keep.append(_fname)
    _cf = tuple(_keep)
    _CHILD_FIELDS[node.__class__] = _cf
    return _cf
def _push_field_children(_v, push) -> None:
    if isinstance(_v, ast.AST):
        push(_v)
    elif _v.__class__ is list:
        for _c in _v:
            if isinstance(_c, ast.AST):
                push(_c)
def _bfs_push_children(node: ast.AST, push) -> None:
    _cls = node.__class__
    _cf = _CHILD_FIELDS.get(_cls)
    if _cf is None:
        _cf = _learn_child_fields(node)
    for _fname in _cf:
        _push_field_children(getattr(node, _fname, None), push)
def _collect_str_span(node: ast.Constant, str_spans: list) -> None:
    if isinstance(node.value, str):
        str_spans.append((node.lineno, node.col_offset,
                          node.end_lineno, node.end_col_offset))
def _collect_scan_node(node: ast.AST, out: list, push) -> None:
    if isinstance(node, ast.ExceptHandler):
        out[0].append(node)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        out[2].append(node)
    elif isinstance(node, ast.Call):
        _bfs_call_candidate(node, out[1])
    elif isinstance(node, ast.Constant):
        _collect_str_span(node, out[3])
    _bfs_push_children(node, push)
def collect_scan_nodes(tree: ast.Module) -> tuple[list, list, list, list]:
    out: list = [[], [], [], []]
    _todo = deque([tree])
    _push = _todo.append
    while _todo:
        _collect_scan_node(_todo.popleft(), out, _push)
    return tuple(out)
STMT_FIELDS: dict[type, tuple[str, ...]] = {
    ast.Module: ("body",),
    ast.FunctionDef: ("body",),
    ast.AsyncFunctionDef: ("body",),
    ast.ClassDef: ("body",),
    ast.If: ("body", "orelse"),
    ast.For: ("body", "orelse"),
    ast.AsyncFor: ("body", "orelse"),
    ast.While: ("body", "orelse"),
    ast.With: ("body",),
    ast.AsyncWith: ("body",),
    ast.Try: ("body", "handlers", "orelse", "finalbody"),
    ast.ExceptHandler: ("body",),
}
if hasattr(ast, "Match"):
    STMT_FIELDS[ast.Match] = ("cases",)
    STMT_FIELDS[ast.match_case] = ("body",)
if hasattr(ast, "TryStar"):
    STMT_FIELDS[ast.TryStar] = ("body", "handlers", "orelse", "finalbody")
class _RetiredBundle(NamedTuple):
    count: int
    by_rule: dict
    detail: list
    truncated: bool
    def payload_fields(self) -> dict:
        return {
            "retired_by_rule": self.by_rule,
            "retired_count": self.count,
            "retired_findings_detail": self.detail,
            "retired_detail_truncated": self.truncated,
            "retired_source_skipped": sorted(RETIRED_RULE_IDS),
        }
def _extended_findings(engine: _SkillScopedEngine,
                       detector_stats: dict) -> list:
    raw = run_extended_detectors(engine.skill_dir, engine.py_files)
    if not isinstance(raw, tuple) or len(raw) != 2:
        raise TypeError(
            "run_extended_detectors 返回非 (issues, failures) 二元组"
            f"({type(raw).__name__})")
    issues_segment, failures = raw
    shaped = coerce_dimension_issues(issues_segment)
    if shaped is None:
        raise TypeError(
            "run_extended_detectors 的 issues 段非 list/tuple 形态"
            f"({type(issues_segment).__name__})")
    if (not isinstance(failures, int) or isinstance(failures, bool)
            or failures < 0):
        logger.warning(
            "[UnifiedAstEngine] extended failures 段非法(%r)，通道按失败处理",
            failures)
        raise TypeError(
            "run_extended_detectors 的 failures 段必须为非负 int"
            f"({failures!r})")
    detector_stats["extended_failures"] = failures
    return shaped
class UnifiedAstEngine(_SkillScopedEngine):
    def _post_init(self) -> None:
        self.py_files: list[str] = collect_scan_py_files(self.skill_dir)
    def _run_dimensions_serial(self, detector_stats: dict) -> tuple:
        dimension_factories = {
            "file": lambda eng: run_file_detectors(eng.py_files, eng.cache),
            "extended": partial(_extended_findings,
                                detector_stats=detector_stats),
            "exception": lambda eng: run_exception_detector(
                eng.skill_dir, _diag_ctx_of(eng.cache)),
            "antipattern": lambda eng: run_antipattern_detector(eng.skill_dir),
            "hallucination": lambda eng: run_hallucination_detector(eng.skill_dir),
            "cohesion": lambda eng: _run_cohesion_dimension(
                eng.skill_dir, eng.cache),
        }
        _dim_run = run_dimension_channels(self.cache, dimension_factories, self)
        return _dim_run.results, _dim_run.failed_dims, _dim_run.timers
    def analyze(self) -> dict:
        detector_stats: dict[str, int] = {}
        _run_start_ts = time.time()
        _results, _failed_dims, _dim_timers = self._run_dimensions_serial(
            detector_stats)
        all_findings, _dim_counts, _dropped_scope, _dropped_malformed = \
            collect_scope_filtered_findings(
                _results, DIM_ORDER,
                is_out_of_scope=partial(is_diagnosis_out_of_scope,
                                        root_dir=self.skill_dir))
        detector_stats.update(_dim_counts)
        if _dropped_malformed:
            logger.warning(
                "[UnifiedAstEngine] 域过滤剔除非 dict 畸形条目 %d 条",
                _dropped_malformed)
        if _dropped_scope:
            logger.info(
                "[UnifiedAstEngine] 域过滤剔除 tests/Temp 范围外发现 %d 条",
                _dropped_scope)
        try:
            a2_metadata = _density_metadata(_results, detector_stats)
        except Exception as _density_exc:
            logger.warning("[UnifiedAstEngine] 密度后处理失败降级: %s",
                           _density_exc, exc_info=True)
            detector_stats["density"] = 0
            _failed_dims["density"] = (
                f"density post-process error: {type(_density_exc).__name__}")
            a2_metadata = {
                "issues": [], "density_hotspots": [],
                "total_violations": 0, "file_violation_count": {},
            }
        all_findings, retired, _, source_drift_findings = \
            self._sanitize_findings(all_findings, detector_stats, _run_start_ts)
        severity_counts, rule_counts, total, score = aggregate_stats(all_findings)
        _b1_verdict, _b1_verdict_reason = verdict_from_severity_counts(
            severity_counts)
        _b1_status = _b1_status_from(
            severity_counts, detector_stats, _failed_dims,
            source_drift_findings)
        if _b1_status == "error":
            _b1_verdict = "unknown"
            _b1_verdict_reason = "扫描执行不完整，结论不可用"
        summary_parts = _b1_summary_parts(
            detector_stats, _failed_dims, source_drift_findings,
            total, score, retired.count,
            verdict=_b1_verdict, verdict_reason=_b1_verdict_reason)
        final_detector_stats = {**detector_stats, "_failed_dims": _failed_dims}
        return {
            "status": _b1_status,
            "verdict": _b1_verdict,
            "verdict_reason": _b1_verdict_reason,
            "findings_count": total,
            "files_scanned": len(self.py_files),
            "findings": all_findings,
            "score": score,
            "by_severity": severity_counts,
            "by_rule": rule_counts,
            "detector_stats": final_detector_stats,
            "summary": ", ".join(summary_parts),
            "a2_metadata": a2_metadata,
            "payload": self._analysis_payload(
                final_detector_stats, severity_counts, rule_counts, retired,
                _dim_timers, a2_metadata, source_drift_findings),
        }
    def _analysis_payload(self, detector_stats: dict,
                          severity_counts: dict, rule_counts: dict,
                          retired: _RetiredBundle, _dim_timers: dict,
                          a2_metadata: dict,
                          source_drift_findings: list) -> dict:
        return {
            "file_count": len(self.py_files),
            "detector_stats": detector_stats,
            "severity_summary": severity_counts,
            "rule_summary": rule_counts,
            **retired.payload_fields(),
            "dim_timers": _dim_timers,
            "a2_density_hotspots": a2_metadata.get("density_hotspots", []),
            "source_drift_findings": source_drift_findings,
        }
    def _sanitize_findings(self, all_findings: list, detector_stats: dict,
                           run_start_ts: float,
                           ) -> tuple[list, _RetiredBundle, int, list]:
        (all_findings, retired_count, retired_by_rule, retired_detail,
         retired_truncated, _bad_retired) = filter_retired(all_findings)
        if _bad_retired:
            logger.warning("[UnifiedAstEngine] 退役过滤剔除非 dict 畸形条目 %d 条",
                           _bad_retired)
        all_findings, _dup_count, _bad_dedup = dedup_cross_dim(all_findings)
        if _bad_dedup:
            logger.warning("[UnifiedAstEngine] 跨维度去重剔除非 dict 畸形条目 %d 条",
                           _bad_dedup)
        if _dup_count:
            logger.info("[UnifiedAstEngine] 跨维度去重剔除重复发现 %d 条", _dup_count)
            detector_stats["cross_dim_deduped"] = _dup_count
        source_drift_findings = mark_source_drift(
            self.skill_dir, all_findings, run_start_ts)
        if source_drift_findings:
            logger.warning(
                "[UnifiedAstEngine] 源漂移守卫: %d 条发现的文件在运行期间被修改",
                len(source_drift_findings))
        retired = _RetiredBundle(retired_count, retired_by_rule,
                                 retired_detail, retired_truncated)
        return all_findings, retired, _dup_count, source_drift_findings
def _density_metadata(_results: dict, detector_stats: dict) -> dict:
    density_result = run_density_post_processor(
        _results.get("antipattern", []))
    density_issues = density_result.get("issues", [])
    detector_stats["density"] = len(density_issues)
    return {
        "issues": density_issues,
        "density_hotspots": density_result.get("density_hotspots", []),
        "total_violations": density_result.get("total_violations", 0),
        "file_violation_count": density_result.get("file_violation_count", {}),
    }
def _b1_summary_parts(detector_stats: dict, failed_dims: dict,
                      source_drift_findings: list, total: int, score,
                      retired_count: int,
                      verdict: str = "", verdict_reason: str = "") -> list:
    parts = [f"AST统一检测: {total}个发现, 评分{score}"]
    if verdict and verdict != "pass":
        _verdict_text = f"结论:{verdict}"
        if verdict_reason:
            _verdict_text += f"({verdict_reason})"
        parts.append(_verdict_text)
    if retired_count:
        parts.append(f"retired_filtered:{retired_count}")
    parts.extend(f"{key}:{count}"
                 for key, count in sorted(detector_stats.items())
                 if count > 0 and not key.endswith("_failures"))
    _ext_failures = detector_stats.get("extended_failures", 0) or 0
    if _ext_failures > 0:
        parts.append(f"extended失败:{_ext_failures}")
    if failed_dims:
        parts.append(
            f"维度失败:{len(failed_dims)}个({','.join(failed_dims.keys())})")
    if source_drift_findings:
        parts.append(
            f"source_drift:{len(source_drift_findings)}"
            f"(文件运行中被修改,须复扫采信)")
    return parts
def _b1_status_from(severity_counts: dict, detector_stats: dict,
                    failed_dims: dict,
                    source_drift_findings: list | None = None) -> str:
    """B1 执行健康：只反映扫描完整性，不承载缺陷严重度。

    P0/P1 计数属于诊断结论（verdict），由 verdict_from_severity_counts 给出；
    把严重度写成 status 会让下游把「发现 P0」误读为「方法执行失败」。
    """
    del severity_counts
    return (
        "error" if (detector_stats.get("extended_failures", 0) > 0
                    or failed_dims or source_drift_findings) else "pass"
    )
def _has_source_drift(result: Any) -> bool:
    if not isinstance(result, dict):
        return False
    payload = result.get("payload")
    return (isinstance(payload, dict)
            and bool(payload.get("source_drift_findings")))
def run_b1_unified_ast_analysis(
        skill_dir: str, cache: Any = _DEFAULT_CACHE) -> dict:
    require_warmed(cache, "B1 AST 核心检测")
    _slots = getattr(cache, "slots", None) if cache is not None else None
    _slot_get = getattr(_slots, "slot_get", None)
    _slot_set = getattr(_slots, "slot_set", None)
    try:
        cached = (_slot_get("unified_ast_result")
                  if _slot_get is not None else None)
        if cached is not None and not _has_source_drift(cached):
            logger.info("[B1] 复用缓存中的 UnifiedAstEngine 结果")
            return cached
        if cached is not None:
            logger.warning("[B1] 缓存结果含源漂移证据，丢弃复用并重新扫描")
        engine = UnifiedAstEngine(skill_dir, cache)
        result = engine.analyze()
        if _slot_set is not None and not _has_source_drift(result):
            _slot_set("unified_ast_result", result)
        return result
    except Exception as e:
        logger.warning("[B1] AST 统一检测异常: %s", e, exc_info=True)
        return {
            "status": "error",
            "verdict": "unknown",
            "verdict_reason": "",
            "findings_count": 0,
            "files_scanned": None,
            "summary": f"AST统一检测错误: {e}",
            "findings": [],
            "score": 0,
            "by_severity": {},
            "by_rule": {},
            "detector_stats": {},
            "a2_metadata": {},
            "payload": {},
        }
def _diag_ctx_of(cache):
    if cache is not None and hasattr(cache, "slots"):
        return as_diag_ctx(cache)
    return None
def _active_cohesion_rules() -> set:
    return COHESION_RULE_IDS - RETIRED_RULE_IDS
def _cohesion_findings(skill_dir: str, cache: Any,
                       active_rules: set) -> list[dict]:
    result = CohesionAnalyzer(skill_dir, cache=cache).analyze(
        active_rules=active_rules)
    return result_to_b1_findings(result)
def _run_cohesion_dimension(skill_dir: str, cache: Any) -> list[dict]:
    _t0 = time.monotonic()
    _active_cohesion = _active_cohesion_rules()
    _outcome = "ok"
    _findings: list[dict] = []
    try:
        if not _active_cohesion:
            logger.info("[UnifiedAstEngine] cohesion 维度前置跳过 "
                        "(全部产出规则已退役: %s)", sorted(COHESION_RULE_IDS))
        else:
            _findings = _cohesion_findings(
                skill_dir, cache, _active_cohesion)
        return _findings
    except Exception as e:
        logger.warning("[UnifiedAstEngine] cohesion 维度异常: %s", e)
        _outcome = "degraded"
        raise
    finally:
        write_module_run(
            "engine_b2_history", "_run_cohesion_dimension",
            outcome=_outcome,
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            findings=len(_findings), active_rules=len(_active_cohesion))
DIM_ORDER = ("file", "extended", "exception", "antipattern", "hallucination", "cohesion")
_RETIRED_DETAIL_CAP = 2000
def _account_retired_one(f: dict, rid: str, retired_by_rule: dict,
                         retired_detail: list) -> bool:
    sev = _severity_of(f)
    retired_by_rule.setdefault(rid, {})
    retired_by_rule[rid][sev] = retired_by_rule[rid].get(sev, 0) + 1
    if len(retired_detail) < _RETIRED_DETAIL_CAP:
        retired_detail.append({
            "rule_id": rid,
            "severity": sev,
            "file": finding_file(f),
            "line": finding_line(f),
            "message": str(f.get("message", ""))[:160],
        })
        return False
    return True
def filter_retired(
    findings: list[dict],
) -> tuple[list[dict], int, dict[str, dict[str, int]], list[dict], bool, int]:
    retired_count = 0
    retired_by_rule: dict[str, dict[str, int]] = {}
    retired_detail: list[dict] = []
    retired_detail_truncated = False
    dropped_malformed, _dicts = split_malformed_issues(findings)
    if not RETIRED_RULE_IDS:
        return (findings if dropped_malformed == 0 else _dicts,
                0, {}, [], False, dropped_malformed)
    kept: list[dict] = []
    for f in _dicts:
        rid = finding_rule_id(f)
        if not is_retired_rule(rid):
            kept.append(f)
            continue
        retired_count += 1
        retired_detail_truncated |= _account_retired_one(
            f, rid, retired_by_rule, retired_detail)
    return (kept, retired_count, retired_by_rule, retired_detail,
            retired_detail_truncated, dropped_malformed)
def dedup_cross_dim(findings: list[dict]) -> tuple[list[dict], int, int]:
    dropped_malformed, dicts = split_malformed_issues(findings)
    seen_keys: dict[tuple, int] = {}
    dup_count = 0
    deduped: list[dict] = []
    for f in dicts:
        key = _dedup_key(f)
        if key in seen_keys:
            dup_count += 1
            kept_index = seen_keys[key]
            current = deduped[kept_index]
            current_severity = _severity_of(current)
            candidate_severity = _severity_of(f)
            if (SEVERITY_RANK[candidate_severity]
                    < SEVERITY_RANK[current_severity]):
                promoted = dict(current)
                promoted["severity"] = candidate_severity
                deduped[kept_index] = promoted
            continue
        seen_keys[key] = len(deduped)
        deduped.append(f)
    return deduped, dup_count, dropped_malformed
def _severity_of(f: dict) -> str:
    _sev = f.get("severity")
    if not isinstance(_sev, str) or not _sev:
        return "P3"
    return normalize_severity(_sev)
_DEDUP_LINE_KEYS = ("line", "lineno", "line_no", "line_number")
def _numeric_line_token(value) -> str | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        return str(int(value)) if value.is_integer() else None
    text = str(value).strip()
    if not text:
        return None
    try:
        number = float(text)
    except ValueError:
        return None
    return str(int(number)) if number.is_integer() else None
def _dedup_line_token(f: dict) -> str:
    _line = finding_line(f)
    if _line > 0:
        return str(_line)
    raw_values: list[str] = []
    for key in _DEDUP_LINE_KEYS:
        _value = f.get(key)
        if _value is None or _value == "" or isinstance(_value, bool):
            continue
        _token = _numeric_line_token(_value)
        if _token is not None:
            return _token
        raw_values.append(repr(_value))
    return f"raw:{'|'.join(raw_values)}" if raw_values else "0"
def _dedup_key(f: dict) -> tuple[str, str, str, str]:
    return (finding_rule_id(f), finding_file(f), _dedup_line_token(f),
            str(f.get("message") or ""))
def aggregate_stats(
    findings: list[dict],
) -> tuple[dict[str, int], dict[str, int], int, int]:
    severity_counts: dict[str, int] = {}
    rule_counts: dict[str, int] = {}
    total = 0
    _, dicts = split_malformed_issues(findings)
    for f in dicts:
        sev = _severity_of(f)
        severity_counts[sev] = severity_counts.get(sev, 0) + 1
        rid = finding_rule_id(f) or "UNKNOWN"
        rule_counts[rid] = rule_counts.get(rid, 0) + 1
        total += 1
    deduction = (
        severity_counts.get("P0", 0) * 15
        + severity_counts.get("P1", 0) * 10
        + severity_counts.get("P2", 0) * 5
        + severity_counts.get("P3", 0) * 2
    )
    score = max(0, 100 - deduction)
    return severity_counts, rule_counts, total, score
def mark_source_drift(
    skill_dir: str, findings: list[dict], run_start_ts: float,
) -> list[dict]:
    drifted: list[dict] = []
    _, dicts = split_malformed_issues(findings)
    for _f in dicts:
        _entry = _drift_entry_of(_f, skill_dir, run_start_ts)
        if _entry is not None:
            drifted.append(_entry)
    return drifted
def _drift_entry_of(f: dict, skill_dir: str,
                    run_start_ts: float) -> dict | None:
    _rel = finding_file(f) if isinstance(f, dict) else ""
    if not _rel:
        return None
    _abs = _rel if os.path.isabs(_rel) else os.path.join(skill_dir, _rel)
    if not os.path.isfile(_abs):
        return None
    if not _modified_after(_abs, run_start_ts):
        return None
    f["source_drift"] = True
    _line = finding_line(f)
    return {
        "file": _rel,
        "line": max(0, _line),
        "rule_id": finding_rule_id(f),
        "note": "文件在诊断运行期间被修改，证据可能来自旧版本，须复扫现行代码后采信",
    }
def _modified_after(path: str, since: float) -> bool:
    try:
        return os.path.getmtime(path) > since
    except OSError as e:
        logger.debug("文件状态探测失败（跳过）: %s: %s", path, e)
        return False
def run_engine_B(skill_dir: str, cache: Any = _DEFAULT_CACHE) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, "主引擎 B 组")
    t0 = time.perf_counter()
    det_results = _run_b_detectors(skill_dir, cache)
    merged, conflicts, stats = consolidate_findings(
        det_results, source_method="B", merged_from="engine_b")
    worst = worst_sub_status(det_results, merged)
    return group_envelope(
        "B", _B_DETECTOR_IDS, worst, merged, stats, det_results, t0,
        summary=(
            f"主引擎B: 检测器{len(det_results)}个, "
            f"原始发现{stats['raw_findings']}, "
            f"预合并后{stats['merged_findings']}, 冲突{stats['conflicts']}"
        ),
        conflicts=conflicts,
    )
def _run_b_detectors(skill_dir: str, cache) -> list:
    det_results: list = []
    with fingerprint_freeze_window(cache, "B组"):
        det_results.append(detector_entry(
            "B1", run_b1_unified_ast_analysis, skill_dir, cache,
            logger=logger, engine_tag="engine_b"))
        det_results.append(detector_entry(
            "B2", run_history_analysis, skill_dir, cache,
            logger=logger, engine_tag="engine_b"))
    return det_results
_B_DETECTOR_IDS = ("B1", "B2")

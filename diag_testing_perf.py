from __future__ import annotations

import ast
import logging
import math
import os
import time
from dataclasses import dataclass

from jwsgj.diag_shared_ast_nodes import (
    call_tail_name,
    collect_param_names,
)
from jwsgj.diag_shared_source_scan import (
    has_inline_suppression,
)
from jwsgj.diag_testing_perf_metrics import (
    _AnalysisCache,
    _AnalysisPolicy,
    _coerce_analysis_policy,
    _ensure_widx,
    _expr_field,
    _is_package_init_entry,
    _iter_self_calls,
    _list_field,
    _local_binding_names,
    _name_id,
    _names_in_expr,
    _node_line_span,
    _perf_detect_recursion,
    _perf_has_identity_self_call,
    _perf_identify_hotspots,
    _postpones_annotations,
    _runtime_header_exprs,
    _self_call_is_identity,
)
from jwsgj.diag_testing_source import (
    MATCH_CASE_T,
    MATCH_T,
    TRY_STAR_T,
    collect_typing_tc_bindings,
    entry_class_method_ids,
    entry_lines,
    entry_nodes,
    entry_rel_path,
    iter_module_binding_nodes,
    iter_own_scope_nodes,
    node_first_line,
    nodes_where,
    resolve_file_cache,
    static_if_branch,
    type_checking_static_body,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
    graded_status_score,
    scan_issue,
    severity_tally,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_test_file_path,
)

_log = logging.getLogger(__name__)
_UNSET = object()
_log.info("diag_testing_perf 已加载")
__all__ = [
    'run_performance_profiling',
    'run_stress_tests',
]
def _loop_iter_var_names(node: ast.AST) -> set[str]:
    names: set[str] = set()
    if isinstance(node, (ast.For, ast.AsyncFor)):
        _tgt = _expr_field(node, 'target')
        if _tgt is not None:
            names |= _names_in_expr(_tgt)
    return names
def _derive_assign_name(ch: ast.AST, derived: set[str]) -> str | None:
    _tgt, _value = _single_assign_target_value(ch)
    _tid = _name_id(_tgt)
    if _tid is None or _tid in derived or _value is None:
        return None
    return _tid if _names_in_expr(_value) & derived else None
def _derive_with_handles(ch: ast.AST, derived: set[str]) -> bool:
    changed = False
    for item in _list_field(ch, 'items'):
        _ovid = _name_id(_expr_field(item, 'optional_vars'))
        _cexpr = _expr_field(item, 'context_expr')
        if (_ovid is not None and _ovid not in derived
                and _cexpr is not None
                and _names_in_expr(_cexpr) & derived):
            derived.add(_ovid)
            changed = True
    return changed
def _derive_step(ch: ast.AST, derived: set[str]) -> bool:
    if isinstance(ch, (ast.Assign, ast.AnnAssign)):
        _tid = _derive_assign_name(ch, derived)
        if _tid is None:
            return False
        derived.add(_tid)
        return True
    if isinstance(ch, (ast.For, ast.AsyncFor)):
        _targets = _loop_iter_var_names(ch) - derived
        if not _targets:
            return False
        derived.update(_targets)
        return True
    if isinstance(ch, (ast.With, ast.AsyncWith)):
        return _derive_with_handles(ch, derived)
    return False
def _loop_orelse_ids(node) -> set:
    return {id(n) for _stmt in _list_field(node, 'orelse')
            for n in walk_nodes(_stmt)}
def _loop_iteration_nodes(node) -> list:
    _skip = _loop_orelse_ids(node)
    ordered: list = []
    stack = [ch for ch in reversed(list(ast.iter_child_nodes(node)))]
    while stack:
        cur = stack.pop()
        if id(cur) in _skip or isinstance(cur, _SCOPE_BOUNDARY_TYPES):
            continue
        ordered.append(cur)
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
    return ordered
def _iter_immediate_nodes(stmts, skip_ids, postponed_annotations: bool):
    stack = list(reversed(list(stmts)))
    while stack:
        cur = stack.pop()
        if id(cur) in skip_ids:
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            stack.extend(reversed(_runtime_header_exprs(
                cur, postponed_annotations=postponed_annotations)))
            continue
        yield cur
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
def _loop_scan_nodes(node: ast.AST, postponed_annotations: bool) -> list:
    return list(_iter_immediate_nodes(
        ast.iter_child_nodes(node), _loop_orelse_ids(node),
        postponed_annotations))
def _derived_loop_names(node: ast.AST, iter_names, extra_seed=()) -> set[str]:
    derived = set(iter_names) | set(extra_seed or ())
    nodes = _loop_iteration_nodes(node)
    changed = True
    while changed:
        changed = False
        for ch in nodes:
            if _derive_step(ch, derived):
                changed = True
    return derived
def _stmt_has_break(s: ast.AST) -> bool:
    if isinstance(s, ast.Break):
        return True
    if isinstance(s, (ast.For, ast.AsyncFor, ast.While)):
        return _has_outer_scope_break(_list_field(s, 'orelse'))
    if isinstance(s, (ast.If, ast.With, ast.AsyncWith)):
        return _bodies_have_break(s, ('body', 'orelse'))
    if isinstance(s, (ast.Try, TRY_STAR_T)):
        return _try_has_break(s)
    if MATCH_T is not None and isinstance(s, MATCH_T):
        return _match_has_break(s)
    return False
def _try_has_break(s: ast.AST) -> bool:
    if _bodies_have_break(s, ('body', 'orelse', 'finalbody')):
        return True
    return any(_has_outer_scope_break(_list_field(_h, 'body'))
               for _h in _list_field(s, 'handlers'))
def _match_has_break(s: ast.AST) -> bool:
    return any(_has_outer_scope_break(_list_field(_c, 'body'))
               for _c in _list_field(s, 'cases'))
def _bodies_have_break(node, fields: tuple) -> bool:
    return any(_has_outer_scope_break(_list_field(node, f)) for f in fields)
def _has_outer_scope_break(stmts) -> bool:
    return any(_stmt_has_break(s) for s in stmts)
def _in_while_direct_scope(candidate: ast.AST, root: ast.AST,
                           parents) -> bool:
    _loop_t = (ast.For, ast.AsyncFor, ast.While)
    _cur = candidate
    while id(_cur) in parents and _cur is not root:
        _par = parents[id(_cur)]
        if (isinstance(_par, _loop_t) and _par is not root
                and any(s is _cur for s in _list_field(_par, 'body'))):
            return False
        _cur = _par
    return True
_BLOCK_CARRIERS = ((ast.If, ast.For, ast.AsyncFor, ast.While, ast.Try,
                    TRY_STAR_T, ast.ExceptHandler, ast.With, ast.AsyncWith)
                   + ((MATCH_CASE_T,) if MATCH_CASE_T is not None else ()))
def _parent_chain(parents: dict, call: ast.Call, loop: ast.AST) -> list:
    _chain: list = []
    _cur: ast.AST = call
    while id(_cur) in parents and _cur is not loop:
        _par = parents[id(_cur)]
        _chain.append(_par)
        _cur = _par
    return _chain
def _break_suffix_clean(_chain: list, loop: ast.AST) -> list:
    _loop_t = (ast.For, ast.AsyncFor, ast.While)
    _suffix_clean = [True] * len(_chain)
    _dirty = False
    for _i in range(len(_chain) - 1, -1, -1):
        _p = _chain[_i]
        if _p is loop:
            continue
        _suffix_clean[_i] = not _dirty and not isinstance(_p, _loop_t)
        if isinstance(_p, _loop_t):
            _dirty = True
    return _suffix_clean
def _finally_guarantees_return(_par) -> bool:
    return (isinstance(_par, (ast.Try, TRY_STAR_T))
            and any(isinstance(t, ast.Return)
                    for t in _list_field(_par, 'finalbody')))
def _sibling_termination(_body, _cur, _allow_break: bool) -> tuple[bool, bool]:
    for _idx, _s in enumerate(_body):
        if _s is not _cur:
            continue
        _rest = _body[_idx + 1:]
        _term = any(isinstance(t, ast.Return) for t in _rest)
        if not _term and _allow_break:
            _term = any(isinstance(t, ast.Break) for t in _rest)
        return True, _term
    return False, False
def _terminates_after_call(_chain: list, call: ast.Call, loop: ast.AST) -> bool:
    _suffix_clean = _break_suffix_clean(_chain, loop)
    for _i, _par in enumerate(_chain):
        _cur = call if _i == 0 else _chain[_i - 1]
        if _finally_guarantees_return(_par):
            return True
        if _layer_terminates(_par, _cur, _suffix_clean[_i]):
            return True
    return False
def _layer_terminates(_par, _cur, allow_break: bool) -> bool:
    if not isinstance(_par, _BLOCK_CARRIERS):
        return False
    for _attr in ("body", "orelse", "finalbody"):
        _matched, _term = _sibling_termination(
            _list_field(_par, _attr), _cur, allow_break)
        if _matched:
            return _term
    return False
def _line_range_in_loops(stmt, loops) -> bool:
    _s, _e = _node_line_span(stmt)
    for lp in loops:
        if lp is stmt:
            continue
        _ls, _le = _node_line_span(lp)
        if _ls <= 0 or _s <= 0 or (_s >= _ls and _e <= _le):
            return True
    return False
_READ_CALL_ATTRS = frozenset(("read", "readlines", "readline"))
_IO_CALL_NAMES = frozenset(
    ("open", "read", "readline", "readlines", "write", "writelines"))
_LOOP_IO_SUPPRESS_RULES = ("loop_io", "E1-loop_io", "PERF-IO-01")
def _line_suppressed(file_path: str, lineno: int, rules) -> bool:
    return any(has_inline_suppression(file_path, _line, _rule)
               for _line in (lineno - 1, lineno)
               if _line >= 1
               for _rule in rules)
_WRITE_CALL_NAMES = frozenset(("write", "writelines"))
@dataclass(frozen=True)
class _PerfAggregates:
    file_profiles: list
    total_lines: int
    total_nodes: int
    avg_walk_ms: float
    slow_files: list
    io_patterns: list
    hotspot_functions: list
    recursion_issues: list
    generator_issues: list
    @property
    def high_hotspot_count(self) -> int:
        return sum(h.get('severity') == 'high'
                   for h in self.hotspot_functions)
    @property
    def high_io_count(self) -> int:
        return sum(p.get('severity') == 'high' for p in self.io_patterns)
def _pattern_occurrences(pattern: dict) -> int:
    for key in ('count', 'io_operations'):
        _value = pattern.get(key)
        if isinstance(_value, int) and not isinstance(_value, bool):
            return _value
    return 1
def _patterns_occurrences(io_patterns, pattern_type: str) -> int:
    return sum(_pattern_occurrences(p) for p in io_patterns
               if p.get('type') == pattern_type)
def _perf_metrics_of(agg: _PerfAggregates) -> dict:
    io_patterns = agg.io_patterns
    hotspot_functions = agg.hotspot_functions
    return {
        "total_files": len(agg.file_profiles),
        "total_lines": agg.total_lines,
        "total_ast_nodes": agg.total_nodes,
        "avg_walk_ms": round(agg.avg_walk_ms, 2),
        "large_files": len(agg.slow_files),
        "io_heavy_files": len({p.get('file') for p in io_patterns
                               if p.get('type') in ('dense_io', 'loop_io')}),
        "hotspot_functions": len(hotspot_functions),
        "top_hotspot": hotspot_functions[0]["function"] if hotspot_functions else None,
        "max_cc": hotspot_functions[0]["cc"] if hotspot_functions else 0,
        "loop_io_count": _patterns_occurrences(io_patterns, 'loop_io'),
        "string_concat_in_loop": _patterns_occurrences(
            io_patterns, 'string_concat_in_loop'),
        "nested_loops": _patterns_occurrences(io_patterns, 'nested_loop'),
        "recursion_issues": len(agg.recursion_issues),
        "generator_issues": len(agg.generator_issues),
        "format_in_loop": _patterns_occurrences(io_patterns, 'format_in_loop'),
    }
def _perf_summary_parts(agg: _PerfAggregates) -> list[str]:
    _parts = []
    _high_hotspots = agg.high_hotspot_count
    if _high_hotspots:
        _parts.append(f"{_high_hotspots} 个高复杂度热点")
    if agg.slow_files:
        _parts.append(f"{len(agg.slow_files)} 个大文件")
    if agg.high_io_count:
        _parts.append(f"{agg.high_io_count} 个高严重度 I/O 模式(循环内I/O/嵌套循环)")
    _dense = _patterns_occurrences(agg.io_patterns, 'dense_io')
    if _dense:
        _parts.append(f"{_dense} 处 I/O 操作密集")
    _concat = _patterns_occurrences(agg.io_patterns, 'string_concat_in_loop')
    if _concat:
        _parts.append(f"{_concat} 处循环内字符串拼接")
    _format = _patterns_occurrences(agg.io_patterns, 'format_in_loop')
    if _format:
        _parts.append(f"{_format} 处循环内格式化")
    if agg.recursion_issues:
        _parts.append(f"{len(agg.recursion_issues)} 个无界递归风险")
    if agg.generator_issues:
        _parts.append(f"{len(agg.generator_issues)} 个生成器内 I/O")
    return _parts
_IO_SEVERITY_RANK = {'high': 0, 'medium': 1, 'low': 2}
def _io_finding_sort_key(pattern: dict) -> tuple:
    return (0 if pattern.get('type') == 'loop_io' else 1,
            _IO_SEVERITY_RANK.get(pattern.get('severity'), 3))
_TEST_LOW_PENALTY = 2
def _severity_verdict(findings) -> tuple[str, int, dict]:
    counts = severity_tally(findings)
    status, score = graded_status_score(
        counts, len(findings), low_penalty=_TEST_LOW_PENALTY)
    return status, score, counts
def _severity_metrics(counts: dict, total: int) -> dict:
    return {
        "total_findings": total,
        "high_severity": counts["high"],
        "medium_severity": counts["medium"],
        "low_severity": counts["low"],
    }
def _perf_findings(agg: _PerfAggregates) -> list:
    return [*agg.slow_files, *agg.io_patterns, *agg.hotspot_functions,
            *agg.recursion_issues, *agg.generator_issues]
def _finalize_perf_results(result, agg: _PerfAggregates, start):
    findings = _perf_findings(agg)
    status, score, counts = _severity_verdict(findings)
    result.metrics = {
        **_perf_metrics_of(agg),
        **_severity_metrics(counts, len(findings)),
    }
    result.findings = agg.slow_files[:15]
    result.findings.extend(sorted(agg.io_patterns, key=_io_finding_sort_key)[:10])
    result.findings.extend(agg.hotspot_functions[:15])
    result.findings.extend(agg.recursion_issues[:5])
    result.findings.extend(agg.generator_issues[:5])
    result.status = status
    result.score = score
    if findings:
        result.summary = ", ".join(_perf_summary_parts(agg))
    else:
        result.summary = (f"剖析 {len(agg.file_profiles)} 文件, "
                          f"{agg.total_lines} 行, 0 热点")
    return result.finish(start)
def _read_call_of(node) -> ast.Call | None:
    if not isinstance(node, ast.Call):
        return None
    _gcf = _expr_field(node, 'func')
    if (isinstance(_gcf, ast.Attribute)
            and getattr(_gcf, 'attr', None) in _READ_CALL_ATTRS):
        return node
    return None
def _generator_io_issue(entry, node, _fname: str) -> dict | None:
    has_yield = False
    io_call = None
    postponed = _postpones_annotations(getattr(entry, 'tree', None))
    for child in _iter_immediate_nodes(node.body, (), postponed):
        if isinstance(child, (ast.Yield, ast.YieldFrom)):
            has_yield = True
        elif io_call is None:
            io_call = (child if isinstance(child, ast.Call)
                       and call_tail_name(child) in _IO_CALL_NAMES else None)
        if has_yield and io_call is not None:
            break
    if not has_yield or io_call is None:
        return None
    return {
        'file': entry_rel_path(entry), 'function': _fname,
        'line': node_first_line(node),
        'type': 'generator_io', 'severity': 'low',
        'message': f'生成器 {_fname} 内有 I/O 操作，可能影响迭代效率',
    }
def _perf_analyze_generators(cache) -> list:
    generator_issues = []
    for entry in cache.valid_entries:
        for node in entry_nodes(entry):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            _fname = getattr(node, 'name', None)
            if not isinstance(_fname, str):
                _fname = ''
            _issue = _generator_io_issue(entry, node, _fname)
            if _issue is not None:
                generator_issues.append(_issue)
    return generator_issues
def _is_not_test(if_node) -> bool:
    _test = _expr_field(if_node, 'test')
    return (isinstance(_test, ast.UnaryOp)
            and isinstance(getattr(_test, 'op', None), ast.Not))
def _not_operand_name(if_node) -> str | None:
    _operand = _expr_field(_expr_field(if_node, 'test'), 'operand')
    return getattr(_operand, 'id', None) if isinstance(_operand, ast.Name) else None
_SCOPE_BOUNDARY_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.Lambda, ast.ClassDef)
_LOOP_BOUNDARY_TYPES = (*_SCOPE_BOUNDARY_TYPES, ast.For, ast.AsyncFor,
                        ast.While)
def _scope_contains_node(stmts, node_type: type,
                         stop_types: tuple[type, ...]) -> bool:
    stack = list(stmts)
    while stack:
        cur = stack.pop()
        if isinstance(cur, node_type):
            return True
        if isinstance(cur, stop_types):
            continue
        stack.extend(ast.iter_child_nodes(cur))
    return False
def _chunk_exit_vars(node: ast.While, parents: dict) -> set:
    _exit_vars: set = set()
    for ch in _loop_iteration_nodes(node):
        if not (isinstance(ch, ast.If) and _is_not_test(ch)):
            continue
        if not _in_while_direct_scope(ch, node, parents):
            continue
        _oid = _not_operand_name(ch)
        if not isinstance(_oid, str):
            continue
        statements = _list_field(ch, 'body') + _list_field(ch, 'orelse')
        if (_has_outer_scope_break(statements)
                or _scope_contains_node(
                    statements, ast.Return, _SCOPE_BOUNDARY_TYPES)):
            _exit_vars.add(_oid)
    return _exit_vars
def _single_assign_target_value(stmt) -> tuple:
    if isinstance(stmt, ast.Assign):
        _tgts = _list_field(stmt, 'targets')
        if len(_tgts) == 1:
            return _tgts[0], _expr_field(stmt, 'value')
        return None, None
    if isinstance(stmt, ast.AnnAssign):
        return _expr_field(stmt, 'target'), _expr_field(stmt, 'value')
    return None, None
def _chunk_read_calls(node: ast.While, break_vars: set) -> set:
    _calls: set = set()
    for ch in _loop_iteration_nodes(node):
        _tgt, _cval = _single_assign_target_value(ch)
        if (_tgt is not None and isinstance(_tgt, ast.Name)
                and getattr(_tgt, 'id', None) in break_vars
                and isinstance(_cval, ast.Call)
                and _read_call_of(_cval) is not None):
            _calls.add(id(_cval))
    return _calls
def _is_numeric_constant(expr) -> int | float | None:
    if isinstance(expr, ast.UnaryOp) and isinstance(
            getattr(expr, 'op', None), (ast.USub, ast.UAdd)):
        _operand = _is_numeric_constant(_expr_field(expr, 'operand'))
        if _operand is None:
            return None
        return -_operand if isinstance(expr.op, ast.USub) else _operand
    if not isinstance(expr, ast.Constant):
        return None
    _value = getattr(expr, 'value', _UNSET)
    if isinstance(_value, bool) or not isinstance(_value, (int, float)):
        return None
    if isinstance(_value, int):
        return _value
    return _value if math.isfinite(_value) else None
def _is_truthy_const_test(test) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(
            getattr(test, 'op', None), (ast.USub, ast.UAdd)):
        _value = _is_numeric_constant(_expr_field(test, 'operand'))
        if _value is None:
            return False
        return _value != 0
    if not isinstance(test, ast.Constant):
        return False
    if getattr(test, 'value', _UNSET) is True:
        return True
    _value = _is_numeric_constant(test)
    return _value is not None and _value != 0
def _write_result_bindings(node) -> dict:
    _bound: dict = {}
    for ch in _loop_iteration_nodes(node):
        _tgt, _val = _single_assign_target_value(ch)
        _tid = getattr(_tgt, 'id', None) if isinstance(_tgt, ast.Name) else None
        if (isinstance(_tid, str) and isinstance(_val, ast.Call)
                and _callee_name(_val) in _WRITE_CALL_NAMES):
            _bound[_tid] = _val
    return _bound
def _write_result_refs(expr, bindings: dict) -> set:
    _ids: set = set()
    if expr is None:
        return _ids
    for n in walk_nodes(expr):
        if isinstance(n, ast.Call) and _callee_name(n) in _WRITE_CALL_NAMES:
            _ids.add(id(n))
    for _nm in _names_in_expr(expr):
        _bound = bindings.get(_nm)
        if _bound is not None:
            _ids.add(id(_bound))
    return _ids
def _advanced_by_write_result(_name: str, _val, bindings: dict) -> set:
    if not (isinstance(_val, ast.BinOp)
            and isinstance(getattr(_val, 'op', None), ast.Add)
            and _name in _names_in_expr(_val)):
        return set()
    return _write_result_refs(_val, bindings)
def _slice_progress_ids(_name: str, _val, bindings: dict) -> set:
    if not (isinstance(_val, ast.Subscript)
            and getattr(_expr_field(_val, 'value'), 'id', None) == _name):
        return set()
    _slice = _expr_field(_val, 'slice')
    if (isinstance(_slice, ast.Slice) and _slice.lower is not None
            and _slice.upper is None):
        return _write_result_refs(_slice.lower, bindings)
    return set()
def _assign_progress_ids(ch, _test_names, bindings: dict) -> set:
    _tgt, _val = _single_assign_target_value(ch)
    _name = getattr(_tgt, 'id', None) if isinstance(_tgt, ast.Name) else None
    if not (isinstance(_name, str) and _name in _test_names):
        return set()
    if (isinstance(_val, ast.Subscript)
            and getattr(_expr_field(_val, 'value'), 'id', None) == _name):
        return _slice_progress_ids(_name, _val, bindings)
    return _advanced_by_write_result(_name, _val, bindings)
def _augassign_progress_ids(ch, _test_names, bindings: dict) -> set:
    _name = getattr(ch.target, 'id', None)
    if (isinstance(_name, str) and _name in _test_names
            and isinstance(ch.op, ast.Add)):
        return _write_result_refs(_expr_field(ch, 'value'), bindings)
    return set()
def _partial_write_progress_calls(node, bindings: dict) -> set:
    _test = _expr_field(node, 'test')
    _test_names = _names_in_expr(_test) if _test is not None else set()
    _ids: set = set()
    for ch in _loop_iteration_nodes(node):
        if isinstance(ch, (ast.Assign, ast.AnnAssign)):
            _ids |= _assign_progress_ids(ch, _test_names, bindings)
        elif isinstance(ch, ast.AugAssign):
            _ids |= _augassign_progress_ids(ch, _test_names, bindings)
    return _ids
def _at_most_once_transfer_calls(node: ast.AST, widx) -> set:
    if not isinstance(node, ast.While):
        return set()
    transfer: set = set()
    if _is_truthy_const_test(_expr_field(node, 'test')):
        _exit_vars = _chunk_exit_vars(node, widx.parent_index(node))
        transfer |= _chunk_read_calls(node, _exit_vars)
    return transfer | _partial_write_progress_calls(
        node, _write_result_bindings(node))
def _literal_loop_at_most_once(loop: ast.AST) -> bool:
    if not isinstance(loop, ast.For):
        return False
    _lit = _expr_field(loop, 'iter')
    if not isinstance(_lit, (ast.Tuple, ast.List)):
        return False
    _elts = _list_field(_lit, 'elts')
    return (len(_elts) <= 1
            and not any(isinstance(_elt, ast.Starred) for _elt in _elts))
def _io_executes_at_most_once(loop: ast.AST, call: ast.Call, widx,
                              lazy_init_sigs) -> bool:
    if _literal_loop_at_most_once(loop):
        return True
    if _is_guarded_lazy_init(loop, call, lazy_init_sigs, widx):
        return True
    parents = widx.parent_index(loop)
    _chain = _parent_chain(parents, call, loop)
    return _terminates_after_call(_chain, call, loop)
def _collect_lazy_init_signatures(tree: ast.AST, widx) -> set:
    _loops = [n for n in widx.walk(tree)
              if isinstance(n, (ast.For, ast.AsyncFor, ast.While))]
    sigs = set()
    for n in widx.walk(tree):
        tgt = _none_init_target(n)
        if tgt is not None and not _line_range_in_loops(n, _loops):
            _sig = _safe_sig(tgt)
            if _sig is not None:
                sigs.add(_sig)
    return sigs
def _constant_none_value(expr) -> bool:
    return (isinstance(expr, ast.Constant)
            and getattr(expr, 'value', _UNSET) is None)
def _none_init_target(n):
    _tgt, _val = _single_assign_target_value(n)
    if _tgt is None:
        return None
    return _tgt if _constant_none_value(_val) else None
def _enclosing_assign_target(parents: dict, call: ast.Call,
                             loop: ast.AST) -> tuple:
    cur: ast.AST = call
    while id(cur) in parents and cur is not loop:
        par = parents[id(cur)]
        if isinstance(par, (ast.Assign, ast.AnnAssign)):
            _tgt, _val = _single_assign_target_value(par)
            if _val is cur:
                return _tgt, par
        cur = par
    return None, None
def _safe_sig(node) -> str | None:
    try:
        return ast.unparse(node)
    except (AttributeError,) + PARSE_DEGRADE_EXC as _e:
        _log.debug("_safe_sig: unparse 降级: %s", _e)
        return None
def _is_none_guard_test(if_node: ast.If, sig: str) -> bool:
    t = _expr_field(if_node, 'test')
    if not _is_single_is_compare(t):
        return False
    _l_none, _l_txt = _none_flag_and_text(_expr_field(t, 'left'))
    _r_none, _r_txt = _none_flag_and_text(
        _list_field(t, 'comparators')[0])
    if _l_txt is None or _r_txt is None:
        return False
    return ((_l_none and _r_txt == sig)
            or (_r_none and _l_txt == sig))
def _is_single_is_compare(t) -> bool:
    if not isinstance(t, ast.Compare):
        return False
    _ops = _list_field(t, 'ops')
    return (len(_ops) == 1 and isinstance(_ops[0], ast.Is)
            and len(_list_field(t, 'comparators')) == 1)
def _none_flag_and_text(_expr) -> tuple[bool, str | None]:
    if _expr is None:
        return False, None
    return _constant_none_value(_expr), _safe_sig(_expr)
def _loop_has_none_reset(loop: ast.AST, sig: str) -> bool:
    for child in _loop_iteration_nodes(loop):
        _target = _none_init_target(child)
        if _target is not None and _safe_sig(_target) == sig:
            return True
    return False
def _is_guarded_lazy_init(loop: ast.AST, call: ast.Call, lazy_init_sigs: set,
                          widx) -> bool:
    if not lazy_init_sigs:
        return False
    parents = widx.parent_index(loop)
    target, par = _enclosing_assign_target(parents, call, loop)
    if target is None:
        return False
    sig = _safe_sig(target)
    if sig is None or sig not in lazy_init_sigs:
        return False
    return (_guarded_by_none_test(parents, par, loop, sig)
            and not _loop_has_none_reset(loop, sig))
def _guarded_by_none_test(parents: dict, start, loop: ast.AST, sig: str) -> bool:
    cur = start
    while id(cur) in parents and cur is not loop:
        parent = parents[id(cur)]
        if isinstance(parent, (ast.For, ast.AsyncFor, ast.While)):
            return False
        if (isinstance(parent, ast.If)
                and any(stmt is cur for stmt in _list_field(parent, 'body'))
                and _is_none_guard_test(parent, sig)):
            return True
        cur = parent
    return False
def _is_per_item_io_call(child: ast.Call, node: ast.AST,
                         ctx: _LoopIoExemptionCtx) -> bool:
    _recv = _handle_receiver_name(child)
    if (_recv is not None
            and (_recv in ctx.per_item_handles or _recv in ctx.derived)):
        return True
    if _recv is None and _receiver_is_per_item_call(child, ctx.derived):
        return True
    if id(child) in ctx.transfer_calls:
        return True
    if _call_args_use_derived(child, ctx.derived):
        return True
    return _inside_loop_iter(child, node)
def _handle_receiver_name(child: ast.Call) -> str | None:
    cfunc = _expr_field(child, 'func')
    if not isinstance(cfunc, ast.Attribute):
        return None
    _cv = _expr_field(cfunc, 'value')
    if not isinstance(_cv, ast.Name):
        return None
    _cv_id = getattr(_cv, 'id', None)
    return _cv_id if isinstance(_cv_id, str) else None
def _call_args_use_derived(child, derived: set) -> bool:
    if not isinstance(child, ast.Call):
        return False
    return any(_names_in_expr(arg) & derived
               for arg in _call_arg_exprs(child))
def _receiver_is_per_item_call(child: ast.Call, derived: set) -> bool:
    cfunc = _expr_field(child, 'func')
    if not isinstance(cfunc, ast.Attribute):
        return False
    return _call_args_use_derived(_expr_field(cfunc, 'value'), derived)
def _inside_loop_iter(child: ast.AST, node: ast.AST) -> bool:
    if not isinstance(node, (ast.For, ast.AsyncFor)):
        return False
    _iter = _expr_field(node, 'iter')
    return (_iter is not None
            and any(n is child for n in walk_nodes(_iter)))
def _is_open_entry_call(call: ast.Call) -> bool:
    _func = _expr_field(call, 'func')
    if isinstance(_func, ast.Attribute):
        return getattr(_func, 'attr', None) == 'open'
    _name = getattr(_func, 'id', None) if isinstance(_func, ast.Name) else None
    return isinstance(_name, str) and (
        _name == 'open' or _name.endswith('_open'))
def _with_open_handle(item) -> tuple[str, ast.Call] | None:
    _ce = _expr_field(item, 'context_expr')
    if not (isinstance(_ce, ast.Call) and _is_open_entry_call(_ce)):
        return None
    _ov_id = getattr(_expr_field(item, 'optional_vars'), 'id', None)
    if not isinstance(_ov_id, str):
        return None
    return _ov_id, _ce
def _callee_name(call) -> str | None:
    return call_tail_name(call) or None
def _span_nests(outer_span: tuple[int, int],
                inner_span: tuple[int, int]) -> bool:
    outer_start, outer_end = outer_span
    inner_start, inner_end = inner_span
    return (outer_start > 0 and inner_start >= outer_start
            and inner_end <= outer_end)
def _loop_topology(tree: ast.AST, _widx) -> tuple:
    _all_nodes = _widx.walk(tree)
    _loop_nodes = [n for n in _all_nodes if isinstance(n, (ast.For, ast.AsyncFor, ast.While))]
    _span_of = {id(_ln): _node_line_span(_ln) for _ln in _loop_nodes}
    _node_depth = {}
    for _ln in _loop_nodes:
        _ls, _le = _span_of[id(_ln)]
        _node_depth[id(_ln)] = sum(
            1 for _other in _loop_nodes
            if _other is not _ln
            and _span_nests(_span_of[id(_other)], (_ls, _le))
        )
    _loop_nodes.sort(key=lambda n: -_node_depth[id(n)])
    return _all_nodes, _loop_nodes, _span_of
def _enclosing_iters_map(_loop_nodes: list, _span_of: dict,
                         _parents: dict) -> dict:
    def _is_live_enclosing_loop(outer: ast.AST, inner: ast.AST) -> bool:
        _cur = inner
        while id(_cur) in _parents:
            _cur = _parents[id(_cur)]
            if isinstance(_cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
                return False
            if _cur is outer:
                return True
        return False

    def _enclosing_of(ln: ast.AST) -> set:
        _own = _loop_iter_var_names(ln)
        _parts = [
            _loop_iter_var_names(other) - _own
            for other in _loop_nodes
            if other is not ln and _is_live_enclosing_loop(other, ln)
        ]
        return set().union(*_parts) if _parts else set()
    return {id(_ln): _enclosing_of(_ln) for _ln in _loop_nodes}
@dataclass
class _LoopIoExemptionCtx:
    derived: set
    per_item_handles: set
    transfer_calls: object
    lazy_init_sigs: object
    widx: object
    file_path: str
@dataclass(frozen=True)
class _ModuleScanEnv:
    log_only_names: set
    while_nodes: list
    seen_stmt_ids: set
    fmt_reported_ids: set
    nested_seen_ids: set
    postponed_annotations: bool
    rel_path: str
def _build_loop_ctx(node, enclosing_iters: dict, lazy_init_sigs: set,
                    widx: object, file_path: str) -> _LoopIoExemptionCtx:
    _iter_names = _loop_iter_var_names(node)
    return _LoopIoExemptionCtx(
        derived=_derived_loop_names(
            node, _iter_names,
            extra_seed=enclosing_iters.get(id(node), ())),
        per_item_handles=set(),
        transfer_calls=_at_most_once_transfer_calls(node, widx),
        lazy_init_sigs=lazy_init_sigs,
        widx=widx,
        file_path=file_path)
def _scan_loop_node(node, ctx: _LoopIoExemptionCtx,
                    env: _ModuleScanEnv) -> tuple:
    loop_io = concat = nested = 0
    patterns = []
    _fmt_count = 0
    _fmt_sample = None
    for child in _loop_scan_nodes(node, env.postponed_annotations):
        _register_per_item_handles(child, ctx)
        loop_io += _counted_loop_io_delta(
            child, node, env.seen_stmt_ids, ctx)
        concat += _concat_in_loop_delta(
            child, node, env.log_only_names, env.seen_stmt_ids)
        _nested_hit = _nested_loop_delta(child, node, env.while_nodes)
        if _nested_hit and id(child) not in env.nested_seen_ids:
            env.nested_seen_ids.add(id(child))
            nested += 1
        if (id(child) not in env.fmt_reported_ids
                and not _inside_loop_iter(child, node)
                and _is_format_in_loop(child)):
            env.fmt_reported_ids.add(id(child))
            _fmt_count += 1
            if _fmt_sample is None:
                _fmt_sample = child
    if _fmt_count:
        patterns.append(_format_pattern(
            env.rel_path, _fmt_sample, count=_fmt_count))
    return loop_io, concat, nested, patterns
def _register_with_item_handles(child, ctx: _LoopIoExemptionCtx) -> None:
    for item in _list_field(child, 'items'):
        _pair = _with_open_handle(item)
        if _pair is not None and _call_args_use_derived(_pair[1], ctx.derived):
            ctx.per_item_handles.add(_pair[0])
def _register_assign_handles(child, ctx: _LoopIoExemptionCtx) -> None:
    _tgt, _av = _single_assign_target_value(child)
    _tgt_id = getattr(_tgt, 'id', None) if isinstance(_tgt, ast.Name) else None
    if not isinstance(_tgt_id, str):
        return
    if _call_args_use_derived(_av, ctx.derived):
        ctx.per_item_handles.add(_tgt_id)
def _register_per_item_handles(child, ctx: _LoopIoExemptionCtx) -> None:
    if isinstance(child, (ast.With, ast.AsyncWith)):
        _register_with_item_handles(child, ctx)
    elif isinstance(child, (ast.Assign, ast.AnnAssign)):
        _register_assign_handles(child, ctx)
def _is_counted_loop_io(child, node,
                        ctx: _LoopIoExemptionCtx) -> bool:
    cname = _callee_name(child)
    if not (isinstance(cname, str) and cname in _IO_CALL_NAMES):
        return False
    if (ctx.file_path and getattr(child, 'lineno', 0)
            and _line_suppressed(ctx.file_path, child.lineno,
                                 _LOOP_IO_SUPPRESS_RULES)):
        return False
    return (not _is_per_item_io_call(child, node, ctx)
            and not _io_executes_at_most_once(
                node, child, ctx.widx, ctx.lazy_init_sigs))
def _io_pattern_findings(rel_path: str, io_count: int, loop_io_count: int,
                         string_concat_in_loop: int,
                         nested_loop_count: int,
                         policy: _AnalysisPolicy) -> list:
    patterns = []
    if io_count > policy.dense_io:
        patterns.append({
            "file": rel_path, "io_operations": io_count,
            "type": "dense_io",
            "severity": "medium",
            "message": f"文件 I/O 操作密集 ({io_count} 处)，建议批量处理",
        })
    if loop_io_count > 0:
        patterns.append({
            "file": rel_path, "io_operations": loop_io_count,
            "type": "loop_io",
            "severity": "high",
            "message": f"循环内 I/O 操作 ({loop_io_count} 处)，严重影响性能",
        })
    if string_concat_in_loop > 0:
        patterns.append({
            "file": rel_path,
            "count": string_concat_in_loop,
            "severity": "medium",
            "message": f"循环内字符串拼接 ({string_concat_in_loop} 处)，建议使用 join()",
            "type": "string_concat_in_loop",
        })
    if nested_loop_count > 0:
        patterns.append({
            "file": rel_path,
            "count": nested_loop_count,
            "severity": "high",
            "message": f"嵌套循环 ({nested_loop_count} 处)，可能存在 O(n²) 复杂度",
            "type": "nested_loop",
        })
    return patterns
def _counted_loop_io_delta(child, node, _seen_stmt_ids: set,
                           ctx: _LoopIoExemptionCtx) -> int:
    if not (isinstance(child, ast.Call) and id(child) not in _seen_stmt_ids):
        return 0
    counted = _is_counted_loop_io(child, node, ctx)
    if counted:
        _seen_stmt_ids.add(id(child))
    return int(counted)
def _is_str_call_form(_val: ast.Call) -> bool:
    _f = _expr_field(_val, 'func')
    return ((isinstance(_f, ast.Name)
             and getattr(_f, 'id', None) == 'str')
            or (isinstance(_f, ast.Attribute)
                and getattr(_f, 'attr', None) == 'format'))
def _is_str_operand(_val) -> bool:
    if isinstance(_val, ast.Constant):
        return isinstance(getattr(_val, 'value', None), str)
    if isinstance(_val, ast.JoinedStr):
        return True
    if isinstance(_val, ast.Call):
        return _is_str_call_form(_val)
    return False
def _is_str_concat_binop(_val: ast.BinOp) -> bool:
    return (_is_str_operand(_expr_field(_val, 'left'))
            or _is_str_operand(_expr_field(_val, 'right')))
def _is_string_concat_value(_val: ast.expr) -> bool:
    if _is_str_operand(_val):
        return True
    return (isinstance(_val, ast.BinOp)
            and isinstance(getattr(_val, 'op', None), ast.Add)
            and _is_str_concat_binop(_val))
def _pairwise_target_names(loop) -> set:
    _tgt = _expr_field(loop, 'target')
    return _names_in_expr(_tgt) if _tgt is not None else set()
def _pairwise_name_set(e) -> set:
    _id = getattr(e, 'id', None) if isinstance(e, ast.Name) else None
    return {_id} if isinstance(_id, str) else set()
def _pairwise_cmp_matches(cmp_, _o_names: set, _i_names: set) -> bool:
    _ops = _list_field(cmp_, 'ops')
    _cmps = _list_field(cmp_, 'comparators')
    if (isinstance(cmp_, ast.Compare) and len(_ops) == 1
            and isinstance(_ops[0], (ast.Is, ast.Eq))
            and len(_cmps) == 1):
        _ln = _pairwise_name_set(_expr_field(cmp_, 'left'))
        _rn = _pairwise_name_set(_cmps[0])
        return bool((_ln & _i_names and _rn & _o_names)
                    or (_ln & _o_names and _rn & _i_names))
    return False
def _pairwise_skip_same(outer: ast.For, inner: ast.For) -> bool:
    _o_names = _pairwise_target_names(outer)
    _i_names = _pairwise_target_names(inner)
    for stmt in _list_field(inner, 'body')[:3]:
        if not isinstance(stmt, ast.If):
            continue
        if (_pairwise_cmp_matches(stmt.test, _o_names, _i_names)
                and _scope_contains_node(
                    _list_field(stmt, 'body'), ast.Continue,
                    _LOOP_BOUNDARY_TYPES)):
            return True
    return False
def _concat_rebuilt_in_loop(loop_node: ast.AST, _name: str,
                           exclude=None) -> bool:
    for stmt in _loop_iteration_nodes(loop_node):
        if stmt is exclude or not isinstance(stmt, (ast.Assign, ast.AnnAssign)):
            continue
        _tgt, _val = _single_assign_target_value(stmt)
        if (_val is None or _name_id(_tgt) != _name
                or _name in _names_in_expr(_val)):
            continue
        return True
    return False
def _call_arg_exprs(node: ast.Call) -> list:
    return list(_list_field(node, 'args')) + [
        v for v in (_expr_field(k, 'value')
                    for k in _list_field(node, 'keywords'))
        if v is not None]
def _concat_consumed_in_loop(loop_node: ast.AST, _name: str) -> bool:
    for stmt in _loop_iteration_nodes(loop_node):
        if not isinstance(stmt, ast.Call):
            continue
        for a in _call_arg_exprs(stmt):
            if _name in _names_in_expr(a):
                return True
    return False
def _range_call_source(expr) -> str | None:
    if not isinstance(expr, ast.Call):
        return None
    _fn = _expr_field(expr, 'func')
    if not (isinstance(_fn, ast.Name) and getattr(_fn, 'id', None) == 'range'):
        return None
    return _safe_sig(expr)
def _is_window_micro_loop(loop_node: ast.AST) -> bool:
    _iter = _expr_field(loop_node, 'iter')
    if _range_call_source(_iter) is None:
        return False
    _call_names = {
        _callee_name(n) for n in walk_nodes(_iter)
        if isinstance(n, ast.Call)
    }
    return (('min' in _call_names and 'len' in _call_names)
            or ('max' in _call_names and 'min' in _call_names))
def _augassign_target_name(child: ast.AugAssign) -> str | None:
    _ct = _expr_field(child, 'target')
    if not isinstance(_ct, ast.Name):
        return None
    _name = getattr(_ct, 'id', None)
    return _name if isinstance(_name, str) else None
def _is_micro_append_value(_cval) -> bool:
    return (isinstance(_cval, ast.Constant)
            and isinstance(getattr(_cval, 'value', None), str)
            and len(_cval.value) <= 3)
def _concat_exempt_reasons(loop_node: ast.AST, child, _name: str,
                             log_only_names) -> str | None:
    _cval = _expr_field(child, 'value')
    checks = (
        ("micro_append", lambda: _is_micro_append_value(_cval)),
        ("rebuilt_in_loop", lambda: _concat_rebuilt_in_loop(
            loop_node, _name, exclude=child)),
        ("consumed_in_loop", lambda: _concat_consumed_in_loop(
            loop_node, _name)),
        ("log_building", lambda: _name in log_only_names),
        ("window_micro_loop", lambda: _is_window_micro_loop(loop_node)),
    )
    for reason, matches in checks:
        if matches():
            return reason
    return None
def _func_scope_nodes(t, _widx):
    for n in _widx.walk(t):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Module)):
            yield n
def _call_consumer_vars(n: ast.Call) -> tuple:
    _cn = _callee_name(n)
    _cname = _cn if isinstance(_cn, str) else ''
    _names: list = []
    for a in _call_arg_exprs(n):
        _names.extend(_names_in_expr(a))
    return _cname, _names
def _collect_log_only_names(tree: ast.AST, widx) -> set:
    _logish = {'log', 'info', 'debug', 'warning', 'error', 'critical',
               'exception', 'print', 'warn'}
    _scope_verdicts: dict[str, list[bool]] = {}
    for fn in _func_scope_nodes(tree, widx):
        _consumers = _scope_call_names(fn, widx)
        for _nm, _cnames in _consumers.items():
            _scope_verdicts.setdefault(_nm, []).append(
                bool(_cnames) and all(_c in _logish for _c in _cnames))
    return {_nm for _nm, _verdicts in _scope_verdicts.items()
            if all(_verdicts)}
def _scope_call_names(fn, _widx) -> dict:
    _consumers: dict = {}
    for n in iter_own_scope_nodes(fn):
        if isinstance(n, ast.Call):
            _cname, _vars = _call_consumer_vars(n)
            for _nm in _vars:
                _consumers.setdefault(_nm, []).append(_cname)
        elif isinstance(n, (ast.Return, ast.Yield, ast.YieldFrom)):
            _value = _expr_field(n, 'value')
            if _value is not None:
                for _nm in _names_in_expr(_value):
                    _consumers.setdefault(_nm, []).append('')
    return _consumers
def _bare_name_equal(_o_it, _i_it) -> bool:
    _oid = getattr(_o_it, 'id', None) if isinstance(_o_it, ast.Name) else None
    _iid = getattr(_i_it, 'id', None) if isinstance(_i_it, ast.Name) else None
    return isinstance(_oid, str) and isinstance(_iid, str) and _oid == _iid
def _while_sandwiched(node: ast.AST, child: ast.AST,
                      while_nodes) -> bool:
    _ns, _ = _node_line_span(node)
    _cs, _ce = _node_line_span(child)
    for _w in while_nodes:
        _ws, _we = _node_line_span(_w)
        if (_w is not node and _w is not child
                and _ns < _ws <= _cs and _ce <= _we):
            return True
    return False
def _range_iters_equal(_o_it, _i_it) -> bool:
    _o_src = _range_call_source(_o_it)
    _i_src = _range_call_source(_i_it)
    return _o_src is not None and _o_src == _i_src
def _is_unintended_nested_loop(node: ast.AST, child: ast.AST,
                               while_nodes=()) -> bool:
    if not (isinstance(node, (ast.For, ast.AsyncFor))
            and isinstance(child, (ast.For, ast.AsyncFor))):
        return False
    _o_it, _i_it = _expr_field(node, 'iter'), _expr_field(child, 'iter')
    if _bare_name_equal(_o_it, _i_it):
        if _pairwise_skip_same(node, child):
            return False
        return not _while_sandwiched(node, child, while_nodes)
    return _range_iters_equal(_o_it, _i_it)
def _concat_assign_parts(child) -> tuple[str | None, ast.expr | None]:
    if isinstance(child, ast.AugAssign):
        _name = _augassign_target_name(child)
        if _name is not None and isinstance(getattr(child, 'op', None), ast.Add):
            return _name, _expr_field(child, 'value')
        return None, None
    if isinstance(child, (ast.Assign, ast.AnnAssign)):
        _tgt, _val = _single_assign_target_value(child)
        _tid = _name_id(_tgt)
        if (isinstance(_tid, str) and isinstance(_val, ast.BinOp)
                and isinstance(getattr(_val, 'op', None), ast.Add)
                and _tid in _names_in_expr(_val)):
            return _tid, _val
    return None, None
def _is_concat_assign_in_loop(child, node, _log_only_names: set) -> bool:
    _name, _value = _concat_assign_parts(child)
    if _name is None or not _is_string_concat_value(_value):
        return False
    return _concat_exempt_reasons(
        node, child, _name, _log_only_names) is None
def _is_format_in_loop(child) -> bool:
    if isinstance(child, ast.JoinedStr):
        return True
    _cfm = _expr_field(child, 'func')
    return (isinstance(child, ast.Call)
            and isinstance(_cfm, ast.Attribute)
            and getattr(_cfm, 'attr', None) == 'format')
def _format_pattern(rel_path: str, child, count: int = 1) -> dict:
    return {
        'file': rel_path,
        'count': count,
        'severity': 'low',
        'type': 'format_in_loop',
        'message': ('循环内 f-string 拼接，建议预计算到循环外'
                    if isinstance(child, ast.JoinedStr) else
                    '循环内字符串格式化，建议预计算或改用 f-string'),
    }
def _concat_in_loop_delta(child, node, _log_only_names, _seen_stmt_ids: set) -> int:
    if not (isinstance(child, (ast.AugAssign, ast.Assign, ast.AnnAssign))
            and id(child) not in _seen_stmt_ids):
        return 0
    counted = _is_concat_assign_in_loop(child, node, _log_only_names)
    if counted:
        _seen_stmt_ids.add(id(child))
    return int(counted)
def _nested_loop_delta(child, node, _while_nodes) -> int:
    return int(child is not node
               and _is_unintended_nested_loop(node, child, _while_nodes))
def _detect_io_patterns(tree: ast.AST, rel_path: str, widx,
                        file_path: str, *,
                        policy: _AnalysisPolicy) -> tuple:
    loop_io_count = 0
    string_concat_in_loop = 0
    nested_loop_count = 0
    patterns = []
    _seen_stmt_ids = set()
    _fmt_reported_ids = set()
    _all_nodes, _loop_nodes, _span_of = _loop_topology(tree, widx)
    _enclosing_iters = _enclosing_iters_map(
        _loop_nodes, _span_of, widx.parent_index(tree))
    _log_only_names = _collect_log_only_names(tree, widx)
    _lazy_init_sigs = _collect_lazy_init_signatures(tree, widx)
    _while_nodes = [n for n in _loop_nodes if isinstance(n, ast.While)]
    io_count = sum(_callee_name(n) in _IO_CALL_NAMES
                   for n in _all_nodes if isinstance(n, ast.Call))
    env = _ModuleScanEnv(
        log_only_names=_log_only_names, while_nodes=_while_nodes,
        seen_stmt_ids=_seen_stmt_ids, fmt_reported_ids=_fmt_reported_ids,
        nested_seen_ids=set(),
        postponed_annotations=_postpones_annotations(tree),
        rel_path=rel_path)
    for node in _loop_nodes:
        ctx = _build_loop_ctx(
            node, _enclosing_iters, _lazy_init_sigs, widx, file_path)
        _lio, _concat, _nested, _fmt = _scan_loop_node(node, ctx, env)
        loop_io_count += _lio
        string_concat_in_loop += _concat
        nested_loop_count += _nested
        patterns.extend(_fmt)
    patterns.extend(_io_pattern_findings(
        rel_path, io_count, loop_io_count,
        string_concat_in_loop, nested_loop_count, policy))
    return io_count, patterns
def _profile_entry(entry, rel_path: str,
                   policy: _AnalysisPolicy) -> tuple[dict, list, list, dict | None]:
    tree = getattr(entry, 'tree', None)
    widx = _ensure_widx(None)
    walk_start = time.perf_counter()
    nodes = list(walk_nodes(tree)) if tree is not None else []
    walk_time = time.perf_counter() - walk_start
    node_count = len(nodes)
    line_count = entry_lines(entry)
    if tree is None:
        io_count, file_io_patterns = 0, []
    else:
        io_count, file_io_patterns = _detect_io_patterns(
            tree, rel_path, widx, getattr(entry, 'path', ''),
            policy=policy)
    entry_hotspots = _perf_identify_hotspots(
        tree, rel_path, _nodes=nodes, policy=policy)
    profile = {
        "file": rel_path,
        "lines": line_count,
        "ast_nodes": node_count,
        "walk_ms": round(walk_time * 1000, 2),
        "io_operations": io_count,
        "nodes_per_line": round(node_count / max(line_count, 1), 2),
    }
    slow_file = None
    if line_count > policy.max_file_lines:
        slow_file = {
            "file": rel_path, "lines": line_count,
            "type": "large_file",
            "rule_id": "SZ-01", "budget": policy.max_file_lines,
            "severity": "low",
            "message": (f"文件 {line_count} 行，超过项目预算 "
                        f"{policy.max_file_lines} 行，建议评估职责与治理收益"),
        }
    return profile, file_io_patterns, entry_hotspots, slow_file
def _profile_entries(cache, policy: _AnalysisPolicy) -> tuple[list, list, list, list]:
    file_profiles = []
    slow_files = []
    io_patterns = []
    hotspot_functions = []
    for entry in cache.valid_entries:
        rel_path = entry_rel_path(entry)
        profile, entry_io_patterns, entry_hotspots, slow_file = _profile_entry(
            entry, rel_path, policy)
        io_patterns.extend(entry_io_patterns)
        hotspot_functions.extend(entry_hotspots)
        file_profiles.append(profile)
        if slow_file is not None:
            slow_files.append(slow_file)
    return file_profiles, slow_files, io_patterns, hotspot_functions
def run_performance_profiling(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    policy = _coerce_analysis_policy(kwargs=kwargs)
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "性能剖析", "performance", "剖析", start)
    cache = _AnalysisCache(cache, policy)
    result = TestMethodResult(method_name="性能剖析", method_id="performance")
    file_profiles, slow_files, io_patterns, hotspot_functions = _profile_entries(
        cache, policy)
    total_lines = sum(f["lines"] for f in file_profiles)
    total_nodes = sum(f["ast_nodes"] for f in file_profiles)
    avg_walk_ms = sum(f["walk_ms"] for f in file_profiles) / len(file_profiles) if file_profiles else 0
    hotspot_functions.sort(key=lambda x: (
        -x.get("cc", 0), str(x.get("file", "")),
        str(x.get("function", ""))))
    recursion_issues = _perf_detect_recursion(cache)
    generator_issues = _perf_analyze_generators(cache)
    return _finalize_perf_results(
        result,
        _PerfAggregates(
            file_profiles=file_profiles,
            total_lines=total_lines,
            total_nodes=total_nodes,
            avg_walk_ms=avg_walk_ms,
            slow_files=slow_files,
            io_patterns=io_patterns,
            hotspot_functions=hotspot_functions,
            recursion_issues=recursion_issues,
            generator_issues=generator_issues,
        ),
        start,
    )
def _listcomp_scale(node: ast.ListComp) -> int:
    gens = node.generators
    if not gens:
        return 0
    scale = 1
    prev_targets: set[str] = set()
    for g in gens:
        if isinstance(g.iter, (ast.Tuple, ast.List)):
            _dim = len(g.iter.elts)
        else:
            _range_size = (_stress_range_size_est(g.iter)
                           if _range_call_source(g.iter) is not None else None)
            if _range_size is not None:
                _dim = _range_size
            elif _names_in_expr(g.iter) & prev_targets:
                _dim = 1
            else:
                _dim = 100
        scale *= _dim
        prev_targets |= _names_in_expr(g.target)
    return scale
def _binop_mult_scale(node: ast.BinOp) -> int:
    for value_node, repeat_node in (
            (node.left, node.right), (node.right, node.left)):
        repeat = _fold_int_const(repeat_node)
        if repeat is None or repeat <= 0:
            continue
        base_size = _estimate_list_size(value_node)
        if base_size > 0:
            return base_size * repeat
    return 0
def _estimate_list_size(node) -> int:
    if isinstance(node, ast.List):
        return len(node.elts)
    if isinstance(node, ast.ListComp):
        return _listcomp_scale(node)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return _binop_mult_scale(node)
    return 0
def _expr_contains_self_call(expr, self_call_ids: set[int]) -> bool:
    return (expr is not None
            and any(id(n) in self_call_ids for n in walk_nodes(expr)))
def _ifexp_has_base(value: ast.IfExp, self_call_ids: set[int]) -> bool:
    return any(not _expr_contains_self_call(expr, self_call_ids)
               for expr in (value.body, value.orelse))
def _return_has_base(node: ast.Return, self_call_ids: set[int],
                     param_names: set) -> bool:
    value = _expr_field(node, 'value')
    if isinstance(value, ast.IfExp):
        # IfExp 的 test 先于分支求值；test 中的非结构下降自调用会阻断基线。
        if _own_scope_has_self_call(
                value.test, self_call_ids, param_names):
            return False
        _live = static_if_branch(value.test)
        if _live is not None:
            _expr = value.body if _live else value.orelse
            return not _expr_contains_self_call(_expr, self_call_ids)
        return _ifexp_has_base(value, self_call_ids)
    return not _expr_contains_self_call(value, self_call_ids)
def _if_guarantees_termination(node: ast.If) -> bool:
    return (bool(node.orelse)
            and all(_block_guarantees_termination(stmts)
                    for stmts in (node.body, node.orelse)))
def _block_guarantees_termination(stmts) -> bool:
    for stmt in stmts:
        if isinstance(stmt, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
            return True
        if isinstance(stmt, ast.If) and _if_guarantees_termination(stmt):
            return True
    return False
def _nested_base_scan_blocks(node):
    for field in ('body', 'orelse', 'finalbody'):
        stmts = _list_field(node, field)
        if stmts and all(isinstance(stmt, ast.stmt) for stmt in stmts):
            yield stmts
    for group in ('handlers', 'cases'):
        for child in _list_field(node, group):
            stmts = _list_field(child, 'body')
            if stmts:
                yield stmts
def _self_call_descends_params(call: ast.Call, param_names: set) -> bool:
    # 实参全部是参数的结构子组件（a.b / a[k]）时，递归规模随结构收敛，
    # 其后的 return 仍可视为可达基线；`f(n - 1)` 这类算术派生实参不在此列。
    args = [
        *_list_field(call, 'args'),
        *(value for value in (
            _expr_field(kw, 'value') for kw in _list_field(call, 'keywords'))
          if value is not None),
    ]
    if not args:
        return False

    def _root_name(expr):
        while isinstance(expr, (ast.Attribute, ast.Subscript)):
            expr = _expr_field(expr, 'value')
        return getattr(expr, 'id', None) if isinstance(expr, ast.Name) else None

    return all(
        not isinstance(arg, ast.Name) and _root_name(arg) in param_names
        for arg in args)
def _own_scope_has_self_call(node: ast.AST, self_call_ids: set[int],
                             param_names: set) -> bool:
    stack = [node]
    while stack:
        cur = stack.pop()
        if (id(cur) in self_call_ids and isinstance(cur, ast.Call)
                and not _self_call_descends_params(cur, param_names)):
            return True
        if isinstance(cur, _SCOPE_BOUNDARY_TYPES) and cur is not node:
            continue
        stack.extend(ast.iter_child_nodes(cur))
    return False
def _stmt_unconditional_test_expr(stmt: ast.AST) -> ast.AST | None:
    if isinstance(stmt, (ast.If, ast.While)):
        return _expr_field(stmt, 'test')
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return _expr_field(stmt, 'iter')
    if MATCH_T is not None and isinstance(stmt, MATCH_T):
        return _expr_field(stmt, 'subject')
    return None
def _stmt_recurses_unconditionally(stmt: ast.AST, self_call_ids: set[int],
                                   param_names: set) -> bool:
    # 语句在无条件执行路径上必然经过自调用时，其后的 return 只有在递归返回后
    # 才可达，不能充当递归基线。条件语句只检查进入分支前必然求值的
    # test/iter/subject；分支体内的自调用仍属条件路径，不阻断。
    test_expr = _stmt_unconditional_test_expr(stmt)
    if test_expr is not None:
        return _own_scope_has_self_call(
            test_expr, self_call_ids, param_names)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        contexts = (_expr_field(item, 'context_expr')
                    for item in _list_field(stmt, 'items'))
        return (any(context is not None and _own_scope_has_self_call(
                        context, self_call_ids, param_names)
                    for context in contexts)
                or any(_stmt_recurses_unconditionally(
                           inner, self_call_ids, param_names)
                       for inner in _list_field(stmt, 'body')))
    if isinstance(stmt, (ast.Try, TRY_STAR_T)):
        return (any(_stmt_recurses_unconditionally(
                        inner, self_call_ids, param_names)
                    for inner in _list_field(stmt, 'body'))
                or any(_stmt_recurses_unconditionally(
                           inner, self_call_ids, param_names)
                       for inner in _list_field(stmt, 'finalbody')))
    if isinstance(stmt, _SCOPE_BOUNDARY_TYPES):
        return False
    return _own_scope_has_self_call(stmt, self_call_ids, param_names)
def _stmt_precheck_recurses(stmt: ast.AST, self_call_ids: set[int],
                            param_names: set) -> bool:
    # 只对条件/容器语句做前置检查：它们的条件部分或 with 体/try-finally
    # 先于后续语句执行；普通语句仍保留「先找基线 return」的原顺序。
    if _stmt_unconditional_test_expr(stmt) is not None or isinstance(
            stmt, (ast.With, ast.AsyncWith, ast.Try, TRY_STAR_T)):
        return _stmt_recurses_unconditionally(
            stmt, self_call_ids, param_names)
    return False
def _branch_has_base_return(stmts, self_call_ids: set[int],
                            param_names: set) -> bool:
    for stmt in stmts:
        if isinstance(stmt, _SCOPE_BOUNDARY_TYPES):
            continue
        if _stmt_precheck_recurses(stmt, self_call_ids, param_names):
            break
        if (isinstance(stmt, ast.Return)
                and _return_has_base(stmt, self_call_ids, param_names)):
            return True
        if isinstance(stmt, ast.If):
            _live = static_if_branch(stmt.test)
        else:
            _live = None
        if _live is not None:
            _blocks = (stmt.body if _live else stmt.orelse,)
        else:
            _blocks = _nested_base_scan_blocks(stmt)
        for block in _blocks:
            if _branch_has_base_return(block, self_call_ids, param_names):
                return True
        if (_block_guarantees_termination((stmt,))
                or _stmt_recurses_unconditionally(
                    stmt, self_call_ids, param_names)):
            break
    return False
def _has_conditional_return(node: ast.AST, self_call_ids: set[int],
                            param_names: set) -> bool:
    return _branch_has_base_return(
        _list_field(node, 'body'), self_call_ids, param_names)
def _has_structural_descent(node: ast.AST, func_name: str, param_names: set,
                             *, allow_bare: bool,
                             postponed_annotations: bool) -> bool:
    shadowed = _local_binding_names(node)
    calls = list(_iter_self_calls(
        node, func_name, allow_bare=allow_bare, shadowed=shadowed,
        postponed_annotations=postponed_annotations))
    self_call_ids = {id(call) for call in calls}
    return (bool(calls)
            and _has_conditional_return(node, self_call_ids, param_names)
            and all(
                (call.args or call.keywords)
                and not _self_call_is_identity(node, call, param_names)
                for call in calls))
def _has_depth_limit(node: ast.AST, func_name: str, *,
                     allow_bare: bool, postponed_annotations: bool) -> bool:
    param_names = collect_param_names(node)
    if _perf_has_identity_self_call(
            node, param_names, allow_bare=allow_bare,
            postponed_annotations=postponed_annotations):
        return False
    return _has_structural_descent(
        node, func_name, param_names, allow_bare=allow_bare,
        postponed_annotations=postponed_annotations)
def _stress_check_func_recursion(node, rel_path: str,
                                in_class: bool = False,
                                postponed_annotations: bool = False) -> list[dict]:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return []
    func_name = node.name
    if not any(_iter_self_calls(
            node, func_name, allow_bare=not in_class,
            postponed_annotations=postponed_annotations)):
        return []
    if _has_depth_limit(
            node, func_name, allow_bare=not in_class,
            postponed_annotations=postponed_annotations):
        return []
    return [{
        "file": rel_path, "line": node_first_line(node),
        "function": func_name,
        "type": "unbounded_recursion", "severity": "medium",
        "message": f"函数 {func_name} 可能存在无深度限制的递归",
    }]
_FOLD_POW_BASE_LIMIT = 65536
_FOLD_POW_EXP_LIMIT = 1024
_FOLD_MULT_BITS_LIMIT = 64
def _fold_binop_pow(base_node: ast.AST, exp_node: ast.AST) -> int | None:
    _base = _fold_int_const(base_node)
    _exp = _fold_int_const(exp_node)
    if (_base is not None and _exp is not None
            and 0 <= _exp <= _FOLD_POW_EXP_LIMIT
            and abs(_base) <= _FOLD_POW_BASE_LIMIT):
        return _base ** _exp
    return None
def _fold_binop_mult(lhs_node: ast.AST, rhs_node: ast.AST) -> int | None:
    _lhs = _fold_int_const(lhs_node)
    _rhs = _fold_int_const(rhs_node)
    if _lhs is None or _rhs is None:
        return None
    _prod = _lhs * _rhs
    if _prod.bit_length() <= _FOLD_MULT_BITS_LIMIT:
        return _prod
    return None
_FOLD_BINOP = {ast.Pow: _fold_binop_pow, ast.Mult: _fold_binop_mult}
def _fold_int_const(node: ast.AST) -> int | None:
    _cls = node.__class__
    if _cls is ast.Constant:
        return _int_literal_value(node)
    if _cls is ast.UnaryOp:
        return _fold_negation(node)
    if _cls is ast.BinOp:
        return _fold_binop(node)
    return None
def _int_literal_value(node) -> int | None:
    value = getattr(node, 'value', None)
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    return None
def _fold_negation(node) -> int | None:
    if not isinstance(getattr(node, 'op', None), ast.USub):
        return None
    inner = _fold_int_const(node.operand)
    return -inner if inner is not None else None
def _fold_binop(node) -> int | None:
    _op = getattr(node, 'op', None)
    handler = _FOLD_BINOP.get(_op.__class__) if _op is not None else None
    return handler(node.left, node.right) if handler is not None else None
_SCALE_PLAIN_LIMIT = 10 ** 7
def _fmt_scale(v: int) -> str:
    if -_SCALE_PLAIN_LIMIT < v < _SCALE_PLAIN_LIMIT:
        return str(v)
    neg = v < 0
    a = -v if neg else v
    d = int(a.bit_length() * 0.30102999566398119) + 1
    if a < 10 ** (d - 1):
        d -= 1
    elif a >= 10 ** d:
        d += 1
    lead = a // 10 ** (d - 2)
    text = f"{lead // 10}.{lead % 10}e{d - 1}"
    return f"-{text}" if neg else text
def _range_iter_count(start: int, stop: int, step: int | None) -> int | None:
    if step is None or step == 0:
        return None
    if step > 0:
        return max(0, (stop - start + step - 1) // step)
    return max(0, (start - stop - step - 1) // (-step))
def _stress_range_size_est(node: ast.Call) -> int | None:
    _args = _list_field(node, 'args')
    if _list_field(node, 'keywords') or len(_args) > 3:
        return None
    ints: list[int | None] = [_fold_int_const(a) for a in _args]
    if len(ints) == 1:
        return None if ints[0] is None else max(0, ints[0])
    if len(ints) >= 2 and ints[0] is not None and ints[1] is not None:
        start, stop = ints[0], ints[1]
        if len(ints) < 3:
            return max(0, stop - start)
        return _range_iter_count(start, stop, ints[2])
    return None
def _stress_check_large_range(
        node: ast.Call, rel_path: str, is_test_file: bool,
        policy: _AnalysisPolicy) -> dict | None:
    func = _expr_field(node, 'func')
    if isinstance(func, ast.Name) and getattr(func, 'id', None) == 'range':
        size_est = _stress_range_size_est(node)
        if (size_est is not None and size_est > policy.large_alloc
                and not is_test_file):
            return {
                "file": rel_path, "line": node_first_line(node),
                "type": "large_range", "severity": "low",
                "message": f"range 迭代规模约 {_fmt_scale(size_est)}，可能造成性能压力",
            }
    return None
def _is_public_writable_name(target: ast.AST) -> bool:
    return (isinstance(target, ast.Name)
            and not target.id.startswith('_')
            and not target.id.isupper())
_MUTABLE_CONTAINER_CTORS = frozenset(('list', 'dict', 'set'))
def _is_mutable_container_value(value: ast.AST | None) -> bool:
    if isinstance(value, (ast.List, ast.Dict, ast.Set)):
        return True
    func = _expr_field(value, 'func') if isinstance(value, ast.Call) else None
    return isinstance(func, ast.Name) and getattr(
        func, 'id', None) in _MUTABLE_CONTAINER_CTORS
def _is_public_mutable_global(node) -> bool:
    if isinstance(node, ast.AugAssign):
        return _is_public_writable_name(node.target)
    if isinstance(node, ast.AnnAssign):
        return (_is_public_writable_name(node.target)
                and _is_mutable_container_value(node.value))
    return False
def _is_mutable_assign_target(target: ast.AST, value: ast.AST) -> bool:
    return (_is_public_writable_name(target)
            and _is_mutable_container_value(value))
def _mutable_assign_target_count(target: ast.AST, value: ast.AST) -> int:
    if _is_mutable_assign_target(target, value):
        return 1
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return 0
    _targets = _list_field(target, 'elts')
    _values = _list_field(value, 'elts')
    if (len(_targets) != len(_values)
            or any(isinstance(item, ast.Starred)
                   for item in (*_targets, *_values))):
        return 0
    return sum(_mutable_assign_target_count(tgt, val)
               for tgt, val in zip(_targets, _values))
def _entry_is_live(entry, stage: str) -> bool:
    if os.path.isfile(entry.path):
        return True
    _log.debug("瞬态文件跳过（%s阶段发现已被外部删除）: %s", stage, entry.path)
    return False
def _statically_dead_module_node_ids(nodes) -> set[int]:
    nodes = tuple(nodes)
    typing_context = collect_typing_tc_bindings(nodes)
    dead: set[int] = set()
    for node in nodes:
        skipped = None
        if isinstance(node, ast.If):
            skipped = type_checking_static_body(node, *typing_context)
            if skipped is None:
                live = static_if_branch(node.test)
                if live is not None:
                    skipped = node.orelse if live else node.body
        elif isinstance(node, ast.While):
            live = static_if_branch(node.test)
            if live is not None:
                skipped = node.orelse if live else node.body
        for stmt in skipped or ():
            dead.update(id(item) for item in walk_nodes(stmt))
    return dead
def _count_global_mutations(entries) -> int:
    total = 0
    for entry in entries:
        if not _entry_is_live(entry, "全局状态扫描"):
            continue
        nodes = tuple(iter_module_binding_nodes(entry.tree))
        dead_ids = _statically_dead_module_node_ids(nodes)
        for node in nodes:
            if id(node) in dead_ids:
                continue
            if isinstance(node, ast.Assign):
                total += sum(
                    _mutable_assign_target_count(target, node.value)
                    for target in node.targets)
            elif isinstance(node, (ast.AugAssign, ast.AnnAssign)) and _is_public_mutable_global(node):
                total += 1
    return total
def _scan_large_ranges(
        entry, rel_path: str, is_test_file: bool,
        policy: _AnalysisPolicy) -> list[dict]:
    findings: list[dict] = []
    _path = getattr(entry, 'path', '')
    for node in nodes_where(entry, (ast.Call,)):
        finding = _stress_check_large_range(
            node, rel_path, is_test_file, policy)
        if not finding:
            continue
        if _path and _line_suppressed(
                _path, getattr(node, 'lineno', 0),
                _LARGE_RANGE_SUPPRESS_RULES):
            continue
        findings.append(finding)
    return findings
def _scan_recursion_risks(entry, rel_path: str, method_ids) -> list[dict]:
    findings: list[dict] = []
    postponed_annotations = _postpones_annotations(getattr(entry, 'tree', None))
    for node in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
        findings.extend(_stress_check_func_recursion(
            node, rel_path, in_class=id(node) in method_ids,
            postponed_annotations=postponed_annotations))
    return findings
_LARGE_ALLOC_SUPPRESS_RULES = ("large_list_alloc", "PERF-ALLOC-01")
_LARGE_RANGE_SUPPRESS_RULES = ("large_range", "PERF-RANGE-01")
def _scan_large_allocs(
        entry, rel_path: str, policy: _AnalysisPolicy) -> list[dict]:
    findings: list[dict] = []
    _path = getattr(entry, 'path', '')
    for node in nodes_where(entry, (ast.List, ast.ListComp, ast.BinOp)):
        if _estimate_list_size(node) > policy.large_alloc:
            if _path and _line_suppressed(
                    _path, getattr(node, 'lineno', 0),
                    _LARGE_ALLOC_SUPPRESS_RULES):
                continue
            findings.append(scan_issue(
                rel_path, getattr(node, 'lineno', 0),
                "large_list_alloc", "medium",
                "大列表分配可能导致内存压力"))
    return findings
def _stress_scan_entry(entry, policy: _AnalysisPolicy) -> list[dict]:
    if not _entry_is_live(entry, "压力测试"):
        return []
    if not policy.analyze_package_init and _is_package_init_entry(entry):
        return []
    rel_path = entry_rel_path(entry)
    is_test_file = is_test_file_path(rel_path)
    findings = _scan_large_ranges(entry, rel_path, is_test_file, policy)
    findings.extend(_scan_recursion_risks(
        entry, rel_path, entry_class_method_ids(entry)))
    if not is_test_file:
        findings.extend(_scan_large_allocs(entry, rel_path, policy))
    return findings
def _collect_stress_risk_findings(cache, policy) -> list[dict]:
    findings: list[dict] = []
    for entry in cache.valid_entries:
        findings.extend(_stress_scan_entry(entry, policy))
    return findings
def run_stress_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    policy = _coerce_analysis_policy(kwargs=kwargs)
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "压力测试", "stress_test", "压测", start)
    cache = _AnalysisCache(cache, policy)
    result = TestMethodResult(method_name="压力测试", method_id="stress_test")
    global_state_issues = []
    global_mutations = _count_global_mutations(cache.valid_entries)
    if global_mutations > policy.global_mutations:
        global_state_issues.append(scan_issue(
            "", 0, "excessive_global_state", "medium",
            f"检测到 {global_mutations} 个模块级可变全局赋值，压力测试可能存在状态泄漏",
            count=global_mutations))
    risk_findings = _collect_stress_risk_findings(cache, policy)
    all_issues = global_state_issues + risk_findings
    status, score, counts = _severity_verdict(all_issues)
    result.findings = all_issues
    result.metrics = {
        "global_mutations": global_mutations,
        "risk_patterns_found": len(risk_findings),
        "mode": "ast_resource_analysis",
        **_severity_metrics(counts, len(all_issues)),
    }
    result.status = status
    result.score = score
    result.summary = (f"AST资源分析: {len(all_issues)} 风险模式 "
                      f"(高危 {counts['high']}, 全局变量: {global_mutations})")
    return result.finish(start)

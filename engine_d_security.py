from __future__ import annotations

import ast
import logging
import math
import os
import re
import time
from collections import Counter
from collections.abc import Iterator, Mapping
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from typing import Any, NamedTuple

from jwsgj.diag_detector_findings import (
    consolidate_findings,
    detector_entry,
    group_envelope,
    normalize_severity,
    worst_sub_status,
)
from jwsgj.diag_shared_ast_nodes import (
    iter_unpack_target_names,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    memoized_module_walk_scope,
    parent_map,
    register_cache_release,
)
from jwsgj.diag_taint_interproc import shared_ast_bridge
from jwsgj.engine_d1_static import StaticAnalyzer
from jwsgj.engine_d1_tool_channels import (
    DEFAULT_INCLUDE_TESTS,
    BanditRunner,
    RuffRunner,
    VulnerabilityScanner,
    postprocess_findings,
    release_bandit_fp_caches,
    release_ruff_fp_caches,
    security_scan_plan,
)
from jwsgj.engine_d2_flow import (
    alias_resolve_map,
    calls_by_lineno_cached,
    collect_d2_taint_source_cached,
    expr_reaches_param,
    function_param_names,
    has_nosec_marker,
    load_sink_tree,
    match_sink,
    parse_module_aliases_cached,
    shell_interpretation_open,
    sink_first_arg,
)
from jwsgj.engine_d2_symbolic import (
    CrossFileSymbolicBridge,
    normalize_e2_finding_fields,
)
from jwsgj.engine_d2_verdict import (
    E2_BRANCH_BOUNDARY,
    GLOBAL_REBOUND_MARKER,
    IMPORTED_NAME_MARKER,
    SanitizeCtx,
    _fn_vars_before_line,
    _scope_has_non_import_binding,
    argv_mutation_name_set,
    clear_e2_scope_memos,
    enclosing_class_assigns,
    enclosing_class_dynamic_attrs,
    enclosing_function,
    enclosing_function_bound_names,
    expr_is_sanitized,
    function_unmodeled_binding_names,
    function_var_exprs,
    is_harness_subprocess_call,
    iter_own_nodes_with_def_sites,
    module_assigns_outside,
    module_multi_assigned_names,
    module_var_map_cached,
    mutation_append_records,
    mutation_positional_records,
    nested_scope_bound_names,
    resolve_bound_chain,
    resolve_local_list_expr,
    resolve_name_closure,
    sentinel_branch_reaches_param,
    subprocess_sink_calls,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.shared_cache import (
    CacheNotWarmedError,
    e1_snapshot_session,
    ensure_entry_warmed,
    fingerprint_freeze_window,
    require_warmed,
)

_log = logging.getLogger("jwsgj.engine_d_security")
__all__ = [
    "SecurityAnalyzer",
    "release_d_group_caches",
    "run_e2_symbolic",
    "run_engine_D",
    "run_security_analysis",
]
def _runtime_env_summary(vuln: Any) -> str:
    runtime_ctx = getattr(vuln, 'runtime_context', {})
    if not isinstance(runtime_ctx, dict):
        runtime_ctx = {}
    parts = [f"{k}={runtime_ctx[k]}" for k in
             ("python_version", "platform", "os") if k in runtime_ctx]
    return "; ".join(parts)
def _e2_finding_message(steps: list, constraints: list,
                         sink_desc: str) -> str:
    if len(steps) >= 2:
        source_descs = [c.split("=", 1)[1] for c in constraints
                        if isinstance(c, str) and c.startswith("taint_source=")]
        _src_desc = source_descs[0] if source_descs else "external_input"
        return (
            f"跨文件污点流: source=[{_src_desc}] → sink=[{sink_desc}] "
            f"({len(steps)} steps, {len(constraints)} constraints; "
            f"外部输入经跨文件调用传播至危险汇点)"
        )
    return (
        f"跨文件符号执行: sink=[{sink_desc}] "
        f"(路径参数可回溯到函数参数，潜在污点待CV仲裁; "
        f"{len(steps)} steps, {len(constraints)} constraints)"
    )
class _E2FilterSpec(NamedTuple):
    count_key: str
    payload_key: str
    detail: str
    summary_suffix: str
_E2_FILTER_SPECS: tuple[_E2FilterSpec, ...] = (
    _E2FilterSpec(
        "filtered_degenerate", "degenerate_filtered",
        "退化单步无约束trace（同文件参数回溯，非跨文件污点流）",
        "退化过滤{n}条同文件单步trace"),
    _E2FilterSpec(
        "filtered_harness", "harness_filtered",
        "工具链调用trace（列表形式固定程序、无 shell、无 -c 脚本参数、"
        "argv[0] 不可回溯参数，确定性误报）",
        "工具链误报过滤{n}条"),
    _E2FilterSpec(
        "filtered_validated", "validated_filtered",
        "已验证注入屏障trace（-c 脚本全部参数派生片段受标识符守卫/"
        "repr转义/静态模板屏障保护，确定性误报）",
        "注入屏障误报过滤{n}条"),
    _E2FilterSpec(
        "filtered_inert_probe", "inert_probe_filtered",
        "惰性探测trace（argv[0] 为解析产物、其余元素恰为常量 "
        "--version，无参数注入通道）",
        "惰性探测误报过滤{n}条"),
    _E2FilterSpec(
        "filtered_audited", "audited_filtered",
        "已审计trace（sink 行携带 nosec 审计标注，开发者显式审计决策）",
        "已审计误报过滤{n}条"),
)
def _filter_payload(filter_counts: dict[str, int]) -> dict[str, int]:
    _known = {spec.count_key for spec in _E2_FILTER_SPECS}
    _unknown = set(filter_counts) - _known
    if _unknown:
        _log.warning("[E2] 未登记的过滤类别被丢弃: %s", sorted(_unknown))
    return {spec.payload_key: filter_counts.get(spec.count_key, 0)
            for spec in _E2_FILTER_SPECS}
def _e2_active_filters(
    filter_counts: dict[str, int],
) -> Iterator[tuple[_E2FilterSpec, int]]:
    for spec in _E2_FILTER_SPECS:
        count = filter_counts.get(spec.count_key, 0)
        if count:
            yield spec, count
@dataclass(slots=True)
class _E2FilterState:
    counts: dict[str, int] = field(
        default_factory=lambda: {spec.count_key: 0 for spec in _E2_FILTER_SPECS})
    details: list = field(default_factory=list)
class _E2ScanStats(NamedTuple):
    files_scanned: int | None = None
    files_failed: int | None = None
_TRACE_LIMIT = 200
def _optional_count(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float):
        return (int(value) if math.isfinite(value) and value >= 0
                and value.is_integer() else None)
    if isinstance(value, str):
        text = value.strip()
        if not text:
            return None
        try:
            number = float(text)
        except ValueError:
            return None
        return (int(number) if math.isfinite(number) and number >= 0
                and number.is_integer() else None)
    return None
def _finding_items(
    items: Any, context: str, *, failures: list[str] | None = None,
) -> list[dict]:
    if items is None:
        return []
    if isinstance(items, Mapping):
        return [dict(items)]
    if isinstance(items, (list, tuple)):
        raw = list(items)
    elif isinstance(items, (str, bytes)):
        detail = f"findings 载体形态非法({type(items).__name__})"
        if failures is not None:
            failures.append(detail)
        _log.warning("[security_analyzer] %s %s，按零产出处理",
                     context, detail)
        return []
    else:
        try:
            raw = list(items)
        except TypeError:
            detail = f"findings 不可展开({type(items).__name__})"
            if failures is not None:
                failures.append(detail)
            _log.warning("[security_analyzer] %s %s，按零产出处理",
                         context, detail)
            return []
    valid = [item for item in raw if isinstance(item, dict)]
    if len(valid) != len(raw):
        detail = f"丢弃 {len(raw) - len(valid)} 个非 dict 发现项"
        if failures is not None:
            failures.append(detail)
        _log.warning("[security_analyzer] %s %s", context, detail)
    return valid
_DEGENERATE_HIGHRISK_SINKS = frozenset({
    "eval", "exec", "system", "popen", "subprocess",
})
_MATCH_AS = getattr(ast, "MatchAs", ())
_MATCH_STAR = getattr(ast, "MatchStar", ())
_MATCH_MAPPING = getattr(ast, "MatchMapping", ())
_MATCH_STMT = getattr(ast, "Match", ())
_TRY_STAR_STMT = getattr(ast, "TryStar", ())
def _dict_literal_children(expr: ast.Dict) -> list:
    return [k for k in expr.keys if k is not None] + list(expr.values)
_PURE_LITERAL_CHILDREN = {
    ast.List: lambda e: list(e.elts),
    ast.Tuple: lambda e: list(e.elts),
    ast.Set: lambda e: list(e.elts),
    ast.Dict: _dict_literal_children,
    ast.JoinedStr: lambda e: list(e.values),
    ast.BinOp: lambda e: [e.left, e.right],
    ast.UnaryOp: lambda e: [e.operand],
}
def _pure_literal_children(expr: ast.AST) -> list | None:
    _extract = _PURE_LITERAL_CHILDREN.get(type(expr))
    return _extract(expr) if _extract is not None else None
def _is_pure_literal_expr(expr: ast.AST | None, _depth: int = 0) -> bool:
    if expr is None or _depth > 12:
        return False
    if isinstance(expr, ast.Constant):
        return True
    _children = _pure_literal_children(expr)
    if _children is None:
        return False
    return all(_is_pure_literal_expr(e, _depth + 1) for e in _children)
def _line_sink_calls(path, tree, line, sink):
    for call, params, assigns, scope_aliases in calls_by_lineno_cached(
            path, tree).get(line, ()):
        if params is None:
            continue
        if match_sink(call, params, assigns, scope_aliases) == sink:
            yield call
def _fn_binding_is_literal(name: str, fn, exprs: list, unmodeled,
                           line: int) -> bool:
    if len(exprs) != 1 or name in unmodeled:
        return False
    mutations = (mutation_append_records(name, fn)
                 + mutation_positional_records(name, fn))
    if any(_r[0] <= line for _r in mutations):
        return False
    return _is_pure_literal_expr(exprs[0])
def _literal_arg_resolver(path: str, tree, line: int):
    fn = enclosing_function(tree, line)
    _shadow = frozenset(nested_scope_bound_names(tree, line))
    _mod_multi = module_multi_assigned_names(path, tree)
    _mod_map = module_var_map_cached(path, tree)
    _fn_vars = (_fn_vars_before_line(function_var_exprs(fn), line)
                if fn is not None else {})
    _fn_free = (function_unmodeled_binding_names(fn)
                if fn is not None else frozenset())
    _fn_params = (frozenset(function_param_names(fn))
                  if fn is not None else frozenset())
    _closure = (enclosing_function_bound_names(tree, fn)
                if fn is not None else frozenset())
    _opaque_names = _shadow | _fn_params | _closure | _fn_free
    _mod_mutated_memo: dict[str, bool] = {}
    def _mod_mutated(name: str) -> bool:
        hit = _mod_mutated_memo.get(name)
        if hit is None:
            hit = bool(mutation_append_records(name, tree)
                       or mutation_positional_records(name, tree))
            _mod_mutated_memo[name] = hit
        return hit
    def _resolve(expr) -> bool:
        if _is_pure_literal_expr(expr):
            return True
        if not isinstance(expr, ast.Name):
            return False
        name = expr.id
        if name in _opaque_names:
            return False
        if name in _fn_vars:
            return _fn_binding_is_literal(
                name, fn, _fn_vars[name], _fn_free, line)
        if name in _mod_multi or _mod_mutated(name):
            return False
        return _is_pure_literal_expr(_mod_map.get(name))
    return _resolve
def _sink_first_arg_pure_literal(
    skill_dir: str, rel_file: str, line: int, sink: str, cache=None,
) -> bool:
    tree, path = load_sink_tree(skill_dir, rel_file, cache)
    if tree is None or path is None:
        return False
    try:
        _calls = list(_line_sink_calls(path, tree, line, sink))
        if not _calls:
            return False
        _resolve = _literal_arg_resolver(path, tree, line)
        return all(_resolve(sink_first_arg(call)) for call in _calls)
    except Exception as e:  
        _log.debug("sink 首参纯字面量判定异常，保守返回 False 交 CV 仲裁: %s", e, exc_info=True)
        return False
def _rebind_targets_of(node) -> list:
    if isinstance(node, ast.Assign):
        return node.targets
    if isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.For,
                        ast.AsyncFor, ast.NamedExpr)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    return []
_STR_BINDING_SITES: tuple[tuple[object, str], ...] = (
    (ast.ExceptHandler, "name"),
    (_MATCH_AS, "name"),
    (_MATCH_STAR, "name"),
    (_MATCH_MAPPING, "rest"),
)
def _import_binds(node) -> set[str]:
    if isinstance(node, ast.Import):
        return {a.asname or a.name.split(".")[0] for a in node.names}
    return {a.asname or a.name for a in node.names if a.name != "*"}
def _bound_names_of(node: ast.AST) -> set[str]:
    names: set[str] = set()
    for target in _rebind_targets_of(node):
        names.update(iter_unpack_target_names(target))
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        names |= _import_binds(node)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                           ast.ClassDef)):
        names.add(node.name)
    elif isinstance(node, ast.Delete):
        names.update(_n for target in node.targets
                     for _n in iter_unpack_target_names(target))
    for _types, _attr in _STR_BINDING_SITES:
        if isinstance(node, _types):
            _bound = getattr(node, _attr, None)
            if _bound:
                names.add(_bound)
    return names
def _node_rebinds_name(node, name: str, after_line: int,
                       before_line: int) -> bool:
    line = getattr(node, "lineno", None)
    if line is None or not (after_line < line <= before_line):
        return False
    return name in _bound_names_of(node)
def _scope_write_names(scope: ast.AST) -> set[str]:
    names: set[str] = set()
    for target in _rebind_targets_of(scope):
        names.update(iter_unpack_target_names(target))
    for stmt in iter_own_nodes_with_def_sites(scope):
        names |= _bound_names_of(stmt)
    return names
def _declared_nested_writers(scope: ast.AST) -> frozenset:
    names: set[str] = set()
    for node in walk_nodes(scope):
        if node is scope or not isinstance(
                node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        declared = {name
                    for stmt in iter_own_nodes_with_def_sites(node)
                    if isinstance(stmt, (ast.Global, ast.Nonlocal))
                    for name in stmt.names}
        if declared:
            names |= declared & _scope_write_names(node)
    return frozenset(names)
def _name_reassigned_between(fn, name: str, after_line: int,
                             before_line: int, nested_writers=None) -> bool:
    if nested_writers is None:
        nested_writers = _declared_nested_writers(fn)
    if name in nested_writers:
        return True
    return any(_node_rebinds_name(node, name, after_line, before_line)
               for node in iter_own_nodes_with_def_sites(fn))
_BAIL_NODE_TYPES = (ast.Return, ast.Raise, ast.Continue, ast.Break)
def _body_always_bails(stmts: list) -> bool:
    return any(
        isinstance(_s, _BAIL_NODE_TYPES)
        or (isinstance(_s, ast.If) and _both_branches_bail(_s))
        for _s in stmts)
def _both_branches_bail(node: ast.If) -> bool:
    return (bool(node.orelse) and _body_always_bails(node.body)
            and _body_always_bails(node.orelse))
def _bail_body_end(node: ast.If) -> int:
    _ends = [getattr(_s, "end_lineno", None) or getattr(_s, "lineno", 0) or 0
             for _s in node.body]
    return max(_ends) if _ends else (getattr(node, "lineno", 0) or 0)
def _ancestor_chain(node: ast.AST, stop: ast.AST, parent: dict):
    chain: list[ast.AST] = []
    cur = node
    while cur is not None and cur is not stop:
        chain.append(cur)
        cur = parent.get(cur)
    return chain, cur
_LOOP_NODE_TYPES = (ast.For, ast.AsyncFor, ast.While)
class _LoopBackEdgeCtx(NamedTuple):
    parent: dict
    fn: object
    sink_loops: tuple
    loop_writes: dict
def _loop_backedge_ctx(fn, sink_node):
    if fn is None or sink_node is None:
        return None
    parent = parent_map(fn)
    chain, _stop = _ancestor_chain(sink_node, fn, parent)
    if _stop is not fn:
        return None
    loops = tuple(_n for _n in chain if isinstance(_n, _LOOP_NODE_TYPES))
    if not loops:
        return None
    return _LoopBackEdgeCtx(
        parent=parent, fn=fn, sink_loops=loops,
        loop_writes={id(_l): frozenset(_scope_write_names(_l))
                     for _l in loops})
def _loop_backedge_invalidates(guard_if: ast.If, name: str, ctx) -> bool:
    if ctx is None:
        return False
    _guard_ids = {id(_n)
                  for _n in _ancestor_chain(guard_if, ctx.fn, ctx.parent)[0]}
    return any(name in ctx.loop_writes.get(id(_loop), frozenset())
               and id(_loop) not in _guard_ids
               for _loop in ctx.sink_loops)
def _guard_within_sink_chain(guard_if: ast.If, s_chain: list) -> bool:
    idx = next((i for i, c in enumerate(s_chain) if c is guard_if), None)
    if idx is None or idx == 0:
        return False
    below = s_chain[idx - 1]
    if any(s is below for s in guard_if.body):
        return False
    return bool(guard_if.orelse
                and any(s is below for s in guard_if.orelse))
def _reduce_guard_chain(guard_if: ast.If, fn: ast.AST, parent: dict,
                        s_ids: set):
    g_chain: list[ast.AST] = []
    cur = guard_if
    lca = fn
    while cur is not None and cur is not fn:
        if id(cur) in s_ids:
            lca = cur
            break
        g_chain.append(cur)
        cur = parent.get(cur)
    return lca, g_chain
_SKIPPABLE_GUARD_CONTAINERS = (
    ast.If, ast.For, ast.While, ast.AsyncFor, ast.ExceptHandler,
    ast.Try, ast.With, ast.AsyncWith,
) + ((_MATCH_STMT,) if _MATCH_STMT else ()) \
    + ((_TRY_STAR_STMT,) if _TRY_STAR_STMT else ())
def _guard_container_skippable(g_chain: list) -> bool:
    return any(isinstance(c, _SKIPPABLE_GUARD_CONTAINERS)
               for c in g_chain[1:])
def _lca_stmt_tops(lca: ast.AST, g_chain: list, s_chain: list,
                   fn: ast.AST):
    s_top = _sink_top_under_lca(lca, s_chain, fn)
    if s_top is None:
        return None
    return g_chain[-1], s_top
def _sink_top_under_lca(lca: ast.AST, s_chain: list,
                        fn: ast.AST) -> ast.AST | None:
    if lca is fn:
        return s_chain[-1] if s_chain else None
    s_idx = next((i for i, c in enumerate(s_chain) if c is lca), None)
    if s_idx is None or s_idx == 0:
        return None
    return s_chain[s_idx - 1]
def _lca_top_stmts(guard_if: ast.If, s_chain: list, s_ids: set,
                   fn: ast.AST, parent: dict):
    lca, g_chain = _reduce_guard_chain(guard_if, fn, parent, s_ids)
    if not g_chain or _guard_container_skippable(g_chain):
        return None
    _tops = _lca_stmt_tops(lca, g_chain, s_chain, fn)
    if _tops is None:
        return None
    return lca, _tops[0], _tops[1]
def _stmt_list_id_sets(node: ast.AST) -> list[list[int]]:
    return [
        [id(x) for x in value]
        for _f in node._fields
        if isinstance(value := getattr(node, _f, None), list)
    ]
def _ordered_in_same_stmt_list(lca: ast.AST, g_top: ast.AST,
                               s_top: ast.AST) -> bool:
    g_id, s_id = id(g_top), id(s_top)
    for _ids in _stmt_list_id_sets(lca):
        if g_id in _ids and s_id in _ids:
            return _ids.index(g_id) < _ids.index(s_id)
    return False
def _guard_covers_sink(guard_if: ast.If, sink_node: ast.AST, fn: ast.AST) -> bool:
    parent = parent_map(fn)
    s_chain, cur = _ancestor_chain(sink_node, fn, parent)
    if cur is not fn:
        return False
    s_ids = {id(c) for c in s_chain}
    if id(guard_if) in s_ids:
        return _guard_within_sink_chain(guard_if, s_chain)
    _tops = _lca_top_stmts(guard_if, s_chain, s_ids, fn, parent)
    if _tops is None:
        return False
    return _ordered_in_same_stmt_list(_tops[0], _tops[1], _tops[2])
@dataclass(frozen=True)
class _PatternCtx:
    fn_vars_map: object
    mod_assigns: object
    mod_aliases: object
    shadowed_names: frozenset = frozenset()
    param_names: frozenset = frozenset()
    unmodeled_names: frozenset = frozenset()
    fn: object = None
    import_identities: object = None
    tree: object = None
def _mutation_rebinds(name: str, fn) -> bool:
    return bool(fn is not None
                and (mutation_append_records(name, fn)
                     or mutation_positional_records(name, fn)))
_SAFE_TOKEN_CHARS = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")
_SAFE_TOKEN_BRACED_QUANTIFIER_RE = re.compile(
    r"\{[0-9]+(?:,[0-9]*)?\}")
def _safe_token_class_is_safe(body: str) -> bool:
    if not body or body.startswith("^") or "\\" in body:
        return False
    i = 0
    while i < len(body):
        if i + 2 < len(body) and body[i + 1] == "-":
            start, end = body[i], body[i + 2]
            if (start > end or start not in _SAFE_TOKEN_CHARS
                    or end not in _SAFE_TOKEN_CHARS):
                return False
            if any(chr(cp) not in _SAFE_TOKEN_CHARS
                   for cp in range(ord(start), ord(end) + 1)):
                return False
            i += 3
            continue
        if body[i] not in _SAFE_TOKEN_CHARS:
            return False
        i += 1
    return True
def _token_quantifier_end(pattern: str, pos: int) -> int:
    if pos >= len(pattern):
        return pos
    if pattern[pos] in "+*?":
        return pos + 1
    if pattern[pos] != "{":
        return pos
    match = _SAFE_TOKEN_BRACED_QUANTIFIER_RE.match(pattern, pos)
    return match.end() if match is not None else -1
def _is_safe_token_pattern(pattern: str) -> bool:
    if not pattern:
        return False
    pattern = pattern.removeprefix("^")
    pattern = pattern.removesuffix("$")
    if not pattern:
        return False
    i = 0
    while i < len(pattern):
        if pattern[i] in _SAFE_TOKEN_CHARS:
            i += 1
        elif pattern[i] == "[":
            close = pattern.find("]", i + 1)
            if close < 0 or not _safe_token_class_is_safe(
                    pattern[i + 1:close]):
                return False
            i = close + 1
        else:
            return False
        i = _token_quantifier_end(pattern, i)
        if i < 0:
            return False
    return True
def _pattern_name_is_static(name_id: str, pctx: _PatternCtx,
                            _depth: int) -> bool:
    _fn_exprs = (list(pctx.fn_vars_map.get(name_id, []))
                 if pctx.fn_vars_map else [])
    if _fn_exprs:
        if (name_id in pctx.param_names
                or name_id in pctx.unmodeled_names):
            return False
        if _mutation_rebinds(name_id, pctx.fn):
            return False
        _exprs = _fn_exprs
    else:
        if name_id in pctx.shadowed_names:
            return False
        _exprs = list(pctx.mod_assigns.get(name_id, []))
        if not _exprs:
            return False
    if any(e is IMPORTED_NAME_MARKER
           or e is GLOBAL_REBOUND_MARKER for e in _exprs):
        return False
    return all(_pattern_is_static(e, pctx, _depth + 1) for e in _exprs)
def _pattern_call_is_static(pexpr: ast.Call, pctx: _PatternCtx,
                            _depth: int) -> bool:
    return (isinstance(pexpr.func, ast.Attribute)
            and pexpr.func.attr == "compile"
            and _is_re_module_receiver(pexpr.func.value, pctx.mod_aliases,
                                       pctx)
            and not pexpr.keywords
            and len(pexpr.args) == 1
            and _pattern_is_static(pexpr.args[0], pctx, _depth + 1))
def _pattern_is_static(pexpr, pctx: _PatternCtx, _depth: int = 0) -> bool:
    if _depth > 5 or pexpr is None:
        return False
    if isinstance(pexpr, ast.Constant):
        return (isinstance(pexpr.value, str)
                and _is_safe_token_pattern(pexpr.value))
    if isinstance(pexpr, ast.Call):
        return _pattern_call_is_static(pexpr, pctx, _depth)
    if isinstance(pexpr, ast.Name):
        return _pattern_name_is_static(pexpr.id, pctx, _depth)
    return False
def _is_guard_call_shape(target) -> bool:
    return (isinstance(target, ast.Call)
            and isinstance(target.func, ast.Attribute)
            and target.func.attr == "fullmatch")
def _guard_call_names(target, pctx: _PatternCtx) -> list:
    if isinstance(target, ast.Call) and target.keywords:
        return []
    if isinstance(target, ast.Call) and isinstance(target.func, ast.Name):
        return _bare_fullmatch_guard_names(target, pctx)
    if not _is_guard_call_shape(target):
        return []
    args = target.args
    if len(args) == 1:
        name_arg, pattern_expr = args[0], target.func.value
        receiver_ok = True
    elif len(args) == 2:
        name_arg, pattern_expr = args[1], args[0]
        receiver_ok = _is_re_module_receiver(
            target.func.value, pctx.mod_aliases, pctx)
    else:
        return []
    if not isinstance(name_arg, ast.Name):
        return []
    if not _guard_pattern_static(pattern_expr, receiver_ok, pctx):
        return []
    return [name_arg.id]
def _bare_fullmatch_guard_names(target: ast.Call,
                                 pctx: _PatternCtx) -> list:
    if _import_identity_of(target.func.id, pctx) != "re.fullmatch":
        return []
    args = target.args
    if len(args) != 2 or not isinstance(args[1], ast.Name):
        return []
    if not _guard_pattern_static(args[0], True, pctx):
        return []
    return [args[1].id]
def _guard_pattern_static(pattern_expr, receiver_ok: bool,
                          pctx: _PatternCtx) -> bool:
    return receiver_ok and _pattern_is_static(pattern_expr, pctx)
def _not_guard_operand(node) -> object | None:
    if not isinstance(node, ast.If):
        return None
    test = node.test
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return test.operand
    return None
def _guard_names_from_node(
    node, pctx: _PatternCtx,
) -> list:
    operand = _not_guard_operand(node)
    if operand is None:
        return []
    return _guard_call_names(operand, pctx)
class _GuardEvidence(NamedTuple):
    nested_writers: frozenset
    loop_ctx: object
def _guard_applies_to_sink(
    node, name: str, fn, sink_line: int | None, sink_node,
    evidence: _GuardEvidence,
) -> bool:
    if not _body_always_bails(node.body):
        return False
    return (sink_line is None
            or _guard_protects_sink(node, name, fn, sink_line, sink_node,
                                    evidence))
def _collect_guarded_names(
    fn, sink_line: int | None, sink_node: ast.AST | None, *,
    mod_assigns: dict, mod_aliases: dict | None, tree: ast.AST | None,
):
    _fn_vars = (function_var_exprs(fn) if mod_assigns is not None else None)
    _params = frozenset(function_param_names(fn))
    _unmodeled = function_unmodeled_binding_names(fn)
    _shadowed = _params | frozenset(_fn_vars or ()) | _unmodeled
    _pctx = _PatternCtx(
        fn_vars_map=_fn_vars,
        mod_assigns=mod_assigns,
        mod_aliases=mod_aliases,
        shadowed_names=_shadowed,
        param_names=_params,
        unmodeled_names=_unmodeled,
        fn=fn,
        import_identities=_visible_import_identities(tree, fn),
        tree=tree,
    )
    _evidence = _GuardEvidence(
        nested_writers=_declared_nested_writers(fn),
        loop_ctx=_loop_backedge_ctx(fn, sink_node))
    return {
        _name
        for node in iter_own_nodes_with_def_sites(fn)
        for _name in _guard_names_from_node(node, _pctx)
        if _guard_applies_to_sink(node, _name, fn, sink_line, sink_node,
                                  _evidence)
    }
def _is_re_module_receiver(expr, mod_aliases, pctx=None) -> bool:
    if not isinstance(expr, ast.Name):
        return False
    if _import_identity_of(expr.id, pctx) == "re":
        return True
    if pctx is not None and pctx.import_identities is not None:
        return False
    if mod_aliases is None:
        return expr.id == "re"
    return (mod_aliases.get(expr.id, expr.id) == "re"
            and not _receiver_name_shadowed(expr.id, pctx))
def _receiver_name_shadowed(name: str, pctx) -> bool:
    if pctx is None or pctx.mod_assigns is None:
        return False
    if name in pctx.shadowed_names:
        return True
    return any(e is not IMPORTED_NAME_MARKER
               for e in pctx.mod_assigns.get(name, ()))
def _import_identity_records(node) -> Iterator[tuple[str, str]]:
    if isinstance(node, ast.Import):
        for alias in node.names:
            local = alias.asname or alias.name.split(".", 1)[0]
            module = alias.name if alias.asname else alias.name.split(".", 1)[0]
            yield local, module
    elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
        for alias in node.names:
            if alias.name != "*":
                yield alias.asname or alias.name, f"{node.module}.{alias.name}"
def _runtime_scope_import_identities(
    scope, excluded_node_ids: frozenset[int],
) -> dict[str, str]:
    identities: dict[str, str] = {}
    for node in iter_own_nodes_with_def_sites(scope):
        if id(node) in excluded_node_ids:
            continue
        for name, identity in _import_identity_records(node):
            identities[name] = identity
    return identities
def _visible_import_identities(tree, scope) -> dict[str, str]:
    if tree is None or not isinstance(scope, ast.AST):
        return {}
    parent = collect_lexical_scope_table(tree).parent
    chain: list[ast.AST] = []
    current: ast.AST | None = scope
    while current is not None:
        if not isinstance(current, ast.ClassDef):
            chain.append(current)
        current = parent.get(current)
    excluded_node_ids = frozenset(type_checking_body_node_ids(tree))
    identities: dict[str, str] = {}
    for scoped in reversed(chain):
        identities.update(_runtime_scope_import_identities(
            scoped, excluded_node_ids))
    return identities
def _visible_name_rebound(tree, scope, name: str) -> bool:
    if tree is None or not isinstance(scope, ast.AST):
        return False
    parent = collect_lexical_scope_table(tree).parent
    current = scope
    while current is not None:
        if (not isinstance(current, ast.ClassDef)
                and _scope_has_non_import_binding(current, name)):
            return True
        current = parent.get(current)
    return False
def _import_identity_of(name: str, pctx) -> str:
    if pctx is None:
        return ""
    identity = (pctx.import_identities or {}).get(name)
    if not identity:
        return ""
    if _visible_name_rebound(pctx.tree, pctx.fn, name):
        return ""
    if name in pctx.param_names:
        return ""
    if pctx.fn_vars_map and name in pctx.fn_vars_map:
        return ""
    if any(e is not IMPORTED_NAME_MARKER
           for e in (pctx.mod_assigns or {}).get(name, ())):
        return ""
    return identity
def _guard_protects_sink(node: ast.If, name: str, fn,
                         sink_line: int, sink_node,
                         evidence: _GuardEvidence) -> bool:
    if node.lineno >= sink_line:
        return False
    if _loop_backedge_invalidates(node, name, evidence.loop_ctx):
        return False
    if sink_node is not None and not _guard_covers_sink(node, sink_node, fn):
        return False
    return not _name_reassigned_between(fn, name, _bail_body_end(node),
                                        sink_line, evidence.nested_writers)
_PYTHON_DASH_C_HEADS = frozenset({
    "python", "pythonw", "pyw", "py", "pypy",
})
_DASH_C_FLAG_HEADS = {
    "-c": _PYTHON_DASH_C_HEADS | {
        "bash", "zsh", "sh", "shell", "dash", "ash", "ksh", "csh",
        "tcsh", "fish", "powershell", "pwsh",
    },
    "/c": ("cmd",),
}
_DASH_C_FLAGS = frozenset(_DASH_C_FLAG_HEADS)
_DASH_C_VERSION_SUFFIX_CHARS = frozenset("0123456789._-")
def _is_sys_executable_node(head) -> bool:
    return (isinstance(head, ast.Attribute)
            and isinstance(head.value, ast.Name)
            and head.value.id == "sys" and head.attr == "executable")
def _normalized_interpreter_head(head) -> str:
    if _is_sys_executable_node(head):
        return "sys.executable"
    if not isinstance(head, ast.Constant) or not isinstance(head.value, str):
        return ""
    base = head.value.lower().replace("\\", "/").rsplit("/", 1)[-1]
    for suffix in (".exe", ".bat", ".cmd", ".com"):
        if base.endswith(suffix):
            return base[:-len(suffix)]
    return base
def _interpreter_head_matches(base: str, hint: str) -> bool:
    return base == hint or (
        base.startswith(hint)
        and all(c in _DASH_C_VERSION_SUFFIX_CHARS
                for c in base[len(hint):]))
def _dash_c_interpreter_flag(head, flag) -> bool:
    if not isinstance(flag, ast.Constant) or flag.value not in _DASH_C_FLAGS:
        return False
    base = _normalized_interpreter_head(head)
    if base == "sys.executable":
        return flag.value == "-c"
    return any(_interpreter_head_matches(base, hint)
               for hint in _DASH_C_FLAG_HEADS[flag.value])
def _dash_c_allows_python_repr(head) -> bool:
    base = _normalized_interpreter_head(head)
    return base == "sys.executable" or any(
        _interpreter_head_matches(base, hint)
        for hint in _PYTHON_DASH_C_HEADS)
def _is_python_literalization_node(node) -> bool:
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "repr"
    ) or (isinstance(node, ast.FormattedValue) and node.conversion == 114)
def _literalization_bindings(node, ctx) -> list:
    if isinstance(node, ast.Name):
        bindings = (ctx.fn_vars.get(node.id)
                    or ctx.mod_assigns.get(node.id) or ())
    elif isinstance(node, ast.Attribute):
        bindings = ctx.cls_assigns.get(node.attr, ())
    else:
        return []
    return [value for value in bindings if isinstance(value, ast.AST)]
def _contains_python_literalization(expr, ctx) -> bool:
    stack = [expr]
    seen: set[int] = set()
    while stack:
        node = stack.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        if _is_python_literalization_node(node):
            return True
        stack.extend(_literalization_bindings(node, ctx))
        stack.extend(ast.iter_child_nodes(node))
    return False
def _argv_multi_assigned(first, elts, var_map, var_map_full) -> bool:
    if (isinstance(first, ast.Name)
            and len(var_map_full.get(first.id, [])) > 1):
        return True
    if any(isinstance(e, ast.Name) and len(var_map_full.get(e.id, [])) > 1
           for e in elts):
        return True
    return any(
        len(var_map_full.get(_n, [])) > 1
        for _n in resolve_name_closure(first, var_map)
    )
def _argv_resolve_or_none(call, var_map, var_map_full, fn):
    if shell_interpretation_open(call):
        return None
    first = sink_first_arg(call)
    list_expr = resolve_local_list_expr(first, var_map)
    if not isinstance(list_expr, ast.List):
        return None
    elts = list_expr.elts
    resolved = [resolve_bound_chain(e, var_map) for e in elts]
    if _argv_multi_assigned(first, elts, var_map, var_map_full):
        return None
    mutation_names = argv_mutation_name_set(first, var_map, var_map_full)
    sink_pos = (call.lineno, call.col_offset)
    if any((_r[0], _r[1]) < sink_pos
           for _n in mutation_names
           for _r in mutation_positional_records(_n, fn)):
        return None
    return first, elts, resolved, mutation_names
def _argv_const_partition(resolved) -> tuple:
    consts = [r.value for r in resolved
              if isinstance(r, ast.Constant) and isinstance(r.value, str)]
    nonconst_idx = [i for i, r in enumerate(resolved)
                    if not (isinstance(r, ast.Constant)
                            and isinstance(r.value, str))]
    return consts, nonconst_idx
_TRUSTED_INERT_RESOLVERS = frozenset({"shutil.which"})
def _judge_import_identity(name: str, jctx) -> str:
    pctx = _PatternCtx(
        fn_vars_map=jctx.var_map_full,
        mod_assigns=jctx.mod_assigns,
        mod_aliases=jctx.mod_aliases,
        param_names=frozenset(jctx.param_names),
        import_identities=_visible_import_identities(jctx.tree, jctx.fn),
        fn=jctx.fn,
        tree=jctx.tree,
    )
    return _import_identity_of(name, pctx)
def _qualified_call_name(call: ast.Call, jctx) -> str:
    func = call.func
    if isinstance(func, ast.Name):
        return _judge_import_identity(func.id, jctx)
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        owner = _judge_import_identity(func.value.id, jctx)
        return f"{owner}.{func.attr}" if owner else ""
    return ""
def _trusted_inert_program(expr, jctx) -> bool:
    return (isinstance(expr, ast.Call)
            and _qualified_call_name(expr, jctx) in _TRUSTED_INERT_RESOLVERS)
def _is_inert_probe_argv(elts, resolved, params, assigns, jctx) -> bool:
    consts, _nonconst_idx = _argv_const_partition(resolved)
    return (bool(elts)
            and _nonconst_idx == [0]
            and len(consts) == len(resolved) - 1 and consts == ["--version"]
            and _trusted_inert_program(resolved[0], jctx)
            and not (isinstance(elts[0], ast.Name) and elts[0].id in params)
            and not expr_reaches_param(elts[0], params, assigns))
def _dash_c_flag_indexes(resolved) -> list:
    return [i for i, r in enumerate(resolved)
            if isinstance(r, ast.Constant) and r.value in _DASH_C_FLAGS]
_E2_OPAQUE_LITERALS = frozenset({
    E2_BRANCH_BOUNDARY, IMPORTED_NAME_MARKER.value, GLOBAL_REBOUND_MARKER.value,
})
def _dash_c_prefix_is_static(expr) -> bool:
    return (_is_pure_literal_expr(expr)
            and not any(isinstance(node, ast.Constant)
                        and node.value in _E2_OPAQUE_LITERALS
                        for node in walk_nodes(expr)))
def _incremental_append_elements(first, fn, sink_pos,
                                 mutation_names=None) -> list | None:
    if not isinstance(first, ast.Name):
        return []
    names = mutation_names or frozenset({first.id})
    _recs = [
        _r
        for _name in sorted(names)
        for _r in mutation_append_records(_name, fn)
        if (_r[0], _r[1]) < sink_pos
    ]
    _recs.sort(key=lambda _r: (_r[0], _r[1]))
    if any(_cond for _lo, _co, _cond, _e in _recs):
        return None
    return [_e for _lo, _co, _cond, _e in _recs]
def _literalized_script_form(expr, ctx, depth=0) -> str | None:
    if depth > 8:
        return None
    if isinstance(expr, ast.Constant):
        return expr.value if isinstance(expr.value, str) else None
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
        left = _literalized_script_form(expr.left, ctx, depth + 1)
        right = _literalized_script_form(expr.right, ctx, depth + 1)
        if left is None or right is None:
            return None
        return left + right
    if (isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Mod)
            and isinstance(expr.left, ast.Constant)
            and isinstance(expr.left.value, str)):
        values = (expr.right.elts if isinstance(expr.right, ast.Tuple)
                  else [expr.right])
        if not all(expr_is_sanitized(value, ctx) for value in values):
            return None
        try:
            return expr.left.value % tuple(None for _ in values)
        except (TypeError, ValueError):
            return None
    if isinstance(expr, ast.JoinedStr):
        parts = []
        for value in expr.values:
            if (isinstance(value, ast.Constant)
                    and isinstance(value.value, str)):
                parts.append(value.value)
            elif (isinstance(value, ast.FormattedValue)
                    and expr_is_sanitized(value, ctx)):
                parts.append("None")
            else:
                return None
        return "".join(parts)
    if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Attribute):
        if expr.func.attr == "replace":
            if expr.keywords or len(expr.args) not in (2, 3):
                return None
            receiver = _literalized_script_form(
                expr.func.value, ctx, depth + 1)
            old = expr.args[0]
            replacement = _literalized_script_form(
                expr.args[1], ctx, depth + 1)
            if (receiver is None or replacement is None
                    or not isinstance(old, ast.Constant)
                    or not isinstance(old.value, str)):
                return None
            if len(expr.args) == 2:
                return receiver.replace(old.value, replacement)
            count = expr.args[2]
            if (not isinstance(count, ast.Constant)
                    or not isinstance(count.value, int)
                    or isinstance(count.value, bool)):
                return None
            return receiver.replace(old.value, replacement, count.value)
        if expr.func.attr == "join":
            if (expr.keywords or len(expr.args) != 1
                    or not isinstance(expr.args[0], (ast.List, ast.Tuple))):
                return None
            separator = _literalized_script_form(
                expr.func.value, ctx, depth + 1)
            values = [_literalized_script_form(value, ctx, depth + 1)
                      for value in expr.args[0].elts]
            if separator is None or any(value is None for value in values):
                return None
            return separator.join(values)
    if isinstance(expr, (ast.Name, ast.Attribute)):
        bindings = _literalization_bindings(expr, ctx)
        if bindings:
            if len(bindings) != 1:
                return None
            return _literalized_script_form(bindings[0], ctx, depth + 1)
    return "None" if expr_is_sanitized(expr, ctx) else None
def _literalized_script_context_safe(expr, ctx) -> bool:
    script = _literalized_script_form(expr, ctx)
    if script is None:
        return False
    try:
        tree = ast.parse(script)
    except (SyntaxError, ValueError):
        return False
    if len(tree.body) != 1:
        return False
    statement = tree.body[0]
    calls = [node for node in walk_nodes(statement) if isinstance(node, ast.Call)]
    if not calls:
        return True
    if len(calls) != 1 or not isinstance(statement, ast.Expr):
        return False
    call = calls[0]
    return (call is statement.value and isinstance(call.func, ast.Name)
            and call.func.id == "print")
def _sanitized_script_expr(expr, ctx) -> bool:
    sanitized = expr_is_sanitized(expr, ctx)
    if not sanitized:
        if not (isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Mod)):
            return False
        template = expr.left
        if not (isinstance(template, ast.Constant)
                and isinstance(template.value, str)):
            return False
        values = (expr.right.elts if isinstance(expr.right, ast.Tuple)
                  else [expr.right])
        sanitized = all(expr_is_sanitized(value, ctx) for value in values)
    if not sanitized:
        return False
    # 纯字面量脚本同样必须通过内容校验：字面量脚本仍可消费经 argv 传入的
    # 污点参数（如 os.system(sys.argv[1])），不得因“无插值”直接放行。
    return _literalized_script_context_safe(expr, ctx)
def _dash_c_scripts_sanitized(idxs, resolved, elts, ctx, head) -> bool:
    allow_repr = _dash_c_allows_python_repr(head)
    for idx in idxs:
        _target = _dash_c_script_target(idx, resolved, elts)
        if _target is None or (
            isinstance(_target, ast.Constant)
            and getattr(_target, "value", None) == E2_BRANCH_BOUNDARY
        ):
            return False
        if not allow_repr and _contains_python_literalization(_target, ctx):
            return False
        if not _sanitized_script_expr(_target, ctx):
            return False
    return True
def _dash_c_script_target(idx: int, resolved: list, elts: list):
    if idx + 1 >= len(resolved):
        return None
    return elts[idx + 1] if idx + 1 < len(elts) else resolved[idx + 1]
@dataclass(frozen=True)
class _SubprocessJudgeCtx:
    tree: object
    fn: object
    line: int
    var_map: dict
    var_map_full: dict
    mod_assigns: dict
    mod_aliases: object
    param_names: list
    cls_assigns: dict
    cls_name: object
    cls_dynamic: set
    alias_map: dict
    taint_funcs: frozenset
def _trusted_interpreter_head(head, jctx) -> bool:
    if not _is_sys_executable_node(head):
        return True
    return _judge_import_identity("sys", jctx) == "sys"
def _judge_subprocess_call(jctx: _SubprocessJudgeCtx, call, params, assigns):
    _argv = _argv_resolve_or_none(call, jctx.var_map, jctx.var_map_full,
                                  jctx.fn)
    if _argv is None:
        return None
    first, elts, resolved, mutation_names = _argv
    _incremental = _incremental_append_elements(
        first, jctx.fn, (call.lineno, call.col_offset), mutation_names)
    if _incremental is None:
        return None
    resolved = resolved + _incremental
    if resolved and not _trusted_interpreter_head(resolved[0], jctx):
        return None
    if _is_inert_probe_argv(elts, resolved, params, assigns, jctx):
        return "filtered_inert_probe"
    if _argv_program_tainted(elts, params, assigns):
        return None
    idxs = _dash_c_flag_indexes(resolved)
    if not idxs:
        return None
    if not resolved or not all(
            _dash_c_interpreter_flag(resolved[0], resolved[idx])
            for idx in idxs):
        return None
    if any(not _dash_c_prefix_is_static(expr)
           for expr in resolved[1:idxs[0]]):
        return None
    ctx = _build_sanitize_ctx(jctx, call)
    if not _dash_c_scripts_sanitized(
            idxs, resolved, elts, ctx, resolved[0]):
        return None
    return "filtered_validated"
def _argv_program_tainted(elts, params, assigns) -> bool:
    return (
        (bool(elts) and expr_reaches_param(elts[0], params, assigns))
        or sentinel_branch_reaches_param(elts, params, assigns))
def _build_sanitize_ctx(jctx: _SubprocessJudgeCtx, call) -> SanitizeCtx:
    guards = _collect_guarded_names(jctx.fn, jctx.line, call,
                                    mod_assigns=jctx.mod_assigns,
                                    mod_aliases=jctx.mod_aliases,
                                    tree=jctx.tree)
    return SanitizeCtx(
        guards, jctx.var_map_full, jctx.param_names, jctx.tree, jctx.fn,
        jctx.mod_assigns,
        cls_assigns=jctx.cls_assigns, cls_name=jctx.cls_name,
        cls_dynamic=jctx.cls_dynamic, import_fims=jctx.alias_map,
        taint_funcs=jctx.taint_funcs)
def _judge_param_surface(tree, fn, line) -> list:
    return (function_param_names(fn)
            + nested_scope_bound_names(tree, line))
def _build_subprocess_judge_ctx(skill_dir, rel_file, line, cache):
    tree, _path = load_sink_tree(skill_dir, rel_file, cache)
    if tree is None:
        return None
    fn = enclosing_function(tree, line)
    if fn is None:
        return None
    var_map_full = _fn_vars_before_line(function_var_exprs(fn), line)
    _cls_assigns, _cls_name = enclosing_class_assigns(tree, fn)
    return (_SubprocessJudgeCtx(
        tree=tree, fn=fn, line=line,
        var_map={k: v[0] for k, v in var_map_full.items() if v},
        var_map_full=var_map_full,
        mod_assigns=module_assigns_outside(tree, fn, _path),
        mod_aliases=parse_module_aliases_cached(_path, tree),
        param_names=_judge_param_surface(tree, fn, line),
        cls_assigns=_cls_assigns, cls_name=_cls_name,
        cls_dynamic=enclosing_class_dynamic_attrs(tree, fn),
        alias_map=alias_resolve_map(tree),
        taint_funcs=frozenset(
            collect_d2_taint_source_cached(_path, tree))), _path)
def _merge_judge_kinds(kinds: list[str]) -> str | None:
    if not kinds:
        return None
    if len(set(kinds)) == 1:
        return kinds[0]
    _primary = ("filtered_validated"
                if "filtered_validated" in kinds else kinds[0])
    return "+".join([_primary] + sorted(set(kinds) - {_primary}))
def _classify_validated_subprocess(skill_dir, rel_file, line, cache=None):
    try:
        _ctxp = _build_subprocess_judge_ctx(skill_dir, rel_file, line, cache)
        if _ctxp is None:
            return None
        _jctx, _path = _ctxp
        _kinds = []
        for call, params, assigns in subprocess_sink_calls(
                _path, _jctx.tree, line):
            _k = _judge_subprocess_call(_jctx, call, params, assigns)
            if _k is None:
                return None
            _kinds.append(_k)
        return _merge_judge_kinds(_kinds)
    except Exception as e:  
        _log.debug("validated 判定异常，保守不判豁免交 CV 仲裁: %s", e,
                   exc_info=True)
        return None
@dataclass(frozen=True)
class _DegenerateVulnContext:
    vuln: object
    skill_dir: str
    file_name: str
    line_num: int
    sink: str
    vuln_id: str
    severity: str
    cache: object
def _single_step_downgrade_report(sink: str, cause: str):
    return None, (
        "P2",
        0.5,
        (f"同文件潜在污点(单步，无跨文件传播步骤): sink=[{sink}] "
         f"({cause};跨文件传播回溯为引擎已知能力边界)"),
    )
def _classify_highrisk_reaches(vctx: _DegenerateVulnContext, sink: str):
    if sink == "subprocess":
        if is_harness_subprocess_call(
                vctx.skill_dir, vctx.file_name, vctx.line_num, vctx.cache):
            return "filtered_harness", None
        _vk = _classify_validated_subprocess(
            vctx.skill_dir, vctx.file_name, vctx.line_num, vctx.cache)
        if _vk is not None:
            return _vk, None
    if has_nosec_marker(vctx.skill_dir, vctx.file_name,
                         vctx.line_num, sink, vctx.cache):
        return "filtered_audited", None
    return _single_step_downgrade_report(
        sink, "汇点参数可回溯到函数参数，最终来源是否外部输入未定，"
              "待CV仲裁")
def _classify_degenerate_trace(vctx: _DegenerateVulnContext):
    _det = getattr(vctx.vuln, 'details', None)
    _det = _det if isinstance(_det, dict) else {}
    _sink_det = _det.get('sink')
    if not isinstance(_sink_det, str) or not _sink_det:
        _sink_det = vctx.sink if isinstance(vctx.sink, str) else ""
    if _sink_det not in _DEGENERATE_HIGHRISK_SINKS:
        return "filtered_degenerate", None
    if _det.get('reaches_param') is True:
        return _classify_highrisk_reaches(vctx, _sink_det)
    if not _sink_first_arg_pure_literal(
            vctx.skill_dir, vctx.file_name, vctx.line_num,
            _sink_det, vctx.cache):
        return _classify_dynamic_argument(vctx, _sink_det)
    return "filtered_degenerate", None
def _classify_dynamic_argument(vctx: _DegenerateVulnContext, sink: str):
    if has_nosec_marker(vctx.skill_dir, vctx.file_name,
                         vctx.line_num, sink, vctx.cache):
        return "filtered_audited", None
    return _single_step_downgrade_report(
        sink, "汇点参数不可回溯到函数参数但含动态成分——"
              "全局变量/模块属性等来源，是否外部输入未定，"
              "待CV仲裁")
def _record_degenerate_filter(
    vctx: _DegenerateVulnContext, filtered_details: list,
    filter_counts: dict,
):
    _kind, _ov = _classify_degenerate_trace(vctx)
    if _kind is None:
        return False, _ov
    _kinds = _kind.split("+")
    _log.debug("[D2] 退化过滤 %s: %s:%s sink=%s", _kind, vctx.file_name,
               vctx.line_num, vctx.sink)
    filtered_details.append({
        "kind": "+".join(k.replace("filtered_", "") for k in _kinds),
        "file": vctx.file_name,
        "line": vctx.line_num,
        "sink": vctx.sink,
        "vuln_id": vctx.vuln_id,
        "severity_raw": vctx.severity,
    })
    for _kind_item in _kinds:
        filter_counts[_kind_item] = filter_counts.get(_kind_item, 0) + 1
    return True, None
def _e2_degenerate_outcome(
    vctx: _DegenerateVulnContext, state: _E2FilterState,
    confidence: float, message: str,
) -> tuple[str, float, str] | None:
    _ok, _ov = _record_degenerate_filter(
        vctx, state.details, state.counts)
    if _ok:
        return None
    _severity = normalize_severity(vctx.severity)
    if _severity == "P0":
        return _severity, confidence, message
    return _ov
def _build_e2_finding(
    vuln: Any, skill_dir: str, cache, state: _E2FilterState,
) -> dict | None:
    fields = normalize_e2_finding_fields(vuln)
    vuln_id, severity, constraints, steps, file_name, line_num, _sink = fields
    _sink_desc = _sink or 'taint_flow'
    _confidence = 0.8
    _msg = _e2_finding_message(steps, constraints, _sink_desc)
    if len(steps) < 2 and len(constraints) < 1:
        _outcome = _e2_degenerate_outcome(
            _DegenerateVulnContext(
                vuln=vuln, skill_dir=skill_dir, file_name=file_name,
                line_num=line_num, sink=_sink,
                vuln_id=vuln_id, severity=severity, cache=cache),
            state, _confidence, _msg)
        if _outcome is None:
            return None
        severity, _confidence, _msg = _outcome
    return {
        "rule_id": f"SYM-{vuln_id or 'taint_flow'}",
        "rule_family": "danger_pattern",
        "severity": severity,
        "confidence": _confidence,
        "message": _msg,
        "file": file_name,
        "line": line_num,
        "path_feasible": True,
        "runtime_env": _runtime_env_summary(vuln),
        "source": "E2",
    }
def _e2_filter_warnings(filter_counts: dict[str, int]) -> None:
    for spec, count in _e2_active_filters(filter_counts):
        _log.warning("[E2] 过滤 %d 个%s", count, spec.detail)
def _e2_summary(n: int, filter_counts: dict[str, int],
                files_failed: int | None,
                scan_errors: int | None = 0) -> str:
    _summary = f"跨文件符号执行: {n}个发现"
    for spec, count in _e2_active_filters(filter_counts):
        _summary += f"（{spec.summary_suffix.format(n=count)}）"
    _failed = _optional_count(files_failed)
    if _failed is None:
        _summary += "（解析失败文件计数未度量!）"
        _log.warning(
            "[E2] 解析失败文件计数未度量，无法证明扫描覆盖完整")
    elif _failed:
        _summary += f"（解析失败{_failed}文件,扫描覆盖不完整!）"
        _log.warning(
            "[E2] %d 个文件解析失败被跳过，扫描覆盖不完整，"
            "这些文件中的潜在污点未被检测", _failed)
    if scan_errors is None:
        _summary += "（扫描覆盖告警字段缺失、为None或形态非法，覆盖告警未度量!）"
        _log.warning(
            "[E2] 扫描覆盖告警字段缺失、为 None 或形态非法，无法证明扫描覆盖完整")
    elif scan_errors:
        _summary += f"（{scan_errors}项扫描覆盖告警,扫描未完全覆盖!）"
        _log.warning(
            "[E2] %d 项扫描覆盖告警（未度量/近似口径/目录不可读），"
            "本次跨文件符号结论不能当作“无风险”证据", scan_errors)
    return _summary
def _e2_payload(
    *, status: str, findings: list[dict], summary: str,
    state: _E2FilterState, scan: _E2ScanStats,
) -> dict:
    _details = state.details
    return {
        "status": status,
        "findings_count": len(findings),
        "summary": summary,
        "findings": findings,
        **_filter_payload(state.counts),
        "filtered_details": _details[:_TRACE_LIMIT],
        "filtered_details_truncated": len(_details) > _TRACE_LIMIT,
        "filtered_details_total": len(_details),
        "files_scanned": scan.files_scanned,
        "files_failed": scan.files_failed,
    }
def _e2_error_payload(exc: BaseException) -> dict:
    return _e2_payload(
        status="error", findings=[], summary=f"跨文件符号执行异常: {exc}",
        state=_E2FilterState(), scan=_E2ScanStats())
def _run_bridge_analysis(bridge: CrossFileSymbolicBridge, cache,
                         py_files: list | None):
    with memoized_module_walk_scope():
        if cache is not None:
            return bridge.analyze(
                max_paths=None, py_files=py_files, cache=cache)
        return bridge.analyze(max_paths=None, py_files=py_files)
def _e2_report_results(report) -> list:
    if report is None:
        raise ValueError("跨文件符号执行未返回报告")
    results = getattr(report, 'results', None)
    if results is None:
        raise ValueError("跨文件符号执行报告 results 缺失或为 None")
    if isinstance(results, (list, tuple)):
        return list(results)
    raise ValueError(
        f"跨文件符号执行报告 results 载体非法: {type(results).__name__}")
def _collect_e2_findings(report, skill_dir: str, cache,
                         state: _E2FilterState) -> list[dict]:
    findings = []
    for vuln in _e2_report_results(report):
        finding = _build_e2_finding(vuln, skill_dir, cache, state)
        if finding is not None:
            findings.append(finding)
    return findings
def _scan_error_count(report) -> int | None:
    errors = getattr(report, 'errors', None)
    if errors is None:
        return None
    if isinstance(errors, (list, tuple)):
        return len(errors)
    return 1 if errors else None
def _e2_success_payload(
    findings: list[dict], state: _E2FilterState, report,
) -> dict:
    n = len(findings)
    _files_scanned = _optional_count(getattr(report, 'files_scanned', None))
    _files_failed = _optional_count(getattr(report, 'files_failed', None))
    _scan_errors = _scan_error_count(report)
    _coverage_gap = (_files_failed is None or _files_failed > 0
                     or _scan_errors is None or _scan_errors > 0)
    _unmeasured_scan = _files_scanned is None or _files_scanned <= 0
    _summary = _e2_summary(n, state.counts, _files_failed, _scan_errors)
    if _unmeasured_scan:
        if _files_scanned == 0:
            _summary += "（0文件扫描：无扫描目标或扫描未度量!）"
            _log.warning(
                "[E2] 0 个文件被扫描，无法区分「无目标」与「未度量」")
        else:
            _summary += "（扫描文件计数缺失或非法，扫描未度量!）"
            _log.warning(
                "[E2] 扫描文件计数缺失或非法(%r)，结论按未度量上报",
                _files_scanned)
    return _e2_payload(
        status=("warn" if n > 0 or _coverage_gap or _unmeasured_scan
                else "pass"),
        findings=findings,
        summary=_summary,
        state=state,
        scan=_E2ScanStats(_files_scanned, _files_failed))
def run_e2_symbolic(skill_dir: str, cache=None) -> dict:
    require_warmed(cache, "E2 跨文件符号执行")
    try:
        bridge = CrossFileSymbolicBridge(skill_dir)
        state = _E2FilterState()
        report = _run_bridge_analysis(
            bridge, cache, getattr(cache, "py_files", None))
        findings = _collect_e2_findings(report, skill_dir, cache, state)
        _e2_filter_warnings(state.counts)
        return _e2_success_payload(findings, state, report)
    except CacheNotWarmedError:
        raise
    except Exception as e:  
        _log.warning("[E2] 跨文件符号执行异常: %s", e, exc_info=True)
        return _e2_error_payload(e)
_ERROR_STATUS = "error"
_FAIL_STATUS = "fail"
_PASS_STATUS = "pass"
class _AnalysisTally(NamedTuple):
    sub_reports: dict
    source_stats: Any
    severity_stats: Any
    total: int
    fp_removed: int
    fp_trace: list
    dedup_trace: list
    stale_removed: int
    channel_results: dict
    @classmethod
    def empty(cls) -> _AnalysisTally:
        return cls(
            sub_reports={}, source_stats={}, severity_stats={}, total=0,
            fp_removed=0, fp_trace=[], dedup_trace=[], stale_removed=0,
            channel_results={})
class SecurityAnalyzer:
    def __init__(self, skill_dir: str, cache=None,
                 include_tests: bool = DEFAULT_INCLUDE_TESTS):
        self.skill_dir = os.path.abspath(skill_dir)
        self._cache = cache
        self._include_tests = include_tests
    def analyze(self, skip_vuln: bool = False) -> dict:
        all_findings: list[dict] = []
        sub_reports: dict[str, dict] = {}
        _channel_results = self._run_channels_parallel(skip_vuln)
        _named_results = [(c.key, _channel_results[c.key]) for c in _CHANNELS
                          if _channel_results.get(c.key) is not None]
        _merge_channel_reports(sub_reports, all_findings, _named_results)
        total = len(all_findings)
        source_stats, severity_stats = _count_by_field(all_findings)
        post = postprocess_findings(self.skill_dir, all_findings)
        deduped = post.findings
        _final_status = _d1_final_status(sub_reports, deduped)
        tally = _AnalysisTally(
            sub_reports=sub_reports, source_stats=source_stats,
            severity_stats=severity_stats, total=total,
            fp_removed=post.fp_removed, fp_trace=post.fp_trace,
            dedup_trace=post.dedup_trace, stale_removed=post.stale_removed,
            channel_results=_channel_results)
        return {
            "status": _final_status,
            "findings_count": len(deduped),
            "summary": _compose_d1_summary(tally, deduped),
            "findings": deduped,
            "payload": _audit_payload(tally, available_default=True),
        }
    def _run_channels_parallel(self, skip_vuln: bool) -> dict:
        active = [c for c in _CHANNELS if not (c.skippable and skip_vuln)]
        shared_py_files, workers = security_scan_plan(
            self.skill_dir, self._include_tests, len(active))
        with (
            e1_snapshot_session(self._cache),
            memoized_module_walk_scope(),
            ThreadPoolExecutor(max_workers=workers) as executor,
        ):
            futures = {
                c.key: executor.submit(
                    self._run_channel_isolated, c, shared_py_files)
                for c in active
            }
            return {k: f.result() for k, f in futures.items()}
    def _run_channel_isolated(self, channel, py_files) -> dict:
        try:
            kwargs = {"include_tests": self._include_tests}
            if channel.use_cache:
                kwargs["cache"] = self._cache
            runner = channel.runner(self.skill_dir, **kwargs)
            if channel.ast_bridge:
                with shared_ast_bridge(self._cache):
                    result = runner.run(py_files=py_files)
            else:
                result = runner.run(py_files=py_files)
        except CacheNotWarmedError:
            raise
        except Exception as e:  
            _log.warning(
                "[security_analyzer] %s 通道异常: %s",
                channel.key, e, exc_info=True)
            return _channel_error(
                f"{channel.key} 通道异常: {type(e).__name__}: {e}")
        if not isinstance(result, dict):
            _log.warning(
                "[security_analyzer] %s 通道返回非 dict 结果(%s)，归入 error 通道",
                channel.key, type(result).__name__)
            return _channel_error(
                f"{channel.key} 通道返回非 dict 结果: {type(result).__name__}")
        return result
class _ChannelSpec(NamedTuple):
    key: str
    source: str
    label: str
    runner: Any
    use_cache: bool = False
    ast_bridge: bool = False
    skippable: bool = False
def _channel_error(summary: str) -> dict:
    return {"findings": [], "findings_count": 0, "status": "error",
            "summary": summary, "elapsed_ms": 0.0}
_CHANNELS = (
    _ChannelSpec("ruff", "E1-ruff", "Ruff", RuffRunner),
    _ChannelSpec("bandit", "E1-bandit", "Bandit", BanditRunner),
    _ChannelSpec("static", "E1-static", "静态", StaticAnalyzer,
                 use_cache=True),
    _ChannelSpec("vulnerability", "E1-vuln", "漏洞", VulnerabilityScanner,
                 use_cache=True, ast_bridge=True, skippable=True),
)
_AST_FAILURE_COUNT_CHANNELS = frozenset({"static", "vulnerability"})
def _report_detect_failed(sub_report: dict, channel: str = "") -> int | None:
    if "detect_failed" not in sub_report:
        return None if channel in _AST_FAILURE_COUNT_CHANNELS else 0
    return _optional_count(sub_report.get("detect_failed"))
def _detect_failed_stats(sub_reports: dict) -> tuple[int, bool]:
    counts = [_report_detect_failed(_sr, _key)
              for _key, _sr in sub_reports.items()]
    return (sum(count for count in counts if count is not None),
            any(count is None for count in counts))
def _scan_file_stats(sub_reports: dict) -> tuple[bool, bool]:
    counts = [_optional_count(_sr.get("files_scanned"))
              for _sr in sub_reports.values()]
    return (any(count is not None and count > 0 for count in counts),
            any(count is None for count in counts))
def _d1_final_status(sub_reports: dict, deduped: list) -> str:
    if not sub_reports:
        _log.warning("[security_analyzer] 零通道产出，扫描未执行，按 error 上报")
        return _ERROR_STATUS
    statuses = {str(_sr.get("status", ""))
                for _sr in sub_reports.values()}
    if _ERROR_STATUS in statuses:
        return _ERROR_STATUS
    if _FAIL_STATUS in statuses:
        return _FAIL_STATUS
    _failed_total, _failed_unmeasured = _detect_failed_stats(sub_reports)
    _has_scanned, _scanned_unmeasured = _scan_file_stats(sub_reports)
    if _failed_unmeasured or _scanned_unmeasured:
        _log.warning("[security_analyzer] 扫描覆盖计数缺失或非法，结论按未度量上报")
    if (statuses - {_PASS_STATUS} or _failed_total or _failed_unmeasured
            or _scanned_unmeasured or deduped):
        return "warn"
    if not _has_scanned:
        _log.warning("[security_analyzer] 没有有效正数 files_scanned，结论按未度量上报")
        return "warn"
    return _PASS_STATUS
def _count_by_field(findings: list) -> tuple[dict[str, int], dict[str, int]]:
    _valid = _finding_items(findings, "统计")
    source = Counter((f.get("source") or "unknown") for f in _valid)
    severity = Counter((f.get("severity") or "unknown") for f in _valid)
    return dict(source), dict(severity)
def _equiv_merged_count(dedup_trace: list) -> int:
    return sum(1 for t in dedup_trace
               if t.get("reason") == "equiv_rule_merged")
def _error_channels(sub_reports: dict) -> list:
    return sorted(k for k, v in sub_reports.items()
                  if v.get("status") == "error")
def _compose_d1_summary(tally: _AnalysisTally, deduped: list) -> str:
    _equiv_merged = _equiv_merged_count(tally.dedup_trace)
    _stale = f", 陈旧剔除{tally.stale_removed}" if tally.stale_removed else ""
    _counts = " ".join(f"{c.label}={tally.source_stats.get(c.source, 0)}"
                       for c in _CHANNELS)
    _summary = (f"安全分析: {len(deduped)} findings ({tally.total}原始: "
                f"FP规则过滤{tally.fp_removed}, 等价合并{_equiv_merged}"
                f"{_stale}) | {_counts}")
    _err_channels = _error_channels(tally.sub_reports)
    if _err_channels:
        _summary += f" | 通道失败: {','.join(_err_channels)}（扫描覆盖不完整!）"
    return _append_coverage_summary(_summary, tally.sub_reports)
def _merge_channel_reports(sub_reports: dict, all_findings: list,
                           named_results: list) -> None:
    for _key, _res in named_results:
        failures: list[str] = []
        items = _finding_items(
            _res.get("findings"), _key, failures=failures)
        if failures:
            _res = dict(_res)
            _res.update({
                "status": _ERROR_STATUS,
                "findings": items,
                "findings_count": len(items),
                "summary": (
                    f"{_res.get('summary', '')} | findings载荷非法: "
                    f"{'; '.join(failures)}"),
            })
        sub_reports[_key] = _res
        all_findings.extend(items)
def _channel_available(channel_results: dict, key: str,
                      default: bool) -> bool:
    _res = channel_results.get(key)
    if _res is None:
        return default
    return _res.get("status") != "error"
def _audit_payload(tally: _AnalysisTally, available_default: bool) -> dict:
    return {
        "source_stats": dict(tally.source_stats),
        "fp_filtered_trace": tally.fp_trace[:_TRACE_LIMIT],
        "fp_filtered_trace_truncated": len(tally.fp_trace) > _TRACE_LIMIT,
        "fp_filtered_trace_total": len(tally.fp_trace),
        "dedup_trace": tally.dedup_trace[:_TRACE_LIMIT],
        "dedup_trace_truncated": len(tally.dedup_trace) > _TRACE_LIMIT,
        "dedup_trace_total": len(tally.dedup_trace),
        "severity_stats": dict(tally.severity_stats),
        "sub_reports": {
            k: {"status": v.get("status"),
                "findings_count": v.get("findings_count", 0),
                "elapsed_ms": v.get("elapsed_ms", 0),
                "detect_failed": _report_detect_failed(v, k)}
            for k, v in tally.sub_reports.items()
        },
        "ruff_available": _channel_available(
            tally.channel_results, "ruff", available_default),
        "bandit_available": _channel_available(
            tally.channel_results, "bandit", available_default),
    }
def _append_coverage_summary(summary: str, sub_reports: dict) -> str:
    _failed_total, _failed_unmeasured = _detect_failed_stats(sub_reports)
    _has_scanned, _scanned_unmeasured = _scan_file_stats(sub_reports)
    if _failed_total:
        summary += f" | 检测失败{_failed_total}文件（扫描覆盖不完整!）"
    if _failed_unmeasured:
        summary += " | 检测失败文件计数缺失或非法（扫描覆盖未度量!）"
    if _scanned_unmeasured:
        summary += " | files_scanned计数缺失或非法（扫描未度量!）"
    elif not _has_scanned:
        summary += " | 0文件扫描（扫描未度量!）"
    return summary
def _analysis_error_result(summary: str) -> dict:
    return {
        "status": "error",
        "findings_count": 0,
        "summary": summary,
        "findings": [],
        "payload": _audit_payload(
            _AnalysisTally.empty(), available_default=False),
    }
def run_security_analysis(
    skill_dir: str, cache: Any = None, *,
    skip_vuln: bool = False,
    include_tests: bool = DEFAULT_INCLUDE_TESTS,
) -> dict:
    try:
        cache = ensure_entry_warmed(
            skill_dir, cache, who="run_security_analysis")
        analyzer = SecurityAnalyzer(skill_dir, cache=cache,
                                    include_tests=include_tests)
        return analyzer.analyze(skip_vuln=skip_vuln)
    except CacheNotWarmedError:
        raise
    except (ImportError, AttributeError) as e:
        _log.warning("[security_analyzer] ImportError/AttributeError: %s", e, exc_info=True)
        return _analysis_error_result(f"安全分析错误: {e}")
    except Exception as e:  
        _log.warning("[security_analyzer] Exception: %s", e, exc_info=True)
        return _analysis_error_result(f"安全分析异常: {e}")
def run_engine_D(skill_dir: str, cache=None) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, "主引擎 D 组")
    t0 = time.perf_counter()
    det_results: list = []
    with fingerprint_freeze_window(cache, "D组"):
        det_results.append(detector_entry(
            "D1", run_security_analysis, skill_dir, cache,
            logger=_log, engine_tag="engine_d"))
        det_results.append(detector_entry(
            "D2", run_e2_symbolic, skill_dir, cache,
            logger=_log, engine_tag="engine_d"))
    merged, conflicts, stats = consolidate_findings(det_results, source_method="D", merged_from="engine_d")
    worst = worst_sub_status(det_results, merged)
    return group_envelope(
        "D", ("D1", "D2"), worst, merged, stats, det_results, t0,
        summary=(
            f"主引擎D: 检测器{len(det_results)}个, 原始发现{stats['raw_findings']}, "
            f"预合并后{stats['merged_findings']}, 冲突{stats['conflicts']}"
        ),
        conflicts=conflicts)
def release_d_group_caches() -> dict:
    return {
        "e1_bandit_fp_caches": release_bandit_fp_caches(),
        "e1_ruff_fp_caches": release_ruff_fp_caches(),
        "e2_scope_memos": clear_e2_scope_memos(),
    }
register_cache_release(
    "d_group_caches", release_d_group_caches, "D 组子引擎缓存", order=80)

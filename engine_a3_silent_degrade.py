from __future__ import annotations

__all__ = ["run_a3_silent_degrade"]
import ast
import bisect
import io
import logging
import os
import re
import tokenize
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor
from typing import Any, NamedTuple

from jwsgj.diag_gate_expr import _is_unshadowed_builtin
from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    collect_param_names,
    dotted_name,
    expr_target_name,
    import_alias_bound_names,
    is_broad_except,
    is_none_literal,
    iter_def_site_nodes,
    iter_pattern_capture_names,
    iter_scope_nodes,
    iter_unpack_target_names,
    str_constant_value,
)
from jwsgj.diag_shared_ast_views import parent_map
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    adaptive_workers,
    read_diagnostic_source_strict,
)
from jwsgj.shared_cache import gate_scan_files_cached, require_warmed

logger = logging.getLogger(__name__)
def _coerce_skill_dir(value) -> str:
    if value is None or isinstance(value, bool):
        return ""
    if not isinstance(value, (str, bytes, os.PathLike)):
        return ""
    try:
        raw = os.fsdecode(os.fspath(value)).strip()
    except (TypeError, ValueError, OSError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_coerce_skill_dir:{type(_e).__name__}')
        return ""
    return os.path.abspath(raw) if raw else ""
def _same_root(left: str, right: str) -> bool:
    return (os.path.normcase(os.path.normpath(left))
            == os.path.normcase(os.path.normpath(right)))
def _resolve_scan_base(skill_dir: str, cache: Any) -> str:
    cache_root = _coerce_skill_dir(getattr(cache, "skill_dir", ""))
    if not cache_root:
        return skill_dir
    if skill_dir and not _same_root(skill_dir, cache_root):
        logger.warning("[A3] 技能目录与缓存根不一致，以缓存根为相对路径基准: "
                       "%s != %s", skill_dir, cache_root)
    return cache_root
class _ReportCtx(NamedTuple):
    findings: list
    relpath: str
    lineno: int
    lines: list
class _FileCtx(NamedTuple):
    findings: list
    relpath: str
    lines: list
    doc_ivs: list
    comment_map: dict | None
class _JudgeCtx(NamedTuple):
    rep: _ReportCtx
    handler: ast.ExceptHandler
    try_node: ast.AST
    func_node: ast.AST
    hnodes: tuple
    perceivable: bool
    doc_ivs: list
    comment_map: dict | None
    empty_binds: dict | None = None
    pass_binds: dict | None = None
    status_binds: dict | None = None
    truth_binds: dict | None = None
class _Perception(NamedTuple):
    has_warn: bool
    has_debug: bool
    has_any_log: bool
    perceivable: bool
    has_explicit_return: bool
    exc_forwarded: bool
    normal_observations: tuple = ()
    return_observations: tuple = ()
def _exc_forward_payload(node, exc_name) -> bool:
    if references_exception(node, exc_name):
        return True
    return any(
        isinstance(sub, ast.Call)
        and expr_target_name(sub.func).endswith("exc_info")
        for sub in walk_nodes(node)
    )
def _sd_exc_forwarded(hnodes, exc_name) -> bool:
    for n in hnodes:
        if not isinstance(n, ast.Call):
            continue
        _name = expr_target_name(n.func)
        if not _name.endswith(("set_exception", "handleError", "handle_error")):
            continue
        if _exc_forward_payload(n, exc_name):
            return True
    return False
def _dict_error_payload_perceivable(node: ast.Dict, exc_name) -> bool:
    for key_node, value in zip(node.keys, node.values, strict=True):
        key = str_constant_value(key_node)
        if (key is not None and _has_error_semantic_key((key,))
                and _payload_carries_error(value, exc_name)):
            return True
    return False
def _sd_return_entry_failure(handler, entry) -> bool:
    value = entry.node.value
    if value is None:
        return False
    if references_exception(value, handler.name):
        return True
    if not isinstance(value, ast.Dict):
        return False
    if (_dict_error_payload_perceivable(value, handler.name)
            or dict_flag_state(value) is False):
        return True
    return _is_failure_status_value(dict_status(value))
def _report_broad_except_silent(rctx, handler, is_broad, p):
    outcomes = (*p.normal_observations, *p.return_observations)
    if outcomes:
        silent = any(
            not (o.has_any_log or o.perceivable or o.exc_forwarded)
            for o in p.normal_observations)
        debug_only = any(
            o.has_debug
            and not (o.has_warn or o.perceivable or o.exc_forwarded)
            for o in outcomes)
    else:
        silent = not any((p.has_any_log, p.has_explicit_return, p.exc_forwarded))
        debug_only = (p.has_debug
                      and not any((p.has_warn, p.exc_forwarded)))
    if is_broad and silent:
        _append_finding(rctx, "SD-04",
                        "宽泛 except 存在无日志/错误结果的正常落空路径，异常被静默消化")
        return True
    if is_broad and debug_only:
        _append_finding(rctx, "SD-03",
                        "异常处理存在仅 logger.debug 的路径，用户不可感知诊断未执行")
        return True
    return False
def _scan_except(fctx, handler, try_node, func_node):
    is_broad = is_broad_except(handler)
    hnodes = tuple(iter_scope_nodes(handler))
    lexical = scan_except_perception(handler, hnodes)
    normal_exits, return_paths = _handler_binding_flow(handler)
    normal_observations = tuple(
        observation
        for state in normal_exits for observation in state.observations)
    return_observations = tuple(
        observation._replace(perceivable=True)
        if _sd_return_entry_failure(handler, entry) else observation
        for entry in return_paths for observation in entry.bindings.observations)
    outcomes = (*normal_observations, *return_observations)
    if outcomes:
        has_warn = bool(return_paths) and all(
            o.has_warn or o.perceivable or o.exc_forwarded
            for o in return_observations)
        perceivable = all(o.perceivable for o in outcomes)
    else:
        has_warn = lexical[0]
        perceivable = lexical[3] or _sd_counter_bookkeeping(hnodes)
    p = _Perception(has_warn, lexical[1], lexical[2], perceivable,
                    bool(return_paths) and not normal_exits,
                    _sd_exc_forwarded(hnodes,
                                      getattr(handler, "name", None)),
                    normal_observations, return_observations)
    rctx = _ReportCtx(fctx.findings, fctx.relpath, handler.lineno, fctx.lines)
    jctx = _JudgeCtx(rep=rctx, handler=handler, try_node=try_node,
                     func_node=func_node, hnodes=hnodes, perceivable=p.perceivable,
                     doc_ivs=fctx.doc_ivs, comment_map=fctx.comment_map)
    if _sd_is_exempt(jctx):
        return
    if _report_broad_except_silent(rctx, handler, is_broad, p):
        return
    if p.has_warn:
        return
    _sd_report_return_degradations(jctx)
def _relpath_or_raw(path, skill_dir) -> str:
    try:
        return os.path.relpath(path, skill_dir)
    except (TypeError, ValueError) as exc:
        log_swallowed(__name__, exc,
                      context=f"_relpath_or_raw:{type(exc).__name__}")
        return str(path)
def _walk_error_findings(skill_dir, errors) -> list:
    out = []
    seen = set()
    for walk_exc in errors:
        path = getattr(walk_exc, "filename", None) or skill_dir
        relpath = _relpath_or_raw(path, skill_dir)
        if relpath in seen:
            continue
        seen.add(relpath)
        out.append(_finding_payload(
            relpath, 1, "SD-05",
            f"目录遍历失败被静默跳过: {type(walk_exc).__name__}: {walk_exc}"))
    return out
def _push_fields(n, todo):
    d = n.__dict__
    for field_name in n._fields:
        v = d.get(field_name)
        if v is None:
            continue
        if isinstance(v, list):
            for item in v:
                if isinstance(item, ast.AST):
                    todo.append(item)
        elif isinstance(v, ast.AST):
            todo.append(v)
def _single_pass_collect(tree):
    doc_ivs, func_nodes, try_nodes = [], [], []
    todo = deque([tree])
    while todo:
        n = todo.popleft()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_nodes.append(n)
            _collect_func_doc_interval(n, doc_ivs)
            _push_fields(n, todo)
            continue
        if isinstance(n, (ast.Try, TRY_STAR)) and n.handlers:
            try_nodes.append(n)
            _push_fields(n, todo)
            continue
        if isinstance(n, ast.expr):
            continue
        _push_fields(n, todo)
    return doc_ivs, func_nodes, try_nodes
def _collect_func_doc_interval(node, doc_ivs: list) -> None:
    first = node.body[0] if node.body else None
    if (isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant)
            and isinstance(first.value.value, str) and first.value.value):
        doc_ivs.append((node.lineno, getattr(node, "end_lineno", node.lineno),
                        first.value.value))
def _sd05_strict_read(rctx, path, fail_msg):
    try:
        return read_diagnostic_source_strict(path)
    except (OSError, UnicodeDecodeError) as e:
        log_swallowed(__name__, e,
                      context=f'_sd05_strict_read:{type(e).__name__}')
        _append_finding(rctx, "SD-05", f"{fail_msg}: {type(e).__name__}")
        return None
def _acquire_src_tree(rctx, path, cache):
    src = None
    tree = None
    if cache is not None:
        try:
            src, tree = cache.get_source_and_ast(path)
        except Exception as e:  # noqa: BLE001 — 缓存回退直读
            logger.debug("[A3] SharedCache 消费失败回退直读: %s (%s)",
                         os.path.basename(path), type(e).__name__)
            src = None
            tree = None
    if src is None:
        src = _sd05_strict_read(rctx, path, "文件读取失败被静默跳过")
        tree = None
    if cache is not None and src is not None and "\ufffd" in src:
        src = _sd05_strict_read(rctx, path, "文件含非法字节被宽松解码掩盖")
        tree = None
    return src, tree
def _parse_or_sd05(rctx, src):
    try:
        return ast.parse(src)
    except (SyntaxError, ValueError, RecursionError,
            MemoryError) as e:
        log_swallowed(__name__, e,
                      context=f'_parse_or_sd05:{type(e).__name__}')
        _append_finding(
            rctx._replace(lineno=getattr(e, "lineno", None) or 1),
            "SD-05", f"文件存在语法错误被静默跳过: {getattr(e, 'msg', None) or e}")
        return None
def _innermost_func(sorted_funcs, func_starts, h):
    i = bisect.bisect_right(func_starts, h.lineno)
    while i > 0:
        fn = sorted_funcs[i - 1]
        fe = getattr(fn, "end_lineno", fn.lineno)
        if fn.lineno <= h.lineno <= fe:
            return fn
        i -= 1
    return None
def _scan_one(path, skill_dir, cache):
    local = []
    relpath = _relpath_or_raw(path, skill_dir)
    rctx = _ReportCtx(local, relpath, 1, [])
    src, tree = _acquire_src_tree(rctx, path, cache)
    if src is None:
        return local
    if tree is None:
        tree = _parse_or_sd05(rctx, src)
        if tree is None:
            return local
    _mark_shadowed_empty_ctors(tree)
    doc_ivs, func_nodes, try_nodes = _single_pass_collect(tree)
    lines = src.split("\n")
    comment_map = build_comment_map(src) if try_nodes else None
    fctx = _FileCtx(local, relpath, lines, doc_ivs, comment_map)
    sorted_funcs = sorted(func_nodes, key=lambda fn: fn.lineno)
    func_starts = [fn.lineno for fn in sorted_funcs]
    for node in try_nodes:
        for h in node.handlers:
            _scan_except(fctx, h, node,
                         _innermost_func(sorted_funcs, func_starts, h))
    return local
def _scan_one_guarded(path, skill_dir, cache):
    try:
        return _scan_one(path, skill_dir, cache)
    except Exception as e:
        logger.warning("[A3] 单文件扫描意外失败: %s (%s)",
                       os.path.basename(path), type(e).__name__, exc_info=True)
        local = []
        relpath = _relpath_or_raw(path, skill_dir)
        try:
            _append_finding(_ReportCtx(local, relpath, 1, []), "SD-05",
                            f"文件扫描意外失败: {type(e).__name__}")
        except Exception as _e:  # noqa: BLE001 — 上报通道异常时手工兜底
            log_swallowed(__name__, _e, context='_scan_one_guarded:Exc')
            local.append(_finding_payload(
                relpath, 1, "SD-05",
                f"文件扫描意外失败: {type(e).__name__}"))
        return local
def _scan_directory(skill_dir, cache, file_list, errors):
    walk_errors = errors
    if len(file_list) <= 1:
        per_file = [_scan_one_guarded(p, skill_dir, cache) for p in file_list]
    else:
        with ThreadPoolExecutor(max_workers=adaptive_workers(len(file_list))) as executor:
            per_file = list(executor.map(
                lambda p: _scan_one_guarded(p, skill_dir, cache), file_list))
    findings = []
    for r in per_file:
        findings.extend(r)
    findings.extend(_walk_error_findings(skill_dir, walk_errors))
    return findings
def _a3_error_envelope(summary):
    return {
        "status": "error",
        "findings_count": 0,
        "files_scanned": 0,
        "summary": summary,
        "findings": [],
    }
def _a3_result(findings, files_scanned):
    n = len(findings)
    by_rule = Counter(f["rule_id"] for f in findings)
    summary_parts = [f"静默降级检测: {n}个候选(扫描{files_scanned}个文件)"]
    summary_parts.extend(f"{rid}={by_rule[rid]}" for rid in sorted(by_rule))
    return {
        "status": "warn" if n > 0 else "pass",
        "findings_count": n,
        "files_scanned": files_scanned,
        "summary": ", ".join(summary_parts),
        "findings": findings,
    }
def _ai_execution_chain(skill_dir):
    return {
        "next_action": "review_and_fix_silent_degrades",
        "instruction": (
            "逐项审核 findings：先核对豁免链（warn+ 日志可感知/错误入"
            "结果集/None 哨兵契约），确认真实静默降级后修复对应 except "
            "分支（补日志/传播异常/结构化错误返回），随后先 "
            f"get_warmed_cache({skill_dir!r}) 预热，再调用本引擎的"
            f" run_a3_silent_degrade({skill_dir!r}, "
            f"cache=get_warmed_cache({skill_dir!r})) 复扫，"
            "直至 findings_count 归零"
        ),
    }
def run_a3_silent_degrade(skill_dir: str, cache: Any=None) -> dict:
    require_warmed(cache, "A3 静默降级检测")
    base_dir = _resolve_scan_base(_coerce_skill_dir(skill_dir), cache)
    if not base_dir:
        return _a3_error_envelope(
            "静默降级检测错误: 技能目录为空且缓存未提供根目录，拒绝在无根"
            "状态下扫描（findings 的相对路径会漂移到进程 cwd）")
    try:
        walk_errors: list = []
        file_list = gate_scan_files_cached(cache, base_dir, walk_errors)
        files_scanned = len(file_list)
        if files_scanned == 0:
            if walk_errors:
                return _a3_error_envelope(
                    "静默降级检测错误: 扫描范围塌缩且目录遍历失败，"
                    f"{len(walk_errors)} 个目录不可读"
                    f"（首个: {type(walk_errors[0]).__name__}）")
            return _a3_error_envelope(
                "静默降级检测错误: 扫描范围塌缩，0 个 Python 文件"
                "（检查 skill_dir 与排除目录）")
        findings = _scan_directory(base_dir, cache, file_list, walk_errors)
        result = _a3_result(findings, files_scanned)
        result["ai_execution"] = _ai_execution_chain(base_dir)
        return result
    except Exception as e:
        logger.warning("[A3] 静默降级检测异常: %s", e, exc_info=True)
        return _a3_error_envelope(f"静默降级检测错误: {e}")
_RULES = {
    "SD-01": ("P2", "静默降级-吞异常返回空值"),
    "SD-02": ("P2", "静默降级-except返回伪装pass兜底"),
    "SD-03": ("P2", "静默降级-异常处理仅logger.debug"),
    "SD-04": ("P2", "静默降级-宽泛except无日志"),
    "SD-05": ("P2", "静默降级-文件解析失败被静默跳过"),
}
_COUNTER_KEYS = frozenset({"failed", "skipped", "error", "error_count",
                           "errors"})
def _sd_counter_bookkeeping(nodes) -> bool:
    for sub in nodes:
        if not isinstance(sub, ast.AugAssign):
            continue
        t = sub.target
        if (isinstance(t, (ast.Name, ast.Attribute))
                and expr_target_name(t) in _COUNTER_KEYS):
            return True
        if (isinstance(t, ast.Subscript)
                and any(k in _COUNTER_KEYS for k in subscript_chain_keys(t))):
            return True
    return False
def _sd_docstring_intent_exempt(handler, doc_intervals) -> bool:
    innermost_doc = None
    innermost_start = -1
    for start, end, doc in doc_intervals:
        if start <= handler.lineno <= end and start > innermost_start:
            innermost_start, innermost_doc = start, doc
    return bool(innermost_doc
                and intent_declared(innermost_doc, doc_scope=True))
def _sd_recovery_reset_exempt(handler, try_node, nodes, func_node) -> bool:
    if try_node is None:
        return False
    handler_returns = bool(_handler_binding_flow(handler)[1])
    if handler_returns:
        return False
    h_names = collect_assigned(handler.body, set())
    if not h_names:
        return False
    t_names = getattr(try_node, "_sd_assigned_names", None)
    if t_names is None:
        t_names = collect_assigned(try_node.body, set())
        try_node._sd_assigned_names = t_names
    if not h_names <= t_names:
        return False
    binds = handler_empty_binds(handler)
    empty_names = {n for n, t in binds.items() if t is not None}
    return not (empty_names
                and tail_returns_empty_name(func_node, handler, empty_names))
def _is_none_attr_assign(stmt: ast.stmt, attr: str) -> bool:
    return (isinstance(stmt, ast.Assign)
            and is_none_literal(stmt.value)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Attribute)
            and stmt.targets[0].attr == attr)
def _sd_stream_reset_only(handler, nodes) -> bool:
    if not handler.body:
        return False
    if not all(_is_none_attr_assign(s, "stream") for s in handler.body):
        return False
    return not any(isinstance(s, (ast.Return, ast.Raise)) for s in nodes)
def _sd_is_exempt(jctx) -> bool:
    return (_sd_observable_exempt(jctx) or _sd_design_exempt(jctx)
            or not _sd_findings_producer(jctx.func_node))
# 只有产出 finding 集合的诊断函数，“吞异常”才等价于“把诊断结果伪装成
# 无发现”。值转换/路径归一/配置解析等辅助函数的 except 兜底是正常的防御式
# 默认值（`_text()` 返回 ""、`_coerce_float()` 返回 0.0），把它们判成静默
# 降级会让 SD-01～SD-04 在整库范围内退化为噪声（实测 243/269 命中落在
# 非诊断辅助函数上）。此处按“函数名诊断动词 + finding 返回注解”双重判据
# 收敛，诊断函数上的真实静默降级保持检出。
# 动词必须是**首段**：``scan_findings`` / ``check_rules`` 是诊断生产者，
# 而 ``_coerce_scan_path`` / ``_scan_target_paths`` 里的 scan 只是中间词，
# 其返回值是归一化后的路径列表，不是 finding 集合。
_DIAGNOSTIC_VERB_RE = re.compile(
    r'^_?(?:scan|detect|diag|audit|analyze|analyse|check|verify|inspect'
    r'|probe|measure|assess|evaluate|collect|find|judge|review|validate'
    r')(?:_|$)', re.IGNORECASE)
def _sd_findings_producer(func_node) -> bool:
    if func_node is None:
        return True
    name = getattr(func_node, 'name', '') or ''
    if isinstance(name, str) and _DIAGNOSTIC_VERB_RE.search(name):
        return True
    annotation = getattr(func_node, 'returns', None)
    if annotation is None:
        return False
    try:
        text = ast.unparse(annotation).lower()
    except (AttributeError, ValueError, TypeError):
        return False
    return 'finding' in text
def _sd_observable_exempt(jctx) -> bool:
    terminates_path = (handler_scope_raise(jctx.hnodes)
                       or handler_scope_exit(jctx.hnodes))
    normal_exits, return_paths = _handler_binding_flow(jctx.handler)
    if terminates_path and not return_paths and not normal_exits:
        return True
    if (jctx.perceivable
            or intent_declared(handler_comments(
                jctx.handler, jctx.rep.lines, jctx.comment_map))):
        return True
    fmts = log_format_strings(jctx.hnodes)
    if any(intent_declared(text) for text in fmts):
        return True
    fmt_text = " ".join(fmts).lower()
    return any(sink in fmt_text for sink in TELEMETRY_SINKS)
def _sd_design_exempt(jctx) -> bool:
    return (is_pure_telemetry_body(jctx.try_node)
            or _sd_docstring_intent_exempt(jctx.handler, jctx.doc_ivs)
            or _sd_recovery_reset_exempt(
                jctx.handler, jctx.try_node, jctx.hnodes, jctx.func_node)
            or _sd_stream_reset_only(jctx.handler, jctx.hnodes))
def _sd_none_sentinel_exempt(handler, func_node) -> bool:
    if func_node is None:
        return False
    stack = list(reversed(list(ast.iter_child_nodes(func_node))))
    while stack:
        child = stack.pop()
        if isinstance(child, ast.ExceptHandler):
            continue
        if (isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                and not (child.lineno <= handler.lineno
                         <= getattr(child, "end_lineno", child.lineno))):
            continue
        if (isinstance(child, ast.Return)
                and (child.value is None or is_none_literal(child.value))):
            return True
        stack.extend(reversed(list(ast.iter_child_nodes(child))))
    return False
def _sd_check_bare_return(jctx):
    if _sd_none_sentinel_exempt(jctx.handler, jctx.func_node):
        return
    _append_finding(jctx.rep, "SD-01",
                    "except 捕获后 bare return（等价 None），非哨兵函数下伪装成'无发现'")
def _is_true_const(node) -> bool:
    return isinstance(node, ast.Constant) and node.value is True
def _is_pass_string_const(node) -> bool:
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, str) and bool(node.value.strip())
            and not is_fail_status_value(node.value))
def _report_degraded_value(jctx, tag: str, form: str) -> None:
    if tag == "none" and _sd_none_sentinel_exempt(jctx.handler, jctx.func_node):
        return
    if tag == "dict":
        _append_finding(jctx.rep, "SD-02",
                        f"except 捕获后{form}空 dict，异常被伪装成通过")
        return
    _append_finding(jctx.rep, "SD-01",
                    f"except 捕获后{form}空值，诊断结果伪装成'无发现'")
def _sd_check_const_return(jctx, val):
    tag = is_empty_value_node(val)
    if tag is not None:
        _report_degraded_value(jctx, tag, "返回")
        return
    if _is_true_const(val):
        _append_finding(jctx.rep, "SD-02",
                        "except 捕获后返回 True 字面量，异常被伪装成通过/可用")
        return
    if _is_pass_string_const(val):
        _append_finding(jctx.rep, "SD-02",
                        "except 捕获后返回字符串常量回退值，异常被伪装成正常结果")
        return
def _sd_check_dict_return(jctx, val):
    keys = dict_str_keys(val)
    st = dict_status(val)
    if (_dict_error_payload_perceivable(val, jctx.handler.name)
            or dict_flag_state(val) is False):
        return
    st_passlike = (_is_pass_status_value(st)
                   or _dynamic_status_passes(val, jctx.status_binds or {}))
    if "status" not in keys or st_passlike:
        _append_finding(jctx.rep, "SD-02",
                        "except 返回 status=pass/通过语义值/无 status 兜底 dict，异常被伪装成通过")
def _sd_check_empty_coll_return(jctx, _val):
    _append_finding(jctx.rep, "SD-01",
                    "except 捕获后返回空集合，诊断结果伪装成'无发现'")
def _sd_check_empty_ctor_return(jctx, val):
    if _empty_call_tag(val) == "dict":
        _append_finding(jctx.rep, "SD-02",
                        "except 返回空 dict 构造 dict()，异常被伪装成通过")
        return
    _append_finding(jctx.rep, "SD-01",
                    "except 捕获后返回空容器构造调用，"
                    "诊断结果伪装成'无发现'")
def _sd_ifexp_branch_tag(jctx, branch):
    if isinstance(branch, ast.NamedExpr):
        branch = branch.value
    tag = is_empty_value_node(branch)
    if tag is not None:
        return tag
    if _is_true_const(branch) or _is_pass_string_const(branch):
        return "pass"
    if isinstance(branch, ast.Name):
        tag = (jctx.empty_binds or {}).get(branch.id)
        if tag is not None:
            return tag
        if (jctx.pass_binds or {}).get(branch.id) is not None:
            return "pass"
        return None
    if _is_boolop_composition(branch) or isinstance(branch, ast.IfExp):
        # 分支本身是短路/条件表达式时，按已知绑定真值归约到具体操作数，
        # 与 `_db_value_binding_tag` 的变量绑定口径一致。
        truth = jctx.truth_binds or {}
        tag = _db_value_binding_tag(
            branch, is_empty_value_node, jctx.empty_binds or {}, truth)
        if tag is None:
            tag = _db_value_binding_tag(
                branch, _pass_tag, jctx.pass_binds or {}, truth)
        return tag
    if isinstance(branch, ast.Dict):
        if (_dict_error_payload_perceivable(branch, jctx.handler.name)
                or dict_flag_state(branch) is False):
            return None
        keys = dict_str_keys(branch)
        status = dict_status(branch)
        if ("status" not in keys or _is_pass_status_value(status)
                or _dynamic_status_passes(branch, jctx.status_binds or {})):
            return "pass"
        return None
    return None
def _sd_check_ifexp_return(jctx, val):
    test_truth = _db_binding_truthiness(val.test, jctx.truth_binds or {})
    if test_truth is not None:
        # 条件真值已由绑定确定时只检查命中分支，与 _db_scan_ifexp 同口径。
        _sd_check_return_form(
            jctx, val.body if test_truth else val.orelse,
            jctx.empty_binds or {}, jctx.pass_binds or {})
        return
    tags = tuple(_sd_ifexp_branch_tag(jctx, branch)
                 for branch in (val.body, val.orelse))
    if any(tag is None for tag in tags):
        return
    if all(tag in {"none", "empty", "dict"} for tag in tags):
        tag = ("dict" if "dict" in tags
               else "none" if tags == ("none", "none") else "empty")
        _report_degraded_value(jctx, tag, "条件表达式两分支均返回")
        return
    _append_finding(
        jctx.rep, "SD-02",
        "except 捕获后条件表达式各分支均返回空值或伪装通过/正常值，异常被伪装")
def _literal_truthiness(node) -> bool | None:
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if any(not isinstance(element, ast.Starred) for element in node.elts):
            return True
        return False if not node.elts else None
    if isinstance(node, ast.Dict):
        if any(key is not None for key in node.keys):
            return True
        return False if not node.keys else None
    if isinstance(node, ast.BoolOp):
        short_circuit_truth = isinstance(node.op, ast.Or)
        last_index = len(node.values) - 1
        outcomes = set()
        for index, operand in enumerate(node.values):
            truth = _literal_truthiness(operand)
            if truth is None:
                outcomes.add(short_circuit_truth)
                if index == last_index:
                    outcomes.add(not short_circuit_truth)
                continue
            if truth is short_circuit_truth:
                outcomes.add(truth)
                break
            if index == last_index:
                outcomes.add(truth)
        return outcomes.pop() if len(outcomes) == 1 else None
    return None
def _sd_check_boolop_return(jctx, val):
    # 按已知绑定真值归约（字面量 + 变量真值），与变量绑定路径
    # `_db_value_binding_tag` 同口径；仅字面量真值会漏掉 `return x or []`
    # 这类 x 已知为假的直接返回形态。
    operand = _db_boolop_determinate_result(val, jctx.truth_binds or {})
    if operand is not None:
        _sd_check_return_form(
            jctx, operand, jctx.empty_binds or {}, jctx.pass_binds or {})
def _sd_check_name_return(jctx, val, binds, pass_binds):
    tag = binds.get(val.id)
    if tag is None:
        ptag = pass_binds.get(val.id)
        if ptag is not None:
            _append_finding(jctx.rep, "SD-02",
                            "except 捕获后经变量返回伪装通过值（True/字符串常量/status通过dict），异常被伪装成通过/正常结果")
        return
    _report_degraded_value(jctx, tag, "经变量返回")
def _is_empty_ctor_call(val):
    return _empty_call_tag(val) is not None
def _is_boolop_composition(val):
    return (isinstance(val, ast.BoolOp) and isinstance(val.op, (ast.Or, ast.And))
            and len(val.values) >= 2)
def _sd_report_return_degradations(jctx) -> None:
    for entry in _handler_binding_flow(jctx.handler)[1]:
        sub = entry.node
        if sub.value is None:
            _sd_check_bare_return(jctx)
            continue
        binds = entry.bindings
        return_jctx = jctx._replace(
            empty_binds=binds.empty, pass_binds=binds.passed,
            status_binds=binds.status, truth_binds=binds.truth)
        _sd_check_return_form(
            return_jctx, sub.value, binds.empty, binds.passed)
_SD_SIMPLE_RETURN_FORMS = (
    (lambda v: isinstance(v, ast.Constant), _sd_check_const_return),
    (lambda v: isinstance(v, ast.Dict), _sd_check_dict_return),
    (lambda v: isinstance(v, (ast.List, ast.Tuple, ast.Set)) and not v.elts,
     _sd_check_empty_coll_return),
    (_is_empty_ctor_call, _sd_check_empty_ctor_return),
    (lambda v: isinstance(v, ast.IfExp), _sd_check_ifexp_return),
    (_is_boolop_composition, _sd_check_boolop_return),
)
def _sd_check_return_form(
    jctx, val: ast.AST, binds: dict, pass_binds: dict,
) -> None:
    if isinstance(val, ast.NamedExpr):
        val = val.value
    for match, handler in _SD_SIMPLE_RETURN_FORMS:
        if match(val):
            handler(jctx, val)
            return
    if isinstance(val, ast.Name):
        _sd_check_name_return(jctx, val, binds, pass_binds)
def _finding_payload(relpath, line, rule_id, message):
    sev, cat = _RULES[rule_id]
    return {
        "rule_id": rule_id,
        "severity": sev,
        "confidence": 0.6,
        "file": relpath,
        "line": line,
        "message": f"[{cat}] {message}",
        "source": "A3",
        "rule_family": "silent_degrade",
    }
def _append_finding(rctx, rule_id, message):
    snippet = (rctx.lines[rctx.lineno - 1].strip()[:80]
               if 0 < rctx.lineno <= len(rctx.lines) else "")
    payload = _finding_payload(rctx.relpath, rctx.lineno, rule_id,
                               f"{message}: {snippet}")
    key = (payload["rule_id"], payload["line"], payload["message"])
    if any((f["rule_id"], f["line"], f["message"]) == key
           for f in rctx.findings):
        return
    rctx.findings.append(payload)
_FAIL_STATUS_VALUES = frozenset({
    "error", "fail", "failure", "failed", "blocked", "rejected",
    "timeout", "abort", "aborted", "skip", "warn", "partial",
})
def _normalized_status_value(value) -> str | None:
    return value.strip().lower() if isinstance(value, str) else None
def is_fail_status_value(value) -> bool:
    return _normalized_status_value(value) in _FAIL_STATUS_VALUES
def _is_failure_status_value(value) -> bool:
    if value is False:
        return True
    if isinstance(value, int) and not isinstance(value, bool) and value == 0:
        return True
    return is_fail_status_value(value)
def _is_failure_status_node(node) -> bool:
    return isinstance(node, ast.Constant) and _is_failure_status_value(node.value)
_PERCEIVABLE_SINKS = {"errors", "warnings", "violations", "failed",
                      "report", "issues", "problems", "results"}
_ERROR_SEMANTIC_CONTAINERS = frozenset({
    "errors", "warnings", "violations", "failed",
})
_ERR_TEXT_SUBSTR = ("error", "fail", "exception", "warning",
                    "timeout", "unable", "cannot", "invalid",
                    "denied", "refused", "abort")
_INTENT_MARKERS = ("降级", "不阻断", "不影响", "忽略", "跳过", "回退", "兜底",
                   "冷启动", "保守", "尽力而为", "best-effort", "fallback",
                   "按不可用处理", "按非保护处理", "不应中断", "防御：", "不中断",
                   "失败返回", "失败时返回", "失败则返回", "不可用时",
                   "suppress", "skip", "cleanup", "non-critical",
                   "纯加速层",
                   "容错：",
                   "最后一道防线",
                   "退化",
                   )
_WEAK_INTENT_MARKERS = ("不影响", "忽略", "跳过", "保守", "suppress",
                        "skip", "cleanup", "不中断", "退化")
_STRONG_INTENT_MARKERS = tuple(m for m in _INTENT_MARKERS
                               if m not in _WEAK_INTENT_MARKERS)
TELEMETRY_SINKS = frozenset({
    "audit", "telemetry", "metric", "metrics", "perf", "trace",
    "monitor", "beacon", "cursor",
})
_TELEMETRY_NAME_TOKENS = TELEMETRY_SINKS | {"stats", "timing", "latency"}
def is_telemetry_sink_name(name: str) -> bool:
    stem = (name or "").lower().replace("-", "_").replace(".", "_")
    return any(tok in _TELEMETRY_NAME_TOKENS
               for tok in stem.split("_") if tok)
def is_pure_telemetry_body(try_node) -> bool:
    if try_node is None:
        return False
    for stmt in try_node.body:
        if not (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Call)
                and is_telemetry_sink_name(
                    dotted_name(stmt.value.func)
                    or expr_target_name(stmt.value.func))):
            return False
    return bool(try_node.body)
ERROR_KEYS = frozenset({"_error", "_partial", "error", "errors", "exception"})
_ERROR_KEY_SET = ERROR_KEYS | {"reason"}
FAILURE_FLAG_KEYS = frozenset({
    "ok", "success", "succeeded", "valid", "available", "healthy",
    "passed",
})
_ERRORISH_SUBSTR = ("error", "errors", "failed", "warning", "warnings")
def dict_flag_state(node: ast.Dict) -> bool | None:
    flags: list[bool] = []
    for k, v in zip(node.keys, node.values, strict=True):
        if str_constant_value(k) not in FAILURE_FLAG_KEYS:
            continue
        if not isinstance(v, ast.Constant):
            continue
        if isinstance(v.value, bool):
            flags.append(v.value)
        elif (isinstance(v.value, int) and not isinstance(v.value, bool)
              and v.value in (0, 1)):
            flags.append(bool(v.value))
    return all(flags) if flags else None
def _has_error_semantic_key(keys) -> bool:
    return any(
        k in _ERROR_KEY_SET or any(m in str(k).lower() for m in _ERRORISH_SUBSTR)
        for k in keys)
def intent_declared(text: str, doc_scope: bool = False) -> bool:
    markers = _STRONG_INTENT_MARKERS if doc_scope else _INTENT_MARKERS
    low = text.lower()
    return any(m in low for m in markers)
def log_format_strings(nodes) -> list:
    out = []
    for sub in nodes:
        if (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
                and sub.func.attr in ("debug", "info", "log") and sub.args):
            text = str_constant_value(_log_msg_arg(sub))
            if text is not None:
                out.append(text)
    return out
def build_comment_map(src: str) -> dict | None:
    try:
        out: dict[int, str] = {}
        for tok in tokenize.generate_tokens(io.StringIO(src).readline):
            if tok.type == tokenize.COMMENT:
                out[tok.start[0]] = tok.string[1:]
        return out
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError):
        logger.debug("build_comment_map: tokenize 失败，回退逐行口径", exc_info=True)
        return None
def _handler_leading_comment_start(handler: ast.AST, lines,
                                   comment_map) -> int:
    start = handler.lineno
    for delta in (1, 2):
        ln = handler.lineno - delta
        if ln < 1 or ln > len(lines):
            break
        raw = lines[ln - 1].strip()
        if not raw.startswith("#"):
            break
        text = (comment_map.get(ln) if comment_map is not None
                else lines[ln - 1].split("#", 1)[1])
        if not text or not text.strip():
            break
        start = ln
    return start
def handler_comments(handler: ast.AST, lines, comment_map) -> str:
    segs = []
    end_lineno = getattr(handler, "end_lineno", None) or handler.lineno
    for ln in range(_handler_leading_comment_start(handler, lines, comment_map),
                    end_lineno + 1):
        if comment_map is not None:
            text = comment_map.get(ln)
            if text:
                segs.append(text)
            continue
        if 0 < ln <= len(lines):
            line = lines[ln - 1]
            if "#" in line:
                segs.append(line.split("#", 1)[1])
    return " ".join(segs)
def subscript_chain_keys(target) -> list:
    keys = []
    node = target
    while isinstance(node, ast.Subscript):
        sl = node.slice
        if isinstance(sl, ast.Constant) and isinstance(sl.value, str):
            keys.append(sl.value)
        node = node.value
    return keys[::-1]
def _comp_shadow_order(comp, sh, exc_name):
    ordered = []
    running = sh
    for gen in comp.generators:
        ordered.append((gen.iter, running))
        inner = running or exc_name in iter_unpack_target_names(gen.target)
        ordered.extend((cond, inner) for cond in gen.ifs)
        running = inner
    return ordered, running
def _lambda_shadow_order(cur, sh, exc_name):
    ordered = [(d, sh) for d in cur.args.defaults]
    ordered += [(d, sh) for d in cur.args.kw_defaults
                if d is not None]
    ordered.append((cur.body, sh or exc_name in collect_param_names(cur)))
    return ordered
def _comp_elt_order(cur, sh, exc_name):
    ordered, running = _comp_shadow_order(cur, sh, exc_name)
    ordered.append((cur.elt, running))
    return ordered
def _dictcomp_shadow_order(cur, sh, exc_name):
    ordered, running = _comp_shadow_order(cur, sh, exc_name)
    ordered.append((cur.key, running))
    ordered.append((cur.value, running))
    return ordered
def _exc_ref_walk(node, exc_name):
    stack = [(node, False)]
    while stack:
        cur, sh = stack.pop()
        if isinstance(cur, ast.Name):
            if (cur.id == exc_name and isinstance(cur.ctx, ast.Load)
                    and not sh):
                return True
            continue
        if isinstance(cur, ast.Lambda):
            ordered = _lambda_shadow_order(cur, sh, exc_name)
        elif isinstance(cur, (ast.ListComp, ast.SetComp,
                              ast.GeneratorExp)):
            ordered = _comp_elt_order(cur, sh, exc_name)
        elif isinstance(cur, ast.DictComp):
            ordered = _dictcomp_shadow_order(cur, sh, exc_name)
        else:
            ordered = [(c, sh) for c in ast.iter_child_nodes(cur)]
        stack.extend(reversed(ordered))
    return False
def references_exception(value, exc_name) -> bool:
    if not exc_name:
        return False
    return _exc_ref_walk(value, exc_name)
def _dict_payload_perceivable(node: ast.Dict, exc_name) -> bool:
    return (_dict_error_payload_perceivable(node, exc_name)
            or _is_failure_status_value(dict_status(node)))
def _append_target_container(base):
    if isinstance(base, ast.Subscript):
        return ("errors" if _has_error_semantic_key(subscript_chain_keys(base))
                else None)
    if isinstance(base, ast.Name):
        return base.id
    return base.attr if isinstance(base, ast.Attribute) else None
def _append_arg_carries_error(arg, nm, exc_name) -> bool:
    if references_exception(arg, exc_name):
        return True
    if isinstance(arg, ast.Dict):
        return _dict_payload_perceivable(arg, exc_name)
    if isinstance(arg, (ast.List, ast.Tuple, ast.Set)):
        return any(_append_arg_carries_error(element, nm, exc_name)
                   for element in arg.elts)
    text = str_constant_value(arg)
    if text is None:
        return False
    if not text.strip():
        return False
    return (nm in _ERROR_SEMANTIC_CONTAINERS
            or any(m in text.lower() for m in _ERR_TEXT_SUBSTR))
def _append_is_perceivable(sub: ast.Call, exc_name):
    if not isinstance(sub.func, ast.Attribute) or not sub.args:
        return False
    nm = _append_target_container(sub.func.value)
    arg = sub.args[0]
    if (nm in _PERCEIVABLE_SINKS
            and _append_arg_carries_error(arg, nm, exc_name)):
        return True
    return (isinstance(arg, ast.Dict)
            and _dict_payload_perceivable(arg, exc_name))
_LOG_WARN_METHODS = ("warn", "warning", "fatal", "error", "info",
                     "critical", "exception")
_TRACEBACK_PRINTERS = frozenset({"print_exc", "print_exception"})
_LOG_METHODS = ("debug", "log", *_LOG_WARN_METHODS)
_LOG_LEVEL_DEBUG = (("DEBUG",), (10,))
_LOG_LEVEL_INFO_PLUS = (
    ("INFO", "WARN", "WARNING", "ERROR", "CRITICAL", "FATAL"),
    (20, 30, 40, 50),
)
_LOG_LEVEL_MSG = (("DEBUG", "INFO"), (10, 20))
def _log_level_arg(call_node: ast.Call):
    if call_node.args:
        return call_node.args[0]
    for kw in call_node.keywords:
        if kw.arg == "level":
            return kw.value
    return None
def _is_log_level_const(call_node: ast.Call, names: tuple, values: tuple) -> bool:
    lv = _log_level_arg(call_node)
    if lv is None:
        return False
    return (expr_target_name(lv) in names
            or (isinstance(lv, ast.Constant) and lv.value in values))
def _is_dynamic_perceivable_level(call_node: ast.Call) -> bool:
    if _is_log_level_const(call_node, *_LOG_LEVEL_INFO_PLUS):
        return True
    level = _log_level_arg(call_node)
    return (isinstance(level, ast.Constant)
            and isinstance(level.value, int)
            and not isinstance(level.value, bool)
            and level.value >= 20)
def _kw_msg_arg(call: ast.Call):
    for kw in call.keywords:
        if kw.arg == "msg":
            return kw.value
    return None
def _log_msg_arg(call: ast.Call):
    if not isinstance(call.func, ast.Attribute):
        return None
    if call.func.attr != "log":
        if call.args:
            return call.args[0]
        return _kw_msg_arg(call)
    if not _is_log_level_const(call, *_LOG_LEVEL_MSG):
        return None
    if len(call.args) > 1:
        return call.args[1]
    return _kw_msg_arg(call)
_ERROR_KW_NAMES = frozenset({"error", "error_message", "errors", "exception"})
_EMPTY_ERROR_PAYLOADS = (None, "", False, 0)
def _payload_carries_error(value, exc_name=None) -> bool:
    if exc_name is not None and references_exception(value, exc_name):
        return True
    if isinstance(value, ast.Constant) and value.value in _EMPTY_ERROR_PAYLOADS:
        return False
    return is_empty_value_node(value) is None
def _kw_perceivable(kw: ast.keyword, exc_name, is_log_method_call: bool) -> bool:
    is_fail_status = (kw.arg == "status"
                      and _is_failure_status_node(kw.value))
    if kw.arg not in _ERROR_KW_NAMES and not is_fail_status:
        return False
    if is_log_method_call:
        return False
    return is_fail_status or _payload_carries_error(kw.value, exc_name)
def _call_kw_perceivable(sub, exc_name) -> bool:
    f = sub.func
    is_log_method_call = isinstance(f, ast.Attribute) and f.attr in _LOG_METHODS
    return any(_kw_perceivable(kw, exc_name, is_log_method_call)
               for kw in sub.keywords)
def _is_sys_stream_write(f: ast.AST) -> bool:
    return dotted_name(f) in ("sys.stderr.write", "sys.stdout.write")
def _attr_log_signals(sub: ast.Call) -> tuple[bool, bool, bool]:
    f = sub.func
    attr = f.attr
    if (attr in _LOG_WARN_METHODS or attr in _TRACEBACK_PRINTERS
            or _is_sys_stream_write(f)):
        return True, False, True
    if attr == "debug":
        return False, True, True
    if attr != "log":
        return False, False, False
    if _is_log_level_const(sub, *_LOG_LEVEL_DEBUG):
        return False, True, True
    if _is_dynamic_perceivable_level(sub):
        return True, False, True
    return False, False, True
def _put_carries_error(sub: ast.Call) -> bool:
    first = sub.args[0]
    if isinstance(first, ast.Tuple) and first.elts:
        first = first.elts[0]
    return str_constant_value(first) in ("error", "exception", "failed")
def _attr_perceivable_signals(sub: ast.Call, exc_name) -> bool:
    attr = sub.func.attr
    if (attr in ("append", "extend")
            and _append_is_perceivable(sub, exc_name)):
        return True
    if (attr == "set_exception" and sub.args
            and references_exception(sub.args[0], exc_name)):
        return True
    return bool(attr == "put" and sub.args
                and _put_carries_error(sub))
def _attr_call_signals(sub, exc_name) -> tuple:
    has_warn, has_debug, has_any_log = _attr_log_signals(sub)
    perceivable = _attr_perceivable_signals(sub, exc_name)
    return has_warn, has_debug, has_any_log, perceivable
def _assign_exc_in_error_container(sub, t, exc_name) -> bool:
    keys = subscript_chain_keys(t)
    return bool(keys and references_exception(sub.value, exc_name)
                and _has_error_semantic_key(keys))
def _assign_error_dict_perceivable(sub, exc_name) -> bool:
    node = sub.value
    if not (isinstance(node, ast.Dict)
            and references_exception(node, exc_name)):
        return False
    return bool(_has_error_semantic_key(dict_str_keys(node))
                and _error_values_reference_exception(node, exc_name))
def dict_str_keys(node: ast.Dict) -> set[str]:
    return {key for k in node.keys
            if (key := str_constant_value(k)) is not None}
def _error_values_reference_exception(node: ast.Dict, exc_name: str | None) -> bool:
    return any(
        references_exception(v, exc_name)
        for k, v in zip(node.keys, node.values, strict=True)
        if _has_error_semantic_key((str_constant_value(k),)))
def _assign_fail_flag_tuple(sub, exc_name) -> bool:
    return (isinstance(sub.value, (ast.Tuple, ast.List))
            and bool(sub.value.elts)
            and isinstance(sub.value.elts[0], ast.Constant)
            and sub.value.elts[0].value is False
            and references_exception(sub.value, exc_name))
def _assign_container_perceivable(sub, t, exc_name) -> bool:
    if _assign_exc_in_error_container(sub, t, exc_name):
        return True
    if _assign_error_dict_perceivable(sub, exc_name):
        return True
    return _assign_fail_flag_tuple(sub, exc_name)
def _assign_status_key_perceivable(sub, t) -> bool:
    key = str_constant_value(t.slice)
    if key is None:
        return False
    if key == "status":
        return _is_failure_status_node(sub.value)
    return (_has_error_semantic_key((key,))
            and _payload_carries_error(sub.value))
def _write_targets(sub) -> tuple:
    if isinstance(sub, ast.Assign):
        return tuple(sub.targets)
    if isinstance(sub, ast.AnnAssign):
        return (sub.target,) if sub.value is not None else ()
    return ()
def _assign_targets_perceivable(sub, exc_name) -> bool:
    perceivable = False
    for t in _write_targets(sub):
        if isinstance(t, ast.Subscript):
            perceivable = (_assign_container_perceivable(sub, t, exc_name)
                           or perceivable)
            if isinstance(t.value, (ast.Name, ast.Attribute)):
                perceivable = (_assign_status_key_perceivable(sub, t)
                               or perceivable)
    return perceivable
def _merge_attr_signals(cur, add):
    warn, debug, any_log, perceivable = cur
    _warn, _debug, _any_log, _perceivable = add
    return (warn or _warn, debug or _debug, any_log or _any_log,
            perceivable or _perceivable)
def scan_except_perception(handler: ast.AST,
                           nodes) -> tuple[bool, bool, bool, bool]:
    state = (False, False, False, False)
    exc_name = getattr(handler, "name", None)
    for sub in nodes:
        if isinstance(sub, ast.Call):
            state = _scan_call_perception(state, sub, exc_name)
        elif isinstance(sub, (ast.Assign, ast.AnnAssign)):
            state = (state[0], state[1], state[2],
                     _assign_targets_perceivable(sub, exc_name) or state[3])
    return state
# 项目自有的可感知错误通道：这些调用会把异常写进用户可见的诊断产物/退出码，
# 与 ``logger.warning`` 等价。此前只认 ``log_swallowed``/``print``，导致
# ``collectors.record_scan_error`` / ``fail_cli``（CLI 边界抛出可见错误）/
# ``_swallow`` 等通道上的降级被反复判成静默（本仓 6 处）。
_PERCEIVABLE_CHANNEL_NAMES = frozenset({
    "log_swallowed", "fail_cli", "fail_fast", "abort_cli",
    "record_scan_error", "record_error", "record_degraded",
    "record_guard_error", "record_skip", "_swallow", "swallow_error",
})
def _is_perceivable_channel(f: ast.AST) -> bool:
    if isinstance(f, ast.Attribute):
        tail = f.attr
    elif isinstance(f, ast.Name):
        tail = f.id
    else:
        return False
    return tail in _PERCEIVABLE_CHANNEL_NAMES
def _scan_call_perception(
    state: tuple[bool, bool, bool, bool], sub: ast.Call, exc_name: str | None,
) -> tuple[bool, bool, bool, bool]:
    warn, debug, any_log, perceivable = state
    perceivable = _call_kw_perceivable(sub, exc_name) or perceivable
    f = sub.func
    if _is_perceivable_channel(f):
        return True, debug, True, True
    if isinstance(f, ast.Attribute):
        return _merge_attr_signals((warn, debug, any_log, perceivable),
                                   _attr_call_signals(sub, exc_name))
    if isinstance(f, ast.Name) and (f.id == "print" or f.id.endswith("_stderr_write")):
        return True, debug, True, perceivable
    return warn, debug, any_log, perceivable
EMPTY_SEQ_CTORS = frozenset({
    "set", "list", "tuple", "frozenset", "bytes", "bytearray",
})
_GROW_MUTATORS = frozenset({
    "append", "extend", "insert",
    "add", "update", "setdefault",
})
def _root_name(node):
    while isinstance(node, ast.Subscript):
        node = node.value
    return node.id if isinstance(node, ast.Name) else None
def dict_status(d: Any) -> Any:
    found, last = False, None
    for k, v in zip(d.keys, d.values, strict=True):
        if str_constant_value(k) == "status":
            found = True
            last = v.value if isinstance(v, ast.Constant) else None
    return last if found else None
PASS_STATUS_VALUES = frozenset({
    "pass", "passed", "ok", "success", "succeeded", "done", "completed",
})
def _is_pass_status_value(value) -> bool:
    if value is True:
        return True
    if isinstance(value, int) and not isinstance(value, bool) and value == 1:
        return True
    return _normalized_status_value(value) in PASS_STATUS_VALUES
def _iter_stmt_nodes(stmts):
    stack = list(stmts)
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            for expr in iter_def_site_nodes(node):
                stack.extend(_namedexpr_in_expr(expr))
            continue
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.stmt, ast.ExceptHandler, ast.match_case)):
                stack.append(child)
            else:
                stack.extend(_namedexpr_in_expr(child))
def _namedexpr_in_expr(expr_node):
    out = []
    stack = [expr_node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            stack.extend(cur.args.defaults)
            stack.extend(d for d in cur.args.kw_defaults if d is not None)
            continue
        if isinstance(cur, ast.ClassDef):
            continue
        if isinstance(cur, ast.NamedExpr):
            out.append(cur)
        stack.extend(ast.iter_child_nodes(cur))
    return out
def _add_assigned_names(target, names) -> None:
    names.update(iter_unpack_target_names(target))
def _assign_names_of_annassign(sub, names) -> None:
    if sub.value is not None and isinstance(sub.target, ast.Name):
        names.add(sub.target.id)
def _assign_names_of_assign(sub, names) -> None:
    for t in sub.targets:
        _add_assigned_names(t, names)
def _assign_names_of_single_target(sub, names) -> None:
    _add_assigned_names(sub.target, names)
def _assign_names_of_augassign(sub, names) -> None:
    if isinstance(sub.target, ast.Name):
        names.add(sub.target.id)
def _assign_names_of_with(sub, names) -> None:
    for item in sub.items:
        if item.optional_vars is not None:
            _add_assigned_names(item.optional_vars, names)
def _assign_names_of_imports(sub, names) -> None:
    names.update(import_alias_bound_names(sub))
_ASSIGNED_FORM_COLLECTORS = {
    ast.Assign: _assign_names_of_assign,
    ast.NamedExpr: _assign_names_of_single_target,
    ast.For: _assign_names_of_single_target,
    ast.AsyncFor: _assign_names_of_single_target,
    ast.AugAssign: _assign_names_of_augassign,
    ast.AnnAssign: _assign_names_of_annassign,
    ast.With: _assign_names_of_with,
    ast.AsyncWith: _assign_names_of_with,
    ast.Import: _assign_names_of_imports,
    ast.ImportFrom: _assign_names_of_imports,
}
def _collect_assigned_stmt(sub, names) -> None:
    collector = _ASSIGNED_FORM_COLLECTORS.get(type(sub))
    if collector is not None:
        collector(sub, names)
def collect_assigned(stmts: Any, names) -> set[str]:
    for sub in _iter_stmt_nodes(stmts):
        _collect_assigned_stmt(sub, names)
    return names
def _is_definite_nonempty_literal(value) -> bool:
    if isinstance(value, ast.Constant):
        constant = value.value
        if constant is None or constant is ...:
            return False
        if isinstance(constant, (str, bytes, int, float, complex)):
            return bool(constant)
        return False
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(element, ast.Starred)
                   for element in value.elts)
    if isinstance(value, ast.Dict):
        return any(key is not None for key in value.keys)
    return False
def _direct_name_rebind(statement):
    if (isinstance(statement, ast.Assign) and len(statement.targets) == 1
            and isinstance(statement.targets[0], ast.Name)):
        target, value = statement.targets[0], statement.value
    elif (isinstance(statement, ast.AnnAssign)
          and isinstance(statement.target, ast.Name)
          and statement.value is not None):
        target, value = statement.target, statement.value
    else:
        return None
    if _is_definite_nonempty_literal(value):
        nonempty = True
    elif is_empty_value_node(value) is not None:
        nonempty = False
    else:
        nonempty = None
    return target.id, nonempty
def _func_tail_ret_info(func_node):
    info = getattr(func_node, "_sd_tail_ret_info", None)
    if info is None:
        rets, nested, rebinds = [], [], []
        for n in walk_nodes(func_node):
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if n is not func_node:
                    nested.append((n.lineno, getattr(n, "end_lineno", n.lineno)))
                continue
            if not isinstance(n, ast.Return):
                continue
            v = n.value
            if isinstance(v, ast.Name):
                rets.append((n.lineno, n.col_offset, v.id))
        statements = (func_node.body if isinstance(
            func_node, (ast.FunctionDef, ast.AsyncFunctionDef)) else ())
        for statement in statements:
            rebind = _direct_name_rebind(statement)
            if rebind is not None:
                name, nonempty = rebind
                rebinds.append((statement.lineno, statement.col_offset,
                                name, nonempty))
        info = (rets, nested, rebinds)
        func_node._sd_tail_ret_info = info
    return info
def tail_returns_empty_name(func_node, handler, empty_names) -> bool:
    if func_node is None or not empty_names:
        return False
    h_end = getattr(handler, "end_lineno", handler.lineno)
    rets, nested, rebinds = _func_tail_ret_info(func_node)
    for ln, col, name in rets:
        if ln <= h_end or name not in empty_names:
            continue
        if any(s <= ln <= e for s, e in nested):
            continue
        latest_rebind = None
        for rebind_ln, rebind_col, rebind_name, nonempty in rebinds:
            position = (rebind_ln, rebind_col)
            if (rebind_name == name and h_end < rebind_ln
                    and position < (ln, col)):
                latest_rebind = (position, nonempty)
        if latest_rebind is not None and latest_rebind[1] is not False:
            continue
        return True
    return False
def _empty_const_tag(value) -> str | None:
    """返回“空集合”语义标签；数值/字符串常量不算“无发现”。

    只有``None``（空位哨兵）、``...``（占位符）与真正的空容器才会
    把异常伪装成“无发现”。``return 0.0`` / ``return ""`` 这类值转换
    兜底是正常的防御式默认值，不会掩盖诊断结论，归入豁免。
    """
    if value is None:
        return "none"
    if value is ...:
        return "empty"
    return None
def _mark_shadowed_empty_ctors(tree) -> None:
    pm = parent_map(tree)
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)):
            continue
        if node.func.id not in EMPTY_SEQ_CTORS | {'dict'}:
            continue
        if not _is_unshadowed_builtin(node, node.func.id, pm):
            node._sd_empty_ctor_shadowed = True
def _empty_call_tag(val) -> str | None:
    if getattr(val, '_sd_empty_ctor_shadowed', False):
        return None
    if (isinstance(val, ast.Call) and isinstance(val.func, ast.Name)
            and not val.args and not val.keywords):
        if val.func.id in EMPTY_SEQ_CTORS:
            return "empty"
        if val.func.id == "dict":
            return "dict"
    return None
def is_empty_value_node(val) -> str | None:
    if isinstance(val, ast.Constant):
        return _empty_const_tag(val.value)
    if isinstance(val, (ast.List, ast.Tuple, ast.Set)) and not val.elts:
        return "empty"
    if isinstance(val, ast.Dict) and not val.keys:
        return "dict"
    return _empty_call_tag(val)
def _is_definite_empty_iterable(value) -> bool:
    if isinstance(value, ast.Constant):
        return isinstance(value.value, (str, bytes)) and not value.value
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return not value.elts
    if isinstance(value, ast.Dict):
        return not value.keys
    return _empty_call_tag(value) is not None
def _is_definite_nonempty_iterable(value) -> bool:
    if isinstance(value, ast.Constant):
        return isinstance(value.value, (str, bytes)) and bool(value.value)
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(element, ast.Starred)
                   for element in value.elts)
    if isinstance(value, ast.Dict):
        return any(key is not None for key in value.keys)
    return False
class _FlowObservation(NamedTuple):
    has_warn: bool = False
    has_debug: bool = False
    has_any_log: bool = False
    perceivable: bool = False
    exc_forwarded: bool = False
_EMPTY_FLOW_OBSERVATION = _FlowObservation()
class _BindingState(NamedTuple):
    empty: dict
    passed: dict
    status: dict
    observations: frozenset = frozenset({_EMPTY_FLOW_OBSERVATION})
    # 追加在 observations 后，保持既有内部位置构造的第四个参数语义不变。
    truth: dict | None = None
class _ReturnBinding(NamedTuple):
    node: ast.Return
    bindings: _BindingState
class _LoopControlStates(NamedTuple):
    breaks: list[_BindingState]
    continues: list[_BindingState]
class _DBFlow(NamedTuple):
    returns: list[_ReturnBinding]
    exception_states: tuple[list[_BindingState], ...]
    loop_controls: tuple[_LoopControlStates, ...] = ()
    exc_name: str | None = None
_FLOW_STATE_LIMIT = 64
def _empty_binding_state() -> _BindingState:
    return _BindingState({}, {}, {}, truth={})
def _clone_binding_state(state: _BindingState) -> _BindingState:
    return _BindingState(
        dict(state.empty), dict(state.passed), dict(state.status),
        state.observations, dict(state.truth or {}))
def _binding_state_signature(state: _BindingState):
    mappings = tuple(
        tuple(sorted(mapping.items()))
        for mapping in (state.empty, state.passed, state.status,
                        state.truth or {}))
    return mappings + (tuple(sorted(state.observations)),)
def _cap_binding_states(states: list[_BindingState]) -> list[_BindingState]:
    unique: list[_BindingState] = []
    seen = set()
    for state in states:
        signature = _binding_state_signature(state)
        if signature not in seen:
            seen.add(signature)
            unique.append(state)
    if len(unique) > _FLOW_STATE_LIMIT:
        logger.debug("[A3] handler 绑定路径超过预算: %d，保留前 %d 条去重路径",
                     len(unique), _FLOW_STATE_LIMIT)
        return unique[:_FLOW_STATE_LIMIT]
    return unique
def _merge_binding_summaries(
        states: list[_BindingState], channel: str) -> dict:
    if not states:
        return {}
    maps = [getattr(state, channel) for state in states]
    names = set().union(*(mapping.keys() for mapping in maps))
    merged = {}
    for name in names:
        tags = {mapping.get(name) for mapping in maps}
        merged[name] = tags.pop() if len(tags) == 1 else None
    return merged
def _handler_binding_flow(handler) -> tuple[list, list[_ReturnBinding]]:
    cached = getattr(handler, "_sd_binding_flow", None)
    if cached is None:
        returns: list[_ReturnBinding] = []
        flow = _DBFlow(
            returns, (), exc_name=getattr(handler, "name", None))
        exits = _db_scan_statements(
            handler.body, [_empty_binding_state()], flow)
        cached = (exits, returns)
        handler._sd_binding_flow = cached
    return cached
def handler_empty_binds(handler) -> dict:
    exits, _returns = _handler_binding_flow(handler)
    return _merge_binding_summaries(exits, "empty")
def _db_mark_mutation(target, binds) -> None:
    root = _root_name(target)
    if root is not None:
        binds[root] = None
def _db_bind_target(target, tag, binds) -> None:
    if isinstance(target, ast.Name):
        binds[target.id] = tag
    elif isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            _db_bind_target(element, tag, binds)
    elif isinstance(target, ast.Starred):
        _db_bind_target(target.value, tag, binds)
    elif isinstance(target, ast.Subscript):
        _db_mark_mutation(target, binds)
def _merge_degraded_tags(tags) -> str | bool | None:
    if None in tags:
        return None
    if not tags:
        return None
    if len(tags) == 1:
        return next(iter(tags))
    if all(isinstance(tag, bool) for tag in tags):
        return None
    concrete = sorted(tags)
    return concrete[0]
def _db_binding_truthiness(value, binds):
    if isinstance(value, ast.NamedExpr):
        value = value.value
    truth = _literal_truthiness(value)
    if truth is not None:
        return truth
    if isinstance(value, ast.Name) and binds is not None:
        bound = binds.get(value.id)
        return bound if isinstance(bound, bool) else None
    if _is_boolop_composition(value):
        operand = _db_boolop_determinate_result(value, binds)
        return (_db_binding_truthiness(operand, binds)
                if operand is not None else None)
    if isinstance(value, ast.IfExp):
        test_truth = _db_binding_truthiness(value.test, binds)
        if test_truth is not None:
            branch = value.body if test_truth else value.orelse
            return _db_binding_truthiness(branch, binds)
        outcomes = {_db_binding_truthiness(branch, binds)
                    for branch in (value.body, value.orelse)}
        return outcomes.pop() if len(outcomes) == 1 else None
    return None
def _db_boolop_determinate_result(value, binds):
    last_index = len(value.values) - 1
    short_circuit_truth = isinstance(value.op, ast.Or)
    for index, operand in enumerate(value.values):
        truthy = _db_binding_truthiness(operand, binds)
        if truthy is short_circuit_truth or index == last_index:
            return operand
        if truthy is None:
            return None
    return None
def _db_value_binding_tag(
        value, tag_fn, binds=None, truth_binds=None):
    if isinstance(value, ast.NamedExpr):
        return _db_value_binding_tag(
            value.value, tag_fn, binds, truth_binds)
    if _is_boolop_composition(value):
        operand = _db_boolop_determinate_result(value, truth_binds)
        return (_db_value_binding_tag(operand, tag_fn, binds, truth_binds)
                if operand is not None else None)
    if isinstance(value, ast.IfExp):
        truth = _db_binding_truthiness(value.test, truth_binds)
        if truth is True:
            return _db_value_binding_tag(
                value.body, tag_fn, binds, truth_binds)
        if truth is False:
            return _db_value_binding_tag(
                value.orelse, tag_fn, binds, truth_binds)
        tags = {_db_value_binding_tag(branch, tag_fn, binds, truth_binds)
                for branch in (value.body, value.orelse)}
        return _merge_degraded_tags(tags)
    tag = tag_fn(value)
    if tag is None and isinstance(value, ast.Name) and binds is not None:
        return binds.get(value.id)
    return tag
def _db_bind_value(
        target, value, tag_fn, binds, truth_binds=None, source_binds=None,
) -> None:
    lookup_binds = binds if source_binds is None else source_binds
    if isinstance(target, (ast.Name, ast.Subscript)):
        tag = _db_value_binding_tag(
            value, tag_fn, lookup_binds, truth_binds)
        _db_bind_target(target, tag, binds)
        return
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(element, ast.Starred)
                        for element in target.elts)):
        for target_elt, value_elt in zip(target.elts, value.elts, strict=True):
            _db_bind_value(
                target_elt, value_elt, tag_fn, binds, truth_binds,
                lookup_binds)
        return
    _db_bind_target(target, None, binds)
def _state_bind_value(
        state: _BindingState, target, value, value_state=None,
) -> None:
    source = state if value_state is None else value_state
    truth_binds = source.truth or {}
    _db_bind_value(
        target, value, is_empty_value_node, state.empty, truth_binds,
        source.empty)
    _db_bind_value(
        target, value, _pass_tag, state.passed, truth_binds, source.passed)
    _db_bind_value(
        target, value, _status_pass_tag, state.status, truth_binds,
        source.status)
    _db_bind_value(
        target, value, _literal_truthiness, state.truth, truth_binds,
        source.truth)
def _state_bind_target(state: _BindingState, target, tag=None) -> None:
    for mapping in (state.empty, state.passed, state.status, state.truth):
        _db_bind_target(target, tag, mapping)
def _state_bind_names(state: _BindingState, names) -> None:
    for name in names:
        for mapping in (state.empty, state.passed, state.status, state.truth):
            mapping[name] = None
def _state_mark_mutation(state: _BindingState, target) -> None:
    for mapping in (state.empty, state.passed, state.status, state.truth):
        _db_mark_mutation(target, mapping)
def _state_mark_perceivable(state: _BindingState) -> _BindingState:
    return state._replace(observations=frozenset(
        observation._replace(perceivable=True)
        for observation in state.observations))
def _state_scan_call_perception(
        state: _BindingState, node: ast.Call, exc_name: str | None,
) -> _BindingState:
    observations = set()
    for current in state.observations:
        warn, debug, any_log, perceivable = _scan_call_perception(
            (current.has_warn, current.has_debug, current.has_any_log,
             current.perceivable), node, exc_name)
        forwarded = (current.exc_forwarded
                     or _sd_exc_forwarded((node,), exc_name))
        observations.add(_FlowObservation(
            warn, debug, any_log, perceivable, forwarded))
    return state._replace(observations=frozenset(observations))
def _state_scan_statement_perception(
        state: _BindingState, node: ast.stmt, exc_name: str | None,
) -> _BindingState:
    if (isinstance(node, (ast.Assign, ast.AnnAssign))
            and _assign_targets_perceivable(node, exc_name)):
        return _state_mark_perceivable(state)
    if isinstance(node, ast.AugAssign) and _sd_counter_bookkeeping((node,)):
        return _state_mark_perceivable(state)
    return state
def _db_record_exception_state(
        state: _BindingState, flow: _DBFlow) -> None:
    for channel in flow.exception_states:
        channel.append(_clone_binding_state(state))
def _merge_expression_states(
        left: _BindingState, right: _BindingState) -> _BindingState:
    states = [left, right]
    merged_channels = []
    for channel in ('empty', 'passed', 'status', 'truth'):
        maps = [(getattr(state, channel) or {}) for state in states]
        names = set().union(*(mapping.keys() for mapping in maps))
        merged = {}
        for name in names:
            tags = {mapping.get(name) for mapping in maps}
            merged[name] = _merge_degraded_tags(tags)
        merged_channels.append(merged)
    merged_truth = merged_channels.pop()
    return _BindingState(
        *merged_channels, left.observations | right.observations,
        merged_truth)
def _db_scan_ifexp(
        node: ast.IfExp, state: _BindingState, flow: _DBFlow) -> _BindingState:
    state = _db_scan_expression(node.test, state, flow)
    truth = _literal_truthiness(node.test)
    if truth is True:
        return _db_scan_expression(node.body, state, flow)
    if truth is False:
        return _db_scan_expression(node.orelse, state, flow)
    body = _db_scan_expression(node.body, _clone_binding_state(state), flow)
    orelse = _db_scan_expression(node.orelse, _clone_binding_state(state), flow)
    return _merge_expression_states(body, orelse)
def _db_scan_boolop(
        node: ast.BoolOp, state: _BindingState, flow: _DBFlow) -> _BindingState:
    state = _db_scan_expression(node.values[0], state, flow)
    short_circuit_truth = isinstance(node.op, ast.Or)
    bypassed: list[_BindingState] = []
    for index, operand in enumerate(node.values[1:], start=1):
        previous_truth = _literal_truthiness(node.values[index - 1])
        if previous_truth is short_circuit_truth:
            break
        if previous_truth is None:
            bypassed.append(_clone_binding_state(state))
            state = _db_scan_expression(operand, state, flow)
        else:
            state = _db_scan_expression(operand, state, flow)
    for bypass in bypassed:
        state = _merge_expression_states(bypass, state)
    return state
def _db_scan_eager_comprehension(
        node: ast.ListComp | ast.SetComp | ast.DictComp,
        state: _BindingState, flow: _DBFlow) -> _BindingState:
    state = _db_scan_expression(node.generators[0].iter, state, flow)
    active = [state]
    skipped: list[_BindingState] = []
    for index, generator in enumerate(node.generators):
        following: list[_BindingState] = []
        for incoming in active:
            iter_state = (incoming if index == 0 else _db_scan_expression(
                generator.iter, incoming, flow))
            if _is_definite_empty_iterable(generator.iter):
                skipped.append(_clone_binding_state(iter_state))
                continue
            if not _is_definite_nonempty_iterable(generator.iter):
                skipped.append(_clone_binding_state(iter_state))
            item_states = [iter_state]
            for condition in generator.ifs:
                filtered: list[_BindingState] = []
                for item_state in item_states:
                    item_state = _db_scan_expression(
                        condition, item_state, flow)
                    truth = _literal_truthiness(condition)
                    if truth is not True:
                        skipped.append(_clone_binding_state(item_state))
                    if truth is not False:
                        filtered.append(item_state)
                item_states = _cap_binding_states(filtered)
                if not item_states:
                    break
            following.extend(item_states)
        active = _cap_binding_states(following)
        if not active:
            break
    outcomes: list[_BindingState] = []
    for item_state in active:
        if isinstance(node, ast.DictComp):
            item_state = _db_scan_expression(node.key, item_state, flow)
            item_state = _db_scan_expression(node.value, item_state, flow)
        else:
            item_state = _db_scan_expression(node.elt, item_state, flow)
        outcomes.append(item_state)
    paths = _cap_binding_states([*skipped, *outcomes])
    merged = paths[0]
    for path in paths[1:]:
        merged = _merge_expression_states(merged, path)
    return merged
def _db_scan_expression(
        node: ast.AST, state: _BindingState, flow: _DBFlow) -> _BindingState:
    if isinstance(node, ast.IfExp):
        return _db_scan_ifexp(node, state, flow)
    if _is_boolop_composition(node):
        return _db_scan_boolop(node, state, flow)
    if isinstance(node, ast.Lambda):
        for expr in node.args.defaults:
            state = _db_scan_expression(expr, state, flow)
        for expr in node.args.kw_defaults:
            if expr is not None:
                state = _db_scan_expression(expr, state, flow)
        return state
    if (isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp))
            and node.generators):
        return _db_scan_eager_comprehension(node, state, flow)
    if isinstance(node, ast.GeneratorExp):
        if node.generators:
            state = _db_scan_expression(node.generators[0].iter, state, flow)
        return state
    if isinstance(node, ast.NamedExpr):
        state = _db_scan_expression(node.value, state, flow)
        _state_bind_value(state, node.target, node.value)
        return state
    if isinstance(node, ast.Dict):
        children = (child for key, value in zip(
            node.keys, node.values, strict=True)
                    for child in (key, value) if child is not None)
    else:
        children = ast.iter_child_nodes(node)
    for child in children:
        if not isinstance(child, (ast.stmt, ast.ExceptHandler)):
            state = _db_scan_expression(child, state, flow)
    if isinstance(node, ast.Call):
        _db_record_exception_state(state, flow)
        state = _state_scan_call_perception(state, node, flow.exc_name)
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in _GROW_MUTATORS):
            _state_mark_mutation(state, node.func.value)
    return state
def _db_scan_statements(
        statements, incoming: list[_BindingState],
        flow: _DBFlow) -> list[_BindingState]:
    states = incoming
    for statement in statements:
        following: list[_BindingState] = []
        for state in states:
            following.extend(_db_scan_statement(statement, state, flow))
        states = _cap_binding_states(following)
        if not states:
            break
    return states
def _db_scan_unknown_target(
        target: ast.AST, state: _BindingState, flow: _DBFlow) -> _BindingState:
    if isinstance(target, ast.Starred):
        return _db_scan_unknown_target(target.value, state, flow)
    if isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            state = _db_scan_unknown_target(element, state, flow)
        return state
    state = _db_scan_expression(target, state, flow)
    _state_bind_target(state, target)
    return state

def _db_scan_assignment_target(
        target: ast.AST, value: ast.AST, state: _BindingState,
        flow: _DBFlow, value_state=None) -> _BindingState:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(element, ast.Starred)
                        for element in target.elts)):
        if value_state is None:
            value_state = _clone_binding_state(state)
        for target_elt, value_elt in zip(
                target.elts, value.elts, strict=True):
            state = _db_scan_assignment_target(
                target_elt, value_elt, state, flow, value_state)
        return state
    if isinstance(target, (ast.Tuple, ast.List, ast.Starred)):
        return _db_scan_unknown_target(target, state, flow)
    state = _db_scan_expression(target, state, flow)
    _state_bind_value(state, target, value, value_state)
    return state

def _db_scan_definition_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """定义位、赋值与导入，遵循目标表达式和值的运行时求值顺序。"""
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        for expr in iter_def_site_nodes(node):
            state = _db_scan_expression(expr, state, flow)
        _state_bind_names(state, (node.name,))
        return [state]
    if isinstance(node, ast.Assign):
        state = _db_scan_expression(node.value, state, flow)
        # RHS 只求值一次；所有目标都必须读取写入前的同一份绑定快照。
        value_state = _clone_binding_state(state)
        for target in node.targets:
            state = _db_scan_assignment_target(
                target, node.value, state, flow, value_state)
    elif isinstance(node, ast.AugAssign):
        state = _db_scan_expression(node.target, state, flow)
        state = _db_scan_expression(node.value, state, flow)
        _state_bind_target(state, node.target)
    elif isinstance(node, ast.AnnAssign):
        if node.value is not None:
            state = _db_scan_expression(node.value, state, flow)
            state = _db_scan_assignment_target(
                node.target, node.value, state, flow)
    elif isinstance(node, (ast.Import, ast.ImportFrom)):
        _state_bind_names(state, import_alias_bound_names(node))
        return [state]
    else:
        return None
    state = _state_scan_statement_perception(state, node, flow.exc_name)
    return [state]


def _db_scan_transfer_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """控制流跳转（return / raise / break / continue）—— 不产生后继状态。"""
    if isinstance(node, ast.Return):
        if node.value is not None:
            state = _db_scan_expression(node.value, state, flow)
        flow.returns.append(
            _ReturnBinding(node, _clone_binding_state(state)))
        return []
    if isinstance(node, ast.Raise):
        for expr in (node.exc, node.cause):
            if expr is not None:
                state = _db_scan_expression(expr, state, flow)
        _db_record_exception_state(state, flow)
        return []
    if isinstance(node, (ast.Break, ast.Continue)):
        if flow.loop_controls:
            channel = flow.loop_controls[-1]
            target = (channel.breaks if isinstance(node, ast.Break)
                      else channel.continues)
            target.append(_clone_binding_state(state))
        return []
    return None


def _db_scan_conditional_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """``if`` 分支合并：可判真值走单支，否则两支取并集。"""
    if not isinstance(node, ast.If):
        return None
    state = _db_scan_expression(node.test, state, flow)
    truth = _literal_truthiness(node.test)
    if truth is True:
        return _db_scan_statements(node.body, [state], flow)
    if truth is False:
        return _db_scan_statements(node.orelse, [state], flow)
    body = _db_scan_statements(
        node.body, [_clone_binding_state(state)], flow)
    orelse = _db_scan_statements(
        node.orelse, [_clone_binding_state(state)], flow)
    return _cap_binding_states(body + orelse)


def _db_scan_loop_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """``for`` / ``while`` 循环体的零次迭代、跳出与正常收尾。"""
    if isinstance(node, (ast.For, ast.AsyncFor)):
        state = _db_scan_expression(node.iter, state, flow)
        if (isinstance(node, ast.For)
                and _is_definite_empty_iterable(node.iter)):
            return _db_scan_statements(node.orelse, [state], flow)
        body_state = _clone_binding_state(state)
        control = _LoopControlStates([], [])
        body_flow = flow._replace(
            loop_controls=(*flow.loop_controls, control))
        body_state = _db_scan_unknown_target(
            node.target, body_state, body_flow)
        body = _db_scan_statements(node.body, [body_state], body_flow)
        zero_iteration = (
            [] if (isinstance(node, ast.For)
                   and _is_definite_nonempty_iterable(node.iter)) else [state])
        normal = _cap_binding_states(
            [*zero_iteration, *body, *control.continues])
        normal = _db_scan_statements(node.orelse, normal, flow)
        return _cap_binding_states([*normal, *control.breaks])
    if isinstance(node, ast.While):
        state = _db_scan_expression(node.test, state, flow)
        truth = _literal_truthiness(node.test)
        if truth is False:
            return _db_scan_statements(node.orelse, [state], flow)
        control = _LoopControlStates([], [])
        body_flow = flow._replace(
            loop_controls=(*flow.loop_controls, control))
        body = _db_scan_statements(
            node.body, [_clone_binding_state(state)], body_flow)
        if truth is True:
            return _cap_binding_states(control.breaks)
        normal = _cap_binding_states([state, *body, *control.continues])
        normal = _db_scan_statements(node.orelse, normal, flow)
        return _cap_binding_states([*normal, *control.breaks])
    return None


def _db_scan_with_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """``with`` / ``async with``：上下文表达式求值后绑定可选目标。"""
    if not isinstance(node, (ast.With, ast.AsyncWith)):
        return None
    for item in node.items:
        state = _db_scan_expression(item.context_expr, state, flow)
        if item.optional_vars is not None:
            state = _db_scan_unknown_target(item.optional_vars, state, flow)
    return _db_scan_statements(node.body, [state], flow)


def _db_scan_try_finalbody(
        node, flow: _DBFlow, state: _BindingState,
        control_channel_at_entry, break_count_at_entry: int,
        continue_count_at_entry: int, exits: list[_BindingState],
        exception_states: list[_BindingState],
        return_start: int) -> list[_BindingState]:
    """``try`` 的 ``finally`` 收尾：重放挂起的 return/break/continue。"""
    pending_returns = list(flow.returns[return_start:])
    if not node.finalbody:
        return _cap_binding_states(exits)
    control_channel = (flow.loop_controls[-1]
                       if flow.loop_controls else None)
    pending_breaks = (
        list(control_channel_at_entry.breaks[break_count_at_entry:])
        if control_channel_at_entry is not None else [])
    pending_continues = (
        list(control_channel_at_entry.continues[continue_count_at_entry:])
        if control_channel_at_entry is not None else [])
    if control_channel_at_entry is not None:
        del control_channel_at_entry.breaks[break_count_at_entry:]
        del control_channel_at_entry.continues[continue_count_at_entry:]
    if not (exits or pending_returns or pending_breaks or pending_continues):
        abrupt = _cap_binding_states(exception_states or [state])
        _db_scan_statements(node.finalbody, abrupt, flow)
        return []
    final_exits = _db_scan_statements(
        node.finalbody, _cap_binding_states(exits), flow)
    suppressed_returns: set[int] = set()
    for entry in pending_returns:
        outcome_exits = _db_scan_statements(
            node.finalbody, [_clone_binding_state(entry.bindings)], flow)
        if not outcome_exits:
            suppressed_returns.add(id(entry))
    if control_channel is not None:
        for target, pending in (
                (control_channel.breaks, pending_breaks),
                (control_channel.continues, pending_continues)):
            for binding in pending:
                target.extend(_db_scan_statements(
                    node.finalbody, [_clone_binding_state(binding)], flow))
    if suppressed_returns:
        flow.returns[:] = [
            entry for entry in flow.returns
            if id(entry) not in suppressed_returns
        ]
    return _cap_binding_states(final_exits)


def _db_scan_try_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """``try`` / ``try*``：异常入口状态与 ``finally`` 重放。"""
    if not isinstance(node, (ast.Try, TRY_STAR)):
        return None
    return_start = len(flow.returns)
    control_channel_at_entry = (flow.loop_controls[-1]
                                if flow.loop_controls else None)
    break_count_at_entry = (len(control_channel_at_entry.breaks)
                            if control_channel_at_entry is not None else 0)
    continue_count_at_entry = (
        len(control_channel_at_entry.continues)
        if control_channel_at_entry is not None else 0)
    exception_states: list[_BindingState] = []
    body_flow = flow._replace(
        exception_states=(*flow.exception_states, exception_states))
    body = _db_scan_statements(
        node.body, [_clone_binding_state(state)], body_flow)
    normal = _db_scan_statements(node.orelse, body, flow)
    exits = list(normal)
    handler_entries = _cap_binding_states([state, *exception_states])
    for handler in node.handlers:
        for entry_state in handler_entries:
            handler_state = _clone_binding_state(entry_state)
            if handler.type is not None:
                handler_state = _db_scan_expression(
                    handler.type, handler_state, flow)
            if handler.name:
                _state_bind_names(handler_state, (handler.name,))
            exits.extend(_db_scan_statements(
                handler.body, [handler_state], flow))
    return _db_scan_try_finalbody(
        node, flow, state, control_channel_at_entry, break_count_at_entry,
        continue_count_at_entry, exits, exception_states, return_start)


def _db_scan_match_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState] | None:
    """``match`` 语句：逐 case 汇入、不可反驳模式截断 fallthrough。"""
    if not isinstance(node, ast.Match):
        return None
    state = _db_scan_expression(node.subject, state, flow)
    fallthrough = [state]
    exits = []
    for case in node.cases:
        pattern_irrefutable = (
            isinstance(case.pattern, ast.MatchAs)
            and case.pattern.pattern is None)
        guard_truth = (_literal_truthiness(case.guard)
                       if case.guard is not None else None)
        next_fallthrough = []
        for incoming in fallthrough:
            if not pattern_irrefutable:
                next_fallthrough.append(incoming)
            case_state = _clone_binding_state(incoming)
            _state_bind_names(
                case_state, iter_pattern_capture_names(case.pattern))
            if case.guard is not None:
                case_state = _db_scan_expression(
                    case.guard, case_state, flow)
                if guard_truth is not True:
                    next_fallthrough.append(
                        _clone_binding_state(case_state))
            if guard_truth is False:
                continue
            exits.extend(_db_scan_statements(
                case.body, [case_state], flow))
        fallthrough = _cap_binding_states(next_fallthrough)
        if (pattern_irrefutable
                and (case.guard is None or guard_truth is True)):
            fallthrough = []
            break
    exits.extend(fallthrough)
    return _cap_binding_states(exits)


def _db_scan_expression_stmt(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState]:
    """表达式语句 / ``del`` / 其余语句的兜底求值。"""
    if isinstance(node, ast.Expr):
        state = _db_scan_expression(node.value, state, flow)
        if isinstance(node.value, ast.Call):
            name = dotted_name(node.value.func)
            if name in _EXIT_CALL_NAMES:
                return []
        return [state]
    if isinstance(node, ast.Delete):
        for target in node.targets:
            state = _db_scan_unknown_target(target, state, flow)
        return [state]
    for child in ast.iter_child_nodes(node):
        if not isinstance(child, (ast.stmt, ast.ExceptHandler)):
            state = _db_scan_expression(child, state, flow)
    return [state]


# 语句族分片：按顺序尝试，首个返回非 ``None`` 的分片即为该语句的语义。
# 顺序即优先级（定义位 → 跳转 → 条件 → 循环 → with → try → match → 兜底）。
_DB_STATEMENT_SHARDS = (
    _db_scan_definition_stmt,
    _db_scan_transfer_stmt,
    _db_scan_conditional_stmt,
    _db_scan_loop_stmt,
    _db_scan_with_stmt,
    _db_scan_try_stmt,
    _db_scan_match_stmt,
)


def _db_scan_statement(
        node: ast.stmt, state: _BindingState,
        flow: _DBFlow) -> list[_BindingState]:
    for shard in _DB_STATEMENT_SHARDS:
        outcome = shard(node, state, flow)
        if outcome is not None:
            return outcome
    return _db_scan_expression_stmt(node, state, flow)
def _pass_const_tag(value) -> str | None:
    if value.value is True:
        return "true"
    if _is_pass_string_const(value):
        return "strc"
    return None
def _pass_dict_tag(value) -> str | None:
    if _dict_error_payload_perceivable(value, None):
        return None
    flag_state = dict_flag_state(value)
    if flag_state is False:
        return None
    keys = dict_str_keys(value)
    st = dict_status(value)
    if _is_pass_status_value(st) or "status" not in keys:
        return "passdict"
    return None
def _status_pass_tag(value) -> str | None:
    if isinstance(value, ast.Dict):
        return _pass_dict_tag(value)
    if not isinstance(value, ast.Constant):
        return None
    return "passdict" if _is_pass_status_value(value.value) else None
def _dynamic_status_passes(value: ast.Dict, binds: dict) -> bool:
    for key, raw in reversed(list(zip(value.keys, value.values, strict=True))):
        if str_constant_value(key) != "status":
            continue
        return (isinstance(raw, ast.Name)
                and binds.get(raw.id) == "passdict")
    return False
def _pass_tag(value):
    if isinstance(value, ast.Constant):
        return _pass_const_tag(value)
    if isinstance(value, ast.Dict):
        return _pass_dict_tag(value)
    return None
def _nested_scope_ranges(hnodes) -> list:
    return [(n.lineno, getattr(n, "end_lineno", n.lineno))
            for n in hnodes
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))]
def _outside_nested_scopes(lineno, ranges) -> bool:
    return not any(s <= lineno <= e for s, e in ranges)
def _scope_parent_map(hnodes) -> dict[ast.AST, ast.AST]:
    return {child: parent for parent in hnodes
            for child in ast.iter_child_nodes(parent)}
def _exception_leaf_name(node: ast.AST | None) -> str | None:
    if node is None:
        return None
    if isinstance(node, ast.Call):
        node = node.func
    name = dotted_name(node) or expr_target_name(node)
    return name.rsplit(".", 1)[-1] if name else None
def _handler_type_nodes(handler: ast.ExceptHandler):
    if handler.type is None:
        return ()
    return (tuple(handler.type.elts) if isinstance(handler.type, ast.Tuple)
            else (handler.type,))
def _handler_definitely_catches(
        handler: ast.ExceptHandler, exception_name: str | None) -> bool:
    if handler.type is None:
        return True
    names = {_exception_leaf_name(node) for node in _handler_type_nodes(handler)}
    if "BaseException" in names:
        return True
    if exception_name is None:
        return False
    if exception_name in names:
        return True
    return ("Exception" in names and exception_name not in {
        "BaseException", "SystemExit", "KeyboardInterrupt", "GeneratorExit",
    })
def _exception_is_caught(
        node: ast.AST, parents: dict[ast.AST, ast.AST],
        exception_name: str | None) -> bool:
    current = node
    while current in parents:
        parent = parents[current]
        if (isinstance(parent, (ast.Try, TRY_STAR))
                and any(statement is current for statement in parent.body)
                and any(_handler_definitely_catches(handler, exception_name)
                        for handler in parent.handlers)):
            return True
        current = parent
    return False
def handler_scope_raise(hnodes) -> bool:
    nested = _nested_scope_ranges(hnodes)
    parents = _scope_parent_map(hnodes)
    for node in hnodes:
        if not (isinstance(node, ast.Raise)
                and _outside_nested_scopes(node.lineno, nested)):
            continue
        exception_name = (_exception_leaf_name(node.exc)
                          if node.exc is not None else None)
        if not _exception_is_caught(node, parents, exception_name):
            return True
    return False
_EXIT_CALL_NAMES = frozenset({"sys.exit", "os._exit", "os.abort"})
def handler_scope_exit(hnodes) -> bool:
    nested = _nested_scope_ranges(hnodes)
    parents = _scope_parent_map(hnodes)
    for node in hnodes:
        if not isinstance(node, ast.Call):
            continue
        name = dotted_name(node.func)
        if (name not in _EXIT_CALL_NAMES
                or not _outside_nested_scopes(node.lineno, nested)):
            continue
        if (name != "sys.exit"
                or not _exception_is_caught(node, parents, "SystemExit")):
            return True
    return False

from __future__ import annotations

import ast
import builtins as _builtins_mod
import copy
import logging
from collections.abc import Iterator
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    collect_param_names,
    extract_loop_target_names,
    flatten_unpack_targets,
    import_alias_bound_names,
    iter_pattern_capture_names,
    iter_target_bindings,
    iter_unpack_target_names,
    module_postpones_annotations,
)
from jwsgj.diag_shared_ast_views import (
    file_bound_names,
    parent_map,
    same_scope_bfs_nodes,
    same_scope_dfs_nodes,
    subtree_nodes,
    tree_nodes,
)
from jwsgj.diag_types_defs import (
    DiagnoseIssue,
    DiagnoseSeverity,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "GATE_DETECTORS",
    "detect_b06_unused_variable",
    "detect_b11_late_binding_closure",
    "detect_b18_unbound_local",
    "detect_b19_shadow_builtin",
    "detect_b27_loop_var_shadow",
    "detect_b62_del_then_reference",
]
logger = logging.getLogger(__name__)
_ALL_BUILTIN_NAMES = frozenset(
    _n for _n in dir(_builtins_mod) if not _n.startswith('__'))
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ''
def _issue(check_id: str, severity: DiagnoseSeverity, message: str,
           line: int, suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(check_id=check_id, severity=severity, message=message,
                         line=line, suggestion=suggestion, auto_fixable=False)
def _finish(label: str, issues: list[DiagnoseIssue],
            filepath: str) -> list[DiagnoseIssue]:
    if issues:
        logger.debug("[GateB] %s 命中: %s x%d", label,
                     filepath or "<inline>", len(issues))
    return issues
def _name_ids(node: ast.AST) -> set[int]:
    return {id(t) for t in walk_nodes(node) if isinstance(t, ast.Name)}
def _ann_only_target_id(node: ast.AST) -> int | None:
    if (isinstance(node, ast.AnnAssign) and node.value is None
            and isinstance(node.target, ast.Name)):
        return id(node.target)
    return None
def _append_unique(issues: list[DiagnoseIssue], seen: set[tuple],
                   key: tuple, issue: DiagnoseIssue) -> None:
    if key in seen:
        return
    seen.add(key)
    issues.append(issue)
_BindSets = tuple[set[str], set[str], set[str]]
def detect_b06_unused_variable(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _annotation_analysis_tree(tree)
    if tree is None:
        return []
    issues = []
    seen: set[tuple[str, int]] = set()
    pm = parent_map(tree)
    binds_memo: dict[int, _BindSets] = {}
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        params: set[str] = collect_param_names(node)
        declared = _b06_declared_names(node)
        loop_target_ids, ann_only_target_ids, aug_target_ids = _b06_excluded_target_ids(node)
        stored = _b06_collect_stored(
            node, loop_target_ids | ann_only_target_ids | aug_target_ids)
        loaded = _b06_collect_loaded(
            node, aug_target_ids, pm, binds_memo)
        for name, lineno in _b06_unused_entries(stored, params, declared, loaded):
            _append_unique(issues, seen, (name, lineno), _issue(
                'B06', DiagnoseSeverity.WARN,
                f"未使用变量: '{name}' 赋值后从未被读取",
                lineno, '移除未使用的赋值，或检查是否遗漏了使用处'))
    return _finish('B06 未使用变量', issues, filepath)
def _b06_unused_entries(stored: dict[str, int], params: set[str],
                        declared: set[str], loaded: set[str]) -> list[tuple[str, int]]:
    return [(name, line) for name, line in stored.items()
            if name not in params and name not in declared
            and not name.startswith('_') and name not in loaded]
def _b06_declared_names(func: ast.AST) -> set[str]:
    declared: set[str] = set()
    for sub in same_scope_dfs_nodes(func):
        if isinstance(sub, (ast.Global, ast.Nonlocal)):
            declared.update(sub.names)
    return declared
def _b06_excluded_target_ids(func: ast.AST) -> tuple[set[int], set[int], set[int]]:
    loop_target_ids: set[int] = set()
    ann_only_target_ids: set[int] = set()
    aug_target_ids: set[int] = set()
    for sub in subtree_nodes(func):
        if isinstance(sub, (ast.For, ast.AsyncFor, ast.comprehension)):
            loop_target_ids |= _name_ids(sub.target)
        elif (isinstance(sub, ast.AugAssign)
                and isinstance(sub.target, ast.Name)):
            aug_target_ids.add(id(sub.target))
        else:
            _ann_id = _ann_only_target_id(sub)
            if _ann_id is not None:
                ann_only_target_ids.add(_ann_id)
    return loop_target_ids, ann_only_target_ids, aug_target_ids
def _b06_is_stored_name(node: ast.Name, excluded: set[int]) -> bool:
    return isinstance(node.ctx, ast.Store) and id(node) not in excluded
def _b06_is_loaded_name(node: ast.Name, aug_target_ids: set[int]) -> bool:
    return id(node) in aug_target_ids or isinstance(node.ctx, ast.Load)
def _b06_collect_stored(func: ast.AST, excluded_store_ids: set[int]) -> dict[str, int]:
    stored: dict[str, int] = {}
    head_ids = _definition_head_node_ids(func)
    for sub in same_scope_dfs_nodes(func):
        if id(sub) in head_ids:
            continue
        if isinstance(sub, ast.Name) and _b06_is_stored_name(sub, excluded_store_ids):
            stored.setdefault(sub.id, sub.lineno)
    for name, lineno, _col in _b06_eval_slot_stores(func):
        stored.setdefault(name, lineno)
    return stored
def _b06_collect_loaded(func: ast.AST, aug_target_ids: set[int], pm: dict,
                        binds_memo: dict[int, _BindSets]) -> set[str]:
    loaded: set[str] = set()
    head_ids = _definition_head_node_ids(func)
    for sub in subtree_nodes(func):
        if id(sub) in head_ids:
            continue
        if (isinstance(sub, ast.Name)
                and _b06_is_loaded_name(sub, aug_target_ids)
                and _ref_resolves_to_scope(sub, func, pm, binds_memo)):
            loaded.add(sub.id)
    return loaded
def _slot_walrus_bindings(slot: ast.AST) -> list[tuple[str, int, int]]:
    if _is_definition_boundary(slot):
        return [binding
                for inner in _definition_eval_slots(slot)
                for binding in _slot_walrus_bindings(inner)]
    roots = [slot] if isinstance(slot, ast.NamedExpr) else []
    return [(node.target.id, node.target.lineno, node.target.col_offset)
            for node in (*roots, *same_scope_dfs_nodes(slot))
            if isinstance(node, ast.NamedExpr)
            and isinstance(node.target, ast.Name)]
def _b06_eval_slot_stores(func: ast.AST) -> list[tuple[str, int, int]]:
    out: list[tuple[str, int, int]] = []
    head_ids = _definition_head_node_ids(func)
    for sub in same_scope_dfs_nodes(func):
        if id(sub) in head_ids:
            continue
        if not isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            continue
        for slot in _definition_eval_slots(sub):
            out.extend(_slot_walrus_bindings(slot))
    return out
def detect_b11_late_binding_closure(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _annotation_analysis_tree(tree)
    if tree is None:
        return []
    issues = []
    seen: set[tuple[str, int]] = set()
    _pm = parent_map(tree)
    _binds_memo: dict[int, _BindSets] = {}
    _name_refs, _call_func_ids_by_name, _sync_key_lambda_ids = _b11_build_index(tree)
    for node in tree_nodes(tree):
        if isinstance(node, (ast.For, ast.AsyncFor)):
            for _iss in _b11_loop_closure_issues(node, _sync_key_lambda_ids,
                                                 _name_refs, _call_func_ids_by_name,
                                                 _pm, _binds_memo):
                _append_unique(issues, seen, ('loop', _iss.line), _iss)
    for node in tree_nodes(tree):
        if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            for _iss in _b11_comp_closure_issues(node, _sync_key_lambda_ids,
                                                 _pm, _binds_memo):
                _append_unique(issues, seen, ('comp', _iss.line), _iss)
    return _finish('B11 循环/推导式延迟绑定', issues, filepath)
def _b11_build_index(tree: ast.Module) -> tuple[dict[str, list[ast.Name]], dict[str, set[int]], set[int]]:
    _sync_key_lambda_ids: set[int] = set()
    _name_refs: dict[str, list[ast.Name]] = {}
    _call_func_ids_by_name: dict[str, set[int]] = {}
    bound_names = file_bound_names(tree)
    for _c in tree_nodes(tree):
        if isinstance(_c, ast.Name):
            _name_refs.setdefault(_c.id, []).append(_c)
        elif isinstance(_c, ast.Call):
            _b11_index_call(_c, _call_func_ids_by_name,
                            _sync_key_lambda_ids, bound_names)
    return _name_refs, _call_func_ids_by_name, _sync_key_lambda_ids
def _b11_index_call(call: ast.Call,
                    call_func_ids_by_name: dict[str, set[int]],
                    sync_key_lambda_ids: set[int],
                    bound_names: set[str]) -> None:
    if isinstance(call.func, ast.Name):
        call_func_ids_by_name.setdefault(call.func.id, set()).add(
            id(call.func))
    is_sync_key_call = (
        (isinstance(call.func, ast.Name)
         and call.func.id in {'sorted', 'min', 'max'}
         and call.func.id not in bound_names)
        or (isinstance(call.func, ast.Attribute) and call.func.attr == 'sort')
    )
    if not is_sync_key_call:
        return
    for _kw in call.keywords:
        if _kw.arg == 'key' and isinstance(_kw.value, ast.Lambda):
            sync_key_lambda_ids.add(id(_kw.value))
def _b11_immediately_invoked(node: ast.AST, pm: dict) -> bool:
    parent = pm.get(node)
    return isinstance(parent, ast.Call) and parent.func is node
def _b11_named_closure_exempt(sub: ast.AST, loop_scope_ids: set[int],
                              name_refs: dict[str, list[ast.Name]],
                              call_func_ids_by_name: dict[str, set[int]],
                              pm: dict,
                              binds_memo: dict[int, _BindSets]) -> bool:
    if not (isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)) and sub.name):
        return False
    refs = name_refs.get(sub.name, [])
    if not refs:
        return False
    scope = pm.get(sub)
    while scope is not None and not isinstance(
            scope, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                    ast.ClassDef)):
        scope = pm.get(scope)
    declared = scope is not None and not isinstance(scope, ast.Module) and any(
        isinstance(node, (ast.Global, ast.Nonlocal)) and sub.name in node.names
        for node in same_scope_dfs_nodes(scope))
    if scope is not None and not declared:
        refs = [ref for ref in refs
                if _ref_resolves_to_scope(ref, scope, pm, binds_memo)]
    if not refs:
        return False
    ref_ids = [id(ref) for ref in refs]
    own_scope_ids = {id(_w) for _w in same_scope_dfs_nodes(sub)}
    if not all(_rid in loop_scope_ids or _rid in own_scope_ids
               for _rid in ref_ids):
        return False
    return all(_rid in call_func_ids_by_name.get(sub.name, ())
               for _rid in ref_ids)
def _iteration_closures(loop: ast.For | ast.AsyncFor) -> Iterator[ast.AST]:
    for stmt in loop.body:
        for sub in subtree_nodes(stmt):
            if isinstance(sub, (ast.Lambda, ast.FunctionDef,
                                ast.AsyncFunctionDef)):
                yield sub
def _b11_loop_closure_issues(node: ast.For | ast.AsyncFor,
                             sync_key_lambda_ids: set[int],
                             name_refs: dict[str, list[ast.Name]],
                             call_func_ids_by_name: dict[str, set[int]],
                             pm: dict,
                             binds_memo: dict[int, _BindSets],
                             ) -> list[DiagnoseIssue]:
    loop_targets = extract_loop_target_names(node)
    if not loop_targets:
        return []
    out: list[DiagnoseIssue] = []
    _loop_scope_ids = {id(_w) for _w in same_scope_bfs_nodes(node)}
    for sub in _iteration_closures(node):
        if id(sub) in sync_key_lambda_ids:
            continue
        if _b11_immediately_invoked(sub, pm):
            continue
        if _b11_named_closure_exempt(sub, _loop_scope_ids, name_refs,
                                     call_func_ids_by_name, pm, binds_memo):
            continue
        if _closure_captures(sub, node, loop_targets, pm, binds_memo):
            out.append(_issue(
                'B11', DiagnoseSeverity.ERROR,
                f"循环延迟绑定: 闭包 '{_closure_name(sub)}' 捕获循环变量，"
                f"所有闭包将共享最终值",
                sub.lineno,
                '用默认参数绑定当前值（lambda i=i: i）或 functools.partial'))
    return out
def _b11_comp_check_roots(node: ast.AST) -> list[tuple[ast.expr, set[str]]]:
    _bound: set[str] = set()
    _check_roots: list[tuple[ast.expr, set[str]]] = []
    for _gi, _gen in enumerate(node.generators):
        if _gi:
            _check_roots.append((_gen.iter, set(_bound)))
        for _t in walk_nodes(_gen.target):
            if isinstance(_t, ast.Name):
                _bound.add(_t.id)
        for _if_expr in _gen.ifs:
            _check_roots.append((_if_expr, set(_bound)))
    if isinstance(node, ast.DictComp):
        _check_roots.append((node.key, _bound))
        _check_roots.append((node.value, _bound))
    else:
        _check_roots.append((node.elt, _bound))
    return _check_roots
def _b11_comp_closure_issues(node: ast.AST, sync_key_lambda_ids: set[int],
                             pm: dict,
                             binds_memo: dict[int, _BindSets],
                             ) -> list[DiagnoseIssue]:
    out: list[DiagnoseIssue] = []
    comp_targets = _extract_comp_target_names(node)
    if not comp_targets:
        return out
    for _tgt, _tgt_names in _b11_comp_check_roots(node):
        for sub in subtree_nodes(_tgt):
            if (isinstance(sub, ast.Lambda)
                    and id(sub) not in sync_key_lambda_ids
                    and not _b11_immediately_invoked(sub, pm)
                    and _closure_captures(sub, node, _tgt_names, pm, binds_memo)):
                out.append(_issue(
                    'B11', DiagnoseSeverity.ERROR,
                    '推导式延迟绑定: lambda 捕获推导变量，所有闭包将共享最终值',
                    sub.lineno, '用默认参数绑定当前值（lambda i=i: i）'))
    return out
def _b18_exception_cleanup_positions(
        func: ast.AST) -> dict[str, list[tuple[int, int]]]:
    positions: dict[str, list[tuple[int, int]]] = {}
    for node in same_scope_dfs_nodes(func):
        if not (isinstance(node, ast.ExceptHandler) and node.name):
            continue
        position = (getattr(node, 'end_lineno', None) or node.lineno,
                    getattr(node, 'end_col_offset', None) or node.col_offset)
        positions.setdefault(node.name, []).append(position)
    return positions
def _b18_binding_is_live(name: str, aug_pos: tuple[int, int],
                         positions: dict[str, list[tuple[int, int]]],
                         cleanup_positions: dict[str, list[tuple[int, int]]]) -> bool:
    prior_bindings = [pos for pos in positions.get(name, ()) if pos < aug_pos]
    if not prior_bindings:
        return False
    prior_cleanups = [pos for pos in cleanup_positions.get(name, ())
                      if pos < aug_pos]
    return not prior_cleanups or max(prior_cleanups) < max(prior_bindings)
def detect_b18_unbound_local(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _annotation_analysis_tree(tree)
    if tree is None:
        return []
    issues = []
    for func in tree_nodes(tree):
        if not isinstance(func, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        bound, augs, declared, positions = \
            _collect_scope_bound_and_augassigns(func)
        params = collect_param_names(func)
        cleanup_positions = _b18_exception_cleanup_positions(func)
        flow = _B18FlowAnalyzer()
        flow.scan_body(func.body, {
            name: 0 for name in bound - params - declared})
        for aug in augs:
            if not isinstance(aug.target, ast.Name):
                continue
            name = aug.target.id
            if name in declared or name in params:
                continue
            aug_pos = (aug.lineno, aug.col_offset)
            if (name in bound and _b18_binding_is_live(
                    name, aug_pos, positions, cleanup_positions)
                    and (id(aug), name) not in flow.unbound_augassigns):
                continue
            op = _AUG_OPS.get(type(aug.op), '+=')
            issues.append(_issue(
                'B18', DiagnoseSeverity.ERROR,
                f"UnboundLocalError: 变量 '{name}' 在函数 '{func.name}' 内做 "
                f"'{op}' 赋值，但未在局部作用域绑定"
                f"（若引用外层变量需声明 nonlocal/global）",
                aug.lineno,
                f"在函数内先初始化 '{name}'，或声明 nonlocal/global 引用外层变量"))
    return _finish('B18 未绑定局部变量', issues, filepath)
def _b19_binding_targets(node: ast.AST) -> list[ast.AST] | None:
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [it.optional_vars for it in node.items
                if it.optional_vars is not None]
    if isinstance(node, ast.Assign):
        return node.targets
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return None
    return [node.target]
def _b19_emit_shadow(name: str, lineno: int, message: str, suggestion: str,
                     seen: set[tuple[str, int]],
                     issues: list[DiagnoseIssue]) -> None:
    if name not in _ALL_BUILTIN_NAMES:
        return
    key = (name, lineno)
    if key in seen:
        return
    seen.add(key)
    issues.append(_issue('B19', DiagnoseSeverity.WARN, message, lineno,
                         suggestion))
def _b19_enclosing_class(node: ast.AST, pm: dict) -> ast.ClassDef | None:
    cur = pm.get(node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            return None
        if isinstance(cur, ast.ClassDef):
            return cur
        cur = pm.get(cur)
    return None
def _b19_pre_binding_node_ids(node: ast.AST,
                              target: ast.AST | None = None) -> set[int]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        roots = [node.target, node.iter]
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        item = next((part for part in node.items
                     if part.optional_vars is target), None)
        if item is not None:
            roots = [item.context_expr, item.optional_vars]
        else:
            roots = [part for item in node.items
                     for part in (item.context_expr, item.optional_vars)
                     if part is not None]
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        roots = [node.value, node.target]
    elif isinstance(node, ast.ExceptHandler):
        roots = [node.type] if node.type is not None else []
    else:
        roots = [node]
    return {id(sub) for root in roots for sub in walk_nodes(root) if root is not None}
def _b19_class_body_loads_after(cls: ast.ClassDef, name: str,
                                node: ast.AST,
                                target: ast.AST | None = None) -> bool:
    head_ids = _definition_head_node_ids(cls)
    pre_binding_ids = _b19_pre_binding_node_ids(node, target)
    positioned = target if target is not None else node
    position = (getattr(positioned, 'lineno', 0),
                getattr(positioned, 'col_offset', 0))
    return any(
        isinstance(sub, ast.Name) and sub.id == name
        and isinstance(sub.ctx, ast.Load) and id(sub) not in pre_binding_ids
        and (sub.lineno, sub.col_offset) > position
        for sub in same_scope_dfs_nodes(cls) if id(sub) not in head_ids)
def _b19_shadow_reaches_call_site(node: ast.AST, name: str, pm: dict,
                                  target: ast.AST | None = None) -> bool:
    cls = _b19_enclosing_class(node, pm)
    if cls is None:
        return True
    return _b19_class_body_loads_after(cls, name, node, target)
def _b19_report_targets(node: ast.AST, targets: list[ast.AST], pm: dict,
                        seen: set[tuple[str, int]],
                        issues: list[DiagnoseIssue]) -> None:
    for t in targets:
        for nm in iter_unpack_target_names(t):
            if not _b19_shadow_reaches_call_site(node, nm, pm, t):
                continue
            _b19_emit_shadow(
                nm, node.lineno,
                f"命名遮蔽内置: 变量 '{nm}' 遮蔽内置函数，后续调用 {nm}(...) 将报 TypeError",
                f"重命名变量（如 '{nm}_'），避免遮蔽内置 {nm}",
                seen, issues)
def _b19_report_import_alias(node: ast.Import | ast.ImportFrom, pm: dict,
                              seen: set[tuple[str, int]],
                              issues: list[DiagnoseIssue]) -> None:
    for bound_name in import_alias_bound_names(node):
        if not _b19_shadow_reaches_call_site(node, bound_name, pm):
            continue
        _b19_emit_shadow(
            bound_name, node.lineno,
            f"命名遮蔽内置: import 绑定名 '{bound_name}' 遮蔽内置函数，后续调用 {bound_name}(...) 将报 TypeError",
            f"重命名 import 别名（如 '{bound_name}_'），避免遮蔽内置 {bound_name}",
            seen, issues)
def _b19_report_except_binding(node: ast.ExceptHandler, pm: dict,
                              seen: set[tuple[str, int]],
                              issues: list[DiagnoseIssue]) -> None:
    if not node.name:
        return
    if not _b19_shadow_reaches_call_site(node, node.name, pm):
        return
    _b19_emit_shadow(
        node.name, node.lineno,
        f"命名遮蔽内置: 异常变量 '{node.name}' 在 except 块内遮蔽内置函数，"
        f"块内调用 {node.name}(...) 将报 TypeError",
        f"重命名异常变量（如 '{node.name}_'），避免遮蔽内置 {node.name}",
        seen, issues)
def _in_function_scope(node: ast.AST, pm: dict) -> bool:
    cur = pm.get(node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return True
        if isinstance(cur, (ast.Module, ast.ClassDef)):
            return False
        cur = pm.get(cur)
    return False
def _b19_report_bare_annotation(node: ast.AnnAssign,
                                seen: set[tuple[str, int]],
                                issues: list[DiagnoseIssue]) -> None:
    target = node.target
    if not isinstance(target, ast.Name):
        return
    nm = target.id
    _b19_emit_shadow(
        nm, node.lineno,
        f"命名遮蔽内置: 函数内注解变量 '{nm}' 被局部化遮蔽内置名（不绑定值），后续引用 {nm}(...) 将报 UnboundLocalError",
        f"移除该注解或重命名（如 '{nm}_'），避免函数内注解目标局部化遮蔽内置 {nm}",
        seen, issues)
def _b19_report_param_shadow(node: ast.AST, label: str,
                             seen: set[tuple[str, int]],
                             issues: list[DiagnoseIssue]) -> None:
    for pname in sorted(collect_param_names(node)):
        _b19_emit_shadow(
            pname, node.lineno,
            f"命名遮蔽内置: {label}的参数 '{pname}' 遮蔽内置函数，函数体内调用 {pname}(...) 将报 TypeError",
            f"重命名参数（如 '{pname}_'），避免遮蔽内置 {pname}",
            seen, issues)
def _b19_report_comprehension_target(node: ast.comprehension,
                                     seen: set[tuple[str, int]],
                                     issues: list[DiagnoseIssue]) -> None:
    for nm in iter_unpack_target_names(node.target):
        _b19_emit_shadow(
            nm, node.target.lineno,
            f"命名遮蔽内置: 推导式变量 '{nm}' 遮蔽内置函数，推导式内调用 {nm}(...) 将报 TypeError",
            f"重命名推导式变量（如 '{nm}_'），避免遮蔽内置 {nm}",
            seen, issues)
def _b19_report_match_binding(node: ast.AST, name: str | None, pm: dict,
                              seen: set[tuple[str, int]],
                              issues: list[DiagnoseIssue]) -> None:
    if not name:
        return
    if not _b19_shadow_reaches_call_site(node, name, pm):
        return
    _b19_emit_shadow(
        name, node.lineno,
        f"命名遮蔽内置: match 分支变量 '{name}' 遮蔽内置函数，分支体内调用 {name}(...) 将报 TypeError",
        f"重命名 match 分支变量（如 '{name}_'），避免遮蔽内置 {name}",
        seen, issues)
def _b19_report_augassign(node: ast.AugAssign, pm: dict,
                          seen: set[tuple[str, int]],
                          issues: list[DiagnoseIssue]) -> None:
    target = node.target
    if not isinstance(target, ast.Name):
        return
    nm = target.id
    if _in_function_scope(node, pm):
        message = (f"命名遮蔽内置: 函数内增强赋值目标 '{nm}' 被局部化遮蔽内置名，"
                   f"未先绑定值时执行 {nm} += ... 将报 UnboundLocalError")
        suggestion = f"改用局部别名或重命名（如 '{nm}_'），避免函数内增强赋值局部化遮蔽内置 {nm}"
    else:
        message = (f"命名遮蔽内置: 增强赋值目标 '{nm}' 重新绑定内置名，"
                   f"后续调用 {nm}(...) 将报 TypeError")
        suggestion = f"避免对内置名做增强赋值，改用其他变量名（如 '{nm}_'）"
    if not _b19_shadow_reaches_call_site(node, nm, pm):
        return
    _b19_emit_shadow(nm, node.lineno, message, suggestion, seen, issues)
def detect_b19_shadow_builtin(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    seen: set[tuple[str, int]] = set()
    _pm = parent_map(tree)
    for node in tree_nodes(tree):
        _b19_dispatch(node, _pm, seen, issues)
    return _finish('B19 内建名遮蔽', issues, filepath)
def _b19_report_definition_shadow(
        node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
        pm: dict, seen: set[tuple[str, int]],
        issues: list[DiagnoseIssue]) -> None:
    label = '类' if isinstance(node, ast.ClassDef) else '函数'
    if not _b19_shadow_reaches_call_site(node, node.name, pm):
        return
    _b19_emit_shadow(
        node.name, node.lineno,
        f"命名遮蔽内置: {label}定义名 '{node.name}' 遮蔽内置函数，后续调用 {node.name}(...) 将解析到该定义",
        f"重命名{label}（如 '{node.name}_'），避免遮蔽内置 {node.name}",
        seen, issues)
def _b19_dispatch(node: ast.AST, pm: dict, seen: set[tuple[str, int]],
                  issues: list[DiagnoseIssue]) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _b19_report_definition_shadow(node, pm, seen, issues)
        _b19_report_param_shadow(node, f"函数 '{node.name}'", seen, issues)
        return
    if isinstance(node, ast.ClassDef):
        _b19_report_definition_shadow(node, pm, seen, issues)
        return
    if isinstance(node, ast.Lambda):
        _b19_report_param_shadow(node, "匿名函数（lambda）", seen, issues)
        return
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        _b19_report_import_alias(node, pm, seen, issues)
        return
    if isinstance(node, ast.ExceptHandler):
        _b19_report_except_binding(node, pm, seen, issues)
        return
    if isinstance(node, ast.comprehension):
        _b19_report_comprehension_target(node, seen, issues)
        return
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        _b19_report_match_binding(node, node.name, pm, seen, issues)
        return
    if isinstance(node, ast.MatchMapping):
        _b19_report_match_binding(node, node.rest, pm, seen, issues)
        return
    if isinstance(node, ast.AugAssign):
        _b19_report_augassign(node, pm, seen, issues)
        return
    if isinstance(node, _TYPE_ALIAS_TYPES):
        _b19_report_targets(node, [node.name], pm, seen, issues)
        return
    if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.For, ast.AsyncFor,
                             ast.With, ast.AsyncWith, ast.NamedExpr)):
        return
    targets = _b19_binding_targets(node)
    if targets is not None:
        _b19_report_targets(node, targets, pm, seen, issues)
        return
    if _in_function_scope(node, pm):
        _b19_report_bare_annotation(node, seen, issues)
def _nested_loop_nodes(loop: ast.For | ast.AsyncFor) -> Iterator[ast.For | ast.AsyncFor]:
    for stmt in loop.body:
        if _is_definition_boundary(stmt):
            continue
        for inner in (stmt, *same_scope_bfs_nodes(stmt)):
            if isinstance(inner, (ast.For, ast.AsyncFor)):
                yield inner
def detect_b27_loop_var_shadow(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    seen: set[tuple[int, str]] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            continue
        outer_names = extract_loop_target_names(node)
        if not outer_names:
            continue
        for inner in _nested_loop_nodes(node):
            inner_names = extract_loop_target_names(inner)
            for name in sorted(outer_names & inner_names):
                _append_unique(issues, seen, (inner.lineno, name), _issue(
                    'B27', DiagnoseSeverity.WARN,
                    f"循环变量遮蔽: 内层循环变量 '{name}' 覆盖外层循环变量，"
                    f"外层值在内层循环体内不可访问",
                    inner.lineno,
                    f"重命名内层循环变量（如 '{name}' → '{name}_inner'）避免遮蔽"))
    return _finish('B27 循环变量遮蔽', issues, filepath)
def _b18_unreachable_nodes(func: ast.AST) -> tuple[set[int], set[tuple[int, int]]]:
    unreachable_ids: set[int] = set()
    unreachable_positions: set[tuple[int, int]] = set()
    def mark(stmt: ast.stmt) -> None:
        for sub in walk_nodes(stmt):
            unreachable_ids.add(id(sub))
            if hasattr(sub, 'lineno') and hasattr(sub, 'col_offset'):
                unreachable_positions.add((sub.lineno, sub.col_offset))
    def scan_nested_bodies(stmt: ast.stmt) -> None:
        if _is_definition_boundary(stmt):
            return
        for field in ('body', 'orelse', 'finalbody'):
            body = getattr(stmt, field, None)
            if isinstance(body, list):
                scan_body(body)
        for handler in getattr(stmt, 'handlers', ()):
            scan_body(handler.body)
        for case in getattr(stmt, 'cases', ()):
            scan_body(case.body)
    def scan_body(body: list[ast.stmt]) -> None:
        for index, stmt in enumerate(body):
            if isinstance(stmt, ast.If):
                constant = _b62_const_truth(stmt.test)
                if constant is None:
                    scan_body(stmt.body)
                    scan_body(stmt.orelse)
                else:
                    taken = stmt.body if constant else stmt.orelse
                    skipped = stmt.orelse if constant else stmt.body
                    for skipped_stmt in skipped:
                        mark(skipped_stmt)
                    scan_body(taken)
            elif isinstance(stmt, ast.While) and _b62_const_truth(
                    stmt.test) is not None:
                if _b62_const_truth(stmt.test):
                    scan_body(stmt.body)
                    for skipped_stmt in stmt.orelse:
                        mark(skipped_stmt)
                else:
                    for skipped_stmt in stmt.body:
                        mark(skipped_stmt)
                    scan_body(stmt.orelse)
            elif (isinstance(stmt, (ast.For, ast.AsyncFor))
                  and _b62_definitely_empty_iter(stmt.iter)):
                for skipped_stmt in stmt.body:
                    mark(skipped_stmt)
                scan_body(stmt.orelse)
            else:
                scan_nested_bodies(stmt)
            if not _b62_statement_falls_through(stmt):
                for skipped_stmt in body[index + 1:]:
                    mark(skipped_stmt)
                break
    scan_body(func.body)
    return unreachable_ids, unreachable_positions
def _b18_scope_analysis_nodes(
        func: ast.AST) -> tuple[list[ast.AST], set[tuple[int, int]]]:
    unreachable_ids, unreachable_positions = _b18_unreachable_nodes(func)
    head_ids = _definition_head_node_ids(func)
    nodes = [sub for sub in same_scope_dfs_nodes(func)
             if id(sub) not in head_ids and id(sub) not in unreachable_ids]
    return nodes, unreachable_positions
def _collect_scope_bound_and_augassigns(
        func: ast.AST) -> tuple[set[str], list[ast.AugAssign], set[str],
                                dict[str, list[tuple[int, int]]]]:
    nodes, unreachable_positions = _b18_scope_analysis_nodes(func)
    augs, aug_target_ids, ann_only_target_ids, comp_target_ids = (
        _scope_augassigns_and_exclusions(nodes))
    excluded_ids = aug_target_ids | ann_only_target_ids | comp_target_ids
    bound = set(collect_param_names(func))
    declared: set[str] = set()
    positions: dict[str, list[tuple[int, int]]] = {}
    for sub in nodes:
        if isinstance(sub, (ast.Global, ast.Nonlocal)):
            declared |= set(sub.names)
            continue
        names = _scope_node_bindings(sub, excluded_ids)
        bound |= names
        pos = _binding_node_position(sub)
        for name in names:
            positions.setdefault(name, []).append(pos)
    for name, line, col in _b06_eval_slot_stores(func):
        if (line, col) in unreachable_positions:
            continue
        bound.add(name)
        positions.setdefault(name, []).append((line, col))
    return bound, augs, declared, positions
def _binding_node_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, ast.match_case):
        node = node.pattern
    return (getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0))
def _scope_augassigns_and_exclusions(
        nodes: list[ast.AST],
) -> tuple[list[ast.AugAssign], set[int], set[int], set[int]]:
    augs = [sub for sub in nodes if isinstance(sub, ast.AugAssign)]
    aug_target_ids = {id(sub.target) for sub in augs
                      if isinstance(sub.target, ast.Name)}
    comp_target_ids, ann_only_target_ids = _comp_and_ann_target_ids(nodes)
    return augs, aug_target_ids, ann_only_target_ids, comp_target_ids
def _scope_node_bindings(node: ast.AST, excluded_ids: set[int]) -> set[str]:
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
        return set() if id(node) in excluded_ids else {node.id}
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return set(import_alias_bound_names(node))
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.ExceptHandler) and node.name:
        return {node.name}
    if isinstance(node, ast.match_case):
        return set(iter_pattern_capture_names(node.pattern))
    return set()
_AUG_OPS: dict[type, str] = {
    ast.Add: '+=', ast.Sub: '-=', ast.Mult: '*=', ast.Div: '/=',
    ast.FloorDiv: '//=', ast.Mod: '%=', ast.Pow: '**=',
    ast.LShift: '<<=', ast.RShift: '>>=', ast.BitOr: '|=',
    ast.BitAnd: '&=', ast.BitXor: '^=', ast.MatMult: '@=',
}
def _iter_comp_target_nodes(node: ast.AST):
    for gen in node.generators:
        for t in walk_nodes(gen.target):
            if isinstance(t, ast.Name):
                yield t
def _extract_comp_target_names(node: ast.AST) -> set[str]:
    return {_t.id for _t in _iter_comp_target_nodes(node)}
def _scope_bind_sets(func: ast.AST, memo: dict[int, _BindSets]) -> _BindSets:
    _hit = memo.get(id(func))
    if _hit is not None:
        return _hit
    head_ids = _definition_head_node_ids(func)
    _nodes = [sub for sub in same_scope_dfs_nodes(func)
              if id(sub) not in head_ids]
    globals_, nonlocals_ = _scope_declared_sets(_nodes)
    declared = globals_ | nonlocals_
    comp_target_ids, ann_only_target_ids = _comp_and_ann_target_ids(_nodes)
    binds = collect_param_names(func)
    binds |= _scope_bind_names(_nodes, comp_target_ids, ann_only_target_ids, declared)
    result = (binds, globals_, nonlocals_)
    memo[id(func)] = result
    return result
def _scope_declared_sets(_nodes: list) -> tuple[set[str], set[str]]:
    globals_: set[str] = set()
    nonlocals_: set[str] = set()
    for sub in _nodes:
        if isinstance(sub, ast.Global):
            globals_.update(sub.names)
        elif isinstance(sub, ast.Nonlocal):
            nonlocals_.update(sub.names)
    return globals_, nonlocals_
def _comp_and_ann_target_ids(_nodes: list) -> tuple[set[int], set[int]]:
    comp_target_ids: set[int] = set()
    ann_only_target_ids: set[int] = set()
    for sub in _nodes:
        _ann_id = _ann_only_target_id(sub)
        if _ann_id is not None:
            ann_only_target_ids.add(_ann_id)
        elif isinstance(sub, ast.comprehension):
            comp_target_ids |= _name_ids(sub.target)
    return comp_target_ids, ann_only_target_ids
def _scope_bind_names(_nodes: list, comp_target_ids: set[int],
                      ann_only_target_ids: set[int],
                      declared: set[str]) -> set[str]:
    binds: set[str] = set()
    excluded_ids = comp_target_ids | ann_only_target_ids
    for sub in _nodes:
        if isinstance(sub, ast.Name):
            if _is_runtime_binding(sub, excluded_ids, declared):
                binds.add(sub.id)
        elif isinstance(sub, (ast.Import, ast.ImportFrom)):
            binds.update(import_alias_bound_names(sub))
        elif _defines_scope_name(sub):
            binds.add(sub.name)
    return binds
def _is_runtime_binding(node: ast.Name, excluded_ids: set[int],
                        declared: set[str]) -> bool:
    return (isinstance(node.ctx, (ast.Store, ast.Del))
            and id(node) not in excluded_ids and node.id not in declared)
def _defines_scope_name(node: ast.AST) -> bool:
    return (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
            or (isinstance(node, ast.ExceptHandler) and bool(node.name)))
_COMPREHENSION_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)
_TYPE_ALIAS_TYPES = (ast.TypeAlias,) if hasattr(ast, 'TypeAlias') else ()
def _ancestor_hits(node: ast.AST, boundary: ast.AST, target_ids: set[int],
                   pm: dict) -> bool:
    cur = node
    while cur is not None and cur is not boundary:
        if id(cur) in target_ids:
            return True
        cur = pm.get(cur)
    return False
def _ref_in_definition_head(ref: ast.AST, scope_node: ast.AST,
                            pm: dict) -> bool:
    head_ids = {id(slot) for slot in _definition_eval_slots(scope_node)}
    return _ancestor_hits(ref, scope_node, head_ids, pm)
def _ref_in_first_comp_iterable(ref: ast.AST, comp_node: ast.AST,
                                pm: dict) -> bool:
    generators = getattr(comp_node, 'generators', ())
    if not generators:
        return False
    return _ancestor_hits(ref, comp_node, {id(generators[0].iter)}, pm)
def _class_scope_visible_to(ref: ast.AST, class_node: ast.AST,
                            pm: dict) -> bool:
    cur = pm.get(ref)
    while cur is not None and cur is not class_node:
        if (isinstance(cur, _COMPREHENSION_TYPES)
                and not _ref_in_first_comp_iterable(ref, cur, pm)):
            return False
        if (isinstance(cur, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef))
                and not _ref_in_definition_head(ref, cur, pm)):
            return False
        cur = pm.get(cur)
    return True
def _resolution_targets_module(stop_node: ast.AST, pm: dict) -> bool:
    cur = stop_node
    while cur is not None:
        if isinstance(cur, ast.Module):
            return True
        if _is_definition_boundary(cur) or isinstance(cur, _COMPREHENSION_TYPES):
            return False
        cur = pm.get(cur)
    return False
def _ref_resolves_to_scope(ref: ast.Name, stop_node: ast.AST, pm: dict,
                           memo: dict[int, _BindSets]) -> bool:
    name = ref.id
    target_is_module = _resolution_targets_module(stop_node, pm)
    cur = pm.get(ref)
    while cur is not None and cur is not stop_node:
        if (isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef))
                and not _ref_in_definition_head(ref, cur, pm)
                and name in _scope_bind_sets(cur, memo)[1]):
            return target_is_module
        if _intermediate_scope_blocks(name, cur, memo, ref, pm):
            return False
        cur = pm.get(cur)
    return cur is stop_node
def _intermediate_scope_blocks(name: str, scope_node: ast.AST,
                               memo: dict[int, _BindSets],
                               ref: ast.AST,
                               pm: dict) -> bool:
    if isinstance(scope_node, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)):
        return _function_scope_blocks(name, scope_node, memo, ref, pm)
    if isinstance(scope_node, ast.ClassDef):
        return _class_scope_blocks(name, scope_node, memo, ref, pm)
    if isinstance(scope_node, _COMPREHENSION_TYPES):
        return _comp_scope_blocks(name, scope_node, ref, pm)
    return False
def _scope_binds_name_blocking(name: str, scope_node: ast.AST,
                               memo: dict[int, _BindSets]) -> bool:
    binds, globals_, nonlocals_ = _scope_bind_sets(scope_node, memo)
    if name in globals_:
        return True
    return name in binds and name not in nonlocals_
def _function_scope_blocks(name: str, scope_node: ast.AST,
                           memo: dict[int, _BindSets],
                           ref: ast.AST, pm: dict) -> bool:
    if ref is not None and pm is not None and _ref_in_definition_head(
            ref, scope_node, pm):
        return False
    return _scope_binds_name_blocking(name, scope_node, memo)
def _class_scope_blocks(name: str, scope_node: ast.AST,
                        memo: dict[int, _BindSets],
                        ref: ast.AST, pm: dict) -> bool:
    if (ref is None or pm is None
            or _ref_in_definition_head(ref, scope_node, pm)
            or not _class_scope_visible_to(ref, scope_node, pm)):
        return False
    return _scope_binds_name_blocking(name, scope_node, memo)
def _comp_scope_blocks(name: str, scope_node: ast.AST,
                       ref: ast.AST, pm: dict) -> bool:
    if name not in _extract_comp_target_names(scope_node):
        return False
    return not (ref is not None and pm is not None
                and _ref_in_first_comp_iterable(ref, scope_node, pm))
def _closure_captures(closure: ast.AST, stop_node: ast.AST, names: set[str],
                      pm: dict, memo: dict[int, _BindSets]) -> bool:
    if not names:
        return False
    bodies = [closure.body] if isinstance(closure, ast.Lambda) else list(closure.body)
    for b in bodies:
        for sub in subtree_nodes(b):
            if (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
                    and sub.id in names
                    and _ref_resolves_to_scope(sub, stop_node, pm, memo)):
                return True
    return False
def _closure_name(node: ast.AST) -> str:
    if isinstance(node, ast.Lambda):
        return '<lambda>'
    return node.name
def _is_definition_boundary(node: ast.AST) -> bool:
    return isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda))
def _stmt_load_ref_positions(node: ast.AST, name: str) -> list[tuple[int, int]]:
    positions: list[tuple[int, int]] = []
    _collect_load_positions(node, name, positions)
    return sorted(set(positions))
def _collect_comp_load_positions(node: ast.AST, name: str,
                                 positions: list[tuple[int, int]],
                                 bound: bool) -> bool:
    inner_bound = bound
    outer_bound = bound
    guaranteed = True
    for gen in node.generators:
        inner_bound = _collect_load_positions(
            gen.iter, name, positions, inner_bound)
        if guaranteed:
            outer_bound = _collect_load_positions(
                gen.iter, name, [], outer_bound)
        if _b62_definitely_empty_iter(gen.iter):
            return outer_bound
        guaranteed = (
            guaranteed and _b62_definitely_nonempty_iter(gen.iter))
        inner_bound = _collect_load_positions(
            gen.target, name, positions, inner_bound)
        for if_expr in gen.ifs:
            inner_bound = _collect_load_positions(
                if_expr, name, positions, inner_bound)
            if guaranteed:
                outer_bound = _collect_load_positions(
                    if_expr, name, [], outer_bound)
            constant = _b62_const_truth(if_expr)
            if constant is False:
                return outer_bound
            guaranteed = guaranteed and constant is True
    roots = (node.key, node.value) if isinstance(node, ast.DictComp) else (node.elt,)
    for root in roots:
        inner_bound = _collect_load_positions(
            root, name, positions, inner_bound)
        if guaranteed:
            outer_bound = _collect_load_positions(
                root, name, [], outer_bound)
    return outer_bound
def _b62_merge_states(paths: list[dict[str, int]]) -> dict[str, int]:
    names = set(paths[0])
    for path in paths[1:]:
        names.intersection_update(path)
    return {name: min(path[name] for path in paths) for name in names}
def _b62_union_states(paths: list[dict[str, int]]) -> dict[str, int]:
    names = set().union(*(set(path) for path in paths)) if paths else set()
    return {name: min(path[name] for path in paths if name in path)
            for name in names}
def _b62_iter_lower_bound(node: ast.AST) -> int:
    if isinstance(node, (ast.List, ast.Tuple)):
        return sum(not isinstance(item, ast.Starred) for item in node.elts)
    if isinstance(node, ast.Set):
        return int(any(not isinstance(item, ast.Starred) for item in node.elts))
    if isinstance(node, ast.Dict):
        return int(any(key is not None for key in node.keys))
    if (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes))):
        return len(node.value)
    return 0
def _b62_definitely_multiple_iter(node: ast.AST) -> bool:
    return _b62_iter_lower_bound(node) >= 2
def _b62_repeat_scan_safe(body: list[ast.stmt]) -> bool:
    for stmt in body:
        for sub in (stmt, *same_scope_dfs_nodes(stmt)):
            if isinstance(sub, (ast.Return, ast.Raise)):
                return False
    return not _b62_loop_has_own_jump(body, ast.Break)
def _b62_irrefutable_pattern(pattern: ast.AST) -> bool:
    return isinstance(pattern, ast.MatchAs) and pattern.pattern is None
def _b62_const_truth(node: ast.AST) -> bool | None:
    if isinstance(node, ast.NamedExpr):
        return _b62_const_truth(node.value)
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.Compare):
        left = node.left
        for op, right in zip(node.ops, node.comparators, strict=True):
            constant = _b62_const_compare(left, op, right)
            if constant is not True:
                return constant
            left = right
        return True
    return None
def _b62_definitely_empty_iter(node: ast.AST) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and not node.value)
def _b62_definitely_nonempty_iter(node: ast.AST) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(item, ast.Starred) for item in node.elts)
    if isinstance(node, ast.Dict):
        return any(key is not None for key in node.keys)
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))
def _load_pos_assert(node: ast.Assert, name: str,
                     positions: list[tuple[int, int]], bound: bool) -> bool:
    bound = _collect_load_positions(node.test, name, positions, bound)
    constant = _b62_const_truth(node.test)
    if constant is True or node.msg is None:
        return bound
    message_bound = _collect_load_positions(
        node.msg, name, positions, bound)
    return message_bound if constant is False else bound
def _b62_expression_exit_states(
        node: ast.AST, name: str, positions: list[tuple[int, int]],
        bound: bool) -> set[tuple[bool, bool]]:
    if isinstance(node, ast.Constant):
        return {(bool(node.value), bound)}
    if isinstance(node, ast.NamedExpr):
        states = _b62_expression_exit_states(
            node.value, name, positions, bound)
        rebinds = node.target.id == name
        return {(truth, bound_after or rebinds)
                for truth, bound_after in states}
    if isinstance(node, ast.IfExp):
        states: set[tuple[bool, bool]] = set()
        for truth, test_bound in _b62_expression_exit_states(
                node.test, name, positions, bound):
            branch = node.body if truth else node.orelse
            states |= _b62_expression_exit_states(
                branch, name, positions, test_bound)
        return states
    if isinstance(node, ast.BoolOp):
        is_and = isinstance(node.op, ast.And)
        exits: set[tuple[bool, bool]] = set()
        incoming = {bound}
        for index, value in enumerate(node.values):
            following: set[bool] = set()
            for entry_bound in incoming:
                states = _b62_expression_exit_states(
                    value, name, positions, entry_bound)
                if index == len(node.values) - 1:
                    exits |= states
                    continue
                for truth, exit_bound in states:
                    if (is_and and not truth) or (not is_and and truth):
                        exits.add((truth, exit_bound))
                    else:
                        following.add(exit_bound)
            incoming = following
            if not incoming:
                break
        return exits
    exit_bound = _collect_load_positions(node, name, positions, bound)
    constant = _b62_const_truth(node)
    if constant is not None:
        return {(constant, exit_bound)}
    return {(True, exit_bound), (False, exit_bound)}
def _load_pos_boolop(node: ast.BoolOp, name: str,
                     positions: list[tuple[int, int]], bound: bool) -> bool:
    exits = _b62_expression_exit_states(node, name, positions, bound)
    return bool(exits) and all(exit_bound for _truth, exit_bound in exits)
def _b62_const_compare(left: ast.AST, op: ast.cmpop,
                       right: ast.AST) -> bool | None:
    if not isinstance(left, ast.Constant) or not isinstance(right, ast.Constant):
        return None
    a, b = left.value, right.value
    if isinstance(op, ast.Eq):
        return a == b
    if isinstance(op, ast.NotEq):
        return a != b
    orderable = (
        (isinstance(a, (int, float)) and isinstance(b, (int, float)))
        or (isinstance(a, str) and isinstance(b, str))
        or (isinstance(a, bytes) and isinstance(b, bytes))
    )
    if not orderable:
        return None
    if isinstance(op, ast.Lt):
        return a < b
    if isinstance(op, ast.LtE):
        return a <= b
    if isinstance(op, ast.Gt):
        return a > b
    if isinstance(op, ast.GtE):
        return a >= b
    return None
def _load_pos_compare(node: ast.Compare, name: str,
                      positions: list[tuple[int, int]], bound: bool) -> bool:
    left = node.left
    bound = _collect_load_positions(left, name, positions, bound)
    exit_bounds: list[bool] = []
    for op, comparator in zip(node.ops, node.comparators, strict=True):
        bound = _collect_load_positions(
            comparator, name, positions, bound)
        constant = _b62_const_compare(left, op, comparator)
        if constant is False:
            exit_bounds.append(bound)
            break
        if constant is None:
            exit_bounds.append(bound)
        left = comparator
    else:
        exit_bounds.append(bound)
    return all(exit_bounds) if exit_bounds else bound
def _load_pos_dict(node: ast.Dict, name: str,
                   positions: list[tuple[int, int]], bound: bool) -> bool:
    for key, value in zip(node.keys, node.values, strict=True):
        if key is not None:
            bound = _collect_load_positions(key, name, positions, bound)
        bound = _collect_load_positions(value, name, positions, bound)
    return bound
def _load_pos_ifexp(node: ast.IfExp, name: str,
                    positions: list[tuple[int, int]], bound: bool) -> bool:
    bound = _collect_load_positions(node.test, name, positions, bound)
    constant = _b62_const_truth(node.test)
    if constant is not None:
        branch = node.body if constant else node.orelse
        return _collect_load_positions(branch, name, positions, bound)
    body_bound = _collect_load_positions(node.body, name, positions, bound)
    else_bound = _collect_load_positions(node.orelse, name, positions, bound)
    return body_bound and else_bound
def _collect_load_positions(node: ast.AST, name: str,
                            positions: list[tuple[int, int]],
                            bound: bool = False) -> bool:
    if _is_definition_boundary(node):
        return _load_pos_definition(node, name, positions, bound)
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return bound or name in import_alias_bound_names(node)
    for node_types, handler in _LOAD_POS_DISPATCH:
        if isinstance(node, node_types):
            return handler(node, name, positions, bound)
    return _load_pos_children(node, name, positions, bound)
def _load_pos_definition(node: ast.AST, name: str,
                         positions: list[tuple[int, int]], bound: bool) -> bool:
    for slot in _definition_eval_slots(node):
        bound = _collect_load_positions(slot, name, positions, bound)
    return bound or getattr(node, 'name', None) == name
def _load_pos_type_alias(node: ast.AST, name: str,
                         positions: list[tuple[int, int]], bound: bool) -> bool:
    return _collect_load_positions(node.name, name, positions, bound)
def _load_pos_assignment(node: ast.AST, name: str,
                         positions: list[tuple[int, int]], bound: bool) -> bool:
    if isinstance(node, ast.Assign):
        bound = _collect_load_positions(node.value, name, positions, bound)
        for target in node.targets:
            bound = _collect_load_positions(target, name, positions, bound)
        return bound
    if isinstance(node, ast.AnnAssign):
        if node.value is None:
            if not isinstance(node.target, ast.Name):
                bound = _collect_load_positions(
                    node.target, name, positions, bound)
            return _collect_load_positions(
                node.annotation, name, positions, bound)
        bound = _collect_load_positions(node.value, name, positions, bound)
        bound = _collect_load_positions(node.target, name, positions, bound)
        return _collect_load_positions(
            node.annotation, name, positions, bound)
    if isinstance(node, ast.AugAssign):
        if (isinstance(node.target, ast.Name) and node.target.id == name):
            if not bound:
                positions.append((node.target.lineno, node.target.col_offset))
            _collect_load_positions(node.value, name, positions, bound)
            return True
        bound = _collect_load_positions(node.target, name, positions, bound)
        return _collect_load_positions(node.value, name, positions, bound)
    bound = _collect_load_positions(node.value, name, positions, bound)
    return _collect_load_positions(node.target, name, positions, bound)
def _load_pos_name(node: ast.Name, name: str,
                   positions: list[tuple[int, int]], bound: bool) -> bool:
    if node.id != name:
        return bound
    if isinstance(node.ctx, ast.Load):
        if not bound:
            positions.append((node.lineno, node.col_offset))
        return bound
    if isinstance(node.ctx, ast.Store):
        return True
    return bound
def _load_pos_children(node: ast.AST, name: str,
                       positions: list[tuple[int, int]], bound: bool) -> bool:
    for child in ast.iter_child_nodes(node):
        bound = _collect_load_positions(child, name, positions, bound)
    return bound
_LOAD_POS_DISPATCH = (
    (_TYPE_ALIAS_TYPES, _load_pos_type_alias),
    (_COMPREHENSION_TYPES, _collect_comp_load_positions),
    ((ast.BoolOp,), _load_pos_boolop),
    ((ast.Compare,), _load_pos_compare),
    ((ast.Dict,), _load_pos_dict),
    ((ast.IfExp,), _load_pos_ifexp),
    ((ast.Assert,), _load_pos_assert),
    ((ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr),
     _load_pos_assignment),
    ((ast.Name,), _load_pos_name),
)
def _iter_arg_annotations(args: ast.arguments):
    for a in (*args.posonlyargs, *args.args, *args.kwonlyargs):
        if a.annotation is not None:
            yield a.annotation
    for a in (args.vararg, args.kwarg):
        if a is not None and a.annotation is not None:
            yield a.annotation
def _argument_eval_slots(args: ast.arguments) -> list[ast.AST]:
    slots: list[ast.AST] = list(args.defaults)
    slots.extend(default for default in args.kw_defaults if default is not None)
    return slots
def _definition_eval_slots(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        slots: list[ast.AST] = list(node.decorator_list)
        slots.extend(_argument_eval_slots(node.args))
        slots.extend(_iter_arg_annotations(node.args))
        if node.returns is not None:
            slots.append(node.returns)
        return slots
    if isinstance(node, ast.Lambda):
        return _argument_eval_slots(node.args)
    if isinstance(node, ast.ClassDef):
        slots = list(node.decorator_list)
        slots.extend(node.bases)
        slots.extend(node.keywords)
        return slots
    return [node]
def _definition_head_node_ids(node: ast.AST) -> set[int]:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
        return set()
    _ids: set[int] = set()
    for _slot in _definition_eval_slots(node):
        _ids.update(id(_sub) for _sub in walk_nodes(_slot))
    return _ids
def _b62_report_deleted_refs(
        node: ast.AST, deleted: dict[str, int], issues: list[DiagnoseIssue],
        seen: set[tuple[str, int]]) -> None:
    for name, del_line in sorted(deleted.items()):
        reported_lines: set[int] = set()
        for ref_pos in _stmt_load_ref_positions(node, name):
            ref_line = ref_pos[0]
            key = (name, ref_line)
            if ref_line in reported_lines or key in seen:
                continue
            reported_lines.add(ref_line)
            seen.add(key)
            issues.append(_issue(
                'B62', DiagnoseSeverity.ERROR,
                f"名 '{name}' 第 {del_line} 行 del 删除后再次引用："
                f"执行即 NameError/UnboundLocalError",
                ref_line, 'del 后不得再引用；需复用请先重新赋值'))
def _b62_drop_rebound(node: ast.AST, deleted: dict[str, int]) -> None:
    for name in list(deleted):
        if _collect_load_positions(node, name, [], False):
            del deleted[name]
def _local_annotation(node: ast.AST, parents: dict) -> bool:
    if not isinstance(node, ast.AnnAssign):
        return False
    cur = parents.get(node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            return True
        if isinstance(cur, (ast.ClassDef, ast.Module)):
            return False
        cur = parents.get(cur)
    return False
def _blank_annotation(node: ast.AnnAssign) -> None:
    replacement = ast.copy_location(ast.Constant(value=None), node.annotation)
    node.annotation = replacement
_ANNOTATION_TREE_MEMO: dict[int, tuple] = {}
_ANNOTATION_TREE_MEMO_MAX = 32


def _annotation_analysis_tree(tree: ast.Module | None) -> ast.Module | None:
    """返回「注解已置空」的分析副本（按源树记忆化）。

    B06/B11/B18 等四个检测器都需要同一份副本，原实现每次调用都
    ``copy.deepcopy`` 整棵树（3000 行文件约 1.7M 次 deepcopy 调用、0.85s），
    单文件累计 3.4s，是安全网关阶段的主要耗时与内存放大来源。副本构造后
    只读，故按源树缓存复用，语义与逐次拷贝等价。
    """
    if tree is None:
        return None
    _key = id(tree)
    _got = _ANNOTATION_TREE_MEMO.get(_key)
    if _got is not None and _got[0] is tree:
        return _got[1]
    _built = _build_annotation_analysis_tree(tree)
    if len(_ANNOTATION_TREE_MEMO) >= _ANNOTATION_TREE_MEMO_MAX:
        _ANNOTATION_TREE_MEMO.clear()
    _ANNOTATION_TREE_MEMO[_key] = (tree, _built)
    return _built


def _build_annotation_analysis_tree(
        tree: ast.Module | None) -> ast.Module | None:
    if tree is None:
        return None
    postponed = module_postpones_annotations(tree)
    parents = parent_map(tree)
    if not postponed and not any(
            _local_annotation(node, parents) for node in tree_nodes(tree)):
        return tree
    analyzed = copy.deepcopy(tree)
    analyzed_parents = parent_map(analyzed)
    for node in tree_nodes(analyzed):
        if (isinstance(node, ast.AnnAssign)
                and (postponed or _local_annotation(
                    node, analyzed_parents))):
            _blank_annotation(node)
        if postponed and isinstance(
                node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            for arg in walk_nodes(node.args):
                if isinstance(arg, ast.arg):
                    arg.annotation = None
            if not isinstance(node, ast.Lambda):
                node.returns = None
    return analyzed
def _b62_loop_has_own_jump(body: list[ast.stmt],
                           jump_type: type[ast.AST]) -> bool:
    def visit(node: ast.AST) -> bool:
        if _is_definition_boundary(node):
            return False
        if isinstance(node, jump_type):
            return True
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            return any(visit(stmt) for stmt in node.orelse)
        return any(visit(child) for child in ast.iter_child_nodes(node))
    return any(visit(stmt) for stmt in body)
def _b62_body_may_raise(body: list[ast.stmt]) -> bool:
    for stmt in body:
        if _b62_may_raise(stmt):
            return True
        if not _b62_statement_falls_through(stmt):
            break
    return False
def _b62_statement_falls_through(stmt: ast.stmt) -> bool:
    if isinstance(stmt, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
        return False
    if isinstance(stmt, ast.If):
        constant = _b62_const_truth(stmt.test)
        if constant is not None:
            taken = stmt.body if constant else stmt.orelse
            return _b62_branch_falls_through(taken)
        return (_b62_branch_falls_through(stmt.body)
                or _b62_branch_falls_through(stmt.orelse))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _b62_branch_falls_through(stmt.body)
    if isinstance(stmt, (ast.Try, TRY_STAR)):
        if not _b62_branch_falls_through(stmt.finalbody):
            return False
        normal = (_b62_branch_falls_through(stmt.body)
                  and _b62_branch_falls_through(stmt.orelse))
        handler_exit = (_b62_body_may_raise(stmt.body) and any(
            _b62_branch_falls_through(handler.body)
            for handler in stmt.handlers))
        return normal or handler_exit
    if isinstance(stmt, ast.Match):
        considered: list[ast.match_case] = []
        exhaustive = False
        for case in stmt.cases:
            considered.append(case)
            if case.guard is None and _b62_irrefutable_pattern(case.pattern):
                exhaustive = True
                break
        if not exhaustive:
            return True
        return any(_b62_branch_falls_through(case.body)
                   for case in considered)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if _b62_definitely_empty_iter(stmt.iter):
            return _b62_branch_falls_through(stmt.orelse)
        else_entry = (
            not _b62_definitely_nonempty_iter(stmt.iter)
            or _b62_branch_falls_through(stmt.body)
            or _b62_loop_has_own_jump(stmt.body, ast.Continue)
        )
        return ((else_entry and _b62_branch_falls_through(stmt.orelse))
                or _b62_loop_has_own_jump(stmt.body, ast.Break))
    if isinstance(stmt, ast.While):
        constant = _b62_const_truth(stmt.test)
        if constant is False:
            return _b62_branch_falls_through(stmt.orelse)
        if constant is True:
            return _b62_loop_has_own_jump(stmt.body, ast.Break)
        return (_b62_branch_falls_through(stmt.orelse)
                or _b62_loop_has_own_jump(stmt.body, ast.Break))
    return True
def _b62_branch_falls_through(body: list[ast.stmt]) -> bool:
    for stmt in body:
        if not _b62_statement_falls_through(stmt):
            return False
    return True
def _b62_known_safe_iterable(node: ast.AST) -> bool:
    return (isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict))
            or (isinstance(node, ast.Constant)
                and isinstance(node.value, (str, bytes))))
def _b62_may_raise(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return False
    if isinstance(node, ast.Name):
        return isinstance(node.ctx, ast.Load)
    if _is_definition_boundary(node):
        if isinstance(node, ast.ClassDef):
            return True
        return any(_b62_may_raise(slot)
                   for slot in _definition_eval_slots(node))
    if isinstance(node, _TYPE_ALIAS_TYPES):
        return False
    if isinstance(node, ast.GeneratorExp):
        first = node.generators[0].iter
        return not _b62_known_safe_iterable(first) or _b62_may_raise(first)
    if isinstance(node, ast.BoolOp):
        for index, value in enumerate(node.values):
            if _b62_may_raise(value):
                return True
            if index == len(node.values) - 1:
                continue
            constant = _b62_const_truth(value)
            if ((isinstance(node.op, ast.And) and constant is False)
                    or (isinstance(node.op, ast.Or) and constant is True)):
                return False
            if constant is None:
                return True
        return False
    if isinstance(node, ast.IfExp):
        if _b62_may_raise(node.test):
            return True
        constant = _b62_const_truth(node.test)
        if constant is None:
            return True
        return _b62_may_raise(node.body if constant else node.orelse)
    if isinstance(node, ast.Compare):
        left = node.left
        if _b62_may_raise(left):
            return True
        for op, comparator in zip(node.ops, node.comparators, strict=True):
            if _b62_may_raise(comparator):
                return True
            constant = _b62_const_compare(left, op, comparator)
            if constant is None:
                return True
            if constant is False:
                return False
            left = comparator
        return False
    if isinstance(node, ast.Assert):
        return _b62_may_raise(node.test) or _b62_const_truth(
            node.test) is not True
    if isinstance(node, (ast.If, ast.While)):
        if _b62_may_raise(node.test):
            return True
        constant = _b62_const_truth(node.test)
        if constant is None:
            return True
        body = node.body if constant else node.orelse
        return any(_b62_may_raise(stmt) for stmt in body)
    if isinstance(node, (ast.For, ast.AsyncFor)):
        if (isinstance(node, ast.AsyncFor)
                or not _b62_known_safe_iterable(node.iter)):
            return True
        return any(_b62_may_raise(child)
                   for child in ast.iter_child_nodes(node))
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp)):
        for gen in node.generators:
            if (not _b62_known_safe_iterable(gen.iter)
                    or _b62_may_raise(gen.iter)
                    or _b62_may_raise(gen.target)
                    or any(_b62_may_raise(expr) for expr in gen.ifs)):
                return True
        roots = ((node.key, node.value) if isinstance(node, ast.DictComp)
                 else (node.elt,))
        return any(_b62_may_raise(root) for root in roots)
    if isinstance(node, (ast.Pass, ast.Global, ast.Nonlocal,
                         ast.Break, ast.Continue)):
        return False
    if isinstance(node, (ast.Call, ast.BinOp, ast.UnaryOp, ast.Attribute,
                         ast.Subscript, ast.Await, ast.Yield, ast.YieldFrom,
                         ast.Starred, ast.FormattedValue, ast.AugAssign,
                         ast.Import, ast.ImportFrom, ast.Raise,
                         ast.With, ast.AsyncWith, ast.MatchClass)):
        return True
    if (isinstance(node, (ast.List, ast.Tuple))
            and isinstance(node.ctx, ast.Store)):
        return True
    if isinstance(node, ast.Dict) and any(key is None for key in node.keys):
        return True
    return any(_b62_may_raise(child) for child in ast.iter_child_nodes(node))
def _b62_eval_may_fail(node: ast.AST) -> bool:
    return _b62_may_raise(node) or any(
        isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
        for sub in walk_nodes(node))
def _b62_target_rebindings_before_raise(
        target: ast.AST, value: ast.AST) -> tuple[set[str], bool]:
    if isinstance(target, ast.Name):
        return {target.id}, False
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return set(), True
    if (len(target.elts) != len(value.elts)
            or any(isinstance(item, ast.Starred)
                   for item in (*target.elts, *value.elts))):
        return set(), True
    rebound: set[str] = set()
    for subtarget, subvalue in zip(target.elts, value.elts, strict=True):
        names, may_raise = _b62_target_rebindings_before_raise(
            subtarget, subvalue)
        rebound.update(names)
        if may_raise:
            return rebound, True
    return rebound, False
def _b62_assignment_rebindings_before_raise(
        node: ast.Assign | ast.AnnAssign) -> set[str]:
    value = node.value
    if value is None or _b62_eval_may_fail(value):
        return set()
    rebound = _b62_rebindings_before_raise(value)
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    for target in targets:
        names, may_raise = _b62_target_rebindings_before_raise(target, value)
        rebound.update(names)
        if may_raise:
            break
    return rebound
def _b62_rebindings_before_raise(node: ast.AST) -> set[str]:
    if isinstance(node, ast.Constant):
        return set()
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        return _b62_assignment_rebindings_before_raise(node)
    if isinstance(node, ast.NamedExpr):
        if _b62_eval_may_fail(node.value):
            return set()
        return {node.target.id} if isinstance(node.target, ast.Name) else set()
    eager_types = (ast.Expr, ast.Tuple, ast.List, ast.Set, ast.Dict,
                   ast.BinOp, ast.UnaryOp)
    if not isinstance(node, eager_types):
        return set()
    if isinstance(node, ast.Dict):
        children = [part for key, value in zip(
            node.keys, node.values, strict=True)
            for part in (key, value) if part is not None]
    else:
        children = list(ast.iter_child_nodes(node))
    rebound: set[str] = set()
    for child in children:
        child_may_raise = _b62_eval_may_fail(child)
        rebound.update(_b62_rebindings_before_raise(child))
        if child_may_raise:
            return rebound
    return rebound
def _b62_body_has_nonexception_exit(body: list[ast.stmt]) -> bool:
    for stmt in body:
        if _is_definition_boundary(stmt):
            continue
        if any(isinstance(node, (ast.Return, ast.Break, ast.Continue))
               for node in (stmt, *same_scope_dfs_nodes(stmt))):
            return True
    return False


class _B62FlowAnalyzer:
    def __init__(self, issues: list[DiagnoseIssue], report: bool = True) -> None:
        self.issues = issues
        self.seen: set[tuple[str, int]] = set()
        self._report = report
        self.unbound_augassigns: set[tuple[int, str]] | None = None
        self._exception_exit_sinks: list[dict[str, int] | None] = []
        self._loop_control_sinks: list[dict[str, list[dict[str, int]]]] = []
    def _record_exception_exit(self, deleted: dict[str, int]) -> None:
        if not self._exception_exit_sinks:
            return
        sink = self._exception_exit_sinks[-1]
        if sink is None:
            sink = {}
            self._exception_exit_sinks[-1] = sink
        merged = _b62_union_states([sink, deleted])
        sink.clear()
        sink.update(merged)
    def _merge(self, paths: list[dict[str, int]]) -> dict[str, int]:
        return _b62_merge_states(paths)
    def _state_scanner(self):
        scanner = copy.copy(self)
        scanner.issues = []
        scanner.seen = set()
        scanner._report = False
        scanner._exception_exit_sinks = []
        scanner._loop_control_sinks = []
        return scanner
    def _scan_node(self, node: ast.AST, deleted: dict[str, int]) -> None:
        if _b62_may_raise(node):
            exception_deleted = dict(deleted)
            for name in _b62_rebindings_before_raise(node):
                exception_deleted.pop(name, None)
            self._record_exception_exit(exception_deleted)
        if (self.unbound_augassigns is not None
                and isinstance(node, ast.AugAssign)
                and isinstance(node.target, ast.Name)
                and node.target.id in deleted):
            self.unbound_augassigns.add((id(node), node.target.id))
        if self._report:
            _b62_report_deleted_refs(node, deleted, self.issues, self.seen)
        _b62_drop_rebound(node, deleted)
    def _record_loop_control(self, stmt: ast.stmt,
                             deleted: dict[str, int]) -> None:
        if not self._loop_control_sinks:
            return
        kind = 'break' if isinstance(stmt, ast.Break) else 'continue'
        self._loop_control_sinks[-1][kind].append(dict(deleted))
    def scan_body(self, body: list[ast.stmt],
                  deleted: dict[str, int]) -> dict[str, int]:
        for stmt in body:
            deleted = self.scan_statement(stmt, deleted)
            if not _b62_statement_falls_through(stmt):
                break
        return deleted
    def _scan_loop_body(self, body: list[ast.stmt],
                        deleted: dict[str, int],
                        ) -> tuple[dict[str, int], dict[str, list[dict[str, int]]]]:
        control: dict[str, list[dict[str, int]]] = {'break': [], 'continue': []}
        self._loop_control_sinks.append(control)
        try:
            body_exit = self.scan_body(body, deleted)
        finally:
            self._loop_control_sinks.pop()
        return body_exit, control
    def scan_statement(self, stmt: ast.stmt,
                       deleted: dict[str, int]) -> dict[str, int]:
        if isinstance(stmt, (ast.Break, ast.Continue)):
            self._record_loop_control(stmt, deleted)
        if isinstance(stmt, ast.Raise):
            self._record_exception_exit(deleted)
        if isinstance(stmt, ast.Delete):
            for tgt in flatten_unpack_targets(stmt.targets):
                bindings = tuple(iter_target_bindings(tgt))
                if (_b62_may_raise(tgt) or any(
                        name in deleted for name, _line, _col in bindings)):
                    self._record_exception_exit(deleted)
                if self._report:
                    _b62_report_deleted_refs(tgt, deleted, self.issues, self.seen)
                for name, line, _col in bindings:
                    if name in deleted:
                        if self._report:
                            _append_unique(self.issues, self.seen, (name, line), _issue(
                                'B62', DiagnoseSeverity.ERROR,
                                f"名 '{name}' 第 {deleted[name]} 行 del 删除后再次 del："
                                f"执行即 NameError",
                                line, '同一名字只能 del 一次；需复用请先重新赋值'))
                        continue
                    deleted[name] = line
            return deleted
        if isinstance(stmt, ast.If):
            return self._scan_if(stmt, deleted)
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            return self._scan_for(stmt, deleted)
        if isinstance(stmt, ast.While):
            return self._scan_while(stmt, deleted)
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            return self._scan_with(stmt, deleted)
        if isinstance(stmt, (ast.Try, TRY_STAR)):
            return self._scan_try(stmt, deleted)
        if isinstance(stmt, ast.Match):
            return self._scan_match(stmt, deleted)
        self._scan_node(stmt, deleted)
        return deleted
    def _scan_if(self, stmt: ast.If,
                 deleted: dict[str, int]) -> dict[str, int]:
        self._scan_node(stmt.test, deleted)
        constant = _b62_const_truth(stmt.test)
        if constant is not None:
            taken = stmt.body if constant else stmt.orelse
            return self.scan_body(taken, deleted)
        body_exit = self.scan_body(stmt.body, dict(deleted))
        else_exit = self.scan_body(stmt.orelse, dict(deleted))
        if not _b62_branch_falls_through(stmt.body):
            return else_exit
        if not _b62_branch_falls_through(stmt.orelse):
            return body_exit
        return self._merge([body_exit, else_exit])
    def _loop_following_state(self, normal_entries: list[dict[str, int]],
                              orelse: list[ast.stmt],
                              break_entries: list[dict[str, int]],
                              deleted: dict[str, int]) -> dict[str, int]:
        following = list(break_entries)
        if normal_entries:
            else_exit = self.scan_body(
                orelse, self._merge(normal_entries))
            if _b62_branch_falls_through(orelse):
                following.append(else_exit)
        if not following:
            return deleted
        return self._merge(following)
    def _scan_for(self, stmt: ast.For | ast.AsyncFor,
                  deleted: dict[str, int]) -> dict[str, int]:
        self._scan_node(stmt.iter, deleted)
        if _b62_definitely_empty_iter(stmt.iter):
            return self.scan_body(stmt.orelse, deleted)
        body_entry = dict(deleted)
        self._scan_node(stmt.target, body_entry)
        body_exit, control = self._scan_loop_body(stmt.body, body_entry)
        body_falls = _b62_branch_falls_through(stmt.body)
        iteration_exits = ([body_exit] if body_falls else [])
        iteration_exits.extend(control['continue'])
        if (_b62_definitely_multiple_iter(stmt.iter)
                and _b62_repeat_scan_safe(stmt.body) and iteration_exits):
            repeat_entry = self._merge(iteration_exits)
            self._scan_node(stmt.target, repeat_entry)
            _repeat_exit, repeat_control = self._scan_loop_body(
                stmt.body, repeat_entry)
            control['break'].extend(repeat_control['break'])
        normal_entries = list(iteration_exits)
        if not _b62_definitely_nonempty_iter(stmt.iter):
            normal_entries.append(dict(deleted))
        return self._loop_following_state(
            normal_entries, stmt.orelse, control['break'], deleted)
    def _scan_while(self, stmt: ast.While,
                    deleted: dict[str, int]) -> dict[str, int]:
        self._scan_node(stmt.test, deleted)
        constant = _b62_const_truth(stmt.test)
        if constant is False:
            return self.scan_body(stmt.orelse, deleted)
        body_exit, control = self._scan_loop_body(stmt.body, dict(deleted))
        body_falls = _b62_branch_falls_through(stmt.body)
        iteration_exits = ([body_exit] if body_falls else [])
        iteration_exits.extend(control['continue'])
        if iteration_exits:
            repeat_entry = self._merge(iteration_exits)
            self._scan_node(stmt.test, repeat_entry)
            if constant is True and _b62_repeat_scan_safe(stmt.body):
                _repeat_exit, repeat_control = self._scan_loop_body(
                    stmt.body, repeat_entry)
                control['break'].extend(repeat_control['break'])
        normal_entries = [] if constant is True else [dict(deleted)]
        if constant is not True:
            normal_entries.extend(iteration_exits)
        return self._loop_following_state(
            normal_entries, stmt.orelse, control['break'], deleted)
    def _scan_with(self, stmt: ast.With | ast.AsyncWith,
                   deleted: dict[str, int]) -> dict[str, int]:
        for item in stmt.items:
            self._scan_node(item.context_expr, deleted)
            if item.optional_vars is not None:
                self._scan_node(item.optional_vars, deleted)
        return self.scan_body(stmt.body, deleted)
    def _loop_control_bookmark(self, finalbody: list[ast.stmt]):
        if not finalbody or not self._loop_control_sinks:
            return None
        sink = self._loop_control_sinks[-1]
        return sink, {kind: len(sink[kind])
                      for kind in ('break', 'continue')}
    def _scan_finalbody(self, finalbody: list[ast.stmt],
                        merged: dict[str, int], bookmark) -> None:
        pending: dict[str, list[dict[str, int]]] = {}
        sink = None
        if bookmark is not None:
            sink, starts = bookmark
            for kind, start in starts.items():
                pending[kind] = sink[kind][start:]
                del sink[kind][start:]
        self.scan_body(finalbody, dict(merged))
        if sink is None or not _b62_branch_falls_through(finalbody):
            return
        for kind, states in pending.items():
            for state in states:
                sink[kind].append(self._state_scanner().scan_body(
                    finalbody, dict(state)))
    def _scan_try(self, stmt: ast.AST,
                  deleted: dict[str, int]) -> dict[str, int]:
        loop_control_bookmark = self._loop_control_bookmark(stmt.finalbody)
        exception_exit_state: dict[str, int] | None = None
        body_may_raise = _b62_body_may_raise(stmt.body)
        self._exception_exit_sinks.append(exception_exit_state)
        try:
            normal_exit = self.scan_body(stmt.body, dict(deleted))
            exception_exit_state = self._exception_exit_sinks[-1]
        finally:
            self._exception_exit_sinks.pop()
        if body_may_raise and exception_exit_state is None:
            exception_exit_state = dict(deleted)
        normal_falls = _b62_branch_falls_through(stmt.body)
        if normal_falls:
            normal_exit = self.scan_body(stmt.orelse, normal_exit)
            normal_falls = _b62_branch_falls_through(stmt.orelse)
        paths = []
        if (normal_falls or not stmt.handlers or exception_exit_state is None
                or _b62_body_has_nonexception_exit(stmt.body)):
            paths.append((normal_exit, normal_falls))
        if exception_exit_state is not None:
            for handler in stmt.handlers:
                handler_exit = self._scan_handler(
                    handler, dict(exception_exit_state))
                paths.append((
                    handler_exit, _b62_branch_falls_through(handler.body)))
            catches_all = (isinstance(stmt, ast.Try)
                           and any(handler.type is None
                                   for handler in stmt.handlers))
            if not catches_all:
                paths.append((dict(exception_exit_state), False))
        merged = _b62_union_states([state for state, _falls in paths])
        self._scan_finalbody(stmt.finalbody, merged, loop_control_bookmark)
        following = [state for state, falls in paths if falls]
        if not following:
            return deleted
        following_state = self._merge(following)
        return self._state_scanner().scan_body(stmt.finalbody, following_state)
    def _scan_handler(self, handler: ast.ExceptHandler,
                      deleted: dict[str, int]) -> dict[str, int]:
        if handler.type is not None:
            self._scan_node(handler.type, deleted)
        previous_delete = deleted.get(handler.name) if handler.name else None
        if handler.name:
            deleted.pop(handler.name, None)
        handler_exit = self.scan_body(handler.body, deleted)
        if handler.name:
            cleanup_line = getattr(handler, 'end_lineno', None) or handler.lineno
            implicit_delete = (previous_delete if previous_delete is not None
                               else cleanup_line)
            handler_exit[handler.name] = handler_exit.get(
                handler.name, implicit_delete)
        return handler_exit
    def _scan_match(self, stmt: ast.Match,
                    deleted: dict[str, int]) -> dict[str, int]:
        self._scan_node(stmt.subject, deleted)
        exits: list[dict[str, int]] = []
        exhaustive = False
        for case in stmt.cases:
            case_entry = dict(deleted)
            self._scan_node(case.pattern, case_entry)
            for name in iter_pattern_capture_names(case.pattern):
                case_entry.pop(name, None)
            if case.guard is not None:
                self._scan_node(case.guard, case_entry)
            case_exit = self.scan_body(case.body, case_entry)
            if _b62_branch_falls_through(case.body):
                exits.append(case_exit)
            if case.guard is None and _b62_irrefutable_pattern(case.pattern):
                exhaustive = True
                break
        if not exhaustive:
            exits.append(dict(deleted))
        if not exits:
            return deleted
        return self._merge(exits)
class _B18FlowAnalyzer(_B62FlowAnalyzer):
    def __init__(self) -> None:
        super().__init__([], report=False)
        self.unbound_augassigns = set()
    def _merge(self, paths: list[dict[str, int]]) -> dict[str, int]:
        return _b62_union_states(paths)
def detect_b62_del_then_reference(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _annotation_analysis_tree(tree)
    if tree is None:
        return []
    issues = []
    analyzer = _B62FlowAnalyzer(issues)
    for node in tree_nodes(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            analyzer.scan_body(node.body, {})
    return _finish('B62 del 后引用', issues, filepath)
GATE_DETECTORS: dict[str, Any] = {
    "B06": detect_b06_unused_variable,
    "B11": detect_b11_late_binding_closure,
    "B18": detect_b18_unbound_local,
    "B19": detect_b19_shadow_builtin,
    "B27": detect_b27_loop_var_shadow,
    "B62": detect_b62_del_then_reference,
}

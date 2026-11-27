from __future__ import annotations

import ast
import difflib as _dl
import logging
import os
import re
import sys
from dataclasses import dataclass, field
from importlib import import_module, util
from operator import itemgetter
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_bindings import (
    binding_names_of,
    enclosing_scope_binds,
    expr_binds,
)
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    _type_checking_guard_node_polarities,
    build_parent_map,
    collect_docstring_node_ids,
    definition_binding_name,
    definition_time_exprs,
    import_binds_of,
    is_star_import,
    iter_arg_nodes,
    iter_docstring_nodes,
    iter_own_scope,
    module_postpones_annotations,
    node_position,
    subtree_node_ids,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_source_core import (
    FRAME_BOUNDARY_NODES,
    aligned_source_lines,
    coerce_source_text,
    extract_code_lines,
    parse_py_file,
    physical_docstring_lines,
    read_source_with_fingerprint,
    safe_source_line,
    suggest,
)
from jwsgj.diag_shared_source_scan import (
    NOQA_ANY_RE,
    get_code_snippet,
    has_noqa,
    is_import_like_line,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    PatternFinding,
    dedupe_findings,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    CAT_MAINTAINABILITY,
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    SPLIT_SAFETY_DIMENSION,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    'ModuleMissingImportDetector',
    'check_IM01',
    'check_IM02',
    'check_IM04',
    'check_IM05',
    'check_PX02',
    'check_PX05',
    'check_SL01',
    'check_SL05',
    'check_UC01',
]
_log.info("diag_wiring_imports 编写时 preflight 规则族已加载: %d 项导出",
          len(__all__))
_IM_DIMENSION = "import"
_PX_DIMENSION = "project"
_SPLIT_DIMENSION = SPLIT_SAFETY_DIMENSION
_IM_SCOPE_FRAMES = FRAME_BOUNDARY_NODES
def _has_mixed_indentation(source: str) -> bool:
    has_tab = False
    has_space = False
    for line in source.splitlines():
        prefix = line[:len(line) - len(line.lstrip(' \t'))]
        has_tab |= '\t' in prefix
        has_space |= ' ' in prefix
    return has_tab and has_space
def _collect_fstring_template_fragments(tree: Any) -> set:
    ids: set = set()
    for joined in walk_nodes(tree):
        if isinstance(joined, ast.JoinedStr) and any(
                isinstance(v, ast.FormattedValue) for v in joined.values):
            ids.update(id(v) for v in joined.values
                       if isinstance(v, ast.Constant))
    return ids
class _PxReportFrame(NamedTuple):
    rule_id: str
    severity: str
    rule_ref: str
_PX02_FRAME = _PxReportFrame("PX-02", "P2", "C11")
_PX05_FRAME = _PxReportFrame("PX-05", "P1", "C3")
def _px_report(issues: list, source: Any, filepath: Any, node: ast.AST,
               frame: _PxReportFrame,
               spec: tuple[str, str, str]) -> None:
    title, description, suggestion = spec
    issues.append(DiagnoseFinding(
        id=frame.rule_id, severity=frame.severity, dimension=_PX_DIMENSION,
        file=filepath, line=node.lineno,
        title=title,
        description=description,
        code_snippet=extract_code_lines(source, node.lineno),
        suggestion=suggestion,
        rule_ref=frame.rule_ref,
    ))
def _px02_has_multiline_mixed_indent(text: str) -> bool:
    return "\n" in text and _has_mixed_indentation(text)
def _px02_const_is_risky(val: str) -> bool:
    return (any(marker in val for marker in ("{", "%", ".format"))
            and _px02_has_multiline_mixed_indent(val))
def _px02_fstring_template_text(node: ast.JoinedStr) -> str | None:
    if not any(isinstance(v, ast.FormattedValue) for v in node.values):
        return None
    return "".join(
        v.value for v in node.values
        if isinstance(v, ast.Constant) and isinstance(v.value, str))
def check_PX02(tree: Any, source_lines: Any, filepath: Any) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    source = coerce_source_text(source_lines)
    docstring_node_ids = collect_docstring_node_ids(tree)
    fstring_fragment_ids = _collect_fstring_template_fragments(tree)
    type_checking_ids = type_checking_body_node_ids(tree)
    for node in walk_nodes(tree):
        if id(node) in type_checking_ids:
            continue
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            _px02_scan_const_channel(
                issues, source, filepath, node,
                docstring_node_ids, fstring_fragment_ids)
        elif isinstance(node, ast.JoinedStr):
            _px02_scan_fstring_channel(
                issues, source, filepath, node)
    return issues
def _px02_scan_const_channel(issues: list, source: str, filepath: Any,
                             node: ast.Constant,
                             docstring_node_ids: set[int],
                             fstring_fragment_ids: set) -> None:
    if id(node) in fstring_fragment_ids or id(node) in docstring_node_ids:
        return
    if _px02_const_is_risky(node.value):
        _px_report(
            issues, source, filepath, node, _PX02_FRAME,
            ("multiline string with mixed indentation (C11 risk)",
             "多行字符串模板中存在缩进不一致,在做字符串替换时可能导致缩进错误.",
             '根因: 多行字符串模板中存在缩进不一致,在做字符串替换时可能导致缩进错误。该问题属于代码模式类别。\n修复策略: 使用repr()确认精确内容后再做替换,不要凭肉眼推断缩进.\n参考标准: PEP 8 / pylint / SonarQube'),
        )
def _px02_scan_fstring_channel(issues: list, source: str, filepath: Any,
                               node: ast.JoinedStr) -> None:
    tpl = _px02_fstring_template_text(node)
    if tpl is not None and _px02_has_multiline_mixed_indent(tpl):
        _px_report(
            issues, source, filepath, node, _PX02_FRAME,
            ("multiline f-string template with mixed indentation (C11 risk)",
             "f-string 模板中存在缩进不一致,占位符替换时可能导致缩进错误.",
             '根因: f-string 模板中存在缩进不一致,占位符替换时可能导致缩进错误。该问题属于代码模式类别。\n修复策略: 使用repr()确认精确内容后再做替换,不要凭肉眼推断缩进.\n参考标准: PEP 8 / pylint / SonarQube'),
        )
def _iter_assign_target_leaves(target: Any):
    if isinstance(target, (ast.Tuple, ast.List)):
        for elt in target.elts:
            yield from _iter_assign_target_leaves(elt)
    elif isinstance(target, ast.Starred):
        yield from _iter_assign_target_leaves(target.value)
    else:
        yield target
def _iter_assign_target_value_pairs(node: Any):
    if isinstance(node, ast.Assign):
        top_pairs = [(t, node.value) for t in node.targets]
    elif isinstance(node, ast.AugAssign):
        top_pairs = [(node.target, node.value)]
    elif isinstance(node, ast.AnnAssign):
        top_pairs = [(node.target, node.value)] if node.target is not None else []
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        top_pairs = [(node.target, node.iter)]
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        top_pairs = [
            (item.optional_vars, item.context_expr)
            for item in node.items if item.optional_vars is not None
        ]
    else:
        top_pairs = []
    for _t, _v in top_pairs:
        yield from _iter_paired_target_values(_t, _v)
def _iter_paired_target_values(target: Any, value: Any):
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)):
        for _te, _ve in zip(target.elts, value.elts, strict=True):
            yield from _iter_paired_target_values(_te, _ve)
    else:
        for _leaf in _iter_assign_target_leaves(target):
            yield _leaf, value
def _binding_precedes_use(node: ast.AST, target: ast.AST) -> bool:
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                         ast.NamedExpr)):
        value = node.value
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        value = node.iter
    elif isinstance(node, ast.withitem):
        value = node.context_expr
    else:
        return True
    return value is None or all(target is not sub for sub in walk_nodes(value))
def _collect_non_module_execution_ids(tree: ast.AST) -> set:
    ids: set = set()
    deferred_frames = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    _stack: list = [(tree, False)]
    while _stack:
        node, in_frame = _stack.pop()
        for child in ast.iter_child_nodes(node):
            if in_frame:
                ids.add(id(child))
            _stack.append(
                (child, in_frame or isinstance(child, deferred_frames)))
    return ids
def _px05_with_call_ids(tree: ast.AST) -> set:
    with_exprs: set = set()
    for w in walk_nodes(tree):
        if not isinstance(w, (ast.With, ast.AsyncWith)):
            continue
        for item in w.items:
            pending = [item.context_expr]
            while pending:
                expr = pending.pop()
                if isinstance(expr, ast.Call):
                    with_exprs.add(id(expr))
                    continue
                if isinstance(expr, ast.IfExp):
                    pending.extend((expr.body, expr.orelse))
                elif isinstance(expr, ast.BoolOp):
                    pending.extend(expr.values)
                elif isinstance(expr, ast.NamedExpr):
                    pending.append(expr.value)
    return with_exprs
def _px05_sys_module_names(tree: ast.AST, tc_ids: set[int]) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if id(node) in tc_ids or not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name == "sys":
                names.add(alias.asname or "sys")
    return names
def _px05_redirect_names(tree: ast.AST, tc_ids: set[int]) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if (id(node) in tc_ids
                or not isinstance(node, ast.ImportFrom)
                or node.level > 0 or node.module != "contextlib"):
            continue
        for alias in node.names:
            if alias.name == "redirect_stdout":
                names.add(alias.asname or alias.name)
    return names
def _px05_contextlib_module_names(tree: ast.AST, tc_ids: set[int]) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if id(node) in tc_ids or not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name == "contextlib":
                names.add(alias.asname or "contextlib")
    return names
def _px05_is_stdout_attr_target(target: Any, sys_names: set[str]) -> bool:
    return (isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id in sys_names and target.attr == "stdout")
def _px05_is_stdout_restore_value(value: Any, sys_names: set[str]) -> bool:
    return (isinstance(value, ast.Attribute)
            and isinstance(value.value, ast.Name)
            and value.value.id in sys_names
            and value.attr == "__stdout__")
def _px05_report_redirect_call(issues: list, source: Any, filepath: Any,
                               node: ast.Call, redirect_names: set[str],
                               contextlib_names: set[str],
                               parents: dict[int, ast.AST]) -> None:
    func = node.func
    if isinstance(func, ast.Name) and func.id in redirect_names:
        if not _px05_is_imported_at(
                node, func.id, parents, "contextlib", "redirect_stdout"):
            return
        _px_report(
            issues, source, filepath, node, _PX05_FRAME,
            ("redirect_stdout used (affects global scope)",
             "contextlib.redirect_stdout影响范围不可控,可能干扰其他输出.",
             '根因: contextlib.redirect_stdout影响范围不可控,可能干扰其他输出。该问题属于代码模式类别。\n修复策略: 使用 StringIO() + sys.stdout 手动重定向和恢复.\n参考标准: PEP 8 / pylint / SonarQube'),
        )
    elif (isinstance(func, ast.Attribute)
          and func.attr == "redirect_stdout"
          and isinstance(func.value, ast.Name)
          and func.value.id in contextlib_names):
        if not _px05_is_imported_at(
                node, func.value.id, parents, "contextlib", None):
            return
        _px_report(
            issues, source, filepath, node, _PX05_FRAME,
            ("sys.stdout redirection detected",
             "全局stdout重定向影响范围不可控.",
             '根因: 全局stdout重定向影响范围不可控。该问题属于代码模式类别。\n修复策略: 使用 StringIO() 局部重定向.\n参考标准: PEP 8 / pylint / SonarQube'),
        )
def _px05_import_binding_state(node: ast.AST, name: str,
                               module_name: str,
                               from_symbol: str | None) -> bool | None:
    if not isinstance(node, (ast.Import, ast.ImportFrom)):
        return None
    state = None
    if isinstance(node, ast.Import):
        for alias in node.names:
            local = alias.asname or alias.name.split(".", 1)[0]
            if local == name:
                state = alias.name == module_name
    else:
        for alias in node.names:
            if (alias.asname or alias.name) == name:
                state = bool(
                    node.level == 0 and node.module == module_name
                    and from_symbol is not None and alias.name == from_symbol)
    return state
def _px05_definition_name_visible_at(
        def_node: ast.AST, target: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    cursor = target
    while cursor is not def_node:
        parent = parents.get(id(cursor))
        if parent is None:
            return True
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef))
                and cursor in parent.body):
            return True
        if isinstance(parent, ast.Lambda) and cursor is parent.body:
            return True
        cursor = parent
    return False
def _px05_scope_import_state(scope: ast.AST, name: str,
                             target: ast.AST, module_name: str,
                             from_symbol: str | None,
                             parents: dict[int, ast.AST],
                             *, include_later: bool = False) -> bool | None:
    target_pos = node_position(target)
    latest_pos = None
    state = None
    for child in iter_own_scope(
            scope, skip_lambda=False, skip_type_checking_body=True):
        lineno = getattr(child, "lineno", None)
        if child is target or lineno is None:
            continue
        pos = node_position(child)
        if not include_later and pos >= target_pos:
            continue
        is_import = isinstance(child, (ast.Import, ast.ImportFrom))
        event = _px05_import_binding_state(
            child, name, module_name, from_symbol)
        if not is_import:
            names: set[str] = set()
            _collect_binding_names(child, names)
            if (isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef))
                    and not _px05_definition_name_visible_at(
                        child, target, parents)):
                names.difference_update(definition_binding_name(child))
            if isinstance(child, FRAME_BOUNDARY_NODES):
                names |= enclosing_scope_binds(child)
            if isinstance(child, ast.Delete):
                for deleted in child.targets:
                    names |= binding_names_of(deleted)
            if name in names and _binding_precedes_use(child, target):
                event = False
        if event is None:
            continue
        if latest_pos is None or pos >= latest_pos:
            latest_pos, state = pos, event
    return state
def _px05_is_imported_at(node: ast.AST, name: str,
                         parents: dict[int, ast.AST], module_name: str,
                         from_symbol: str | None) -> bool:
    if name in _im_comprehension_bindings(parents, node):
        return False
    scope = _im_enclosing_scope(parents, node)
    cursor = node
    deftime_path = True
    runtime_path = False
    global_only = False
    function_frames = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    while scope is not None:
        current_deftime = False
        if isinstance(scope, FRAME_BOUNDARY_NODES):
            current_deftime = deftime_path and id(node) in subtree_node_ids(
                _definition_binding_exprs(scope, False))
        is_module = isinstance(scope, ast.Module)
        is_function = isinstance(scope, function_frames)
        skip_scope = ((global_only and not is_module)
                      or (isinstance(scope, ast.ClassDef)
                          and not deftime_path))
        redirected: set[str] = set()
        global_names: set[str] = set()
        if not is_module and not skip_scope:
            redirected, global_names = _im_scope_redirects(scope)
        if not skip_scope:
            state = _px05_scope_import_state(
                scope, name, cursor, module_name, from_symbol, parents,
                include_later=runtime_path)
            if state is not None:
                return state
            if is_function and not current_deftime:
                imports, local = _collect_func_scope_sets(
                    scope, include_exception_targets=True)
                if name in (imports | local) - redirected:
                    return False
            if not current_deftime and name in global_names:
                global_only = True
        if is_module:
            break
        if is_function and not current_deftime:
            runtime_path = True
            deftime_path = False
        elif isinstance(scope, ast.ClassDef) and not current_deftime:
            deftime_path = False
        cursor = scope
        scope = _im_enclosing_scope(parents, scope)
    return False
def check_PX05(tree: Any, source: Any, filepath: Any) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    with_exprs = _px05_with_call_ids(tree)
    _non_module_ids = _collect_non_module_execution_ids(tree)
    type_checking_ids = type_checking_body_node_ids(tree)
    parents = build_parent_map(tree)
    unevaluated_annotation_ids = (
        subtree_node_ids(list(_annotation_exprs(tree)))
        if module_postpones_annotations(tree)
        else _im_function_local_annotation_ids(tree, parents))
    sys_names = _px05_sys_module_names(tree, type_checking_ids)
    redirect_names = _px05_redirect_names(tree, type_checking_ids)
    contextlib_names = _px05_contextlib_module_names(tree, type_checking_ids)
    for node in walk_nodes(tree):
        if (id(node) in type_checking_ids
                or id(node) in unevaluated_annotation_ids):
            continue
        if isinstance(node, ast.Call):
            if id(node) in with_exprs:
                continue
            _px05_report_redirect_call(
                issues, source, filepath, node, redirect_names,
                contextlib_names, parents)
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                               ast.For, ast.AsyncFor,
                               ast.With, ast.AsyncWith)):
            _px05_scan_assign_targets(
                issues, source, filepath, node, _non_module_ids, sys_names,
                tree, parents)
    return issues
def _px05_scan_assign_targets(issues: list, source: Any, filepath: Any,
                              node: Any, non_module_ids: set,
                              sys_names: set[str], tree: ast.AST,
                              parents: dict[int, ast.AST]) -> None:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return
    if id(node) in non_module_ids:
        return
    prior_bindings: set[str] = (
        expr_binds(node.value)
        if isinstance(node, (ast.Assign, ast.AnnAssign)) else set())
    for _t, _val in _iter_assign_target_value_pairs(node):
        is_stdout_target = _px05_is_stdout_attr_target(_t, sys_names)
        target_name = _t.value.id if is_stdout_target else ""
        value_bindings = expr_binds(_val)
        shadowed = target_name in prior_bindings or (
            not isinstance(node, ast.AugAssign) and target_name in value_bindings)
        prior_bindings |= binding_names_of(_t) | value_bindings
        if not is_stdout_target or shadowed:
            continue
        if not _px05_is_imported_at(
                node, target_name, parents, "sys", None):
            continue
        if (isinstance(node, (ast.Assign, ast.AnnAssign))
                and _px05_is_stdout_restore_value(_val, sys_names)
                and _px05_is_imported_at(
                    node, _val.value.id, parents, "sys", None)):
            continue
        _px_report(
            issues, source, filepath, node, _PX05_FRAME,
            ("sys.stdout global reassignment",
             "模块级 sys.stdout 直接赋值在 import 时全局生效,影响所有导入方的输出.",
             '根因: 模块级 sys.stdout 赋值是进程级全局重定向。该问题属于代码模式类别。\n修复策略: 改用 contextlib.redirect_stdout 上下文管理器限定作用域,或移入函数内在 finally 中恢复原值.\n参考标准: PEP 8 / pylint / SonarQube'),
        )
        break
_IM_STDLIB_MODULES = frozenset(sys.stdlib_module_names)
def _im_enclosing_scope(parents: dict[int, ast.AST],
                        node: ast.AST) -> ast.AST | None:
    parent = parents.get(id(node))
    while parent is not None and not isinstance(
            parent, (ast.Module, *_IM_SCOPE_FRAMES)):
        parent = parents.get(id(parent))
    return parent
def _im_scope_redirects(scope: ast.AST) -> tuple[set[str], set[str]]:
    redirected: set[str] = set()
    global_names: set[str] = set()
    for child in iter_own_scope(
            scope, skip_lambda=True, skip_type_checking_body=True):
        if isinstance(child, ast.Global):
            global_names.update(child.names)
        if isinstance(child, (ast.Global, ast.Nonlocal)):
            redirected.update(child.names)
    return redirected, global_names
def _im_function_local_annotation_ids(
        tree: ast.AST, parents: dict[int, ast.AST]) -> set[int]:
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.AnnAssign):
            continue
        scope = _im_enclosing_scope(parents, node)
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            ids.update(subtree_node_ids([node.annotation]))
    return ids
def _im_exception_target_bindings(parents: dict[int, ast.AST],
                                   node: ast.AST) -> set[str]:
    bound: set[str] = set()
    cursor = node
    while True:
        parent = parents.get(id(cursor))
        if parent is None:
            return bound
        if (isinstance(parent, ast.ExceptHandler) and parent.name
                and any(cursor is stmt for stmt in parent.body)):
            bound.add(parent.name)
        cursor = parent
class _ImportScopeResolver:
    def __init__(self, tree: ast.Module, module_bound: set) -> None:
        self.tree = tree
        self.module_bound = module_bound
        self.future_annotations = module_postpones_annotations(tree)
        self.parents = build_parent_map(tree)
        self.type_checking_body_ids = type_checking_body_node_ids(tree)
        self.func_cache: dict[int, set] = {}
        self.redirect_cache: dict[int, tuple[set[str], set[str]]] = {}
        self.deftime_cache: dict[int, set[int]] = {}
        self.unevaluated_annotation_ids = (
            subtree_node_ids(list(_annotation_exprs(tree)))
            if self.future_annotations
            else _im_function_local_annotation_ids(tree, self.parents))
    def visible(self, node: ast.AST) -> set:
        return (self._frame_bindings(node)
                | _im_comprehension_bindings(self.parents, node)
                | _im_exception_target_bindings(self.parents, node))
    def _in_definition_time(self, frame: ast.AST, node: ast.AST) -> bool:
        ids = self.deftime_cache.get(id(frame))
        if ids is None:
            ids = subtree_node_ids(
                _definition_binding_exprs(frame, self.future_annotations))
            self.deftime_cache[id(frame)] = ids
        return id(node) in ids
    def _redirects(self, frame: ast.AST) -> tuple[set[str], set[str]]:
        cached = self.redirect_cache.get(id(frame))
        if cached is None:
            cached = _im_scope_redirects(frame)
            self.redirect_cache[id(frame)] = cached
        return cached
    def _func_bindings(self, frame: ast.AST) -> set:
        cached = self.func_cache.get(id(frame))
        if cached is None:
            imports, local = _collect_func_scope_sets(
                frame, include_exception_targets=False)
            redirected, _global_names = self._redirects(frame)
            cached = (imports | local) - redirected
            self.func_cache[id(frame)] = cached
        return cached
    def _frame_bindings(self, node: ast.AST) -> set:
        bound: set = set()
        cursor: ast.AST = node
        deftime_path = True
        module_full = False
        frame = _im_enclosing_scope(self.parents, node)
        while frame is not None and not isinstance(frame, ast.Module):
            if isinstance(frame, ast.ClassDef):
                if deftime_path:
                    if _im_class_scope_visible_at(self.parents, frame, node):
                        bound |= _collect_scope_bindings_before(
                            frame, cursor,
                            future_annotations=self.future_annotations,
                            parents=self.parents)
                    if not self._in_definition_time(frame, node):
                        deftime_path = False
                cursor = frame
                frame = _im_enclosing_scope(self.parents, frame)
                continue
            if deftime_path and self._in_definition_time(frame, node):
                bound |= _collect_scope_bindings_before(
                    frame, cursor,
                    future_annotations=self.future_annotations,
                    parents=self.parents)
            elif deftime_path and cursor is not node:
                bound |= _collect_scope_bindings_before(
                    frame, cursor,
                    future_annotations=self.future_annotations,
                    parents=self.parents)
                bound |= {arg.arg for arg in iter_arg_nodes(frame.args)}
                _redirected, global_names = self._redirects(frame)
                if isinstance(node, ast.Name):
                    if node.id in global_names:
                        module_full = True
                        break
                    if node.id in self._func_bindings(frame):
                        return bound
                deftime_path = False
                module_full = True
            else:
                _redirected, global_names = self._redirects(frame)
                if isinstance(node, ast.Name) and node.id in global_names:
                    imports, local = _collect_func_scope_sets(
                        frame, include_exception_targets=False)
                    bound |= (imports | local) & global_names
                    module_full = True
                    break
                bound |= self._func_bindings(frame)
                deftime_path = False
                module_full = True
            cursor = frame
            frame = _im_enclosing_scope(self.parents, frame)
        if module_full:
            bound |= self.module_bound
        else:
            bound |= _collect_scope_bindings_before(
                self.tree, node,
                future_annotations=self.future_annotations,
                parents=self.parents)
        return bound
_IM_COMPREHENSION_NODES = COMP_SCOPE_NODES
def _im_comprehension_bindings(parents: dict[int, ast.AST],
                               node: ast.AST) -> set:
    path: list[ast.AST] = []
    cursor: ast.AST | None = node
    while cursor is not None:
        path.append(cursor)
        cursor = parents.get(id(cursor))
    bound: set = set()
    for index, ancestor in enumerate(path):
        if not isinstance(ancestor, _IM_COMPREHENSION_NODES):
            continue
        generators = ancestor.generators
        visible_count = len(generators)
        child = path[index - 1] if index else None
        if isinstance(child, ast.comprehension):
            generator_index = next(
                (i for i, generator in enumerate(generators)
                 if generator is child), -1)
            if generator_index >= 0:
                visible_count = generator_index + 1
                if id(node) in subtree_node_ids([child.iter]):
                    visible_count = generator_index
        for generator in generators[:visible_count]:
            bound |= binding_names_of(generator.target)
    return bound
def _im_class_scope_visible_at(parents: dict[int, ast.AST],
                               class_node: ast.ClassDef,
                               node: ast.AST) -> bool:
    cursor: ast.AST | None = node
    while cursor is not class_node:
        parent = parents.get(id(cursor))
        if parent is None:
            return True
        if isinstance(parent, _IM_COMPREHENSION_NODES):
            generators = parent.generators
            if (not generators
                    or id(node) not in subtree_node_ids(
                        [generators[0].iter])):
                return False
        cursor = parent
    return True
def _own_annotation_exprs(node: ast.AST):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        for arg in iter_arg_nodes(node.args):
            if arg.annotation is not None:
                yield arg.annotation
        if node.returns is not None:
            yield node.returns
    elif isinstance(node, ast.AnnAssign):
        yield node.annotation
def _annotation_exprs(tree: ast.AST):
    for node in walk_nodes(tree):
        yield from _own_annotation_exprs(node)
def check_IM01(tree: Any, source: Any, filepath: Any) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    if _im_has_star_import(tree):
        _log.debug("[IM-01] 存在 import * 导入，绑定集不可枚举，跳过: %s", filepath)
        return issues
    module_bound = _collect_module_bindings(
        tree, include_exception_targets=False)
    resolver = _ImportScopeResolver(tree, module_bound)
    reported: set = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Name)
                and isinstance(node.ctx, ast.Load)
                and id(node) not in resolver.unevaluated_annotation_ids
                and id(node) not in resolver.type_checking_body_ids
                and node.id in _IM_STDLIB_MODULES
                and node.id not in reported):
            continue
        if node.id in resolver.visible(node):
            continue
        name = node.id
        reported.add(name)
        issues.append(_im01_make_issue(name, node, source, filepath))
    return issues
def _im01_make_issue(name: str, node: ast.Name, source: Any,
                     filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="IM-01", severity="P0", dimension=_IM_DIMENSION,
        file=filepath, line=node.lineno,
        title=f"引用未导入的标准库模块 '{name}'",
        description=(f"模块 '{name}' 被引用但文件内未 import 且未定义同名对象, "
                     "运行时触发 NameError. 常见成因: 批量替换/编辑意外移除 import 行."),
        code_snippet=extract_code_lines(source, node.lineno),
        suggestion=("根因: 模块被引用但未导入, 运行时 NameError。该问题属于导入卫生类别。\n"
                    f"修复策略: 在文件顶部添加 import {name}\n参考标准: PEP 8 / pylint E0601"),
        rule_ref="IM-01/GF-09 关键导入意外移除",
    )
def check_IM02(tree: Any, source: Any, filepath: Any) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    type_checking_ifs = {
        node_id
        for node_id, negated in _type_checking_guard_node_polarities(tree).items()
        if not negated}
    _im02_scan_stmts(
        tree.body, False, issues, source, filepath, type_checking_ifs)
    return issues
def _im02_scan_stmt(stmt: ast.stmt, in_loop: bool, issues: list,
                    source: Any, filepath: Any,
                    type_checking_ifs: set[int]) -> None:
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _im02_scan_stmts(
            stmt.body, False, issues, source, filepath, type_checking_ifs)
        return
    if isinstance(stmt, ast.ClassDef):
        _im02_scan_stmts(
            stmt.body, in_loop, issues, source, filepath, type_checking_ifs)
        return
    if isinstance(stmt, ast.If) and id(stmt) in type_checking_ifs:
        _im02_scan_stmts(
            stmt.orelse, in_loop, issues, source, filepath, type_checking_ifs)
        return
    now = in_loop or isinstance(stmt, (ast.For, ast.AsyncFor, ast.While))
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        if now:
            issues.append(_im02_make_issue(stmt, source, filepath))
        return
    if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
        _im02_scan_stmts(
            stmt.body, now, issues, source, filepath, type_checking_ifs)
        _im02_scan_stmts(
            stmt.orelse, in_loop, issues, source, filepath, type_checking_ifs)
        return
    for _field in ("body", "orelse", "finalbody", "handlers", "cases"):
        _child = getattr(stmt, _field, None)
        if isinstance(_child, list):
            _im02_scan_stmts(
                _child, now, issues, source, filepath, type_checking_ifs)
def _im02_scan_stmts(stmts: list, in_loop: bool, issues: list,
                     source: Any, filepath: Any,
                     type_checking_ifs: set[int]) -> None:
    for stmt in stmts:
        _im02_scan_stmt(
            stmt, in_loop, issues, source, filepath, type_checking_ifs)
def _im02_make_issue(stmt: ast.stmt, source: Any,
                     filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="IM-02", severity="P1", dimension=_IM_DIMENSION,
        file=filepath, line=stmt.lineno,
        title="import inside loop",
        description="循环内重复 import 有性能和语义问题.",
        code_snippet=extract_code_lines(source, stmt.lineno),
        suggestion=("根因: 循环内重复 import 有性能和语义问题。该问题属于导入卫生类别。\n"
                    "修复策略: 将 import 语句移至文件顶部\n参考标准: PEP 8 / isort / pylint W0611"),
        rule_ref="C5",
    )
_IM_LOGGING_SYMBOL_NAMES = frozenset({
    "logging", "LOG", "LOGGER",
    "getLogger", "basicConfig", "StreamHandler", "FileHandler",
    "_log", "logger",
})
def _im_has_star_import(tree: Any) -> bool:
    type_checking_ids = type_checking_body_node_ids(tree)
    return any(is_star_import(node) and id(node) not in type_checking_ids
               for node in walk_nodes(tree))
def _im04_find_import_hit(
        doc_lines: list[str], filepath: Any) -> tuple[int, str] | None:
    for i, text_line in enumerate(doc_lines):
        s = text_line.strip()
        if not s or s.startswith((">>>", "#")):
            continue
        if (is_import_like_line(s)
                and not _im04_is_exempt_hit(doc_lines, i, s, filepath)):
            return i, s
    return None
def _im04_is_exempt_hit(doc_lines: list[str], hit_rel: int,
                         hit_line_text: str, filepath: Any) -> bool:
    return (_im04_is_self_reference(hit_line_text, filepath)
            or _im04_has_example_marker(doc_lines, hit_rel))
def _im04_is_self_reference(hit_line_text: str, filepath: Any) -> bool:
    try:
        _fp = os.fspath(filepath)
    except TypeError:
        _fp = ""
    if isinstance(_fp, bytes):
        _fp = _fp.decode("utf-8", errors="replace")
    filename = _fp.replace("\\", "/").rsplit("/", 1)[-1]
    module_stem = os.path.splitext(filename)[0] if filename else ""
    return bool(module_stem
                and re.search(rf'\b{re.escape(module_stem)}\b', hit_line_text))
def _im04_has_example_marker(doc_lines: list[str], hit_rel: int) -> bool:
    prefix_text = "\n".join(doc_lines[:hit_rel + 1])
    return bool(re.search(r"用法|示例|样例|Usage|Example|>>>", prefix_text,
                          re.IGNORECASE))
def check_IM04(tree: Any, source: Any, filepath: Any) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    type_checking_ids = type_checking_body_node_ids(tree)
    for node, first in iter_docstring_nodes(tree):
        if id(first) in type_checking_ids:
            continue
        doc_lines = physical_docstring_lines(source, first)
        if doc_lines is None:
            continue
        hit = _im04_find_import_hit(doc_lines, filepath)
        if hit is None:
            continue
        hit_rel, hit_line_text = hit
        doc_start = getattr(first.value, "lineno", first.lineno)
        line_no = doc_start + hit_rel
        issues.append(_im04_make_issue(
            node, line_no, hit_line_text, source, filepath))
        break
    return issues
def _im04_make_issue(node: ast.AST, line_no: int, hit_line_text: str,
                    source: Any, filepath: Any) -> DiagnoseFinding:
    node_type = type(node).__name__
    node_name = getattr(node, "name", "") or "<module>"
    return DiagnoseFinding(
        id="IM-04", severity="P0", dimension=_IM_DIMENSION,
        file=filepath, line=line_no,
        title=f"docstring 内包含 import 语句 ({node_type}: {node_name})",
        description=(
            "docstring 中发现 import 语句形态的行,可能是代码被误放入三引号"
            "文档字符串,导致预期导入未执行.命中行: " + hit_line_text[:60]
        ),
        code_snippet=extract_code_lines(source, line_no),
        suggestion=("根因: 代码被误包进三引号文档字符串,导入未执行。该问题属于导入卫生类别。\n"
                    "修复策略: 检查该 docstring 是否误包含代码;若为示例代码应使用 >>> doctest"
                    " 标记或移出 docstring.\n参考标准: PEP 8 / pylint W0611"),
        rule_ref="1392",
    )
def check_IM05(tree: Any, source: Any, filepath: Any) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None or finding_scan_exempt(filepath):
        return issues
    if _im_has_star_import(tree):
        return issues
    module_bound = _collect_module_bindings(
        tree, include_exception_targets=False)
    hit = _im05_first_hit(tree, _ImportScopeResolver(tree, module_bound))
    if hit is not None:
        name, node = hit
        issues.append(_im05_make_issue(name, node, source, filepath))
    return issues
def _im05_first_hit(tree: ast.AST,
                    resolver: _ImportScopeResolver) -> tuple[str, ast.Name] | None:
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
            continue
        if (id(node) in resolver.unevaluated_annotation_ids
                or id(node) in resolver.type_checking_body_ids):
            continue
        name = node.id
        if name not in _IM_LOGGING_SYMBOL_NAMES:
            continue
        if name in _IM_STDLIB_MODULES:
            continue
        if name in resolver.visible(node):
            continue
        return name, node
    return None
def _im05_make_issue(name: str, node: ast.Name, source: Any,
                     filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="IM-05", severity="P0", dimension=_IM_DIMENSION,
        file=filepath, line=node.lineno,
        title=f"使用 logging 相关符号 '{name}' 但未导入 logging",
        description=("代码引用 logging 符号但文件内未 import logging 且无同名本地绑定, "
                     "运行时触发 NameError."),
        code_snippet=extract_code_lines(source, node.lineno),
        suggestion=("根因: logging 符号被引用但未导入。该问题属于导入卫生类别。\n"
                    "修复策略: 在文件顶部添加 import logging 或 from logging import getLogger\n"
                    "参考标准: PEP 8 / pylint E0601"),
        rule_ref="2600 NameError: name 'logging' is not defined / 1392",
    )
def _common_prefix_len(a: str, b: str) -> int:
    i = 0
    for c1, c2 in zip(a, b, strict=False):
        if c1.lower() == c2.lower():
            i += 1
        else:
            break
    return i
def _is_empty_str_const(node: Any) -> bool:
    return (
        isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and node.value == ""
    )
_SL01_CONTAINER_FORMS = (ast.List, ast.Set, ast.Dict, ast.Tuple,
                         ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)
_SL01_NOT_LITERAL = object()
def _sl01_literal_value(node: Any) -> Any:
    try:
        return ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError) as _swallowed_exc:
        _log.debug("_sl01_literal_value: 非字面量形态: %s",
                   type(_swallowed_exc).__name__)
        return _SL01_NOT_LITERAL
    except (MemoryError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_sl01_literal_value:resource_limit')
        return _SL01_NOT_LITERAL
def _is_provably_non_str_operand(node: Any) -> bool:
    if isinstance(node, _SL01_CONTAINER_FORMS):
        return True
    _value = _sl01_literal_value(node)
    return _value is not _SL01_NOT_LITERAL and not isinstance(_value, str)
def _scan_inputs(tree: Any, source_lines: Any) -> tuple[Any, list] | None:
    source = coerce_source_text(source_lines)
    if source is None:
        return None
    if isinstance(tree, ast.Module):
        tree_ast = tree
    else:
        try:
            tree_ast = ast.parse(source)
        except PARSE_DEGRADE_EXC:
            _log.warning(MSG_SYNTAX_ERROR_SKIP)
            return None
    return tree_ast, aligned_source_lines(source)
def _split_line_snippet(source_lines: list, line_no: int) -> str:
    return (source_lines[line_no - 1].strip()
            if 0 < line_no <= len(source_lines) else "")
def _is_provably_str_operand(node: Any) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, str)
    if isinstance(node, ast.JoinedStr):
        return True
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'str')
def _is_provably_nonempty_str_operand(node: Any) -> bool:
    if not _is_provably_str_operand(node):
        return False
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.JoinedStr):
        return any(isinstance(part, ast.Constant)
                   and isinstance(part.value, str) and bool(part.value)
                   for part in node.values)
    if node.keywords or len(node.args) != 1:
        return False
    value = _sl01_literal_value(node.args[0])
    return value is not _SL01_NOT_LITERAL and bool(str(value))
def _sl01_resolve_empty_segment(node: ast.Compare) -> tuple:
    operands = [node.left, *node.comparators]
    for i, op in enumerate(node.ops):
        if not isinstance(op, (ast.In, ast.NotIn)):
            continue
        left, right = operands[i], operands[i + 1]
        if _is_empty_str_const(left):
            if _is_provably_non_str_operand(right):
                continue
            truth = (isinstance(op, ast.In)
                     if _is_provably_str_operand(right) else None)
            return truth, left, True
        if _is_empty_str_const(right):
            if _is_provably_non_str_operand(left):
                continue
            if _is_provably_nonempty_str_operand(left):
                return isinstance(op, ast.NotIn), right, False
            return None, right, False
    return None, None, False
def check_SL01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    issues = []
    if not source_lines or finding_scan_exempt(filepath):
        return issues
    prepared = _scan_inputs(tree, source_lines)
    if prepared is None:
        return issues
    tree_ast, sl_lines = prepared
    type_checking_ids = type_checking_body_node_ids(tree_ast)
    for node in walk_nodes(tree_ast):
        if not isinstance(node, ast.Compare) or id(node) in type_checking_ids:
            continue
        _truth, _target, _left_empty = _sl01_resolve_empty_segment(node)
        if _target is None:
            continue
        line_no = _target.lineno
        code_line = _split_line_snippet(sl_lines, line_no)
        issues.append(_sl01_build_finding(
            filepath, line_no, _target.col_offset, code_line, _truth,
            left_empty=_left_empty))
    return issues
def _sl01_build_finding(filepath: Any, line_no: int, col_offset: int,
                        code_line: str, constant_truth: bool | None,
                        *, left_empty: bool = False) -> DiagnoseFinding:
    if constant_truth is None:
        _title = "空字符串成员条件退化"
        if left_empty:
            _desc = ("左操作数为空字符串时，结果取决于右操作数的运行时类型："
                     "字符串上恒为 True，列表/元组/集合上按元素判断。"
                     "该条件不是恒真或恒假，但通常不是预期的通用成员判断.")
        else:
            _desc = ("右操作数为空字符串时，结果取决于左操作数是否也为空："
                     "空左操作数的 in/not in 结果分别为 True/False，非空左操作数则相反。"
                     "该条件不是恒真或恒假，但通常不是预期的通用成员判断.")
        _sugg = ('根因: 空字符串成员条件退化，结果依赖操作数的空串边界与运行时类型。\n'
                 '修复策略: 明确空串边界；需要子串判断时同时检查左右操作数，或改为显式等值/真值判断.\n'
                 '参考标准: PEP 8 / pylint E1120/C1801')
    elif constant_truth:
        _title = "空字符串in条件恒True"
        _desc = ("当前空字符串成员条件可静态判定为 True：空字符串是任意字符串的子串，"
                 "且非空左操作数 not in 空字符串也为 True。可能导致错误分支.")
        _sugg = ('根因: 当前空字符串成员条件可静态判定为 True。该问题属于字符串/列表类别。\n'
                 '修复策略: 检查操作数与成员方向，改用显式的空串或真值判断.\n'
                 '参考标准: PEP 8 / pylint E1120/C1801')
    else:
        _title = "空字符串in条件恒False"
        _desc = ("当前空字符串成员条件可静态判定为 False：空字符串 not in 任意字符串为 False，"
                 "且非空左操作数 in 空字符串也为 False。可能是逻辑错误或永不可达的死分支.")
        _sugg = ('根因: 当前成员条件可静态判定为 False。该问题属于字符串/列表类别。\n'
                 '修复策略: 检查操作数与成员方向；死分支应删除或改用其他条件判断.\n'
                 '参考标准: PEP 8 / pylint E1120/C1801')
    return DiagnoseFinding(
        id="SL-01", severity="P0", dimension=_SPLIT_DIMENSION,
        file=filepath, line=line_no, col_offset=col_offset,
        title=_title, description=_desc, code_snippet=code_line,
        suggestion=_sugg, rule_ref="CS-174")
_SL05_BINDING_EXTRACTORS = (
    ((ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef),
     definition_binding_name),
    ((ast.Import, ast.ImportFrom), import_binds_of),
)
def _sl05_node_binding_names(node: ast.AST) -> set:
    for node_types, extract in _SL05_BINDING_EXTRACTORS:
        if isinstance(node, node_types):
            return extract(node)
    names: set = set()
    _collect_binding_names(node, names)
    return names
_SL05_ABSENT = object()
def _sl05_probe_attr(target_mod: Any, name: str, default: Any = None) -> Any:
    try:
        return getattr(target_mod, name, default)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_sl05_probe_attr:{type(_e).__name__}')
        return default
def _sl05_symbol_in_source(target_mod: Any, symbol: str) -> bool:
    try:
        origin = _sl05_probe_attr(target_mod, "__file__")
        if (not isinstance(origin, str) or not origin
                or not os.path.isfile(origin)):
            return False
        origin_src, _fingerprint = read_source_with_fingerprint(
            origin, strict=True)
        if origin_src is None:
            return False
        _tree = ast.parse(origin_src)
    except (OSError, *PARSE_DEGRADE_EXC) as _e:
        log_swallowed(__name__, _e,
                      context=f'_sl05_symbol_in_source:{type(_e).__name__}')
        return False
    top_level_names: set = set()
    for _node in ast.iter_child_nodes(_tree):
        top_level_names |= _sl05_node_binding_names(_node)
    return symbol in top_level_names
def _sl05_is_submodule(module_name: str, symbol: str) -> bool:
    try:
        return util.find_spec(f"{module_name}.{symbol}") is not None
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_sl05_is_submodule:{type(_e).__name__}')
        return False
def check_SL05(tree: Any, source_lines: Any, filepath: Any) -> Any:
    issues = []
    if not source_lines or finding_scan_exempt(filepath):
        return issues
    prepared = _scan_inputs(tree, source_lines)
    if prepared is None:
        return issues
    tree_ast, sl05_lines = prepared
    type_checking_ids = type_checking_body_node_ids(tree_ast)
    for node in walk_nodes(tree_ast):
        if id(node) in type_checking_ids:
            continue
        if isinstance(node, ast.ImportFrom):
            if node.module is None or node.level > 0:
                continue
            issues.extend(_sl05_check_importfrom(node, filepath, sl05_lines))
    return issues
def _sl05_check_importfrom(node: ast.ImportFrom, filepath: Any,
                           sl05_lines: list) -> list:
    findings = []
    target_mod = _sl05_resolve_target_module(node)
    if target_mod is None:
        return findings
    for alias in node.names:
        if alias.name == '*':
            continue
        if not _sl05_alias_is_residual(target_mod, node.module, alias.name):
            continue
        findings.append(_sl05_make_issue(
            node, alias.name, filepath, sl05_lines, target_mod))
    return findings
def _sl05_alias_is_residual(target_mod: Any, module_name: str | None,
                            alias_name: str) -> bool:
    if _sl05_probe_attr(target_mod, alias_name, _SL05_ABSENT) is not _SL05_ABSENT:
        return False
    if _sl05_is_submodule(module_name, alias_name):
        return False
    return not _sl05_symbol_in_source(target_mod, alias_name)
def _sl05_make_issue(node: ast.ImportFrom, alias_name: str, filepath: Any,
                     sl05_lines: list, target_mod: Any) -> DiagnoseFinding:
    candidates = _sl05_find_candidates(target_mod, alias_name)
    line_no = node.lineno
    return DiagnoseFinding(
        id="SL-05", severity="P0", dimension=_SPLIT_DIMENSION,
        file=filepath, line=line_no, col_offset=node.col_offset,
        title=f"残留导入: {node.module}.{alias_name} 不存在",
        description=(
            f"from {node.module} import {alias_name} — "
            f"符号 '{alias_name}' 在模块 '{node.module}' 中不存在."
            f"拆分文件后函数/变量迁移到新模块,导入语句未同步更新."
        ),
        code_snippet=_split_line_snippet(sl05_lines, line_no),
        suggestion=_sl05_build_suggestion(node.module, candidates),
        rule_ref="CS-178",
    )
def _sl05_resolve_target_module(node: ast.ImportFrom) -> Any | None:
    target_mod = sys.modules.get(node.module)
    if target_mod is not None:
        return target_mod
    try:
        return import_module(node.module)
    except Exception as e:  # noqa: BLE001
        _log.debug("[SL-05] 目标模块 %s 导入失败,跳过: %s", node.module, e)
        return None
def _sl05_find_candidates(target_mod: Any, alias_name: str) -> list:
    try:
        module_names = dir(target_mod)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_sl05_find_candidates:{type(_e).__name__}')
        return []
    _lowered = alias_name.lower()
    scored = []
    for name in module_names:
        ratio = _dl.SequenceMatcher(None, _lowered, name.lower()).ratio()
        if ratio > 0.25:
            scored.append((_common_prefix_len(alias_name, name), ratio, name))
    scored.sort(key=itemgetter(0, 1), reverse=True)
    return [name for _, _, name in scored]
def _sl05_build_suggestion(module_name: str, candidates: list) -> str:
    if len(candidates) == 1:
        return f'根因: 代码使用了不规范或有风险的实现方式。该问题属于代码质量类别。\n修复策略: 将导入修正为最相似的候选符号 {candidates[0]}。注意: 仅候选相似度极高且已由 AI 确认其语义等价时方可替换, 否则应人工补全缺失符号。\n参考标准: PEP 8 / pylint / SonarQube'
    if len(candidates) >= 2:
        return f"根因: 代码实现中存在代码质量方面的问题, 需要规范化处理。\n修复策略: 多个候选: {', '.join(candidates[:5])} — 需人工选择\n参考标准: PEP 8 / pylint / SonarQube"
    return f'根因: 代码实现中存在代码质量方面的问题, 需要规范化处理。\n修复策略: 模块 {module_name} 中无近似匹配,可能需要创建该符号\n参考标准: PEP 8 / pylint / SonarQube'
def _uc01_nonlocal_import_owner(
        scope: ast.AST, name: str,
        parents: dict[int, ast.AST]) -> ast.AST | None:
    owner = _im_enclosing_scope(parents, scope)
    while owner is not None and not isinstance(owner, ast.Module):
        if isinstance(owner, ast.ClassDef):
            owner = _im_enclosing_scope(parents, owner)
            continue
        redirected, global_names = _im_scope_redirects(owner)
        if name in global_names:
            return None
        if name not in redirected:
            imports, local = _collect_func_scope_sets(
                owner, include_exception_targets=True)
            if name in imports | local:
                return owner
        owner = _im_enclosing_scope(parents, owner)
    return None
def _uc01_collect_imports(
        tree: Any, tc_ids: set[int]) -> list[tuple[str, int, ast.AST | None]]:
    imports: list[tuple[str, int, ast.AST | None]] = []
    parents = build_parent_map(tree)
    scope_redirects: dict[int, tuple[set[str], set[str]]] = {}
    nonlocal_owners: dict[tuple[int, str], ast.AST | None] = {}
    for node in walk_nodes(tree):
        if id(node) in tc_ids:
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            scope = _im_enclosing_scope(parents, node)
            redirected: set[str] = set()
            global_names: set[str] = set()
            if scope is not None and not isinstance(scope, ast.Module):
                scope_key = id(scope)
                if scope_key not in scope_redirects:
                    scope_redirects[scope_key] = _im_scope_redirects(scope)
                redirected, global_names = scope_redirects[scope_key]
            nonlocal_names = redirected - global_names
            for name, line in _uc01_import_entries(node):
                if name in global_names:
                    owner = tree
                elif scope is not None and name in nonlocal_names:
                    owner_key = (id(scope), name)
                    if owner_key not in nonlocal_owners:
                        nonlocal_owners[owner_key] = _uc01_nonlocal_import_owner(
                            scope, name, parents)
                    owner = nonlocal_owners[owner_key] or scope
                else:
                    owner = scope
                imports.append((name, line, owner))
    return imports
def _uc01_import_entries(
        node: ast.Import | ast.ImportFrom) -> list[tuple[str, int]]:
    if isinstance(node, ast.ImportFrom) and node.module == '__future__':
        return []
    return [(name, node.lineno) for name in sorted(import_binds_of(node))]
def _uc01_dynamic_import_names(call: Any) -> set[str]:
    if not (isinstance(call.func, ast.Name)
            and call.func.id == '__import__' and call.args):
        return set()
    first = call.args[0]
    if isinstance(first, ast.Constant) and isinstance(first.value, str):
        root = first.value.split('.', 1)[0]
        return {root} if root else set()
    return set()
_UC01_ALL_APPEND_METHODS = frozenset({
    "append", "extend", "add", "insert", "update"})
def _uc01_dunder_all_names(tree: Any, *, own_scope: bool = False) -> set[str]:
    names: set[str] = set()
    nodes = (iter_own_scope(
        tree, skip_lambda=True, skip_type_checking_body=True,
        tc_polarities=_type_checking_guard_node_polarities(tree))
        if own_scope else walk_nodes(tree))
    for node in nodes:
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            targets = (node.targets if isinstance(node, ast.Assign)
                       else (node.target,))
            if (node.value is not None and any(
                    isinstance(target, ast.Name) and target.id == "__all__"
                    for target in targets)):
                names.update(
                    sub.value for sub in walk_nodes(node.value)
                    if isinstance(sub, ast.Constant)
                    and isinstance(sub.value, str))
        elif (isinstance(node, ast.Call)
              and isinstance(node.func, ast.Attribute)
              and isinstance(node.func.value, ast.Name)
              and node.func.value.id == "__all__"
              and node.func.attr in _UC01_ALL_APPEND_METHODS):
            names.update(
                sub.value for arg in node.args for sub in walk_nodes(arg)
                if isinstance(sub, ast.Constant)
                and isinstance(sub.value, str))
    return names
def _uc01_node_used_names(node: Any) -> set[str]:
    if isinstance(node, ast.Name) and not isinstance(node.ctx, ast.Store):
        return {node.id}
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        return {node.value.id}
    if isinstance(node, ast.Call):
        return _uc01_dynamic_import_names(node)
    return set()
_UC01_ANNOTATION_PREFIX_RE = re.compile(r"(?<![\w.])([A-Za-z_]\w*)\s*\.")
@dataclass(frozen=True)
class _UC01ForwardRefContext:
    literal_names: frozenset[str] = frozenset()
    module_names: frozenset[str] = frozenset()
_UC01_EMPTY_FORWARD_REF_CONTEXT = _UC01ForwardRefContext()
def _uc01_forward_ref_names(
        text: str,
        context: _UC01ForwardRefContext = _UC01_EMPTY_FORWARD_REF_CONTEXT,
    ) -> set[str]:
    names: set[str] = set()
    pending: list[str] = [text]
    seen: set[str] = set()
    while pending:
        value = pending.pop()
        if value in seen:
            continue
        seen.add(value)
        try:
            expr = ast.parse(value, mode='eval').body
        except PARSE_DEGRADE_EXC as _e:
            _log.debug("suppressed forward-ref parse failure: %s: %s",
                       type(_e).__name__, _e)
            names.update(_UC01_ANNOTATION_PREFIX_RE.findall(value))
            continue
        names.update(
            sub.id for sub in _uc01_forward_ref_nodes(expr, context)
            if isinstance(sub, ast.Name))
        pending.extend(_uc01_forward_ref_fragments(expr, context))
    return names
_UC01_LITERAL_MODULES = frozenset({"typing", "typing_extensions"})
def _uc01_forward_ref_context(tree: Any) -> _UC01ForwardRefContext:
    literal_names, module_names = _uc01_literal_bindings(tree)
    return _UC01ForwardRefContext(
        literal_names=frozenset(literal_names | {"Literal"}),
        module_names=frozenset(module_names | _UC01_LITERAL_MODULES),
    )
def _uc01_literal_bindings(tree: Any) -> tuple[set[str], set[str]]:
    literal_names: set[str] = set()
    module_names: set[str] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module in _UC01_LITERAL_MODULES):
            for alias in node.names:
                if alias.name == "Literal":
                    literal_names.add(alias.asname or alias.name)
                elif alias.name == "*":
                    literal_names.add("Literal")
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in _UC01_LITERAL_MODULES:
                    module_names.add(alias.asname or alias.name)
    return literal_names, module_names
def _uc01_is_literal_subscript(
        node: ast.AST, literal_names: set[str], module_names: set[str],
    ) -> bool:
    if not isinstance(node, ast.Subscript):
        return False
    target = node.value
    return ((isinstance(target, ast.Name) and target.id in literal_names)
            or (isinstance(target, ast.Attribute)
                and target.attr == "Literal"
                and isinstance(target.value, ast.Name)
                and target.value.id in module_names))
def _uc01_literal_string_ids(
        tree: Any,
        bindings: tuple[set[str], set[str]] | None = None) -> set[int]:
    literal_names, module_names = (
        _uc01_literal_bindings(tree) if bindings is None else bindings)
    return {
        id(sub) for node in walk_nodes(tree)
        if _uc01_is_literal_subscript(node, literal_names, module_names)
        for sub in walk_nodes(node.slice)
        if isinstance(sub, ast.Constant) and isinstance(sub.value, str)
    }
def _uc01_forward_ref_nodes(
        expr: ast.AST, context: _UC01ForwardRefContext) -> list[ast.AST]:
    literal_string_ids = _uc01_literal_string_ids(
        expr, (context.literal_names, context.module_names))
    return [node for node in walk_nodes(expr) if id(node) not in literal_string_ids]
def _uc01_forward_ref_fragments(
        expr: ast.AST, context: _UC01ForwardRefContext) -> list[str]:
    return [
        node.value for node in _uc01_forward_ref_nodes(expr, context)
        if isinstance(node, ast.Constant) and isinstance(node.value, str)
    ]
def _uc01_annotation_expr_names(
        annotation: ast.AST, literal_string_ids: set[int],
        *, forward_context: _UC01ForwardRefContext = (
            _UC01_EMPTY_FORWARD_REF_CONTEXT)) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(annotation):
        if (isinstance(node, ast.Constant) and isinstance(node.value, str)
                and id(node) not in literal_string_ids):
            names |= _uc01_forward_ref_names(
                node.value, context=forward_context)
    return names
def _uc01_annotation_string_names(
        tree: Any, literal_string_ids: set[int], *,
        forward_context: _UC01ForwardRefContext = (
            _UC01_EMPTY_FORWARD_REF_CONTEXT)) -> set[str]:
    names: set[str] = set()
    for annotation in _annotation_exprs(tree):
        names |= _uc01_annotation_expr_names(
            annotation, literal_string_ids, forward_context=forward_context)
    return names
_UC01_INCLUDE_DIRECT_DEFAULT = True
_UC01_IMPLICIT_USED_NAMES = frozenset({
    '__all__', '__version__', '__author__', '__doc__'})
def _uc01_collect_used_names(
        tree: Any, *, include_direct: bool = _UC01_INCLUDE_DIRECT_DEFAULT,
        literal_string_ids: set[int]) -> set[str]:
    used = set(_UC01_IMPLICIT_USED_NAMES)
    for node in walk_nodes(tree):
        if include_direct:
            used |= _uc01_node_used_names(node)
        elif isinstance(node, ast.Call):
            used |= _uc01_dynamic_import_names(node)
    export_names = (_uc01_dunder_all_names(tree, own_scope=True)
                    if isinstance(tree, ast.Module) else set())
    forward_context = _uc01_forward_ref_context(tree)
    return (used | _uc01_annotation_string_names(
            tree, literal_string_ids, forward_context=forward_context)
            | export_names)
def _uc01_definition_time_used_names(
        node: ast.AST, future_annotations: bool, *,
        include_direct: bool = _UC01_INCLUDE_DIRECT_DEFAULT,
        literal_string_ids: set[int]) -> set[str]:
    used: set[str] = set()
    for expr in _definition_binding_exprs(node, future_annotations):
        for sub in walk_nodes(expr):
            if include_direct:
                used |= _uc01_node_used_names(sub)
            elif isinstance(sub, ast.Call):
                used |= _uc01_dynamic_import_names(sub)
    for annotation in _own_annotation_exprs(node):
        used |= _uc01_annotation_expr_names(annotation, literal_string_ids)
    return used
def _uc01_class_used_names(
        tree: ast.ClassDef, future_annotations: bool, *,
        include_direct: bool = _UC01_INCLUDE_DIRECT_DEFAULT,
        literal_string_ids: set[int]) -> set[str]:
    used = set(_UC01_IMPLICIT_USED_NAMES)
    stack: list[ast.AST] = [tree]
    while stack:
        node = stack.pop()
        if node is not tree and isinstance(node, _IM_SCOPE_FRAMES):
            used |= _uc01_definition_time_used_names(
                node, future_annotations, include_direct=include_direct,
                literal_string_ids=literal_string_ids)
            continue
        if include_direct:
            used |= _uc01_node_used_names(node)
        elif isinstance(node, ast.Call):
            used |= _uc01_dynamic_import_names(node)
        if isinstance(node, (ast.Assign, ast.AnnAssign,
                             ast.AugAssign, ast.Call)):
            used |= _uc01_dunder_all_names(node)
        if isinstance(node, ast.AnnAssign):
            used |= _uc01_annotation_expr_names(
                node.annotation, literal_string_ids)
        stack.extend(ast.iter_child_nodes(node))
    return used
def _uc01_scope_binding_names(scope: ast.AST,
                              module_bound: set[str]) -> set[str]:
    if isinstance(scope, ast.Module):
        return module_bound
    if isinstance(scope, ast.ClassDef):
        bound: set[str] = set()
        for child in iter_own_scope(
                scope, skip_lambda=True, skip_type_checking_body=True):
            if isinstance(child, (ast.Import, ast.ImportFrom)):
                bound.update(import_binds_of(child))
            _collect_binding_names(child, bound)
        return bound
    imports, local = _collect_func_scope_sets(
        scope, include_exception_targets=True)
    return imports | local
def _uc01_resolved_used_names(tree: ast.AST) -> dict[int, set[str]]:
    parents = build_parent_map(tree)
    module_bound = _collect_module_bindings(
        tree, include_exception_targets=True)
    resolver = _ImportScopeResolver(tree, module_bound)
    binding_cache: dict[int, set[str]] = {}
    redirect_cache: dict[int, tuple[set[str], set[str]]] = {}
    used: dict[int, set[str]] = {}
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Name)
                and not isinstance(node.ctx, ast.Store)):
            continue
        name = node.id
        if name in _im_comprehension_bindings(parents, node):
            continue
        deftime_path = True
        owner = None
        frame = _im_enclosing_scope(parents, node)
        while frame is not None and not isinstance(frame, ast.Module):
            scope_key = id(frame)
            if scope_key not in binding_cache:
                binding_cache[scope_key] = _uc01_scope_binding_names(
                    frame, module_bound)
            if scope_key not in redirect_cache:
                redirect_cache[scope_key] = _im_scope_redirects(frame)
            redirected, global_names = redirect_cache[scope_key]
            bindings = binding_cache[scope_key] - redirected
            in_deftime = resolver._in_definition_time(frame, node)
            if not (deftime_path and in_deftime) and name in global_names:
                if name in module_bound:
                    owner = tree
                break
            if isinstance(frame, ast.ClassDef):
                if deftime_path and not in_deftime:
                    if _im_class_scope_visible_at(parents, frame, node):
                        bindings = _collect_scope_bindings_before(
                            frame, node,
                            future_annotations=resolver.future_annotations,
                            parents=parents) - redirected
                        if name in bindings:
                            owner = frame
                            break
                    deftime_path = False
            elif not (deftime_path and in_deftime):
                if name in bindings:
                    owner = frame
                    break
                deftime_path = False
            frame = _im_enclosing_scope(parents, frame)
        if owner is None:
            if name not in module_bound:
                continue
            owner = tree
        used.setdefault(id(owner), set()).add(name)
    return used
def _uc01_stmt_noqa_lines(tree: Any, source_lines: Any) -> set[int]:
    lines = _uc01_normalized_lines(source_lines)
    if not lines:
        return set()
    anchors: set[int] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.Import, ast.ImportFrom))
                and _uc01_stmthas_noqa(node, lines)):
            anchors.add(node.lineno)
    return anchors
def _uc01_normalized_lines(source_lines: Any) -> list | tuple:
    if not source_lines:
        return ()
    if isinstance(source_lines, str):
        return aligned_source_lines(source_lines)
    if isinstance(source_lines, (list, tuple)):
        return source_lines
    return ()
def _uc01_stmthas_noqa(node: ast.AST, source_lines: list | tuple) -> bool:
    end = getattr(node, 'end_lineno', node.lineno)
    return any(
        1 <= ln <= len(source_lines)
        and NOQA_ANY_RE.search(str(source_lines[ln - 1]))
        for ln in range(node.lineno, end + 1))
def _uc01_skip_binding(name: str, line: int, used_names: set[str],
                       noqa_lines: set[int], source_lines: Any) -> bool:
    if name in used_names:
        return True
    if name.startswith('_'):
        return True
    return line in noqa_lines or has_noqa(source_lines, line)
def _uc01_finding(name: str, line: int, filepath: Any,
                  source_lines: Any) -> dict:
    return {
        "rule_id": "UC-01",
        "severity": "P2",
        "dimension": CAT_MAINTAINABILITY,
        "file": filepath,
        "line": line,
        "col_offset": 0,
        "import_name": name,
        "title": f"未使用的导入: {name}",
        "description": f"模块'{name}'被导入但未在文件中使用,增加了不必要的命名空间污染和导入开销.如果是有副作用的导入(如import logging.config),可添加# noqa注释.",
        "code_snippet": get_code_snippet(source_lines, line),
        "suggestion": f'根因: 代码中存在冗余或无效内容, 影响可维护性。该问题属于代码质量类别。\n修复策略: 删除未使用的import {name},或使用# noqa: UC-01标记副作用导入\n参考标准: PEP 8 / pylint / SonarQube',
        "rule_ref": "PEP 8 / pylint unused-import"
    }
def check_UC01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    issues = []
    if tree is None or finding_scan_exempt(filepath):
        return issues
    imports = _uc01_collect_imports(tree, type_checking_body_node_ids(tree))
    _stmt_noqa_lines = _uc01_stmt_noqa_lines(tree, source_lines)
    resolved_used_names = _uc01_resolved_used_names(tree)
    literal_string_ids = _uc01_literal_string_ids(tree)
    module_used_names = (
        _uc01_collect_used_names(
            tree, include_direct=False, literal_string_ids=literal_string_ids)
        | resolved_used_names.get(id(tree), set()))
    future_annotations = module_postpones_annotations(tree)
    scope_used_names: dict[int, set[str]] = {}
    for name, line, scope in sorted(
            imports, key=lambda entry: (entry[1], entry[0])):
        if scope is None or isinstance(scope, ast.Module):
            used_names = module_used_names
        else:
            scope_key = id(scope)
            if scope_key not in scope_used_names:
                if isinstance(scope, ast.ClassDef):
                    scope_used_names[scope_key] = (
                        _uc01_class_used_names(
                            scope, future_annotations, include_direct=False,
                            literal_string_ids=literal_string_ids)
                        | resolved_used_names.get(scope_key, set()))
                else:
                    scope_used_names[scope_key] = (
                        _uc01_collect_used_names(
                            scope, include_direct=False,
                            literal_string_ids=literal_string_ids)
                        | resolved_used_names.get(scope_key, set()))
            used_names = scope_used_names[scope_key]
        if _uc01_skip_binding(name, line, used_names,
                              _stmt_noqa_lines, source_lines):
            continue
        issues.append(_uc01_finding(name, line, filepath, source_lines))
    return issues
@dataclass
class _MissingImportScanCtx:
    module_bindings: set
    source_lines: list[str]
    future_annotations: bool
    filepath: str
    parents: dict[int, ast.AST]
    type_checking_ifs: set[int]
    findings: list[PatternFinding] = field(default_factory=list)
@dataclass(frozen=True)
class _LexicalScope:
    imports: frozenset = frozenset()
    variables: frozenset = frozenset()
    owner: ast.AST | None = None
    entry_visible: frozenset = frozenset()
    deftime_outer: frozenset = frozenset()
    def visible_with(self, module_bindings: set) -> set:
        return module_bindings | self.imports | self.variables
def _push_scope_children(stack: list, node: ast.AST,
                         scope: _LexicalScope) -> None:
    stack.extend((child, scope)
                 for child in reversed(list(ast.iter_child_nodes(node))))
def _definition_binding_exprs(node: ast.AST,
                              future_annotations: bool) -> list:
    exprs = list(definition_time_exprs(node))
    if isinstance(node, ast.ClassDef):
        exprs.extend(node.bases)
        exprs.extend(keyword.value for keyword in node.keywords)
    if not future_annotations:
        exprs.extend(_own_annotation_exprs(node))
    return exprs
def _collect_global_import_bindings(tree: ast.AST) -> set[str]:
    bound: set[str] = set()
    type_checking_ifs = {
        node_id
        for node_id, negated in _type_checking_guard_node_polarities(tree).items()
        if not negated}
    stack: list[tuple[ast.AST, set[str]]] = [(tree, set())]
    while stack:
        node, global_names = stack.pop()
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            bound.update(
                name for name in import_binds_of(node)
                if name in global_names)
            continue
        if isinstance(node, ast.If) and id(node) in type_checking_ifs:
            stack.extend((child, global_names) for child in node.orelse)
            continue
        if isinstance(node, FRAME_BOUNDARY_NODES):
            global_names = _im_scope_redirects(node)[1]
        stack.extend(
            (child, global_names) for child in ast.iter_child_nodes(node))
    return bound
def _collect_module_bindings(tree: ast.AST, *,
                             include_exception_targets: bool) -> set:
    future_annotations = module_postpones_annotations(tree)
    type_checking_ifs = {
        node_id
        for node_id, negated in _type_checking_guard_node_polarities(tree).items()
        if not negated}
    bound: set = set()
    stack: list[ast.AST] = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            bound.update(import_binds_of(node))
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
            bound.add(node.name)
            stack.extend(reversed(
                _definition_binding_exprs(node, future_annotations)))
            continue
        if isinstance(node, ast.If) and id(node) in type_checking_ifs:
            stack.extend(reversed(node.orelse))
            continue
        if isinstance(node, ast.Lambda):
            stack.extend(reversed(_definition_binding_exprs(node, future_annotations)))
            continue
        if isinstance(node, ast.ExceptHandler) and not include_exception_targets:
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
            continue
        _collect_binding_names(node, bound)
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
    bound.update(_collect_global_import_bindings(tree))
    return bound
def _target_within_handler(target: ast.AST, handler: ast.ExceptHandler) -> bool:
    return any(
        target is sub for stmt in handler.body for sub in walk_nodes(stmt))
def _im_ancestor_ids(parents: dict[int, ast.AST], node: ast.AST) -> set[int]:
    ancestors: set[int] = set()
    cursor = parents.get(id(node))
    while cursor is not None:
        ancestors.add(id(cursor))
        cursor = parents.get(id(cursor))
    return ancestors
def _definition_name_visible_at(def_node: ast.AST, target: ast.AST,
                                target_ancestors: set[int],
                                future_annotations: bool) -> bool:
    if id(def_node) not in target_ancestors:
        return True
    if isinstance(def_node, ast.ClassDef):
        return False
    deftime_ids = subtree_node_ids(
        _definition_binding_exprs(def_node, future_annotations))
    return id(target) not in deftime_ids
def _collect_scope_bindings_before(root: ast.AST, target: ast.AST, *,
                                   future_annotations: bool,
                                   parents: dict[int, ast.AST]) -> set:
    bound: set = set()
    type_checking_ifs = {
        node_id
        for node_id, negated in _type_checking_guard_node_polarities(root).items()
        if not negated}
    stack: list[ast.AST] = [root]
    target_pos = node_position(target)
    target_ancestors = _im_ancestor_ids(parents, target)
    while stack:
        node = stack.pop()
        if node is target:
            continue
        lineno = getattr(node, 'lineno', None)
        if (node is not root and lineno is not None
                and node_position(node) >= target_pos):
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            bound.update(import_binds_of(node))
            continue
        if node is not root and isinstance(
                node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if _definition_name_visible_at(
                    node, target, target_ancestors, future_annotations):
                bound.add(node.name)
            stack.extend(reversed(
                _definition_binding_exprs(node, future_annotations)))
            continue
        if isinstance(node, ast.If) and id(node) in type_checking_ifs:
            stack.extend(reversed(node.orelse))
            continue
        if isinstance(node, ast.Lambda):
            stack.extend(reversed(_definition_binding_exprs(node, future_annotations)))
            continue
        if isinstance(node, ast.ExceptHandler):
            if node.name and _target_within_handler(target, node):
                bound.add(node.name)
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
            continue
        if node is not root and _binding_precedes_use(node, target):
            _collect_binding_names(node, bound)
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
    return bound
def _collect_binding_names(node: ast.AST, local: set) -> None:
    _collect_def_binding(node, local)
    _collect_assignment_binding(node, local)
    _collect_pattern_binding(node, local)
def _collect_def_binding(node: ast.AST, local: set) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
        local.add(node.name)
def _collect_assignment_binding(node: ast.AST, local: set) -> None:
    if isinstance(node, ast.Assign):
        for target in node.targets:
            local.update(binding_names_of(target))
    elif isinstance(node, ast.AnnAssign):
        if node.value is not None:
            local.update(binding_names_of(node.target))
    elif isinstance(node, (ast.AugAssign, ast.NamedExpr, ast.For,
                            ast.AsyncFor)):
        local.update(binding_names_of(node.target))
    elif isinstance(node, ast.withitem) and node.optional_vars is not None:
        local.update(binding_names_of(node.optional_vars))
def _collect_pattern_binding(node: ast.AST, local: set) -> None:
    if isinstance(node, (ast.ExceptHandler, ast.MatchAs,
                          ast.MatchStar)) and node.name:
        local.add(node.name)
    elif isinstance(node, ast.MatchMapping) and node.rest:
        local.add(node.rest)
def _collect_func_scope_sets(
        func_node: ast.AST,
        include_exception_targets: bool) -> tuple[set, set]:
    imported: set = set()
    local: set = {arg.arg for arg in iter_arg_nodes(func_node.args)}
    for node in iter_own_scope(func_node, skip_lambda=True,
                                skip_type_checking_body=True):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            imported.update(import_binds_of(node))
        if isinstance(node, ast.arg):
            local.add(node.arg)
        if include_exception_targets or not isinstance(node, ast.ExceptHandler):
            _collect_binding_names(node, local)
    local.update({'self', 'cls'})
    return imported, local
def _comprehension_shadowed_ids(func_node: ast.AST) -> set:
    shadowed: set = set()
    for comp in walk_nodes(func_node):
        if isinstance(comp, (ast.ListComp, ast.SetComp,
                             ast.DictComp, ast.GeneratorExp)):
            shadowed |= _comp_shadowed_ids(comp)
    return shadowed
def _comp_shadowed_ids(comp: ast.AST) -> set:
    shadowed: set = set()
    visible_targets: set = set()
    for gen in comp.generators:
        shadowed |= _shadowed_attr_ids(gen.iter, visible_targets)
        visible_targets.update(binding_names_of(gen.target))
        for condition in gen.ifs:
            shadowed |= _shadowed_attr_ids(condition, visible_targets)
    result_exprs = ((comp.key, comp.value)
                    if isinstance(comp, ast.DictComp) else (comp.elt,))
    for expr in result_exprs:
        shadowed |= _shadowed_attr_ids(expr, visible_targets)
    return shadowed
def _shadowed_attr_ids(root: ast.AST, targets: set) -> set:
    if not targets:
        return set()
    return {
        id(sub) for sub in walk_nodes(root)
        if _is_shadowed_attr_use(sub, targets)
    }
def _is_shadowed_attr_use(node: ast.AST, targets: set) -> bool:
    return (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id in targets)
def _exception_target_attr_ids(func_node: ast.AST) -> set:
    shadowed: set = set()
    for node in iter_own_scope(func_node, skip_lambda=True,
                                skip_type_checking_body=True):
        if not isinstance(node, ast.ExceptHandler) or not node.name:
            continue
        for stmt in node.body:
            shadowed |= _shadowed_attr_ids(stmt, {node.name})
    return shadowed
def _collect_deftime_ids(func_node: ast.AST,
                         future_annotations: bool) -> tuple[set, set]:
    deftime_ids = subtree_node_ids(list(definition_time_exprs(func_node)))
    annotation_ids = subtree_node_ids(list(_own_annotation_exprs(func_node)))
    deftime_ids |= annotation_ids
    if future_annotations:
        unevaluated_annotation_ids = set(annotation_ids)
    else:
        unevaluated_annotation_ids = set()
        for node in iter_own_scope(
                func_node, skip_lambda=True, skip_type_checking_body=True):
            if isinstance(node, ast.AnnAssign):
                unevaluated_annotation_ids |= subtree_node_ids(
                    [node.annotation])
    return deftime_ids, unevaluated_annotation_ids
def _module_use_name(child: ast.AST, comp_shadowed: set,
                     unevaluated_annotation_ids: set) -> str | None:
    if id(child) in comp_shadowed or id(child) in unevaluated_annotation_ids:
        return None
    if (isinstance(child, ast.Attribute)
            and isinstance(child.value, ast.Name)):
        return child.value.id
    return None
def _definition_time_known(node: ast.AST, scope: _LexicalScope,
                           ctx: _MissingImportScanCtx) -> set:
    owner = scope.owner
    if owner is None:
        return scope.visible_with(ctx.module_bindings)
    prior = _collect_scope_bindings_before(
        owner, node, future_annotations=ctx.future_annotations,
        parents=ctx.parents)
    if isinstance(owner, ast.Module):
        return prior
    if isinstance(owner, ast.ClassDef):
        if not _im_class_scope_visible_at(ctx.parents, owner, node):
            prior = set()
        return set(scope.deftime_outer) | prior
    if isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef)):
        redirected, _global_names = _im_scope_redirects(owner)
        imports, local = _collect_func_scope_sets(
            owner, include_exception_targets=False)
        parameters = {arg.arg for arg in iter_arg_nodes(owner.args)}
        blocked = (imports | local) - redirected - parameters - prior
        return (set(scope.entry_visible) - blocked) | prior
    return scope.visible_with(ctx.module_bindings) | prior
class ModuleMissingImportDetector:
    DETECTOR_ID = "D53"
    PATTERN_NAME = "模块级缺失导入"
    _STDLIB_MODULES = _IM_STDLIB_MODULES
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        source, tree = parse_py_file(filepath)
        if tree is None:
            _log.debug("[D53] 解析失败跳过: %s", filepath)
            return []
        ctx = _MissingImportScanCtx(
            module_bindings=_collect_module_bindings(
                tree, include_exception_targets=False),
            source_lines=aligned_source_lines(source),
            future_annotations=module_postpones_annotations(tree),
            filepath=filepath,
            parents=build_parent_map(tree),
            type_checking_ifs={
                node_id
                for node_id, negated in _type_checking_guard_node_polarities(
                    tree).items()
                if not negated},
        )
        scope_stack: list[tuple[ast.AST, _LexicalScope]] = [
            (tree, _LexicalScope(owner=tree))]
        while scope_stack:
            node, scope = scope_stack.pop()
            self._dispatch_scope_child(node, scope, scope_stack, ctx)
        findings = dedupe_findings(ctx.findings)
        _log.debug("[D53] %s: %d 项模块级缺失导入", filepath, len(findings))
        return findings
    def _dispatch_scope_child(self, child: ast.AST, scope: _LexicalScope,
                              scope_stack: list,
                              ctx: _MissingImportScanCtx) -> None:
        if isinstance(child, ast.ClassDef):
            deftime_outer = _definition_time_known(child, scope, ctx)
            self._check_class_definition(child, deftime_outer, scope, ctx)
            class_scope = _LexicalScope(
                scope.imports, scope.variables,
                owner=child, deftime_outer=deftime_outer)
            _push_scope_children(scope_stack, child, class_scope)
            return
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            func_imports, local_vars = _collect_func_scope_sets(
                child, include_exception_targets=False)
            own_known = func_imports | local_vars
            redirected, global_names = _im_scope_redirects(child)
            nonlocal_names = redirected - global_names
            all_known = scope.visible_with(ctx.module_bindings) | own_known
            deftime_known = _definition_time_known(child, scope, ctx)
            self._check_function_scope(
                child, all_known, deftime_known, ctx, own_known, global_names)
            parameters = {
                arg.arg for arg in iter_arg_nodes(child.args)}
            outer_imports = scope.imports - global_names
            outer_variables = scope.variables - global_names
            entry_visible = frozenset(
                ctx.module_bindings | outer_imports | outer_variables | parameters)
            child_scope = _LexicalScope(
                outer_imports | (func_imports - nonlocal_names),
                outer_variables | (local_vars - nonlocal_names),
                owner=child, entry_visible=entry_visible)
            _push_scope_children(scope_stack, child, child_scope)
            return
        if isinstance(child, ast.If) and id(child) in ctx.type_checking_ifs:
            scope_stack.extend(
                (stmt, scope) for stmt in reversed(child.orelse))
            return
        _push_scope_children(scope_stack, child, scope)
    def _check_class_definition(self, class_node: ast.ClassDef,
                                deftime_known: set, scope: _LexicalScope,
                                ctx: _MissingImportScanCtx) -> None:
        pending = list(_definition_binding_exprs(
            class_node, ctx.future_annotations))
        comp_shadowed = _comprehension_shadowed_ids(class_node)
        while pending:
            child = pending.pop()
            if isinstance(child, ast.Lambda):
                pending.extend(_definition_binding_exprs(
                    child, ctx.future_annotations))
                continue
            mod_name = _module_use_name(child, comp_shadowed, set())
            known = deftime_known
            if (isinstance(scope.owner, ast.ClassDef)
                    and not _im_class_scope_visible_at(
                        ctx.parents, scope.owner, child)):
                known = _definition_time_known(child, scope, ctx)
            if (mod_name in self._STDLIB_MODULES
                    and mod_name not in known):
                ctx.findings.append(self._make_finding(
                    class_node, child, mod_name, child.lineno, ctx))
            pending.extend(ast.iter_child_nodes(child))
    def _check_function_scope(self, func_node: ast.AST, all_known: set,
                              deftime_known: set,
                              ctx: _MissingImportScanCtx,
                              own_known: set, global_names: set) -> None:
        _deftime_ids, _unevaluated_annotation_ids = _collect_deftime_ids(
            func_node, ctx.future_annotations)
        _comp_shadowed = (_comprehension_shadowed_ids(func_node)
                          | _exception_target_attr_ids(func_node))
        for child in iter_own_scope(func_node, skip_lambda=True,
                                     skip_type_checking_body=True):
            mod_name = _module_use_name(
                child, _comp_shadowed, _unevaluated_annotation_ids)
            if mod_name not in self._STDLIB_MODULES:
                continue
            if id(child) in _deftime_ids:
                known = deftime_known
            elif mod_name in global_names:
                known = ctx.module_bindings | own_known
            else:
                known = all_known
            if mod_name in known:
                continue
            ctx.findings.append(self._make_finding(
                func_node, child, mod_name, child.lineno, ctx))
    def _make_finding(self, func_node: ast.AST, attr_node: ast.Attribute,
                      mod_name: str, line_no: int,
                      ctx: _MissingImportScanCtx) -> PatternFinding:
        snippet = safe_source_line(ctx.source_lines, line_no)[:120]
        func_name = getattr(func_node, 'name', '<lambda>')
        owner_kind = '类' if isinstance(func_node, ast.ClassDef) else '函数'
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="ERROR",
            filepath=ctx.filepath,
            line=line_no,
            snippet=snippet,
            message=f"{owner_kind} '{func_name}' 内使用 {mod_name}.{attr_node.attr} "
                    f"但模块 '{mod_name}' 未在文件级 import",
            suggestion=suggest('代码缺少必要的元素。该问题属于代码质量类别。',
                f"在文件顶部添加 `import {mod_name}`"))
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            'SL01': check_SL01, 'SL05': check_SL05, 'UC01': check_UC01,
            'IM01': check_IM01, 'IM02': check_IM02, 'IM04': check_IM04,
            'IM05': check_IM05, 'PX02': check_PX02,
            'PX05': check_PX05,
        },
        "audit_detector_classes": {'D53': ModuleMissingImportDetector},
    }}

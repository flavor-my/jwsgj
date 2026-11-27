from __future__ import annotations  # noqa: I001
import ast
import logging
import os
import re
import time
from typing import Any, NamedTuple
if __package__ in (None, ""):
    import sys as _sys
    _pkg_parent = os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))
    if _pkg_parent not in _sys.path:
        _sys.path.insert(0, _pkg_parent)
import jwsgj.engine_d1_tool_channels as _tool_channels  # noqa: I001
from jwsgj.diag_shared_ast_nodes import (
    TYPE_ALIAS_NODES,
    attr_chain_key,
    is_mutable_default,
    is_none_literal,
    iter_arg_defaults,
    iter_arg_nodes,
    iter_target_bindings,
    iter_unpack_target_names,
    module_postpones_annotations,
    split_identifier,
    subtree_node_ids,
)
from jwsgj.diag_shared_source_core import (
    parse_py_file,
)
from jwsgj.diag_shared_source_scan import (
    has_inline_suppression,
)
from jwsgj.diag_taint_tracker import TaintTracker
from jwsgj.diag_types_normalize import signal_bool
from jwsgj.runtime_scope import (
    CACHE_TEMP_DIR_NAMES,
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    coerce_skill_dir,
    is_pruned_scan_dir,
    is_scan_py_name,
    safe_relpath,
)
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    "StaticAnalyzer",
    "analyze_directory",
]
logger = logging.getLogger("jwsgj.engine_d1_static")
_DEFAULT_INCLUDE_ANNOTATIONS = True
_MUTATING_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear",
    "update", "setdefault", "popitem", "add", "discard",
    "sort", "reverse", "difference_update",
    "intersection_update", "symmetric_difference_update",
})
_UNBOUND_MUTATOR_TYPES = frozenset({"list", "dict", "set", "bytearray"})
def _iter_arg_eval_exprs(
        a: ast.arguments,
        include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS):
    yield from iter_arg_defaults(a)
    if not include_annotations:
        return
    for param in iter_arg_nodes(a):
        if param.annotation is not None:
            yield param.annotation
def _eval_zone_exprs(
        def_node, include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS) -> list:
    exprs: list = []
    if isinstance(def_node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
        exprs.extend(def_node.decorator_list or [])
    if isinstance(def_node, ast.ClassDef):
        exprs.extend(def_node.bases)
        exprs.extend(kw.value for kw in def_node.keywords)
    _a = getattr(def_node, "args", None)
    if _a is not None:
        exprs.extend(_iter_arg_eval_exprs(_a, include_annotations))
    returns = getattr(def_node, "returns", None)
    if include_annotations and returns is not None:
        exprs.append(returns)
    return exprs
_COMP_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_FUNCTION_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_SCOPE_DEF_TYPES = (*_FUNCTION_SCOPE_TYPES, ast.ClassDef)
_TYPE_PARAM_NODES = tuple(
    getattr(ast, name) for name in ("TypeVar", "TypeVarTuple", "ParamSpec")
    if hasattr(ast, name))
def _iter_analysis_children(
        node, annotations_evaluated: bool = _DEFAULT_INCLUDE_ANNOTATIONS):
    if isinstance(node, ast.AnnAssign) and not annotations_evaluated:
        return [child for child in ast.iter_child_nodes(node)
                if child is not node.annotation]
    return list(ast.iter_child_nodes(node))
def _deferred_eval_child_ids(node) -> set[int]:
    deferred = set()
    if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
        deferred.add(id(node.value))
    if _TYPE_PARAM_NODES and isinstance(node, _TYPE_PARAM_NODES):
        for field_name in ("bound", "default_value"):
            value = getattr(node, field_name, None)
            if value is not None:
                deferred.add(id(value))
    return deferred
def _descend_in_comp(n, in_comp: bool) -> bool:
    return in_comp or isinstance(n, _COMP_TYPES)
def _own_nodes(
        scope_node, include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS):
    zone = _zone_ids(scope_node)
    annotations_evaluated = (
        include_annotations
        and not isinstance(scope_node, _FUNCTION_SCOPE_TYPES))
    stack = [(c, False) for c in ast.iter_child_nodes(scope_node)
             if id(c) not in zone]
    while stack:
        n, in_comp = stack.pop()
        yield n, in_comp
        if isinstance(n, _SCOPE_DEF_TYPES):
            continue
        child_comp = _descend_in_comp(n, in_comp)
        stack.extend(
            (k, child_comp) for k in _drill_children(
                n, annotations_evaluated))
def _drill_children(
        node, annotations_evaluated: bool = _DEFAULT_INCLUDE_ANNOTATIONS):
    if isinstance(node, ast.arg):
        return ()
    kids = _iter_analysis_children(node, annotations_evaluated)
    if not isinstance(node, ast.arguments):
        return kids
    eval_zone = _args_eval_zone_ids(node)
    return [c for c in kids if id(c) not in eval_zone]
def _source_pos(node) -> tuple[int, int]:
    return (node.lineno, node.col_offset)
def _mut_names(t, shadow_sites: dict | None
               ) -> list[tuple[str, tuple[int, int]]]:
    if isinstance(t, (ast.Tuple, ast.List)):
        _out: list[tuple[str, tuple[int, int]]] = []
        for _el in t.elts:
            _out.extend(_mut_names(_el, shadow_sites))
        return _out
    if isinstance(t, ast.Starred):
        return _mut_names(t.value, shadow_sites)
    if isinstance(t, ast.Name):
        return []
    if shadow_sites and id(t) in shadow_sites:
        return []
    name = _receiver_root_name(t)
    return [] if name is None else [(name, _source_pos(t))]
def _bind_min(name: str, pos: tuple[int, int], acc: dict) -> None:
    prev = acc.get(name)
    if prev is None or pos < prev:
        acc[name] = pos
def _binding_visible_pos(node) -> tuple[int, int]:
    if isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
                         ast.ExceptHandler)) and node.body:
        return _source_pos(node.body[0])
    end_line = getattr(node, 'end_lineno', None)
    end_col = getattr(node, 'end_col_offset', None)
    return (node.lineno if end_line is None else end_line,
            node.col_offset if end_col is None else end_col)
def _bind_names(t, acc: dict, visible_pos: tuple[int, int] | None = None) -> None:
    for name, line, col in iter_target_bindings(t):
        _bind_min(name, visible_pos or (line, col), acc)
def _zone_ids(def_node) -> set:
    ids = {id(e) for e in _eval_zone_exprs(def_node)}
    if isinstance(def_node, ast.ClassDef):
        ids.update(id(kw) for kw in def_node.keywords)
    return ids
def _args_eval_zone_ids(a: ast.arguments) -> set:
    return {id(expr) for expr in _iter_arg_eval_exprs(a)}
def _receiver_root_name(expr) -> str | None:
    while isinstance(expr, ast.Subscript):
        expr = expr.value
    return expr.id if isinstance(expr, ast.Name) else None
def _inplace_method_root(node) -> str | None:
    f = node.func if isinstance(node, ast.Call) else node
    if not isinstance(f, ast.Attribute) or f.attr not in _MUTATING_METHODS:
        return None
    if (isinstance(node, ast.Call) and isinstance(f.value, ast.Name)
            and f.value.id in _UNBOUND_MUTATOR_TYPES and node.args):
        return _receiver_root_name(node.args[0])
    return _receiver_root_name(f.value)
def _inplace_call_mut(n: ast.Call, muts: list,
                      shadow_sites: dict | None) -> None:
    _root = _inplace_method_root(n)
    if _root is not None and not (shadow_sites and id(n) in shadow_sites):
        muts.append((_root, _source_pos(n)))
def _comp_shadow_targets(comp) -> set[str]:
    targets: set[str] = set()
    for generator in comp.generators:
        targets |= set(iter_unpack_target_names(generator.target))
    return targets
def _comp_shadow_sites(tree) -> dict[int, str]:
    shadow: dict[int, str] = {}
    for comp in walk_nodes(tree):
        if not isinstance(comp, _COMP_TYPES):
            continue
        targets = _comp_shadow_targets(comp)
        if not targets:
            continue
        outer_scope = subtree_node_ids([comp.generators[0].iter])
        for sub in walk_nodes(comp):
            if id(sub) in outer_scope:
                continue
            _root = _write_site_root(sub)
            if _root is not None and _root in targets:
                shadow[id(sub)] = _root
    return shadow
class _EvalZoneCtx(NamedTuple):
    loc: dict
    muts: list
    comp_out: list
    site_comp: bool
    loc_is_class: bool
    shadow_sites: dict
def _eval_expr_walrus_bind(n: ast.NamedExpr, in_comp: bool,
                           ctx: _EvalZoneCtx) -> None:
    if ctx.loc_is_class and in_comp:
        ctx.comp_out.append((n.target.id, _source_pos(n)))
    else:
        _bind_min(n.target.id, _source_pos(n), ctx.loc)
def _walk_eval_expr(node, ctx: _EvalZoneCtx) -> None:
    stack: list[tuple[ast.AST, bool]] = [(node, ctx.site_comp)]
    while stack:
        n, in_comp = stack.pop()
        if isinstance(n, ast.Lambda):
            stack.extend((d, in_comp) for d in iter_arg_defaults(n.args))
            continue
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
            continue
        _collect_eval_node(n, in_comp, ctx)
        child_comp = _descend_in_comp(n, in_comp)
        stack.extend((k, child_comp) for k in ast.iter_child_nodes(n))
def _collect_eval_node(n, in_comp: bool, ctx: _EvalZoneCtx) -> None:
    if isinstance(n, ast.Call):
        _inplace_call_mut(n, ctx.muts, ctx.shadow_sites)
    elif isinstance(n, ast.NamedExpr):
        _eval_expr_walrus_bind(n, in_comp, ctx)
    elif isinstance(n, ast.comprehension):
        ctx.muts.extend(_mut_names(n.target, ctx.shadow_sites))
def _collect_def_eval_zone(def_node, ctx: _EvalZoneCtx,
                           include_annotations: bool) -> None:
    for _expr in _eval_zone_exprs(def_node, include_annotations):
        _walk_eval_expr(_expr, ctx)
def _bind_fn_params(a, loc: dict) -> None:
    for p in iter_arg_nodes(a):
        _bind_min(p.arg, _source_pos(p), loc)
def _collect_scope_assign_family(n, loc: dict, muts: list,
                                 is_function: bool,
                                 shadow_sites: dict | None) -> None:
    if isinstance(n, (ast.For, ast.AsyncFor, ast.comprehension)):
        _collect_scope_iter_family(n, loc, muts, shadow_sites)
    else:
        _collect_scope_assign_trio(n, loc, muts, is_function, shadow_sites)
def _collect_scope_iter_family(n, loc: dict, muts: list,
                               shadow_sites: dict | None) -> None:
    if isinstance(n, (ast.For, ast.AsyncFor)):
        _bind_names(n.target, loc, _binding_visible_pos(n))
        muts.extend(_mut_names(n.target, shadow_sites))
        return
    muts.extend(_mut_names(n.target, shadow_sites))
def _collect_scope_assign_trio(n, loc: dict, muts: list,
                                is_function: bool,
                                shadow_sites: dict | None) -> None:
    targets = n.targets if isinstance(n, ast.Assign) else [n.target]
    if not _class_bare_annotated(n, is_function):
        for t in targets:
            _bind_names(t, loc, _binding_visible_pos(n))
    _collect_assign_muts(targets, n, muts, shadow_sites)
def _class_bare_annotated(node, is_function: bool) -> bool:
    return (isinstance(node, ast.AnnAssign) and node.value is None
            and not is_function)
def _collect_assign_muts(targets: list, node, muts: list,
                       shadow_sites: dict | None) -> None:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return
    for t in targets:
        if isinstance(node, ast.AugAssign) and isinstance(t, ast.Name):
            muts.append((t.id, _source_pos(node)))
        else:
            muts.extend(_mut_names(t, shadow_sites))
def _collect_scope_stmt_bind_family(n, loc: dict, muts: list,
                                   shadow_sites: dict | None) -> None:
    if isinstance(n, (ast.Import, ast.ImportFrom)):
        for al in n.names:
            _bind_min(al.asname or al.name.split(".")[0],
                      _source_pos(n), loc)
        return
    if isinstance(n, ast.ExceptHandler):
        if n.name:
            _bind_min(n.name, _binding_visible_pos(n), loc)
        return
    _collect_with_binds(n, loc, muts, shadow_sites)
def _collect_with_binds(node, loc: dict, muts: list,
                        shadow_sites: dict | None) -> None:
    for item in node.items:
        if item.optional_vars is not None:
            _bind_names(item.optional_vars, loc, _binding_visible_pos(node))
            muts.extend(_mut_names(item.optional_vars, shadow_sites))
def _collect_scope_walrus_bind(n: ast.NamedExpr, loc: dict,
                                comp_walrus: list, in_comp: bool,
                                is_function: bool) -> None:
    if in_comp and not is_function:
        comp_walrus.append((n.target.id, _source_pos(n)))
    else:
        _bind_min(n.target.id, _binding_visible_pos(n), loc)
def _collect_scope_match_bind(n, loc: dict) -> None:
    if isinstance(n, (ast.MatchAs, ast.MatchStar)) and n.name:
        _bind_min(n.name, _source_pos(n), loc)
        return
    if isinstance(n, ast.MatchMapping) and n.rest:
        _bind_min(n.rest, _source_pos(n), loc)
def _collect_scope_del_muts(n: ast.Delete, loc: dict, muts: list,
                           shadow_sites: dict | None) -> None:
    for t in n.targets:
        _bind_names(t, loc)
        muts.extend(_mut_names(t, shadow_sites))
class _ScopeSink(NamedTuple):
    loc: dict
    glo: set
    muts: list
    comp_walrus: list
    comp_muts: list
    is_function: bool
def _mutation_target(sink: _ScopeSink, in_comp: bool) -> list:
    return sink.comp_muts if in_comp else sink.muts
def _collect_binding_node(n, in_comp: bool, sink: _ScopeSink,
                          shadow_sites: dict | None,
                          include_annotations: bool) -> bool:
    if isinstance(n, ast.Global):
        sink.glo.update(n.names)
        return True
    if isinstance(n, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                     ast.For, ast.AsyncFor, ast.comprehension)):
        _collect_scope_assign_family(
            n, sink.loc, _mutation_target(sink, in_comp), sink.is_function,
            shadow_sites)
        return True
    if isinstance(n, (ast.Import, ast.ImportFrom, ast.ExceptHandler,
                     ast.With, ast.AsyncWith)):
        _collect_scope_stmt_bind_family(n, sink.loc, sink.muts, shadow_sites)
        return True
    return _collect_expr_binding(
        n, in_comp, sink, shadow_sites, include_annotations)
def _collect_expr_binding(n, in_comp: bool, sink: _ScopeSink,
                          shadow_sites: dict | None,
                          include_annotations: bool) -> bool:
    if isinstance(n, ast.NamedExpr):
        _collect_scope_walrus_bind(n, sink.loc, sink.comp_walrus, in_comp,
                                   sink.is_function)
        return True
    if isinstance(n, (ast.MatchAs, ast.MatchStar, ast.MatchMapping)):
        _collect_scope_match_bind(n, sink.loc)
        return True
    if isinstance(n, TYPE_ALIAS_NODES):
        _bind_min(n.name.id, _source_pos(n), sink.loc)
        return True
    if isinstance(n, _SCOPE_DEF_TYPES):
        _def_name = getattr(n, "name", None)
        if isinstance(_def_name, str):
            _bind_min(_def_name, _binding_visible_pos(n), sink.loc)
        _collect_def_eval_zone(
            n, _EvalZoneCtx(sink.loc, _mutation_target(sink, in_comp),
                            sink.comp_walrus, in_comp, not sink.is_function,
                            shadow_sites or {}), include_annotations)
        return True
    return False
def _collect_mutation_node(n, in_comp: bool, sink: _ScopeSink,
                           shadow_sites: dict | None) -> bool:
    if isinstance(n, ast.Delete):
        _collect_scope_del_muts(n, sink.loc, sink.muts, shadow_sites)
        return True
    if isinstance(n, ast.Call):
        _inplace_call_mut(n, _mutation_target(sink, in_comp), shadow_sites)
        return True
    return False
def _collect_scope(
        scope_node, is_function: bool,
        shadow_sites: dict | None,
        include_annotations: bool,
) -> tuple[dict, set, list, list, list]:
    loc: dict = {}
    if is_function:
        _bind_fn_params(scope_node.args, loc)
    sink = _ScopeSink(
        loc=loc, glo=set(), muts=[], comp_walrus=[], comp_muts=[],
        is_function=is_function)
    for n, in_comp in _own_nodes(scope_node, include_annotations):
        if _collect_binding_node(
                n, in_comp, sink, shadow_sites, include_annotations):
            continue
        _collect_mutation_node(n, in_comp, sink, shadow_sites)
    return sink.loc, sink.glo, sink.muts, sink.comp_walrus, sink.comp_muts
class _ModuleScopeDispatcher:
    def __init__(self, shadow_sites: dict | None,
                 include_annotations: bool) -> None:
        self.mutated: set = set()
        self._shadow_sites: dict = shadow_sites or {}
        self._include_annotations = include_annotations
    def _record(self, name: str, fn_stack) -> None:
        for _loc, _glo in reversed(fn_stack):
            if name in _glo:
                self.mutated.add(name)
                return
            if name in _loc:
                return
        self.mutated.add(name)
    def _mut_target(self, t, fn_stack) -> None:
        for _name, _line in _mut_names(t, self._shadow_sites):
            self._record(_name, fn_stack)
    def _enter_class(self, child, fn_stack, outer_class_scope=None) -> None:
        ns, glo, muts, comp_walrus, comp_muts = _collect_scope(
            child, is_function=False, shadow_sites=self._shadow_sites,
            include_annotations=self._include_annotations)
        if comp_walrus and fn_stack:
            _outer_loc = fn_stack[-1][0]
            for _name, _line in comp_walrus:
                _bind_min(_name, _line, _outer_loc)
        self._dispatch_eval_scopes(child, fn_stack, outer_class_scope)
        self._visit(child, fn_stack, False, self._include_annotations,
                    (ns, glo))
        for _name, _mline in comp_muts:
            self._record(_name, fn_stack)
        self._converge_class_muts(muts, ns, glo, fn_stack)
    def _converge_class_muts(self, muts: list, ns: dict, glo: set,
                             fn_stack) -> None:
        for _name, _mline in muts:
            if _name in glo:
                self.mutated.add(_name)
            elif _name in ns and _mline >= ns[_name]:
                continue
            else:
                self._record(_name, fn_stack)
    def _enter_fn(self, child, fn_stack, class_scope=None) -> None:
        loc, glo, muts, _comp_walrus, comp_muts = _collect_scope(
            child, is_function=True, shadow_sites=self._shadow_sites,
            include_annotations=self._include_annotations)
        muts = muts + comp_muts
        _stack2 = fn_stack + [(loc, glo)]
        self._dispatch_eval_scopes(child, fn_stack, class_scope)
        self._visit(child, _stack2, False, False)
        for _name, _line in muts:
            self._record(_name, _stack2)
    def _dispatch_eval_scopes(self, def_node, fn_stack,
                              class_scope=None) -> None:
        for _expr in _eval_zone_exprs(
                def_node, self._include_annotations):
            eval_fn_stack = fn_stack
            if class_scope is not None:
                ns, glo = class_scope
                visible = {
                    name: pos for name, pos in ns.items()
                    if pos <= _source_pos(_expr)
                }
                eval_fn_stack = [*fn_stack, (visible, glo)]
            stack = [_expr]
            while stack:
                n = stack.pop()
                if isinstance(n, ast.Lambda):
                    self._enter_fn(n, fn_stack, class_scope)
                    continue
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                    continue
                self._record_child_muts(n, eval_fn_stack)
                stack.extend(ast.iter_child_nodes(n))
    def _visit(
            self, node, fn_stack, record_muts: bool = True,
            annotations_evaluated: bool = _DEFAULT_INCLUDE_ANNOTATIONS,
            class_scope=None) -> None:
        _zone = _drill_zone(node)
        deferred = _deferred_eval_child_ids(node)
        for child in _iter_analysis_children(node, annotations_evaluated):
            if id(child) in _zone:
                continue
            if self._enter_child_scope(child, fn_stack, class_scope):
                continue
            child_fn_stack = fn_stack
            child_record_muts = record_muts
            if id(child) in deferred and not fn_stack:
                child_fn_stack = [
                    class_scope if class_scope is not None else ({}, set())]
                child_record_muts = True
            if child_record_muts:
                self._record_child_muts(child, child_fn_stack)
            self._visit(child, child_fn_stack, child_record_muts,
                        annotations_evaluated, class_scope)
    def _enter_child_scope(self, child, fn_stack, class_scope=None) -> bool:
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            self._enter_fn(child, fn_stack, class_scope)
            return True
        if isinstance(child, ast.ClassDef):
            self._enter_class(child, fn_stack, class_scope)
            return True
        return False
    def _record_target_family_muts(self, child, fn_stack) -> None:
        if isinstance(child, (ast.Assign, ast.Delete)):
            for t in child.targets:
                self._mut_target(t, fn_stack)
            return
        self._mut_target(child.target, fn_stack)
    def _record_augassign_mut(self, child, fn_stack) -> None:
        if isinstance(child.target, ast.Name):
            self._record(child.target.id, fn_stack)
        else:
            self._mut_target(child.target, fn_stack)
    def _record_child_muts(self, child, fn_stack) -> None:
        if isinstance(child, (ast.Assign, ast.Delete, ast.For, ast.AsyncFor,
                             ast.comprehension)):
            self._record_target_family_muts(child, fn_stack)
            return
        if isinstance(child, ast.AnnAssign):
            if child.value is not None:
                self._mut_target(child.target, fn_stack)
            return
        if isinstance(child, ast.AugAssign):
            self._record_augassign_mut(child, fn_stack)
            return
        if isinstance(child, (ast.With, ast.AsyncWith)):
            self._record_with_muts(child, fn_stack)
            return
        if isinstance(child, ast.Call):
            self._record_call_mut(child, fn_stack)
    def _record_with_muts(self, child, fn_stack) -> None:
        for _item in child.items:
            if _item.optional_vars is not None:
                self._mut_target(_item.optional_vars, fn_stack)
    def _record_call_mut(self, child, fn_stack) -> None:
        _root = _inplace_method_root(child)
        if _root is not None and id(child) not in self._shadow_sites:
            self._record(_root, fn_stack)
    def run(self, tree) -> set:
        self._visit(tree, [], annotations_evaluated=self._include_annotations)
        return self.mutated
def _drill_zone(node):
    if isinstance(node, _SCOPE_DEF_TYPES):
        return _zone_ids(node)
    if isinstance(node, ast.arguments):
        return _args_eval_zone_ids(node)
    return frozenset()
_LOCK_NAME_TOKENS = frozenset({
    "lock", "locks", "locked", "locking",
    "rlock", "rlocks", "mutex", "mutexes",
    "semaphore", "semaphores", "condition", "conditions",
})
def _has_lock_token(name: str) -> bool:
    return any(token in _LOCK_NAME_TOKENS for token in split_identifier(name))
def _lock_expr_hint(expr) -> bool:
    if _has_lock_token(str(attr_chain_key(expr) or "")):
        return True
    if isinstance(expr, ast.Call):
        callee = str(attr_chain_key(expr.func)
                     or getattr(expr.func, "id", "") or "")
        return _has_lock_token(callee)
    return False
def _with_guards_lock(node: ast.With | ast.AsyncWith) -> bool:
    return any(_lock_expr_hint(item.context_expr) for item in node.items)
def _write_site_root(node: ast.AST) -> str | None:
    if isinstance(node, ast.Subscript):
        if not isinstance(node.ctx, (ast.Store, ast.Del)):
            return None
        return _receiver_root_name(node.value)
    if isinstance(node, ast.Call):
        return _inplace_method_root(node)
    if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
        return node.target.id
    return None
def _deferred_body_ids(node: ast.AST) -> set[int]:
    if isinstance(node, ast.Lambda):
        body = getattr(node, "body", None)
        return {id(body)} if body is not None else set()
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return {id(child) for child in node.body}
    return set()
def _is_module_write_in_scope(name: str, node: ast.AST, fn_stack,
                              class_scope) -> bool:
    if class_scope is not None:
        ns, glo = class_scope
        if name in glo:
            return True
        bound_at = ns.get(name)
        if bound_at is not None and _source_pos(node) >= bound_at:
            return False
    for loc, glo in reversed(fn_stack):
        if name in glo:
            return True
        if name in loc:
            return False
    return True
def _push_function_lock_frames(node, inner, fn_stack, class_scope,
                               shadow_sites, include_annotations, stack) -> None:
    loc, glo, _muts, _walrus, _comp_muts = _collect_scope(
        node, is_function=True, shadow_sites=shadow_sites,
        include_annotations=include_annotations)
    deferred = _deferred_body_ids(node)
    inner_stack = [*fn_stack, (loc, glo)]
    eval_exprs = _eval_zone_exprs(node, include_annotations)
    eval_zone = {id(expr) for expr in eval_exprs}
    args_node = getattr(node, "args", None)
    returns_node = getattr(node, "returns", None)
    stack.extend(
        (expr, inner, fn_stack, class_scope) for expr in eval_exprs)
    stack.extend(
        (child, inner, fn_stack, class_scope)
        for child in ast.iter_child_nodes(node)
        if id(child) not in deferred
        and id(child) not in eval_zone
        and child is not args_node
        and child is not returns_node)
    stack.extend(
        (child, False, inner_stack, None)
        for child in ast.iter_child_nodes(node)
        if id(child) in deferred)
def _push_class_lock_frames(node, inner, fn_stack, class_scope,
                            shadow_sites, include_annotations, stack) -> None:
    ns, glo, _muts, _walrus, _comp_muts = _collect_scope(
        node, is_function=False, shadow_sites=shadow_sites,
        include_annotations=include_annotations)
    body_ids = {id(child) for child in node.body}
    stack.extend(
        (child, inner, fn_stack, class_scope)
        for child in ast.iter_child_nodes(node)
        if id(child) not in body_ids)
    stack.extend(
        (child, inner, fn_stack, (ns, glo))
        for child in node.body)
def _lock_guard_stats(tree: ast.Module, names, shadow_sites: dict,
                      include_annotations: bool) -> dict[str, list[int]]:
    stats: dict[str, list[int]] = {name: [0, 0] for name in names}
    if not stats:
        return stats
    stack = [(tree, False, [], None)]
    while stack:
        node, guarded, fn_stack, class_scope = stack.pop()
        inner = guarded or (
            isinstance(node, (ast.With, ast.AsyncWith))
            and _with_guards_lock(node))
        root = _write_site_root(node)
        if (root in stats and id(node) not in shadow_sites
                and _is_module_write_in_scope(
                    root, node, fn_stack, class_scope)):
            counts = stats[root]
            counts[0] += 1
            if inner:
                counts[1] += 1
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            _push_function_lock_frames(
                node, inner, fn_stack, class_scope, shadow_sites,
                include_annotations, stack)
            continue
        if isinstance(node, ast.ClassDef):
            _push_class_lock_frames(
                node, inner, fn_stack, class_scope, shadow_sites,
                include_annotations, stack)
            continue
        if isinstance(node, (ast.With, ast.AsyncWith)):
            item_guard = guarded
            for item in node.items:
                stack.append((
                    item.context_expr, item_guard, fn_stack, class_scope))
                item_guard = item_guard or _lock_expr_hint(item.context_expr)
                if item.optional_vars is not None:
                    stack.append((
                        item.optional_vars, item_guard, fn_stack, class_scope))
            stack.extend(
                (child, item_guard, fn_stack, class_scope)
                for child in node.body)
            continue
        annotations_evaluated = (
            include_annotations and not (fn_stack and class_scope is None))
        deferred = _deferred_eval_child_ids(node)
        for child in _iter_analysis_children(node, annotations_evaluated):
            child_deferred = id(child) in deferred
            child_fn_stack = fn_stack
            if child_deferred and not fn_stack:
                child_fn_stack = [({}, set())]
            stack.append((child, False if child_deferred else inner,
                          child_fn_stack, class_scope))
    return stats
def _is_fully_guarded(counts) -> bool:
    total, guarded = counts
    return total > 0 and guarded == total
_CRED_NAME_RE = re.compile(
    r'(?:password|passwd|pwd|secret|api_key|apikey|access_key|token|private_key)(?![A-Za-z])',
    re.IGNORECASE)
_PEM_BLOCK_RE = re.compile(r"-----BEGIN [A-Z0-9 ]+-----")
_OPAQUE_CRED_LINE_MIN = 16
_OPAQUE_CRED_LINE_RE = re.compile(r"[A-Za-z0-9+/=_.\-]+")
def _is_multiline_secret(value: str) -> bool:
    if _PEM_BLOCK_RE.search(value):
        return True
    return any(len(line) >= _OPAQUE_CRED_LINE_MIN
               and _OPAQUE_CRED_LINE_RE.fullmatch(line)
               for line in (ln.strip() for ln in value.splitlines()))
_RULE_ID_SHAPE_RE = re.compile(r"^[A-Z][A-Z0-9]*(?:[-_][A-Z0-9]+)+$")
_REGEX_META_CHARS = frozenset("\\[](){}?^$|*")
def _looks_like_regex_pattern(value: str) -> bool:
    metas = [ch for ch in value if ch in _REGEX_META_CHARS]
    return len(metas) >= 2 and any(ch in value for ch in "\\[(")
def _is_credential_fixture(value: str) -> bool:
    if "\\n" in value:
        return True
    if "import " in value or "os.system" in value:
        return True
    if "\n" in value and not _is_multiline_secret(value):
        return True
    if _RULE_ID_SHAPE_RE.fullmatch(value):
        return True
    if _looks_like_regex_pattern(value):
        return True
    return _is_ident_like(value)
def _is_ident_like(value: str) -> bool:
    if not _is_snake_case_shape(value):
        return False
    return all(("a" <= c <= "z") or ("0" <= c <= "9") or c == "_"
               for c in value)
def _is_snake_case_shape(value: str) -> bool:
    return ("_" in value and value[0] != "_"
            and value[-1] != "_" and "__" not in value)
_CONTROL_FLOW_STMTS = (ast.If, ast.For, ast.AsyncFor, ast.While, ast.Try,
                       ast.With, ast.AsyncWith, ast.ExceptHandler,
                       ast.Match, ast.match_case)
if hasattr(ast, "TryStar"):
    _CONTROL_FLOW_STMTS = _CONTROL_FLOW_STMTS + (ast.TryStar,)
def _iter_control_flow_stmts(body):
    stack: list[ast.AST] = list(reversed(body))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, _CONTROL_FLOW_STMTS):
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _declared_global_names(node) -> set[str]:
    names: set[str] = set()
    for child, _in_comp in _own_nodes(node, include_annotations=False):
        if isinstance(child, ast.Global):
            names.update(child.names)
    return names
def _iter_import_time_classes(tree: ast.Module):
    stack = [node for node in reversed(list(_iter_control_flow_stmts(tree.body)))
             if isinstance(node, ast.ClassDef)]
    while stack:
        node = stack.pop()
        yield node
        nested = [child for child in _iter_control_flow_stmts(node.body)
                  if isinstance(child, ast.ClassDef)]
        stack.extend(reversed(nested))
def _cred_target_name(target: ast.AST) -> str:
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        return target.attr
    if (isinstance(target, ast.Subscript)
            and isinstance(target.slice, ast.Constant)
            and isinstance(target.slice.value, str)):
        return target.slice.value
    return ""
def _cred_target_ok(target: ast.AST) -> bool:
    return bool(_CRED_NAME_RE.search(_cred_target_name(target)))
_CRED_MIN_VALUE_LEN = 6
def _is_credential_value_shape(value: str) -> bool:
    if len(value) < _CRED_MIN_VALUE_LEN or not value.isascii():
        return False
    _has_digit = any(ch.isdigit() for ch in value)
    _has_symbol = any(not ch.isalnum() and not ch.isspace()
                      for ch in value)
    _has_case_mix = (any(ch.islower() for ch in value)
                     and any(ch.isupper() for ch in value))
    return _has_digit or _has_symbol or _has_case_mix
def _cred_value_ok(value: ast.AST) -> bool:
    return (isinstance(value, ast.Constant) and isinstance(value.value, str)
            and _is_credential_value_shape(value.value)
            and not _is_credential_fixture(value.value))
def _collect_cred_line(node: ast.AST, cred_lines: list) -> None:
    for value in _cred_assigned_values(node):
        if _cred_value_ok(value):
            cred_lines.append(getattr(value, "lineno", node.lineno))
def _cred_value_pairs(target: ast.AST, value: ast.AST):
    if isinstance(target, (ast.Name, ast.Attribute, ast.Subscript)):
        if _cred_target_ok(target):
            yield value
        return
    if not isinstance(target, (ast.Tuple, ast.List)):
        return
    if not isinstance(value, (ast.Tuple, ast.List)):
        return
    targets = list(target.elts)
    values = list(value.elts)
    starred = [index for index, item in enumerate(targets)
               if isinstance(item, ast.Starred)]
    if len(starred) > 1:
        return
    if not starred and len(targets) != len(values):
        return
    if starred and len(values) < len(targets) - 1:
        return
    for index, target_item in enumerate(targets):
        if starred:
            star_index = starred[0]
            value_offset = len(values) - len(targets)
            if isinstance(target_item, ast.Starred):
                trailing = len(targets) - star_index - 1
                star_stop = len(values) - trailing if trailing else len(values)
                star_values = values[index:star_stop]
                if isinstance(target_item.value, (ast.Tuple, ast.List)):
                    bound_value = ast.copy_location(
                        ast.List(elts=star_values, ctx=ast.Load()), value)
                    yield from _cred_value_pairs(target_item.value, bound_value)
                elif _cred_target_ok(target_item.value):
                    yield from star_values
                continue
            value_index = (index if index < star_index
                           else index + value_offset)
        else:
            value_index = index
        if value_index < len(values):
            yield from _cred_value_pairs(target_item, values[value_index])
def _cred_assigned_values(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.Assign):
        values: list[ast.AST] = []
        for target in node.targets:
            values.extend(_cred_value_pairs(target, node.value))
        return values
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return list(_cred_value_pairs(node.target, node.value))
    if isinstance(node, ast.NamedExpr):
        return list(_cred_value_pairs(node.target, node.value))
    return []
def _collect_none_compare(node: ast.AST, none_compares: list) -> None:
    if not isinstance(node, ast.Compare):
        return
    for i, op in enumerate(node.ops):
        if (isinstance(op, (ast.Eq, ast.NotEq))
                and _has_none_operand(node, i)):
            none_compares.append(node)
            break
def _has_none_operand(node: ast.Compare, index: int) -> bool:
    comparator = node.comparators[index]
    left = node.left if index == 0 else node.comparators[index - 1]
    return is_none_literal(comparator) or is_none_literal(left)
def _static_scan_pass(tree: ast.Module) -> tuple[set, list, list]:
    shadow_sites = _comp_shadow_sites(tree)
    include_annotations = not module_postpones_annotations(tree)
    mutated_names = _ModuleScopeDispatcher(
        shadow_sites, include_annotations=include_annotations).run(tree)
    guard_stats = _lock_guard_stats(
        tree, mutated_names, shadow_sites, include_annotations)
    mutated = {_name for _name, _counts in guard_stats.items()
               if not _is_fully_guarded(_counts)}
    cred_lines: list = []
    none_compares: list = []
    for node in walk_nodes(tree):
        _collect_cred_line(node, cred_lines)
        _collect_none_compare(node, none_compares)
    return mutated, sorted(set(cred_lines)), none_compares
def _iter_assign_pairs(targets: list, value):
    for t in targets:
        if isinstance(t, ast.Name):
            yield t.id, value
            continue
        destructured = _destructure_pairs(t, value)
        if destructured:
            for e, v in destructured:
                yield e.id, v
def _destructure_pairs(target: Any,
                       value: Any) -> list[tuple[ast.Name, ast.expr]] | None:
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return None
    targets = list(target.elts)
    values = list(value.elts)
    starred = [index for index, item in enumerate(targets)
               if isinstance(item, ast.Starred)]
    if len(starred) > 1:
        return None
    if not starred and len(targets) != len(values):
        return None
    if starred and len(values) < len(targets) - 1:
        return None
    if starred:
        star_index = starred[0]
        trailing = len(targets) - star_index - 1
        value_offset = len(values) - len(targets)
        star_stop = len(values) - trailing if trailing else len(values)
        aligned = []
        for index, target_item in enumerate(targets):
            if index == star_index:
                bound_value = ast.copy_location(
                    ast.List(elts=values[star_index:star_stop], ctx=ast.Load()),
                    value)
            else:
                value_index = index if index < star_index else index + value_offset
                bound_value = values[value_index]
            aligned.append((target_item, bound_value))
    else:
        aligned = list(zip(targets, values, strict=True))
    pairs: list[tuple[ast.Name, ast.expr]] = []
    for target_item, bound_value in aligned:
        if isinstance(target_item, ast.Name):
            pairs.append((target_item, bound_value))
        elif isinstance(target_item, ast.Starred):
            if isinstance(target_item.value, ast.Name):
                pairs.append((target_item.value, bound_value))
            elif isinstance(target_item.value, (ast.Tuple, ast.List)):
                nested = _destructure_pairs(target_item.value, bound_value)
                if nested:
                    pairs.extend(nested)
        elif isinstance(target_item, (ast.Tuple, ast.List)):
            nested = _destructure_pairs(target_item, bound_value)
            if nested:
                pairs.extend(nested)
    return pairs
def _walrus_module_paired(n, class_depth: int, in_comp: bool) -> bool:
    return (isinstance(n, ast.NamedExpr)
            and (class_depth == 0 or in_comp))
def _push_eval_zone(stack: list, node: Any, class_depth: int,
                    in_comp: bool, include_annotations: bool,
                    global_names=()) -> None:
    stack.extend(
        (_e, class_depth, in_comp, global_names)
        for _e in _eval_zone_exprs(node, include_annotations))
def _iter_module_walrus_bindings(tree: ast.Module):
    include_annotations = not module_postpones_annotations(tree)
    stack: list[tuple[ast.AST, int, bool, set | tuple]] = [
        (n, 0, False, ()) for n in tree.body]
    while stack:
        n, class_depth, in_comp, global_names = stack.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.Lambda, ast.ClassDef)):
            _push_eval_zone(
                stack, n, class_depth, in_comp, include_annotations,
                global_names)
            stack.extend(_class_body_frames(n, class_depth, in_comp))
            continue
        if (_walrus_module_paired(n, class_depth, in_comp)
                or (isinstance(n, ast.NamedExpr)
                    and n.target.id in global_names)):
            yield n.target.id, n.value, n.lineno
        child_comp = _descend_in_comp(n, in_comp)
        stack.extend(
            (k, class_depth, child_comp, global_names)
            for k in _iter_analysis_children(n, include_annotations))
def _class_body_frames(node: ast.AST, class_depth: int, in_comp: bool):
    if not isinstance(node, ast.ClassDef):
        return ()
    global_names = _declared_global_names(node)
    return [(_b, class_depth + 1, in_comp, global_names)
            for _b in node.body]
class _StaticFindingSink(NamedTuple):
    findings: list
    fp: str
    rel_path: str
def _append_static_finding(sink: _StaticFindingSink, *,
                          rule_id: str, severity: str, confidence: float,
                          message: str, line: int, family: str) -> None:
    if has_inline_suppression(sink.fp, line, rule_id):
        return
    sink.findings.append({
        "rule_id": rule_id,
        "severity": severity,
        "confidence": confidence,
        "message": message,
        "file": sink.rel_path, "line": line,
        "source": "E1-static",
        "family": family,
    })
def _collect_cred_findings(sink: _StaticFindingSink,
                           cred_lines: list) -> None:
    for cred_line in cred_lines:
        _append_static_finding(
            sink, rule_id="E1-HARDCODED-CRED",
            severity="P0", confidence=0.85,
            message="检测到硬编码凭据", line=cred_line,
            family="credential_leak")
def _collect_none_compare_findings(sink: _StaticFindingSink,
                                   none_compare_nodes: list) -> None:
    for node in none_compare_nodes:
        _append_static_finding(
            sink, rule_id="E1-NONE-COMPARE",
            severity="P3", confidence=0.60,
            message="使用 ==/!= 与 None 比较，应使用 is/is not",
            line=node.lineno, family="code_smell")
def _append_mutable_global_finding(sink: _StaticFindingSink,
                                   name: str, lineno: int) -> None:
    _append_static_finding(
        sink, rule_id="E1-MUTABLE-GLOBAL",
        severity="P2", confidence=0.50,
        message=f"模块级可变变量 '{name}'", line=lineno,
        family="mutable_global")
def _is_mutable_candidate(name: str, bound, mutated_names) -> bool:
    return (not name.startswith("_")
            and is_mutable_default(bound)
            and name in mutated_names)
def _module_assign_pairs(node: ast.AST):
    if isinstance(node, ast.Assign):
        return _iter_assign_pairs(node.targets, node.value)
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return _iter_assign_pairs([node.target], node.value)
    return ()
def _iter_class_global_assign_bindings(tree: ast.Module):
    for class_node in _iter_import_time_classes(tree):
        global_names = _declared_global_names(class_node)
        if not global_names:
            continue
        for node in _iter_control_flow_stmts(class_node.body):
            for name, bound in _module_assign_pairs(node):
                if name in global_names:
                    yield name, bound, node.lineno
def _iter_function_global_bindings(tree: ast.Module):
    for function_node in walk_nodes(tree):
        if not isinstance(function_node,
                          (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        global_names = _declared_global_names(function_node)
        if not global_names:
            continue
        for node, _in_comp in _own_nodes(function_node):
            for name, bound in _module_assign_pairs(node):
                if name in global_names:
                    yield name, bound, node.lineno
            if (isinstance(node, ast.NamedExpr)
                    and node.target.id in global_names):
                yield node.target.id, node.value, node.lineno

def _collect_mutable_global_findings(sink: _StaticFindingSink,
                                     tree: ast.Module, mutated_names) -> None:
    for node in _iter_control_flow_stmts(tree.body):
        for name, bound in _module_assign_pairs(node):
            if _is_mutable_candidate(name, bound, mutated_names):
                _append_mutable_global_finding(sink, name, node.lineno)
    for bindings in (_iter_class_global_assign_bindings(tree),
                     _iter_function_global_bindings(tree)):
        for name, bound, lineno in bindings:
            if _is_mutable_candidate(name, bound, mutated_names):
                _append_mutable_global_finding(sink, name, lineno)
def _collect_walrus_mutable_findings(sink: _StaticFindingSink,
                                     tree: ast.Module, mutated_names) -> None:
    for wname, wbound, wline in _iter_module_walrus_bindings(tree):
        if _is_mutable_candidate(wname, wbound, mutated_names):
            _append_mutable_global_finding(sink, wname, wline)
_TAINT_SCAN_SKIP_DIRS = frozenset(
    GENERIC_SCAN_IGNORE_DIRS_LOWER | CACHE_TEMP_DIR_NAMES)
def _log_walk_error(err: OSError) -> None:
    logger.warning("[E1-static] 目录不可读，跳过并继续: %s", err)
def analyze_directory(dirpath: str) -> list:
    if not os.path.isdir(dirpath):
        if os.path.isfile(dirpath) and is_scan_py_name(os.path.basename(dirpath)):
            return [TaintTracker().analyze_file(dirpath)]
        return []
    tracker = TaintTracker()
    results = []
    for root, dirs, files in os.walk(dirpath, onerror=_log_walk_error):
        dirs[:] = sorted(
            d for d in dirs
            if not is_pruned_scan_dir(d, _TAINT_SCAN_SKIP_DIRS))
        for fname in sorted(files):
            if is_scan_py_name(fname):
                results.append(tracker.analyze_file(os.path.join(root, fname)))
    return results
class StaticAnalyzer:
    def __init__(
            self, skill_dir: str, cache=None,
            include_tests: bool = _tool_channels.DEFAULT_INCLUDE_TESTS):
        root = coerce_skill_dir(skill_dir)
        self.skill_dir = os.path.abspath(root) if root.strip() else ""
        self._cache = cache
        self._include_tests = signal_bool(include_tests)
    def run(self, py_files: list[str] | None = None) -> dict:
        start = time.perf_counter()
        findings: list[dict] = []
        py_files = (_tool_channels.resolve_scan_targets(
            py_files, self.skill_dir, self._include_tests)
            if self.skill_dir else [])
        detect_failed = 0
        for fp in py_files:
            finding_start = len(findings)
            try:
                scanned = self._scan_one_file(findings, fp)
            except Exception as exc:
                logger.warning(
                    "[E1-static] 静态检测失败，跳过 %s: %s",
                    fp, exc, exc_info=True)
                scanned = False
            if not scanned:
                del findings[finding_start:]
                detect_failed += 1
        no_targets = not py_files
        all_failed = bool(py_files) and detect_failed == len(py_files)
        status = "error" if no_targets or all_failed else "pass"
        summary = f"静态分析: {len(findings)} findings"
        if no_targets:
            summary += "；没有可扫描的 Python 文件，扫描未执行"
        elif detect_failed:
            summary += (f"（检测失败{detect_failed}文件,"
                        f"扫描覆盖不完整!）")
        if all_failed:
            summary += "；所有目标文件均未能完成扫描"
        return {
            "findings": findings,
            "findings_count": len(findings),
            "status": status,
            "summary": summary,
            "elapsed_ms": _tool_channels.elapsed_ms(start),
            "detect_failed": detect_failed,
            "files_scanned": len(py_files) - detect_failed,
        }
    def _scan_one_file(self, findings: list[dict], fp: str) -> bool:
        tree = _cached_tree(self._cache, fp)
        if tree is None:
            return False
        rel_path = safe_relpath(fp, self.skill_dir, normalize=False)
        mutated_names, cred_lines, none_compare_nodes = _static_scan_pass(tree)
        sink = _StaticFindingSink(findings, fp, rel_path)
        _collect_cred_findings(sink, cred_lines)
        _collect_none_compare_findings(sink, none_compare_nodes)
        _collect_mutable_global_findings(sink, tree, mutated_names)
        _collect_walrus_mutable_findings(sink, tree, mutated_names)
        return True
def _cached_tree(cache, fp: str):
    if cache is not None:
        try:
            tree = cache.get_ast(fp)
        except Exception as e:
            logger.debug("缓存 AST 读取失败，回退解析: %s", e, exc_info=True)
            tree = None
        if tree is not None:
            if isinstance(tree, ast.Module):
                return tree
            logger.debug("缓存 AST 形态非法（%s），回退解析: %s",
                         type(tree).__name__, fp)
    return parse_py_file(fp, quiet=True)[1]

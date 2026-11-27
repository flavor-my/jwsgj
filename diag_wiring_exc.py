from __future__ import annotations

import ast
import logging
import re
from collections.abc import Iterable, Iterator
from typing import Any, NamedTuple

from jwsgj.diag_detector_findings import normalize_id_set
from jwsgj.diag_shared_ast_nodes import (
    block_may_fall_through,
    get_call_name,
    import_alias_bound_name,
    import_alias_bound_names,
    is_placeholder_stmt,
    iter_arg_defaults,
    iter_def_site_nodes,
    iter_own_scope,
    iter_pattern_capture_names,
    matches_any,
    module_postpones_annotations,
    walk_stmts,
)
from jwsgj.diag_shared_ast_nodes import dotted_name as _dotted_name
from jwsgj.diag_shared_ast_views import iter_nodes as _iter_nodes
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    ast_split_lines,
    extract_code_lines,
    leading_quote_states,
    scan_line_quote_state,
)
from jwsgj.diag_shared_source_scan import (
    extract_log_level,
    has_noqa,
    has_recovery_assignment,
    is_logger_call,
    is_silent_handler,
)
from jwsgj.diag_types_defs import finding_scan_exempt
from jwsgj.log_config import log_swallowed

__all__ = [
    'check_RF01',
    'check_SN01',
    'check_SN02',
    'check_SN03',
    'check_SN04',
    'check_SN05',
    'check_all_SN',
    'collect_frame_evidence',
    'walk_handler_scope_frame_aware',
]
_log = logging.getLogger(__name__)
_log.info(
    "diag_wiring_exc 作用域/静默吞错域已加载: %d 项导出",
    len(__all__))
_EXC_STACK_EXHAUSTED = object()
_EMPTY_NAMES: frozenset = frozenset()
_COMPREHENSION_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                        ast.GeneratorExp)
_NESTED_FRAME_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                       *_COMPREHENSION_TYPES, ast.ClassDef)
_MATCH_CASE_TYPES = ((ast.match_case,) if hasattr(ast, "match_case") else ())
_PATTERN_TYPES = ((ast.pattern,) if hasattr(ast, "pattern") else ())
def _exception_type_nodes(exc_node) -> tuple:
    if isinstance(exc_node, ast.Tuple):
        nodes: list = []
        for element in exc_node.elts:
            nodes.extend(_exception_type_nodes(element))
        return tuple(nodes)
    return (exc_node,)
def _except_type_names(exc_node) -> list[str]:
    names: list[str] = []
    for node in _exception_type_nodes(exc_node):
        name = _dotted_name(node)
        if name:
            names.append(name.removeprefix('builtins.'))
    return names
def _note_direct_bind(child, parent, binds: set) -> None:
    if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Store):
        binds.add(child.id)
        return
    if isinstance(child, ast.arg):
        binds.add(child.arg)
        return
    if isinstance(child, ast.alias):
        bind_name = import_alias_bound_name(
            child, from_import=isinstance(parent, ast.ImportFrom))
        if bind_name is not None:
            binds.add(bind_name)
        return
    if _PATTERN_TYPES and isinstance(child, _PATTERN_TYPES):
        binds.update(iter_pattern_capture_names(child))
        return
    if isinstance(child, ast.ExceptHandler) and child.name:
        binds.add(child.name)
def _iter_frame_binding_roots(frame_root: ast.AST):
    if isinstance(frame_root, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda)):
        body = frame_root.body
        body_nodes = body if isinstance(body, list) else [body]
        yield from body_nodes
        args = getattr(frame_root, 'args', None)
        if args is not None:
            yield from _iter_frame_param_nodes(args)
        return
    if isinstance(frame_root, ast.ClassDef):
        yield from frame_root.body
        return
    yield from ast.iter_child_nodes(frame_root)
def _walrus_names_no_scope(node) -> frozenset:
    if node is None:
        return frozenset()
    if isinstance(node, ast.NamedExpr):
        inner = _walrus_names_no_scope(node.value)
        if isinstance(node.target, ast.Name):
            return frozenset((node.target.id,)) | inner
        return inner
    if isinstance(node, (ast.Lambda, *_COMPREHENSION_TYPES)):
        return frozenset()
    names: set = set()
    for sub in ast.iter_child_nodes(node):
        if isinstance(sub, ast.expr):
            names |= _walrus_names_no_scope(sub)
        elif isinstance(sub, ast.keyword):
            names |= _walrus_names_no_scope(sub.value)
    return frozenset(names)
def _enclosing_scope_walrus_names(node) -> frozenset:
    if node is None:
        return frozenset()
    if isinstance(node, ast.NamedExpr):
        inner = _enclosing_scope_walrus_names(node.value)
        if isinstance(node.target, ast.Name):
            return frozenset((node.target.id,)) | inner
        return inner
    if isinstance(node, _COMPREHENSION_TYPES):
        names = (_enclosing_scope_walrus_names(node.generators[0].iter)
                 if node.generators else frozenset())
        for gen in node.generators[1:]:
            names |= _walrus_names_no_scope(gen.iter)
        for gen in node.generators:
            for cond in gen.ifs:
                names |= _walrus_names_no_scope(cond)
        if isinstance(node, ast.DictComp):
            names |= _walrus_names_no_scope(node.key)
            names |= _walrus_names_no_scope(node.value)
        else:
            names |= _walrus_names_no_scope(node.elt)
        return frozenset(names)
    if isinstance(node, ast.Lambda):
        names = set()
        for default in iter_arg_defaults(node.args):
            names |= _enclosing_scope_walrus_names(default)
        return frozenset(names)
    names = set()
    for sub in ast.iter_child_nodes(node):
        if isinstance(sub, ast.expr):
            names |= _enclosing_scope_walrus_names(sub)
        elif isinstance(sub, ast.keyword):
            names |= _enclosing_scope_walrus_names(sub.value)
    return frozenset(names)
def _iter_frame_param_nodes(args):
    for _name in ('posonlyargs', 'args', 'kwonlyargs'):
        yield from (getattr(args, _name, None) or [])
    for _name in ('vararg', 'kwarg'):
        _node = getattr(args, _name, None)
        if _node is not None:
            yield _node
def _collect_direct_frame_binds(frame_root: ast.AST) -> frozenset:
    binds: set = set()
    declared: set = set()
    stack = [(iter(_iter_frame_binding_roots(frame_root)), frame_root)]
    while stack:
        _it, _parent = stack[-1]
        child = next(_it, _EXC_STACK_EXHAUSTED)
        if child is _EXC_STACK_EXHAUSTED:
            stack.pop()
            continue
        if isinstance(child, _COMPREHENSION_TYPES):
            binds.update(_enclosing_scope_walrus_names(child))
            continue
        if isinstance(child, _NESTED_FRAME_TYPES):
            for site in iter_def_site_nodes(child):
                binds.update(_enclosing_scope_walrus_names(site))
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                binds.add(child.name)
            continue
        if isinstance(child, (ast.Global, ast.Nonlocal)):
            declared.update(child.names)
            continue
        _note_direct_bind(child, _parent, binds)
        if isinstance(child, ast.arg):
            continue
        stack.append((iter(ast.iter_child_nodes(child)), child))
    return frozenset(binds - declared)
class _FrameCtx:
    __slots__ = ('kind', 'lexical_base', 'local_binds', 'module_scope',
                 'shadow', 'visible', 'walrus_ctx')
    def __init__(self, kind: str, *, module_scope: bool,
                 shadow: frozenset = _EMPTY_NAMES,
                 visible: frozenset = _EMPTY_NAMES,
                 lexical_base: frozenset = _EMPTY_NAMES,
                 local_binds: set | None = None,
                 walrus_ctx: _FrameCtx | None = None) -> None:
        self.kind = kind
        self.module_scope = module_scope
        self.shadow = shadow
        self.visible = visible
        self.lexical_base = lexical_base
        self.local_binds = local_binds if local_binds is not None else set()
        self.walrus_ctx = walrus_ctx
    def inherited_base(self) -> frozenset:
        return self.lexical_base if self.kind == 'class' else self.visible
    def with_shadow(self, shadow: frozenset) -> _FrameCtx:
        return _FrameCtx(self.kind, module_scope=self.module_scope,
                         shadow=shadow, visible=self.visible,
                         lexical_base=self.lexical_base,
                         local_binds=self.local_binds,
                         walrus_ctx=self.walrus_ctx)
    def nested(self, kind: str, inner_binds: frozenset) -> _FrameCtx:
        base = self.inherited_base()
        visible = base | inner_binds
        local_binds = (set()
                       if kind == 'class' and self.module_scope
                       else set(inner_binds))
        return _FrameCtx(
            kind, module_scope=self.module_scope,
            shadow=self.shadow, visible=visible,
            lexical_base=(base if kind == 'class' else visible),
            local_binds=local_binds, walrus_ctx=None)
def _name_evidence_suppressed(child, ctx: _FrameCtx,
                              evidence: bool) -> bool:
    if child.id in ctx.shadow:
        return True
    pool = (ctx.local_binds
            if evidence or ctx.kind == 'class' else ctx.visible)
    return child.id in pool
def _name_event_emitted(ctx: _FrameCtx, child, evidence: bool) -> bool:
    if isinstance(child.ctx, ast.Store) and ctx.kind == 'class':
        ctx.local_binds.add(child.id)
        return False
    if (evidence and isinstance(child.ctx, ast.Store)
            and ctx.kind != 'handler'):
        return False
    return not _name_evidence_suppressed(child, ctx, evidence)
def _nested_frame_kind(ctx: _FrameCtx, child: ast.AST) -> str:
    if ctx.kind == 'deferred':
        return 'deferred'
    if isinstance(child, ast.ClassDef):
        return 'class'
    return 'deferred'
def _iter_nested_body_nodes(node: ast.AST):
    body = node.body
    if isinstance(body, list):
        return iter(body)
    return iter((body,))
def _function_annotation_nodes(node: ast.AST) -> frozenset:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return frozenset()
    nodes = {arg.annotation for arg in _iter_frame_param_nodes(node.args)
             if arg.annotation is not None}
    if node.returns is not None:
        nodes.add(node.returns)
    return frozenset(nodes)
def _iter_runtime_def_site_nodes(node: ast.AST, *,
                                 annotations_postponed: bool):
    annotations = (_function_annotation_nodes(node)
                   if annotations_postponed else frozenset())
    for site in iter_def_site_nodes(node):
        if site not in annotations:
            yield site
def _direct_frame_global_names(frame_root: ast.AST) -> frozenset:
    return frozenset(
        name
        for node in iter_own_scope(frame_root, skip_lambda=True)
        if isinstance(node, ast.Global)
        for name in node.names)
def _push_nested_frame(stack: list, ctx: _FrameCtx, child: ast.AST, *,
                       annotations_postponed: bool) -> None:
    inner = ctx.nested(_nested_frame_kind(ctx, child),
                       _collect_direct_frame_binds(child))
    global_names = _direct_frame_global_names(child)
    if global_names:
        inner = inner.with_shadow(inner.shadow | global_names)
    stack.append((inner, _iter_nested_body_nodes(child)))
    _sites = list(_iter_runtime_def_site_nodes(
        child, annotations_postponed=annotations_postponed))
    if _sites:
        _push_nodes(stack, ctx, iter(_sites))
def _comprehension_inner_nodes(comp) -> list:
    nodes: list = []
    for _idx, gen in enumerate(comp.generators):
        if _idx:
            nodes.append(gen.iter)
        nodes.append(gen.target)
        nodes.extend(gen.ifs)
    if isinstance(comp, ast.DictComp):
        nodes.extend((comp.key, comp.value))
    else:
        nodes.append(comp.elt)
    return nodes
def _push_comprehension(stack: list, ctx: _FrameCtx, comp) -> None:
    inner_kind = ('deferred'
                  if (ctx.kind == 'deferred'
                      or isinstance(comp, ast.GeneratorExp))
                  else 'comp')
    inner_binds = (_collect_direct_frame_binds(comp)
                   - _enclosing_scope_walrus_names(comp))
    inner = ctx.nested(inner_kind, inner_binds)
    inner.walrus_ctx = ctx.walrus_ctx or ctx
    stack.append((inner, iter(_comprehension_inner_nodes(comp))))
    _push_nodes(stack, ctx, iter((comp.generators[0].iter,)))
def _extended_shadow(shadow, child) -> frozenset:
    if child.name:
        return shadow | frozenset((child.name,))
    return shadow
def _annotation_loads_evaluated(ctx: _FrameCtx,
                                annotations_evaluated: bool,
                                annotations_postponed: bool = False) -> bool:
    if annotations_postponed:
        return False
    if ctx.kind == 'class':
        return True
    if ctx.kind in ('handler', 'comp'):
        return annotations_evaluated
    return False
def _note_frame_decl_bind(ctx: _FrameCtx, child: ast.AST,
                          evidence: bool) -> None:
    if (evidence and ctx.kind == 'class'
            and isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef))):
        ctx.local_binds.add(child.name)
def _walk_frame_events(ctx: _FrameCtx, children, *,
                       evidence: bool, annotations_evaluated: bool,
                       annotations_postponed: bool):
    stack = [(ctx, iter(children))]
    while stack:
        ctx, children = stack[-1]
        child = next(children, _EXC_STACK_EXHAUSTED)
        if child is _EXC_STACK_EXHAUSTED:
            stack.pop()
            continue
        emitted, handled = _frame_dispatch(
            stack, ctx, child, evidence, annotations_evaluated,
            annotations_postponed)
        yield from emitted
        if handled:
            continue
        yield (child, ctx.kind)
        _push_nodes(stack, ctx, iter(ast.iter_child_nodes(child)))
def walk_handler_scope_frame_aware(handler: ast.ExceptHandler, *,
                                   evidence: bool = False,
                                   annotations_evaluated: bool = False,
                                   annotations_postponed: bool = False,
                                   module_scope: bool = False):
    yield from _walk_frame_events(
        _FrameCtx('handler', module_scope=module_scope),
        handler.body or (), evidence=evidence,
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
def _frame_visit_except_handler(stack: list, ctx: _FrameCtx,
                                child: ast.ExceptHandler) -> tuple:
    _push_nodes(stack,
                ctx.with_shadow(_extended_shadow(ctx.shadow, child)),
                iter(child.body or ()))
    if child.type is not None:
        _push_nodes(stack, ctx, iter((child.type,)))
    return ()
def _frame_visit_comprehension(stack: list, ctx: _FrameCtx,
                               child: ast.AST) -> tuple:
    _push_comprehension(stack, ctx, child)
    return ((child, ctx.kind),)
def _frame_visit_nested(stack: list, ctx: _FrameCtx, child: ast.AST, *,
                        evidence: bool,
                        annotations_postponed: bool) -> tuple:
    _note_frame_decl_bind(ctx, child, evidence)
    _push_nested_frame(stack, ctx, child,
                       annotations_postponed=annotations_postponed)
    return ((child, ctx.kind),)
def _frame_visit_annassign(stack: list, ctx: _FrameCtx,
                           child: ast.AnnAssign, *,
                           annotations_evaluated: bool,
                           annotations_postponed: bool) -> tuple:
    nodes: list = []
    if child.value is not None:
        nodes.extend((child.value, child.target))
    elif not isinstance(child.target, ast.Name):
        nodes.append(child.target)
    if _annotation_loads_evaluated(
            ctx, annotations_evaluated, annotations_postponed):
        nodes.append(child.annotation)
    if nodes:
        _push_nodes(stack, ctx, iter(nodes))
    return ((child, ctx.kind),)
def _frame_visit_namedexpr(stack: list, ctx: _FrameCtx, child: ast.NamedExpr,
                           *, evidence: bool) -> tuple:
    target_ctx = ctx.walrus_ctx or ctx
    emitted: tuple = ()
    deferred_cross_frame = (ctx.kind == 'deferred'
                            and target_ctx.kind != 'deferred')
    if deferred_cross_frame:
        pass
    elif evidence and target_ctx.kind == 'class':
        target_ctx.local_binds.add(child.target.id)
    elif not evidence or target_ctx.kind == 'handler':
        emitted = ((child.target, target_ctx.kind),)
    _push_nodes(stack, ctx, iter((child.value,)))
    return emitted
def _frame_visit_name(ctx: _FrameCtx, child: ast.Name, *,
                      evidence: bool) -> tuple:
    if not _name_event_emitted(ctx, child, evidence):
        return ()
    return ((child, ctx.kind),)
def _frame_visit_match_case(stack: list, ctx: _FrameCtx,
                            child: ast.AST) -> tuple:
    captures = frozenset(iter_pattern_capture_names(child.pattern))
    case_ctx = (ctx.with_shadow(ctx.shadow | captures)
                if captures else ctx)
    _push_nodes(stack, case_ctx, iter(ast.iter_child_nodes(child)))
    return ((child, ctx.kind),)
def _frame_visit_class_if(child: ast.If, ctx: _FrameCtx, *,
                          evidence: bool, annotations_evaluated: bool,
                          annotations_postponed: bool):
    yield (child, ctx.kind)
    yield from _walk_frame_events(
        ctx, (child.test,), evidence=evidence,
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    base = set(ctx.local_binds)
    outcomes = []
    blocks = (child.body, child.orelse)
    if isinstance(child.test, ast.Constant):
        blocks = (child.body if bool(child.test.value) else child.orelse,)
    for block in blocks:
        branch_ctx = ctx.with_shadow(ctx.shadow)
        branch_ctx.local_binds = set(base)
        yield from _walk_frame_events(
            branch_ctx, block, evidence=evidence,
            annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed)
        if block_may_fall_through(block):
            outcomes.append(branch_ctx.local_binds)
    if not outcomes:
        return
    merged = set(outcomes[0])
    for state in outcomes[1:]:
        merged.intersection_update(state)
    ctx.local_binds.clear()
    ctx.local_binds.update(merged)
def _class_loop_guarantees_body(child: ast.AST) -> bool:
    if isinstance(child, ast.While):
        return (isinstance(child.test, ast.Constant)
                and bool(child.test.value))
    if not isinstance(child, (ast.For, ast.AsyncFor)):
        return False
    iterable = child.iter
    if isinstance(iterable, (ast.List, ast.Tuple, ast.Set)):
        return bool(iterable.elts) and all(
            not isinstance(element, ast.Starred)
            for element in iterable.elts)
    if isinstance(iterable, ast.Dict):
        return bool(iterable.keys) and all(
            key is not None for key in iterable.keys)
    return (isinstance(iterable, ast.Constant)
            and isinstance(iterable.value, (str, bytes))
            and bool(iterable.value))

def _loop_has_own_break(node: ast.AST) -> bool:
    stack = list(getattr(node, 'body', ()))
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Break):
            return True
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef,
                                ast.For, ast.AsyncFor, ast.While)):
            continue
        stack.extend(ast.iter_child_nodes(current))
    return False

def _frame_visit_class_loop(child: ast.AST, ctx: _FrameCtx, *,
                            evidence: bool, annotations_evaluated: bool,
                            annotations_postponed: bool):
    yield (child, ctx.kind)
    evaluated = child.test if isinstance(child, ast.While) else child.iter
    yield from _walk_frame_events(
        ctx, (evaluated,), evidence=evidence,
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    base = set(ctx.local_binds)
    body_ctx = ctx.with_shadow(ctx.shadow)
    body_ctx.local_binds = set(base)
    if isinstance(child, (ast.For, ast.AsyncFor)):
        yield from _walk_frame_events(
            body_ctx, (child.target,), evidence=evidence,
            annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed)
    yield from _walk_frame_events(
        body_ctx, child.body, evidence=evidence,
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    body_bound = set(body_ctx.local_binds)
    guaranteed = _class_loop_guarantees_body(child)
    else_ctx = ctx.with_shadow(ctx.shadow)
    else_ctx.local_binds = set(body_bound if guaranteed else base)
    yield from _walk_frame_events(
        else_ctx, child.orelse, evidence=evidence,
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    if _loop_has_own_break(child):
        merged = ((body_bound if guaranteed else base)
                  & else_ctx.local_binds)
    else:
        merged = else_ctx.local_binds
    ctx.local_binds.clear()
    ctx.local_binds.update(merged)

def _frame_dispatch(stack: list, ctx: _FrameCtx, child: ast.AST,
                    evidence: bool, annotations_evaluated: bool,
                    annotations_postponed: bool) -> tuple[Any, bool]:
    if isinstance(child, ast.ExceptHandler):
        return _frame_visit_except_handler(stack, ctx, child), True
    if isinstance(child, _COMPREHENSION_TYPES):
        return _frame_visit_comprehension(stack, ctx, child), True
    if isinstance(child, _NESTED_FRAME_TYPES):
        return _frame_visit_nested(
            stack, ctx, child, evidence=evidence,
            annotations_postponed=annotations_postponed), True
    if isinstance(child, ast.AnnAssign):
        return _frame_visit_annassign(
            stack, ctx, child, annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed), True
    if isinstance(child, ast.If) and ctx.kind == 'class':
        return _frame_visit_class_if(
            child, ctx, evidence=evidence,
            annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed), True
    if (isinstance(child, (ast.For, ast.AsyncFor, ast.While))
            and ctx.kind == 'class'):
        return _frame_visit_class_loop(
            child, ctx, evidence=evidence,
            annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed), True
    if isinstance(child, ast.NamedExpr) and ctx.walrus_ctx is not None:
        return _frame_visit_namedexpr(
            stack, ctx, child, evidence=evidence), True
    if isinstance(child, ast.Name):
        return _frame_visit_name(ctx, child, evidence=evidence), True
    if _MATCH_CASE_TYPES and isinstance(child, _MATCH_CASE_TYPES):
        return _frame_visit_match_case(stack, ctx, child), True
    if (evidence and ctx.kind == 'class'
            and isinstance(child, (ast.Import, ast.ImportFrom))):
        ctx.local_binds.update(import_alias_bound_names(child))
    return (), False
def _push_nodes(stack: list, ctx: _FrameCtx, nodes) -> None:
    stack.append((ctx, nodes))
def _note_declared_binds(child, bind_lines) -> None:
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
        bind_lines.setdefault(child.name, []).append(child.lineno)
        return
    if isinstance(child, (ast.Import, ast.ImportFrom)):
        from_import = isinstance(child, ast.ImportFrom)
        for alias in child.names:
            bind_name = import_alias_bound_name(
                alias, from_import=from_import)
            if bind_name is not None:
                bind_lines.setdefault(bind_name, []).append(alias.lineno)
        return
    if isinstance(child, ast.Nonlocal):
        for gname in child.names:
            bind_lines.setdefault(gname, []).append(child.lineno)
        return
    if _PATTERN_TYPES and isinstance(child, _PATTERN_TYPES):
        for capture in iter_pattern_capture_names(child):
            bind_lines.setdefault(capture, []).append(child.lineno)
def collect_frame_evidence(
        handler: ast.ExceptHandler, *,
        annotations_evaluated: bool = False,
        annotations_postponed: bool = False,
        module_scope: bool = False,
        ) -> tuple[dict[str, list[int]], dict[str, list[int]]]:
    bind_lines: dict[str, list[int]] = {}
    load_lines: dict[str, list[int]] = {}
    for child, frame_kind in walk_handler_scope_frame_aware(
            handler, evidence=True,
            annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed,
            module_scope=module_scope):
        if frame_kind == 'deferred':
            continue
        if isinstance(child, ast.Name):
            if isinstance(child.ctx, ast.Load):
                load_lines.setdefault(child.id, []).append(child.lineno)
            elif frame_kind == 'handler' and isinstance(child.ctx, ast.Store):
                bind_lines.setdefault(child.id, []).append(child.lineno)
            continue
        if frame_kind != 'handler':
            continue
        _note_declared_binds(child, bind_lines)
    return bind_lines, load_lines
def _conditional_non_reraise_exit(stmts, _loop_depth: int = 0) -> bool:
    for stmt in stmts:
        if isinstance(stmt, ast.Raise):
            return False
        if isinstance(stmt, ast.Return):
            return True
        if isinstance(stmt, (ast.Break, ast.Continue)):
            return _loop_depth == 0
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(stmt, ast.If):
            if isinstance(stmt.test, ast.Constant):
                branch = stmt.body if bool(stmt.test.value) else stmt.orelse
                if _conditional_non_reraise_exit(branch, _loop_depth):
                    return True
                continue
            if (stmt.orelse and _always_reraises(stmt.body)
                    and _always_reraises(stmt.orelse)):
                return False
            if (_conditional_non_reraise_exit(stmt.body, _loop_depth)
                    or _conditional_non_reraise_exit(
                        stmt.orelse, _loop_depth)):
                return True
            continue
        if isinstance(stmt, TRY_TYPES):
            if stmt.finalbody and _always_reraises(stmt.finalbody):
                return False
            scopes = [stmt.body, stmt.finalbody]
            if not _always_reraises(stmt.body):
                scopes.append(stmt.orelse)
            scopes.extend(handler.body for handler in stmt.handlers)
            if any(_conditional_non_reraise_exit(scope, _loop_depth)
                   for scope in scopes):
                return True
            continue
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            if (_conditional_non_reraise_exit(stmt.body, _loop_depth + 1)
                    or _conditional_non_reraise_exit(
                        stmt.orelse, _loop_depth)):
                return True
            continue
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            if _conditional_non_reraise_exit(stmt.body, _loop_depth):
                return True
            continue
        if (isinstance(stmt, ast.Match)
                and any(_conditional_non_reraise_exit(
                    case.body, _loop_depth) for case in stmt.cases)):
            return True
    return False
def _match_irrefutable_pattern(pattern) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return (pattern.pattern is None
                or _match_irrefutable_pattern(pattern.pattern))
    if isinstance(pattern, ast.MatchOr):
        return any(_match_irrefutable_pattern(sub)
                   for sub in pattern.patterns)
    return False
def _match_always_reraises(stmt: ast.Match) -> bool:
    for case in stmt.cases:
        if not _always_reraises(case.body):
            return False
        if case.guard is None and _match_irrefutable_pattern(case.pattern):
            return True
    return False
def _always_reraises(stmts) -> bool:
    for stmt in stmts:
        if isinstance(stmt, ast.Raise):
            return True
        if isinstance(stmt, (ast.Return, ast.Break, ast.Continue)):
            return False
        if isinstance(stmt, ast.If):
            if isinstance(stmt.test, ast.Constant):
                branch = stmt.body if bool(stmt.test.value) else stmt.orelse
                if _always_reraises(branch):
                    return True
                if _conditional_non_reraise_exit(branch):
                    return False
                continue
            if (stmt.orelse and _always_reraises(stmt.body)
                    and _always_reraises(stmt.orelse)):
                return True
            if (_conditional_non_reraise_exit(stmt.body)
                    or _conditional_non_reraise_exit(stmt.orelse)):
                return False
        elif isinstance(stmt, ast.Match):
            if _match_always_reraises(stmt):
                return True
            if any(_conditional_non_reraise_exit(case.body)
                   for case in stmt.cases):
                return False
        elif isinstance(stmt, ast.While):
            if (isinstance(stmt.test, ast.Constant) and bool(stmt.test.value)
                    and _always_reraises(stmt.body)):
                return True
        elif (isinstance(stmt, (ast.With, ast.AsyncWith))
              and _always_reraises(stmt.body)):
            return True
        elif isinstance(stmt, ast.ClassDef):
            if _always_reraises(stmt.body):
                return True
        elif (not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef, ast.Lambda))
              and _conditional_non_reraise_exit((stmt,))):
            return False
        if isinstance(stmt, TRY_TYPES):
            if _always_reraises(stmt.finalbody):
                return True
            if ((_always_reraises(stmt.body)
                 or _always_reraises(stmt.orelse))
                    and all(_always_reraises(handler.body)
                            for handler in stmt.handlers)):
                return True
    return False
_GUARDIAN_PATTERNS = [
    r'guard', r'heal(?!th)', r'defen[cs]e', r'protect', r'repair',
    r'restore', r'bootstrap', r'ensure_', r'invariant',
    r'pre(?:[_-]\w*)?check', r'precondition\w*',
]
_STATE_PATTERNS = [
    r'mark_', r'record', r'increment_', r'track_', r'health_?check',
    r'(?:save|load|persist|restore|snapshot)_state', r'check_pre_',
]
_GENERAL_CRITICAL_PATTERNS = [
    r'validate_', r'verify_', r'execute_',
    r'write_', r'commit_', r'sync_', r'upload_',
    r'store_', r'persist_',
]
_GUARDIAN_RE = [re.compile(p, re.IGNORECASE) for p in _GUARDIAN_PATTERNS]
_GENERAL_RE = [re.compile(p, re.IGNORECASE) for p in _GENERAL_CRITICAL_PATTERNS]
_STATE_RE = [re.compile(p, re.IGNORECASE) for p in _STATE_PATTERNS]
def _walk_immediate_execution_nodes(stmts: Any, *,
                                    annotations_postponed: bool):
    queue = list(stmts)
    head = 0
    while head < len(queue):
        node = queue[head]
        head += 1
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            queue.extend(_iter_runtime_def_site_nodes(
                node, annotations_postponed=annotations_postponed))
            if isinstance(node, ast.ClassDef):
                queue.extend(node.body)
            continue
        yield node
        queue.extend(ast.iter_child_nodes(node))
def _collect_critical_calls(body: Any, *,
                            annotations_postponed: bool) -> list[str]:
    names: list[str] = []
    for node in _walk_immediate_execution_nodes(
            body, annotations_postponed=annotations_postponed):
        if isinstance(node, ast.Call):
            name = get_call_name(node)
            if name:
                names.append(name)
    return names
_GUARDIAN_TIER = (_GUARDIAN_RE, "P0", "guardian")
_STATE_TIER = (_STATE_RE, "P1", "state")
_GENERAL_TIER = (_GENERAL_RE, "P2", "general")
_SEVERITY_PATTERN_SPECS = (_GUARDIAN_TIER, _STATE_TIER, _GENERAL_TIER)
def _classify_severity(call_names: Any) -> tuple[str | None, str | None]:
    for patterns, severity, category in _SEVERITY_PATTERN_SPECS:
        for name in call_names:
            if matches_any(name, patterns):
                return severity, category
    return None, None
_EXPECTED_EXCEPTIONS = frozenset({
    "SyntaxError", "IndentationError", "TabError",
    "FileNotFoundError", "FileExistsError", "IsADirectoryError",
    "PermissionError", "OSError", "IOError",
    "ImportError", "ModuleNotFoundError",
    "AttributeError", "KeyError", "IndexError", "LookupError",
    "TypeError", "ValueError",
    "UnicodeDecodeError", "UnicodeEncodeError", "UnicodeError",
    "NotImplementedError", "RuntimeError",
})
def _is_expected_exception_handler(handler: Any) -> bool:
    exc_names = set(_except_type_names(
        handler.type))
    return bool(exc_names and exc_names.issubset(_EXPECTED_EXCEPTIONS))
class _SilentRuleSpec(NamedTuple):
    severity: str
    rule_id: str
    label: str
def _check_silent_swallow_by_severity(tree: Any, source_lines: Any,
                                       filepath: Any,
                                       spec: _SilentRuleSpec) -> list[dict]:
    issues = []
    annotations_postponed = module_postpones_annotations(tree)
    for node in _iter_nodes(tree, None):
        if not isinstance(node, TRY_TYPES):
            continue
        call_names = _collect_critical_calls(
            node.body, annotations_postponed=annotations_postponed)
        sev, _cat = _classify_severity(call_names)
        if sev != spec.severity:
            continue
        issues.extend(_severity_handler_issues(
            node, source_lines, filepath, spec, call_names))
    return issues
def _severity_handler_issues(node: Any, source_lines: Any, filepath: Any,
                             spec: _SilentRuleSpec,
                             call_names: list[str]) -> list[dict]:
    findings = []
    for handler in node.handlers:
        is_silent, reason = is_silent_handler(handler, source_lines)
        if not is_silent:
            continue
        findings.append({
            "rule_id": spec.rule_id,
            "severity": spec.severity,
            "file": filepath,
            "line": node.lineno,
            "handler_line": handler.lineno,
            "reason": reason,
            "critical_calls": call_names,
            "message": (
                f"{spec.label}被沉默吞错({reason}): "
                f"{', '.join(call_names[:5])}"
            ),
        })
    return findings
_SN01_SPEC = _SilentRuleSpec(_GUARDIAN_TIER[1], "SN-01",
                              "守护/修复关键调用")
_SN02_SPEC = _SilentRuleSpec(_STATE_TIER[1], "SN-02", "状态管理调用")
_SN03_SPEC = _SilentRuleSpec(_GENERAL_TIER[1], "SN-03", "关键操作")
def _make_sn_check(spec: _SilentRuleSpec):
    def _check(tree: Any, source_lines: Any, filepath: Any) -> list[dict]:
        if finding_scan_exempt(filepath):
            return []
        _log.debug("规则入口 %s 执行", spec.rule_id)
        return _check_silent_swallow_by_severity(
            tree, source_lines, filepath, spec)
    _check.__name__ = f"check_{spec.rule_id.replace('-', '')}"
    _check.__qualname__ = _check.__name__
    _check.__doc__ = f"规则 {spec.rule_id}：{spec.label}被静默吞错。"
    return _check
check_SN01 = _make_sn_check(_SN01_SPEC)
check_SN02 = _make_sn_check(_SN02_SPEC)
check_SN03 = _make_sn_check(_SN03_SPEC)
def _sn04_bare_issue(handler: Any, node: Any, source_lines: Any,
                     filepath: Any) -> dict | None:
    if handler.type is not None:
        return None
    if (source_lines is not None
            and has_noqa(source_lines, handler.lineno)):
        return None
    if _is_placeholder_body(handler.body):
        return _sn04_issue(node, handler, filepath, severity="P0",
                           reason="bare_except_pass",
                           message="裸 except: + pass —— 最危险的沉默吞错模式")
    if not _always_reraises(handler.body):
        return _sn04_issue(node, handler, filepath, severity="P1",
                           reason="bare_except_silent",
                           message="裸 except: 未重新抛出（吞掉 BaseException）")
    return None
def _sn04_issue(node: Any, handler: Any, filepath: Any, *, severity: str,
                reason: str, message: str) -> dict:
    return {
        "rule_id": "SN-04",
        "severity": severity,
        "file": filepath,
        "line": node.lineno,
        "handler_line": handler.lineno,
        "reason": reason,
        "message": message,
    }
def check_SN04(tree: Any, source_lines: Any, filepath: Any) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_SN04 执行")
    issues = []
    for node in _iter_nodes(tree, None):
        if isinstance(node, TRY_TYPES):
            for handler in node.handlers:
                issue = _sn04_bare_issue(handler, node, source_lines, filepath)
                if issue is not None:
                    issues.append(issue)
    return issues
_VISIBLE_LOG_LEVELS = frozenset({
    'info', 'warning', 'warn', 'error', 'critical', 'exception', 'fatal',
})
def _sn05_debug_issue_lines(handler: Any, source_lines: Any) -> list[int]:
    if _is_expected_exception_handler(handler):
        return []
    is_silent, _reason = is_silent_handler(handler, source_lines)
    if not is_silent:
        return []
    if has_recovery_assignment(handler.body):
        return []
    lines: list[int] = []
    for stmt in walk_stmts(handler.body):
        if not isinstance(stmt, ast.Call):
            continue
        level = extract_log_level(stmt)
        if level == 'debug':
            lines.append(stmt.lineno)
        elif level in _VISIBLE_LOG_LEVELS:
            return []
    return lines
def check_SN05(tree: Any, source_lines: Any, filepath: Any) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_SN05 执行")
    issues = []
    annotations_postponed = module_postpones_annotations(tree)
    for node in _iter_nodes(tree, None):
        if isinstance(node, TRY_TYPES):
            call_names = _collect_critical_calls(
                node.body, annotations_postponed=annotations_postponed)
            if not call_names:
                continue
            sev, _cat = _classify_severity(call_names)
            if sev is None:
                continue
            issues.extend(_sn05_try_issues(
                node, source_lines, filepath, call_names))
    return issues
def _sn05_try_issues(node: Any, source_lines: Any, filepath: Any,
                     call_names: list[str]) -> list[dict]:
    findings = []
    for handler in node.handlers:
        handler_line = getattr(handler, "lineno", node.lineno)
        for line_no in _sn05_debug_issue_lines(handler, source_lines):
            findings.append({
                "rule_id": "SN-05",
                "severity": "P2",
                "file": filepath,
                "line": line_no,
                "handler_line": handler_line,
                "reason": "debug_only",
                "message": (
                    "关键操作异常仅记录debug日志,生产环境不可见: "
                    f"{', '.join(call_names[:3])}"
                ),
            })
    return findings
_SN_RULE_CHECKS = (
    (check_SN01, "SN-01"),
    (check_SN02, "SN-02"),
    (check_SN03, "SN-03"),
    (check_SN04, "SN-04"),
    (check_SN05, "SN-05"),
)
def _upper_rule_id(rule_id: Any) -> str:
    return str(rule_id).strip().upper()
def _normalize_sn_exclude_rules(exclude_rules: Any) -> frozenset[str]:
    if not exclude_rules:
        return frozenset()
    candidates = ((exclude_rules,) if isinstance(exclude_rules, str)
                  else exclude_rules)
    if not isinstance(candidates, Iterable):
        return frozenset()
    if not isinstance(candidates, (set, frozenset, list, tuple)):
        candidates = tuple(candidates)
    return frozenset(normalize_id_set(
        str(item).strip().upper() for item in candidates))
def _rule_id_excluded(rule_id: str, exclude_rules: Any) -> bool:
    normalized = _normalize_sn_exclude_rules(exclude_rules)
    return bool(normalize_id_set((_upper_rule_id(rule_id),)) & normalized)
def check_all_SN(tree: Any, source_lines: Any, filepath: Any,
                  exclude_rules: Any = None) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_all_SN 执行")
    all_issues = []
    normalized_excludes = _normalize_sn_exclude_rules(exclude_rules)
    _fns = [
        fn for fn, rule_id in _SN_RULE_CHECKS
        if not _rule_id_excluded(rule_id, normalized_excludes)
    ]
    for fn in _fns:
        try:
            all_issues.extend(fn(tree, source_lines, filepath))
        except (AttributeError, IndexError, KeyError, TypeError, ValueError,
                RuntimeError) as e:
            log_swallowed(
                __name__, e,
                context=f"check_all_SN.{fn.__name__}:{type(e).__name__}")
    return all_issues
_BROAD_EXC_NAMES = frozenset({"Exception", "BaseException"})
_BUILTINS_BROAD_DOTTED = frozenset(
    f"builtins.{name}" for name in _BROAD_EXC_NAMES)
def _is_broad_exc_expr(t: ast.AST) -> bool:
    if isinstance(t, ast.Name):
        return t.id in _BROAD_EXC_NAMES
    if isinstance(t, ast.Attribute):
        return _dotted_name(t) in _BUILTINS_BROAD_DOTTED
    return False
def _is_broad_except_type(node: ast.ExceptHandler) -> bool:
    if node.type is None:
        return True
    return any(_is_broad_exc_expr(t)
               for t in _exception_type_nodes(node.type))
def _iter_nodes_of_type(tree: ast.AST, node_types: Any) -> Iterator[ast.AST]:
    return (node for node in _iter_nodes(tree, None)
            if isinstance(node, node_types))
def _normalize_source_lines(source: Any) -> list:
    if isinstance(source, (list, tuple)):
        return [line if isinstance(line, str) else '' for line in source]
    if isinstance(source, str) and source:
        return ast_split_lines(source)
    return []
def _span_has_comment(source_lines: list, start: int, end: int,
                      lead_states: list | None = None) -> bool:
    if not source_lines:
        return False
    _lo = max(start, 1)
    _hi = min(end, len(source_lines))
    if _lo > _hi:
        return False
    if lead_states is None:
        lead_states = leading_quote_states(source_lines)
    for ln in range(_lo, _hi + 1):
        _state = lead_states[ln - 1] if ln - 1 < len(lead_states) else ""
        if scan_line_quote_state(source_lines[ln - 1], _state)[0] >= 0:
            return True
    return False
def _is_placeholder_body(body: list[ast.stmt]) -> bool:
    return bool(body) and all(is_placeholder_stmt(stmt) for stmt in body)
def _is_silent_pass_handler(node: ast.ExceptHandler) -> bool:
    return _is_placeholder_body(node.body) and _is_broad_except_type(node)
def _make_pass_silent_issue(source_lines: list, filepath: Any,
                            pass_line: int) -> dict:
    snippet = (source_lines[pass_line - 1].strip()
               if pass_line <= len(source_lines) else '')
    return {
        "rule_id": "RF-01", "severity": "P1", "dimension": "refactor",
        "file": filepath, "line": pass_line,
        "title": "except块内仅pass且缺乏注释说明",
        "description": (
            "except块内仅含pass语句且无注释解释为何合法地静默吞异常."
            "这使得后续维护者无法判断是刻意降级还是遗漏处理."
        ),
        "code_snippet": snippet,
        "suggestion": "根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于异常处理类别。\n修复策略: 添加注释说明为何静默吞异常,如 '# 降级:xxx场景下此异常不影响核心流程'\n参考标准: PEP 8 / contextlib / pylint R1732",
        "rule_ref": "kd260602220003, rf370",
    }
def _rf01_comment_context(source: Any) -> tuple[list, list]:
    source_lines = _normalize_source_lines(source)
    return source_lines, leading_quote_states(source_lines)
def _pass_handler_comment_end(source_lines: list, node: ast.ExceptHandler,
                              pass_line: int) -> int:
    if not source_lines:
        return pass_line
    handler_line = source_lines[
        min(max(getattr(node, 'lineno', 1), 1), len(source_lines)) - 1]
    handler_indent = len(handler_line) - len(handler_line.lstrip())
    end = pass_line
    for index in range(pass_line, len(source_lines)):
        raw = source_lines[index]
        if not raw.strip():
            end = index + 1
            continue
        indent = len(raw) - len(raw.lstrip())
        if indent <= handler_indent or not raw.lstrip().startswith('#'):
            break
        end = index + 1
    return end
def _check_except_pass_silent(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None or not source:
        return issues
    source_lines, lead_states = _rf01_comment_context(source)
    if not source_lines:
        return issues
    for node in _iter_nodes_of_type(tree, ast.ExceptHandler):
        if not _is_silent_pass_handler(node):
            continue
        pass_line = node.body[0].lineno
        exc_line = node.lineno
        body_end = max(
            (getattr(stmt, 'end_lineno',
                     getattr(stmt, 'lineno', pass_line))
             for stmt in node.body),
            default=pass_line,
        )
        comment_end = _pass_handler_comment_end(
            source_lines, node, body_end)
        if not _span_has_comment(
                source_lines, exc_line, comment_end, lead_states):
            issues.append(_make_pass_silent_issue(
                source_lines, filepath, pass_line))
    return issues
def _handler_span_comment_exempt(source_lines: Any, node: Any,
                                  body: Any, lead_states: Any) -> bool:
    if not source_lines:
        return False
    block_start = node.lineno
    block_end = max(
        (getattr(_st, 'end_lineno',
                 getattr(_st, 'lineno', block_start))
         for _st in body),
        default=block_start,
    )
    comment_end = _pass_handler_comment_end(source_lines, node, block_end)
    return _span_has_comment(source_lines, block_start, comment_end,
                             lead_states)
def _handler_body_has_logging(body: Any, *,
                              annotations_postponed: bool) -> bool:
    for child in _walk_immediate_execution_nodes(
            body, annotations_postponed=annotations_postponed):
        if not isinstance(child, ast.Call):
            continue
        if is_logger_call(child):
            return True
        if isinstance(child.func, ast.Name) and child.func.id == 'print':
            return True
    return False
def _make_no_logging_issue(node: Any, source: Any, filepath: Any) -> dict:
    return {
        "rule_id": "RF-01", "severity": "P1", "dimension": "refactor",
        "file": filepath, "line": node.lineno,
        "title": "except块有处理代码但无日志记录",
        "description": (
            "except块中有处理逻辑但缺少 logging 调用."
            "异常被静默处理,问题追踪困难."
        ),
        "code_snippet": extract_code_lines(source, node.lineno),
        "suggestion": '根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于异常处理类别。\n修复策略: 在except块内使用项目自身的 logger 记录异常(如 logger.warning() / logging.exception())\n参考标准: PEP 8 / contextlib / pylint R1732',
        "rule_ref": "biz083",
    }
def _no_logging_exempt(node: ast.ExceptHandler,
                       source_lines: list, lead_states: Any) -> bool:
    if _always_reraises(node.body):
        return True
    if not _is_broad_except_type(node):
        return True
    return _handler_span_comment_exempt(source_lines, node, node.body,
                                        lead_states)
def _check_except_no_logging(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None:
        return issues
    source_lines, lead_states = _rf01_comment_context(source)
    annotations_postponed = module_postpones_annotations(tree)
    for node in _iter_nodes_of_type(tree, ast.ExceptHandler):
        if not node.body or _is_placeholder_body(node.body):
            continue
        if _no_logging_exempt(node, source_lines, lead_states):
            continue
        if not _handler_body_has_logging(
                node.body, annotations_postponed=annotations_postponed):
            issues.append(_make_no_logging_issue(node, source, filepath))
    return issues
def check_RF01(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_RF01 执行")
    issues = []
    issues.extend(_check_except_pass_silent(tree, source, filepath))
    issues.extend(_check_except_no_logging(tree, source, filepath))
    return issues
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            **{rule_id.replace('-', ''): fn
               for fn, rule_id in _SN_RULE_CHECKS},
            'RF01': check_RF01,
        },
        "early_channels": {
            "SN": (20, check_all_SN, False),
        },
    }}

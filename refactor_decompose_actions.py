from __future__ import annotations

import ast
import logging
import os
import symtable
from collections.abc import Callable
from dataclasses import dataclass, field
from os.path import abspath, normcase
from pathlib import Path
from typing import Any

from jwsgj.build_safe_write import commit_writes
from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    collect_shadow_bindings,
    enclosing_scope_binds,
    enclosing_scope_load_names,
    expr_binds,
    expr_load_roots,
    import_bound_names,
    import_stmt_binds,
    module_scope_binds,
    owner_scope,
    symtable_global_refs,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    NESTED_CTRL_TYPES,
    build_parent_map,
    collect_param_names,
    iter_import_time_nodes,
    iter_module_level_stmts,
    module_postpones_annotations,
    parse_ast_safely,
    parse_source_tree,
    pattern_capture_name,
    scope_chain,
    symbol_start_line,
)
from jwsgj.diag_shared_ast_surface import (
    extract_all_names,
    is_all_assignment,
    is_all_target,
)
from jwsgj.diag_shared_source_core import (
    physical_lines_keepends,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_normalize import as_sequence, int_or
from jwsgj.diag_types_vocab import INPLACE_MUTATING_METHODS
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.refactor_migration_commit import (
    _shared_all_assignment_error,
    remove_symbols_from_source,
    top_symbol_segments,
)
from jwsgj.refactor_migration_prepare import (
    _MODULE_CONTEXT_BUILTINS,
    retained_source_reference_blocks,
)
from jwsgj.refactor_write_actions import (
    BaseExecutor,
    ExecutorResult,
    _all_rebind_line,
    _control_flow_child_bodies,
    _dotted_module,
    _is_foldable_all_declaration,
    _is_pure_all_annotation,
    _package_parts,
    _resolve_relative_module,
)

_log = logging.getLogger(__name__)
_SYMTABLE_UNSET = object()
_STATE_MUTATING_METHODS = INPLACE_MUTATING_METHODS | frozenset({
    "__delattr__", "__setattr__",
})
_UNBOUND_STATE_MUTATOR_RECEIVERS = frozenset({
    "bytearray", "dict", "list", "object", "set",
})
_STATE_MUTATING_BUILTIN_CALLS = frozenset({"delattr", "setattr"})
_MODULE_SPLIT_CONTEXT_NAMES = frozenset({"__all__", "__annotations__"})
_CONST_SCALAR_TYPES = (str, bytes, bool, int, float, complex)
_CONST_NUMERIC_TYPES = (bool, int, float, complex)
def _is_signed_number(node: ast.expr) -> bool:
    return (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, _CONST_NUMERIC_TYPES))
def _split_pure_literal(node: ast.expr) -> bool:
    if isinstance(node, ast.Constant):
        return (isinstance(node.value, _CONST_SCALAR_TYPES)
                or node.value is None)
    if _is_signed_number(node):
        return True
    if isinstance(node, ast.Tuple):
        return all(_split_pure_literal(e) for e in node.elts)
    return False
@dataclass
class _SplitContext:
    builtin_names: set[str]
    sym_table: Any
    header_bindings: set[str]
    const_segments: dict[str, list[tuple[int, int]]]
    const_anno_loads: dict[str, set[str]]
    unsafe_names: set[str]
    outside_binds: set[str]
    outside_stars: list[str]
    src_top_defs: set[str]
    symbol_owner: dict[str, str]
    outside_bound_names: set[str]
    group_state_writes: dict[str, dict[str, str]]
    shared_state_names: set[str]
    import_bound_names: set[str]
    dynamic_context_aliases: dict[str, str]
    dynamic_module_aliases: set[str]
def _dynamic_context_imports(
        tree: ast.Module, header_end: int,
) -> tuple[dict[str, str], set[str]]:
    aliases: dict[str, str] = {}
    module_aliases: set[str] = set()
    header_nodes = [node for node in tree.body if node.lineno <= header_end]
    wrapper = ast.Module(body=header_nodes, type_ignores=[])
    for node in iter_module_level_stmts(wrapper):
        if (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module == "builtins"):
            for alias in node.names:
                if alias.name in _MODULE_CONTEXT_BUILTINS:
                    aliases[alias.asname or alias.name] = alias.name
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == "builtins":
                    module_aliases.add(alias.asname or "builtins")
    return aliases, module_aliases
def _collect_split_context(source_path: Path, src: str, tree,
                           header_end: int, header_bindings: set,
                           groups: dict, sym_table=_SYMTABLE_UNSET) -> _SplitContext:
    const_state = _classify_const_segments(tree, header_end)
    outside_binds, outside_stars = _collect_outside_binds(tree, header_end)
    _sym_table = (_build_sym_table(source_path, src)
                  if sym_table is _SYMTABLE_UNSET else sym_table)
    symbol_owner: dict[str, str] = {}
    for g, syms in groups.items():
        for s in syms:
            symbol_owner.setdefault(s, g)
    src_top_defs: set[str] = {
        node.name for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef))}
    outside_bound_names = (set(const_state.segments) | const_state.unsafe
                           | outside_binds | src_top_defs)
    header_imports = import_bound_names(
        [node for node in tree.body if node.lineno <= header_end])
    dynamic_aliases, dynamic_modules = _dynamic_context_imports(
        tree, header_end)
    return _SplitContext(
        group_state_writes=_group_state_writes(tree, symbol_owner),
        shared_state_names=((header_bindings - header_imports)
                            | set(const_state.segments)),
        import_bound_names=header_imports,
        builtin_names=set(BUILTIN_NAMES),
        sym_table=_sym_table,
        header_bindings=header_bindings,
        const_segments=const_state.segments,
        const_anno_loads=const_state.anno_loads,
        unsafe_names=const_state.unsafe,
        outside_binds=outside_binds,
        outside_stars=outside_stars,
        src_top_defs=src_top_defs,
        symbol_owner=symbol_owner,
        outside_bound_names=outside_bound_names,
        dynamic_context_aliases=dynamic_aliases,
        dynamic_module_aliases=dynamic_modules,
    )
def _target_write_kinds(target: ast.AST) -> dict[str, str]:
    if isinstance(target, ast.Name):
        return {target.id: "rebind"}
    if isinstance(target, (ast.Tuple, ast.List)):
        kinds: dict[str, str] = {}
        for elt in target.elts:
            for name, kind in _target_write_kinds(elt).items():
                if kinds.get(name) != "rebind":
                    kinds[name] = kind
        return kinds
    if isinstance(target, ast.Starred):
        return _target_write_kinds(target.value)
    root = target
    while isinstance(root, (ast.Attribute, ast.Subscript)):
        root = root.value
    if isinstance(root, ast.Name):
        return {root.id: "mutate"}
    return {name: "mutate" for name in sorted(expr_load_roots(root))}
def _state_scope_name(scope_node: ast.AST,
                      scope_index: dict[int, str]) -> str:
    if isinstance(scope_node, ast.Module):
        return ""
    name = getattr(scope_node, "name", "")
    if not name:
        return ""
    outer = scope_index.get(id(scope_node), "")
    return f"{outer}.{name}" if outer else name
def _expression_scope_shadows(
        node: ast.AST, parents: dict[int, ast.AST]) -> set[str]:
    shadowed: set[str] = set()
    generator: ast.comprehension | None = None
    in_generator_iter = False
    child = node
    parent = parents.get(id(child))
    comp_types = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
    while parent is not None:
        if isinstance(parent, ast.Lambda) and child is parent.body:
            shadowed.update(collect_param_names(parent))
            shadowed.update(expr_binds(parent.body))
        if isinstance(parent, ast.comprehension):
            generator = parent
            in_generator_iter = child is parent.iter
        elif isinstance(parent, comp_types):
            if generator is None:
                visible = list(parent.generators)
            else:
                try:
                    index = parent.generators.index(generator)
                except ValueError:
                    visible = []
                else:
                    stop = index if in_generator_iter else index + 1
                    visible = list(parent.generators[:stop])
            for current in visible:
                shadowed.update(_target_write_kinds(current.target))
            generator = None
            in_generator_iter = False
        child, parent = parent, parents.get(id(parent))
    return shadowed
def _event_scope_name(node: ast.AST, scope_index: dict[int, str],
                      parents: dict[int, ast.AST]) -> str:
    scope = scope_index.get(id(node))
    if scope is not None:
        return scope
    return next(
        (_state_scope_name(scope_node, scope_index)
         for scope_node in scope_chain(node, parents)
         if not isinstance(scope_node, ast.Lambda)), "")
def _module_state_writes(
        node: ast.AST, module_bindings: set[str] | None = None) -> dict[str, str]:
    module = (node if isinstance(node, ast.Module)
              else ast.Module(body=[node], type_ignores=[]))
    if module_bindings is None:
        module_bindings = (module_scope_binds(node.body)
                           if isinstance(node, ast.Module) else set())
    local_bindings, global_names, class_scopes = collect_shadow_bindings(module)
    scope_index = build_scope_index(module)
    parents = build_parent_map(module)
    writes: dict[str, str] = {}
    for sub in walk_nodes(node):
        targets: list[tuple[ast.AST, str]] = []
        scope = _event_scope_name(sub, scope_index, parents)
        if isinstance(sub, (ast.Assign, ast.Delete)):
            targets = [(item, "rebind") for item in sub.targets]
        elif isinstance(sub, (ast.AugAssign, ast.AnnAssign, ast.For,
                              ast.AsyncFor, ast.NamedExpr,
                              ast.comprehension)):
            targets = [(sub.target, "rebind")]
        elif isinstance(sub, (ast.With, ast.AsyncWith)):
            targets = [(item.optional_vars, "rebind")
                       for item in sub.items
                       if item.optional_vars is not None]
        elif isinstance(sub, ast.Call):
            if (isinstance(sub.func, ast.Attribute)
                    and sub.func.attr in _STATE_MUTATING_METHODS):
                receiver = sub.func.value
                # 非绑定的内建容器类（dict.update(d, ...)）只变异首参，
                # 类对象自身不是模块状态，不得记为写入。
                unbound_builtin = bool(
                    sub.args and isinstance(receiver, ast.Name)
                    and receiver.id in _UNBOUND_STATE_MUTATOR_RECEIVERS
                    and receiver.id not in module_bindings
                    and not owner_scope(
                        scope, receiver.id, local_bindings,
                        global_names, class_scopes))
                targets = ([(sub.args[0], "mutate")] if unbound_builtin
                           else [(receiver, "mutate")])
            elif (isinstance(sub.func, ast.Name)
                  and sub.func.id in _STATE_MUTATING_BUILTIN_CALLS
                  and sub.args and sub.func.id not in module_bindings
                  and not owner_scope(
                      scope, sub.func.id, local_bindings,
                      global_names, class_scopes)):
                targets = [(sub.args[0], "mutate")]
        direct_binds = (
            _bind_names_of(sub)
            if not targets and sub is not node and scope else set())
        if not targets and not direct_binds:
            continue
        expression_locals = _expression_scope_shadows(sub, parents)
        candidates: list[tuple[str, str]] = []
        for target, default_kind in targets:
            kinds = (_target_write_kinds(target) if default_kind == "rebind"
                     else {name: "mutate"
                           for name in _target_write_kinds(target)})
            candidates.extend(kinds.items())
        candidates.extend((name, "rebind") for name in direct_binds)
        for name, kind in candidates:
            if name in expression_locals:
                continue
            owner = owner_scope(
                scope, name, local_bindings, global_names, class_scopes)
            if not owner and writes.get(name) != "rebind":
                writes[name] = kind
    return writes
def _group_state_writes(tree: ast.Module,
                        symbol_owner: dict[str, str]) -> dict[str, dict[str, str]]:
    writes: dict[str, dict[str, str]] = {}
    module_bindings = module_scope_binds(tree.body)
    for node in tree.body:
        group_name = symbol_owner.get(getattr(node, "name", ""))
        if group_name is None:
            continue
        group_writes = writes.setdefault(group_name, {})
        for name, kind in _module_state_writes(node, module_bindings).items():
            if group_writes.get(name) != "rebind":
                group_writes[name] = kind
    return writes
def _assign_target_names(node: ast.Assign) -> tuple[list[str], bool]:
    names: list[str] = []
    plain = True
    for target in node.targets:
        if isinstance(target, ast.Name):
            names.append(target.id)
        elif (isinstance(target, (ast.Tuple, ast.List))
              and all(isinstance(elt, ast.Name) for elt in target.elts)):
            names.extend(elt.id for elt in target.elts)
        else:
            plain = False
            names.extend(_target_write_kinds(target))
    return names, plain
def _mark_target_unsafe(target: ast.AST, state: _ConstState) -> None:
    for name in _target_write_kinds(target):
        state.unsafe.add(name)
        state.segments.pop(name, None)
@dataclass
class _ConstState:
    segments: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    anno_loads: dict[str, set[str]] = field(default_factory=dict)
    unsafe: set[str] = field(default_factory=set)
def _classify_assign_const(node: ast.Assign, state: _ConstState) -> None:
    names, plain = _assign_target_names(node)
    if plain and _split_pure_literal(node.value):
        for n in names:
            state.segments.setdefault(n, []).append(
                (node.lineno, node.end_lineno))
        return
    state.unsafe.update(names)
    for n in names:
        state.segments.pop(n, None)
def _classify_annassign_const(node: ast.AnnAssign, state: _ConstState) -> None:
    if not isinstance(node.target, ast.Name):
        if node.value is not None:
            _mark_target_unsafe(node.target, state)
        return
    if node.value is not None:
        if _split_pure_literal(node.value):
            state.segments.setdefault(node.target.id, []).append(
                (node.lineno, node.end_lineno))
            state.anno_loads.setdefault(
                node.target.id, set()).update(
                expr_load_roots(node.annotation))
        else:
            state.unsafe.add(node.target.id)
            state.segments.pop(node.target.id, None)
def _classify_augassign_unsafe(node: ast.AugAssign, state: _ConstState) -> None:
    if not isinstance(node.target, ast.Name):
        _mark_target_unsafe(node.target, state)
        return
    state.unsafe.add(node.target.id)
    state.segments.pop(node.target.id, None)
def _classify_delete_unsafe(node: ast.Delete, state: _ConstState) -> None:
    for target in node.targets:
        _mark_target_unsafe(target, state)
_CONST_CLASSIFIERS: dict[type, Callable[..., None]] = {
    ast.Assign: _classify_assign_const,
    ast.AnnAssign: _classify_annassign_const,
    ast.AugAssign: _classify_augassign_unsafe,
    ast.Delete: _classify_delete_unsafe,
}
def _classify_const_segments(tree, header_end: int) -> _ConstState:
    state = _ConstState()
    for node in tree.body:
        if node.lineno <= header_end:
            continue
        classifier = _CONST_CLASSIFIERS.get(type(node))
        if classifier is not None:
            classifier(node, state)
    return state
def _collect_outside_binds(tree, header_end: int) -> tuple[set, list]:
    outside_binds: set[str] = set()
    outside_stars: list[str] = []
    for node in tree.body:
        if node.lineno <= header_end:
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            outside_binds |= enclosing_scope_binds(node)
            continue
        if isinstance(node, (ast.Assign, ast.AnnAssign,
                             ast.AugAssign)):
            outside_binds |= expr_binds(getattr(node, "value", None))
            if isinstance(node, ast.AnnAssign):
                outside_binds |= expr_binds(node.annotation)
            continue
        outside_binds |= module_scope_binds([node])
        wrapper = ast.Module(body=[node], type_ignores=[])
        for child in iter_module_level_stmts(wrapper):
            if (isinstance(child, ast.ImportFrom)
                    and any(alias.name == "*" for alias in child.names)):
                outside_stars.append(
                    "." * child.level + (child.module or ""))
    return outside_binds, outside_stars
def _build_sym_table(source_path, src: str):
    try:
        return symtable.symtable(src, str(source_path), "exec")
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_build_sym_table:{type(_e).__name__}')
        return None
def _split_group_load_deps(ctx: _SplitContext, group_name, tree, segs) -> set:
    seg_syms = {n for _s, _e, n in segs}
    deps: set[str] = set()
    _sym_table = ctx.sym_table
    for node in tree.body:
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef))
                and node.name in seg_syms):
            enclosing = enclosing_scope_load_names(node)
            sym_refs = (None if _sym_table is None else
                        symtable_global_refs(_sym_table, node.name))
            if sym_refs is not None:
                deps |= sym_refs | enclosing
                continue
            deps |= _flat_symbol_loads(node) | enclosing
    deps |= set(ctx.group_state_writes.get(group_name, {}))
    deps -= _visible_builtin_names(ctx) - _MODULE_CONTEXT_BUILTINS
    deps -= seg_syms
    deps -= _header_provided(ctx) - _MODULE_SPLIT_CONTEXT_NAMES
    deps -= _MODULE_PROVIDED_NAMES - _MODULE_SPLIT_CONTEXT_NAMES
    return deps
def _visible_builtin_names(ctx: _SplitContext) -> set[str]:
    shadowed = ctx.header_bindings | ctx.outside_bound_names
    return ctx.builtin_names - shadowed
def _header_provided(ctx: _SplitContext) -> set[str]:
    return ctx.header_bindings - ctx.outside_bound_names
def _bind_names_of(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return import_stmt_binds(node)
    capture = pattern_capture_name(node)
    if capture:
        return {capture}
    type_alias = getattr(ast, "TypeAlias", None)
    if type_alias is not None and isinstance(node, type_alias):
        return {node.name.id}
    return set()
def _flat_symbol_loads(node) -> set:
    module = (node if isinstance(node, ast.Module)
              else ast.Module(body=[node], type_ignores=[]))
    local_bindings, global_names, class_scopes = collect_shadow_bindings(module)
    scope_index = build_scope_index(module)
    parents = build_parent_map(module)
    loads: set[str] = set()
    for sub in walk_nodes(node):
        if not (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)):
            continue
        if sub.id in _expression_scope_shadows(sub, parents):
            continue
        scope = _event_scope_name(sub, scope_index, parents)
        owner = owner_scope(
            scope, sub.id, local_bindings, global_names, class_scopes)
        if not owner:
            loads.add(sub.id)
    return loads
def _dynamic_context_getattr_escape(
        node: ast.AST, global_loads: set[str],
        visible_builtins: set[str], ctx: _SplitContext,
) -> tuple[str, str, int] | None:
    if not (isinstance(node, ast.Call)
            and len(node.args) in (2, 3) and not node.keywords):
        return None
    func = node.func
    bare_getattr = (
        isinstance(func, ast.Name) and func.id == "getattr"
        and func.id in global_loads and func.id in visible_builtins)
    module_getattr = (
        isinstance(func, ast.Attribute) and func.attr == "getattr"
        and isinstance(func.value, ast.Name)
        and func.value.id in global_loads
        and func.value.id in ctx.dynamic_module_aliases)
    if not (bare_getattr or module_getattr):
        return None
    receiver, attribute = node.args[:2]
    if not (isinstance(receiver, ast.Name)
            and receiver.id in global_loads
            and receiver.id in ctx.dynamic_module_aliases
            and isinstance(attribute, ast.Constant)
            and isinstance(attribute.value, str)
            and attribute.value in _MODULE_CONTEXT_BUILTINS):
        return None
    origin = f"getattr({receiver.id}, {attribute.value!r})"
    return attribute.value, origin, node.lineno

def _dynamic_context_escape_blocks(
        group_name: str, tree: ast.Module,
        segs: list[tuple[int, int, str]], ctx: _SplitContext,
) -> list[str]:
    seg_syms = {name for _s, _e, name in segs}
    escapes: set[tuple[str, str, int]] = set()
    visible_builtins = _visible_builtin_names(ctx)
    for node in tree.body:
        if not (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef))
                and node.name in seg_syms):
            continue
        global_loads = _flat_symbol_loads(node) | enclosing_scope_load_names(node)
        for sub in walk_nodes(node):
            if (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
                    and sub.id in global_loads):
                if sub.id in ctx.dynamic_context_aliases:
                    escapes.add((ctx.dynamic_context_aliases[sub.id],
                                 sub.id, sub.lineno))
                elif sub.id == "__builtins__":
                    escapes.add(("globals/eval/exec", sub.id, sub.lineno))
            indirect = _dynamic_context_getattr_escape(
                sub, global_loads, visible_builtins, ctx)
            if indirect is not None:
                escapes.add(indirect)
            if not (isinstance(sub, ast.Attribute)
                    and sub.attr in _MODULE_CONTEXT_BUILTINS
                    and isinstance(sub.value, ast.Name)
                    and sub.value.id in global_loads
                    and sub.value.id in ctx.dynamic_module_aliases):
                continue
            escapes.add((sub.attr, f"{sub.value.id}.{sub.attr}", sub.lineno))
    return [
        f"组 {group_name!r} 的移动代码使用动态模块命名空间通道 "
        f"{origin!r}（解析到 {canonical!r}，第 {lineno} 行）；"
        "globals/eval/exec 可通过 builtins 别名或 __builtins__ 间接访问，"
        "其执行上下文仍是产物自身的模块全局字典，拆分后符号解析和状态"
        "读写发生分叉，拒绝落盘；请改为显式参数/依赖注入或调整拆分边界"
        for canonical, origin, lineno in sorted(escapes)
    ]
def _classify_split_deps(ctx: _SplitContext, group_segs: dict,
                         tree, lines: list) -> tuple:
    blocked: list[str] = []
    group_const_blocks: dict[str, str] = {}
    group_const_segments: dict[str, list[tuple[int, int]]] = {}
    unresolved: list[str] = []
    header_provided = _header_provided(ctx)
    for group_name, segs in group_segs.items():
        deps = _split_group_load_deps(ctx, group_name, tree, segs)
        blocked.extend(_dynamic_context_escape_blocks(
            group_name, tree, segs, ctx))
        group_blocked, group_unresolved, segments = _classify_group_deps(
            group_name, deps, ctx, tree, header_provided)
        blocked.extend(group_blocked)
        blocked.extend(_state_split_blocks(group_name, ctx))
        unresolved.extend(group_unresolved)
        ordered_segments = sorted(segments)
        group_const_segments[group_name] = ordered_segments
        group_const_blocks[group_name] = "".join(
            "".join(lines[s - 1:e]) for s, e in ordered_segments)
    return (blocked, unresolved, group_const_blocks, group_const_segments)
def _state_split_blocks(group_name: str, ctx: _SplitContext) -> list[str]:
    messages: list[str] = []
    for name, kind in sorted(
            ctx.group_state_writes.get(group_name, {}).items()):
        if name in ctx.shared_state_names:
            messages.append(
                f"组 {group_name!r} 的移动代码写模块级状态 {name!r}"
                "（global 重绑定或容器/属性原地变异），拆分会在源模块与各产物中"
                "复制出互相独立的副本（状态分裂，读写方看不到彼此的变更）: "
                "请把该状态与其写入方留在同一模块或改为显式参数/实例状态")
        elif kind == "rebind" and name in ctx.import_bound_names:
            messages.append(
                f"组 {group_name!r} 的移动代码重绑定 header 导入名 {name!r}"
                "（global 赋值/删除），产物的模块全局字典与源模块各自持有"
                "不同对象，后续读取方看不到另一侧的绑定变更（状态分裂）: "
                "请把该重绑定留在源模块，或改为显式参数/实例状态")
        elif (name not in ctx.header_bindings
              and name not in ctx.outside_bound_names):
            messages.append(
                f"组 {group_name!r} 的移动代码写未静态声明的模块级状态 "
                f"{name!r}；拆分前该名可由同模块写方先创建或由外部注入，"
                "产物却只会读写自身全局字典，源模块及其他产物无法看到"
                "同一绑定（状态分裂或 NameError），拒绝落盘；请改为显式"
                "参数/实例状态，或在拆分边界内静态声明并保留同一状态")
    return messages
def _classify_group_deps(group_name: str, deps: set, ctx: _SplitContext, tree,
                         header_provided: set) -> tuple[list, list, set]:
    blocked: list[str] = []
    unresolved: list[str] = []
    segments: set[tuple[int, int]] = set()
    seen_names: set[str] = set()
    worklist: list[tuple[str, str]] = [(d, "") for d in sorted(deps)]
    while worklist:
        dep, via = worklist.pop(0)
        if dep in seen_names:
            continue
        seen_names.add(dep)
        kind, payload, segs, pends = _classify_dep(
            dep, group_name, via, ctx, tree, header_provided)
        if kind == "blocked":
            blocked.append(payload)
        elif kind == "unresolved":
            unresolved.append(f"{group_name}.{dep}")
        else:
            segments.update(segs)
            worklist.extend(pends)
    return blocked, unresolved, segments
def _is_const_candidate(dep: str, ctx: _SplitContext) -> bool:
    return (dep in ctx.const_segments
            and dep not in ctx.unsafe_names
            and dep not in ctx.outside_binds
            and dep not in ctx.header_bindings
            and dep not in ctx.src_top_defs)
def _blocked_by_split_module_context(
        dep, group_name, via_suffix, ctx) -> str | None:
    if dep not in _MODULE_SPLIT_CONTEXT_NAMES:
        return None
    if dep == "__all__":
        detail = ("__all__ 会在源端修剪并按各组符号重写，移动代码"
                  "读取到的将是本组子集而不是源模块完整导出面")
    else:
        detail = ("__annotations__ 的内容随各组复制的注解段变化；"
                  "产物没有注解段时该名甚至不会创建，运行即 NameError")
    return (f"组 {group_name!r} 的移动代码读取拆分敏感模块上下文 {dep!r}："
            f"{detail}，拒绝落盘；请改为显式参数/依赖注入"
            f"或调整拆分边界{via_suffix}")
def _blocked_by_dynamic_module_context(
        dep, group_name, via_suffix, ctx) -> str | None:
    if (dep not in _MODULE_CONTEXT_BUILTINS
            or dep not in _visible_builtin_names(ctx)):
        return None
    return (f"组 {group_name!r} 的移动代码使用动态模块命名空间内建 "
            f"{dep!r}（globals/eval/exec 以所在模块全局字典为执行上下文），"
            "拆分后源模块与产物的符号解析和状态读写发生分叉，拒绝落盘；"
            "请改为显式参数/依赖注入或调整拆分边界"
            f"{via_suffix}")
def _blocked_by_outside_bind(dep, group_name, via_suffix, ctx) -> str | None:
    if dep not in ctx.outside_binds:
        return None
    return (f"组 {group_name!r} 依赖界外控制流/导入绑定 "
            f"{dep!r}（模块域 if/try/for/with 等控制流内的"
            "赋值/导入/定义或 header 区外直接导入——条件/"
            "回退语义不可静态复制随迁），请调整拆分边界"
            f"或先合并组{via_suffix}")
def _blocked_by_multi_region_const(dep, group_name, via_suffix,
                                   ctx) -> str | None:
    if not (dep in ctx.header_bindings
            and dep in ctx.const_segments):
        return None
    return (f"组 {group_name!r} 依赖 {dep!r}，该名在 "
            f"header 区有静态绑定且在界外被再次静态赋值"
            "（同名多区域绑定，复制旧值或新值均产生值分歧"
            f"），请先合并组或调整拆分边界{via_suffix}")
def _blocked_by_unsafe_assign(dep, group_name, via_suffix,
                              ctx) -> str | None:
    if dep not in ctx.unsafe_names:
        return None
    return (f"组 {group_name!r} 依赖界外非静态赋值/删除 {dep!r}"
            f"（可变单例/动态值/导入期改值或解绑，复制将产生状态分裂）"
            f"{via_suffix}")
def _blocked_by_cross_group(dep, group_name, via_suffix, ctx) -> str | None:
    if dep not in ctx.src_top_defs:
        return None
    owner = ctx.symbol_owner.get(dep, "")
    if owner == group_name:
        return (f"组 {group_name!r} 的常量段依赖同组顶层符号 {dep!r}，"
                "产物中常量段先于组体定义求值，注解/初始化将 NameError；"
                f"请把 {dep!r} 移入 header 常量区或调整拆分边界{via_suffix}")
    if not owner:
        return (f"组 {group_name!r} 引用顶层符号 {dep!r}（被模块钩子钉住，"
                "不随组迁移），拆分产物将缺少该定义；"
                f"请解除钩子绑定或调整拆分边界{via_suffix}")
    return (f"组 {group_name!r} 引用顶层符号 {dep!r}（归属组 "
            f"{owner!r}），跨组依赖不可自动随迁，请先合并组"
            f"或调整拆分边界{via_suffix}")
_DEP_BLOCK_RULES = (
    _blocked_by_split_module_context,
    _blocked_by_dynamic_module_context,
    _blocked_by_outside_bind,
    _blocked_by_multi_region_const,
    _blocked_by_unsafe_assign,
    _blocked_by_cross_group,
)
def _dep_block_message(dep: str, group_name: str, via_suffix: str,
                       ctx: _SplitContext) -> str | None:
    for rule in _DEP_BLOCK_RULES:
        message = rule(dep, group_name, via_suffix, ctx)
        if message is not None:
            return message
    return None
def _classify_dep(dep: str, group_name: str, via: str, ctx: _SplitContext,
                  tree, header_provided: set) -> tuple:
    via_suffix = f"（{via}）" if via else ""
    message = _dep_block_message(dep, group_name, via_suffix, ctx)
    if message is not None:
        return ("blocked", message, (), ())
    if _is_const_candidate(dep, ctx):
        return _classify_const_dep(dep, group_name, via, via_suffix,
                                   ctx, tree, header_provided)
    return ("unresolved", None, (), ())
def _const_coline_nodes(dep: str, ctx: _SplitContext, tree) -> list[int]:
    coline_lines: set[int] = set()
    for start, end in ctx.const_segments[dep]:
        overlapping = [
            node for node in tree.body
            if node.lineno <= end and node.end_lineno >= start
        ]
        if len(overlapping) > 1:
            coline_lines.add(start)
    return sorted(coline_lines)
def _const_anno_pends(dep: str, via: str, ctx: _SplitContext,
                      header_provided: set) -> list[tuple[str, str]]:
    pends: list[tuple[str, str]] = []
    visible_builtins = _visible_builtin_names(ctx)
    for anno in sorted(ctx.const_anno_loads.get(dep, ())):
        if anno in visible_builtins or anno in header_provided:
            continue
        _via = (f"{via}→常量段 {dep!r} 注解" if via
                else f"常量段 {dep!r} 注解")
        pends.append((anno, _via))
    return pends
def _classify_const_dep(dep: str, group_name: str, via: str,
                        via_suffix: str, ctx: _SplitContext, tree,
                        header_provided: set) -> tuple:
    if _const_coline_nodes(dep, ctx, tree):
        return ("blocked",
                (f"组 {group_name!r} 依赖的常量 {dep!r} 所在行"
                 "含其他顶层语句（单行多语句），整行复制将把同行"
                 "语句静默带进产物，拒绝落盘（请先归一为多行形态）"
                 f"{via_suffix}"), (), ())
    return ("const", None, ctx.const_segments[dep],
            _const_anno_pends(dep, via, ctx, header_provided))
@dataclass(frozen=True)
class SplitAnalysis:
    blocked: list[str]
    unresolved: list[str]
    group_segs: dict[str, list[tuple[int, int, str]]]
    group_const_blocks: dict[str, str]
    group_const_segments: dict[str, list[tuple[int, int]]] = field(
        default_factory=dict, compare=False, repr=False)
def _group_overlap_blocks(groups: dict) -> list[str]:
    owners: dict[str, list[str]] = {}
    for group_name, symbols in groups.items():
        for name in symbols:
            group_names = owners.setdefault(name, [])
            if group_name not in group_names:
                group_names.append(group_name)
    return [
        f"符号 {name!r} 同时归属多个功能组 {group_names!r}：同一顶层"
        "定义会被复制进多个产物并只在源文件删除一次，产物间形成"
        "独立副本（重复定义/行为分叉），请先把该符号归入唯一组"
        for name, group_names in sorted(owners.items())
        if len(group_names) > 1
    ]
def analyze_split_deps(source_path: Path, src: str, tree, header_end: int,
                        groups: dict, lines: list, sym_table=_SYMTABLE_UNSET) -> SplitAnalysis:
    header_nodes = [node for node in tree.body if node.lineno <= header_end]
    header_bindings: set[str] = module_scope_binds(header_nodes)
    ctx = _collect_split_context(
        source_path, src, tree, header_end, header_bindings, groups, sym_table)
    group_segs = _group_segments(groups, src)
    (blocked, unresolved, group_const_blocks,
     group_const_segments) = _classify_split_deps(ctx, group_segs, tree, lines)
    blocked[:0] = _group_overlap_blocks(groups)
    _star_gate(ctx.outside_stars, unresolved, blocked)
    moved_names = {name for segs in group_segs.values()
                   for _s, _e, name in segs}
    blocked.extend(retained_source_reference_blocks(tree, moved_names))
    return SplitAnalysis(
        blocked, unresolved, group_segs, group_const_blocks,
        group_const_segments)
def _star_gate(outside_stars: list, unresolved: list,
               blocked: list[str]) -> None:
    if not outside_stars:
        return
    unresolved_detail = ""
    if unresolved:
        unresolved_detail = ("；源内无归属依赖名 "
                             + ", ".join(sorted(set(unresolved)))
                             + " 也可能由其提供")
    blocked.append(
        "界外存在星号导入 " + ", ".join(
            repr(s) for s in dict.fromkeys(outside_stars))
        + "，其绑定面不可枚举，可能提供或重绑定 header 常量、同组符号及"
        "内建名；该导入只留在源模块而不随产物迁移，无法保持模块全局"
        "解析等价，拒绝落盘" + unresolved_detail)
_MODULE_HOOK_NAMES = frozenset({"__getattr__", "__dir__"})
_MODULE_PROVIDED_NAMES = frozenset({
    "__annotations__", "__builtins__", "__cached__", "__doc__",
    "__file__", "__loader__", "__name__", "__package__", "__spec__",
})
def _module_hook_names(tree: ast.Module) -> set[str]:
    return {node.name for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name in _MODULE_HOOK_NAMES}
def _top_definition_nodes(tree: ast.Module) -> dict[str, list[ast.AST]]:
    nodes: dict[str, list[ast.AST]] = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            nodes.setdefault(node.name, []).append(node)
    return nodes
def _pin_hook_closure(tree: ast.Module,
                      top_nodes: dict[str, list[ast.AST]],
                      sym_table: Any = None) -> set[str]:
    hooks = _module_hook_names(tree)
    if not hooks:
        return set()
    top_defs = set(top_nodes)
    pinned: set[str] = set()
    worklist = list(hooks)
    while worklist:
        name = worklist.pop()
        if name in pinned:
            continue
        pinned.add(name)
        refs: set[str] = set()
        sym_refs = (None if sym_table is None else
                    symtable_global_refs(sym_table, name))
        if sym_refs is not None:
            refs |= sym_refs
        for node in top_nodes.get(name, ()):
            refs |= enclosing_scope_load_names(node)
            if sym_refs is None:
                refs |= _flat_symbol_loads(node)
        for dep in refs & top_defs:
            if dep not in pinned:
                worklist.append(dep)
    return pinned
def hook_pinned_symbols(tree: ast.Module, source_path: Path,
                         src: str, sym_table=_SYMTABLE_UNSET) -> set[str]:
    top_nodes = _top_definition_nodes(tree)
    if sym_table is _SYMTABLE_UNSET:
        sym_table = _build_sym_table(source_path, src)
    return _pin_hook_closure(tree, top_nodes, sym_table)
def auto_group_defs(tree: ast.Module,
                     pinned: set[str] | None = None) -> dict[str, list[str]]:
    pinned_names = (_pin_hook_closure(tree, _top_definition_nodes(tree))
                    if pinned is None else pinned)
    groups: dict[str, list[str]] = {}
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, (ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
            name = node.name
            if name in pinned_names:
                continue
            stem = _infer_group(name)
            if stem not in groups:
                groups[stem] = []
            groups[stem].append(name)
    return groups
_GROUP_PREFIX_ALIASES: dict[str, str] = {
    "diag": "diagnosis",
    "xv": "cross_validation",
    "fix": "fixer",
}
_GROUP_SUFFIX_RULES: tuple[tuple[tuple[str, ...], str], ...] = (
    (("Type", "Types"), "types"),
    (("Error", "Exception"), "errors"),
    (("Config",), "config"),
)
def _symbol_prefix(name: str) -> str:
    if not name or name.startswith("_"):
        return ""
    head, sep, _rest = name.partition("_")
    return head if sep and head.isidentifier() else ""
def _infer_group(name: str) -> str:
    prefix = _symbol_prefix(name)
    if prefix:
        return _GROUP_PREFIX_ALIASES.get(prefix, prefix)
    for suffixes, group in _GROUP_SUFFIX_RULES:
        if name.endswith(suffixes):
            return group
    return "core"
def _group_segments(groups: dict,
                    src: str) -> dict[str, list[tuple[int, int, str]]]:
    group_segs: dict[str, list[tuple[int, int, str]]] = {}
    for group_name, syms in groups.items():
        segs = top_symbol_segments(src, syms)
        if segs:
            group_segs[group_name] = segs
    return group_segs
class SplitExecutor(BaseExecutor):
    def execute(self, action: Any) -> ExecutorResult:
        self.result = ExecutorResult(action_type="split")
        source = self._action_get(action, "source", "")
        target = self._action_get(action, "target", "")
        evidence_elements = as_sequence(self._action_get(action, "symbols", []))
        source_path = self._resolve_path(source, "source")
        if source_path is None:
            return self.result
        self.result.source_files = [str(source_path)]
        src, tree = self._load_split_source(source_path)
        if src is None:
            return self.result
        sym_table = _build_sym_table(source_path, src)
        groups = auto_group_defs(
            tree, hook_pinned_symbols(tree, source_path, src, sym_table))
        if evidence_elements:
            self.result.details.append(
                f"拆分证据（边界分析候补）: {evidence_elements[:10]}")
        empty_group_error = self._empty_group_error(groups)
        if empty_group_error:
            self._fail(empty_group_error)
            return self.result
        if not target:
            if self.dry_run:
                self._report_pending_targets(groups)
            else:
                self._fail("缺少 target 参数：落盘须给出目标文件模板（支持 "
                    "{group} 占位符），否则无任何产物却报成功")
            return self.result
        target_tpl = self._path_text(target, "target")
        if target_tpl is None:
            return self.result
        expanded_targets, error = self._expand_group_targets(
            target_tpl, groups, source_path)
        if error:
            self._fail(error)
            return self.result
        self.result.target_files.extend(expanded_targets.values())
        if self.dry_run:
            self._preview_split(source_path, src, target_tpl, groups, sym_table)
        else:
            self._commit_split(source_path, src, target_tpl, groups, sym_table)
        if self.result.status != "failed":
            self.result.status = "success"
        return self.result
    def _report_pending_targets(self, groups: dict) -> None:
        self.result.details.append(
            f"目标文件名待定（AI 审核时确定），共 {len(groups)} 个功能组: "
            + ", ".join(groups)
        )
        self.result.status = "success"
    def _path_text(self, value: Any, key: str) -> str | None:
        if not isinstance(value, (str, os.PathLike)):
            self._fail(f"{key} 参数形态非法: {type(value).__name__}"
                       "（须为 str/PathLike）")
            return None
        try:
            raw = os.fspath(value)
        except (OSError, TypeError, ValueError) as _swallowed_exc:
            log_swallowed(__name__, _swallowed_exc,
                          context=f'_path_text:{type(_swallowed_exc).__name__}')
            self._fail(f"{key} 参数形态非法: {type(value).__name__}"
                       "（须为 str/PathLike）")
            return None
        if not isinstance(raw, str):
            self._fail(f"{key} 参数形态非法: 路径须为文本")
            return None
        if not raw:
            self._fail(f"缺少 {key} 参数")
            return None
        return raw
    def _resolve_path(self, value: Any, key: str) -> Path | None:
        raw = self._path_text(value, key)
        if raw is None:
            return None
        try:
            return self._resolve_action_path(raw)
        except ValueError as exc:
            self._fail(f"{key} 路径非法或越出技能目录: {raw!r}")
            _log.warning("[SplitExecutor] 拒绝非法路径 %s=%r: %s",
                         key, raw, exc)
            return None
    def _load_split_source(self, source_path: Path
                           ) -> tuple[str | None, Any]:
        if not source_path.exists():
            self._fail(f"源文件不存在: {source_path}")
            return None, None
        src, tree = self._read_source(str(source_path))
        if src is None:
            self._fail(f"源文件读取/解析失败: {source_path}")
        return src, tree
    def _empty_group_error(self, groups: dict) -> str:
        if groups:
            return ""
        self.result.details.append(
            "无可拆分的顶层符号（源文件不含 def/class），拆分将无产物")
        return ("无可拆分的顶层符号（源文件不含 def/class），拆分无"
                "产物，拒绝执行（预览/落盘同口径：落盘必败）")
    def _commit_split(self, source_path: Path, src: str, target: str,
                      groups: dict, sym_table=_SYMTABLE_UNSET) -> None:
        commit = self._write_split_files(
            source_path, src, target, groups, sym_table)
        if self._finalize_commit(commit, "拆分落盘失败"):
            self.result.changes_made = len(groups)
    def _expand_group_targets(self, target_tpl: str,
                              groups: dict[str, list[str]],
                              source_path: str | Path
                              ) -> tuple[dict[str, str], str]:
        src_norm = normcase(abspath(str(source_path)))
        targets: dict[str, str] = {}
        seen: dict[str, tuple[str, str]] = {}
        for group_name in groups:
            target_path = self._resolve_path(
                target_tpl.replace("{group}", group_name), "target")
            if target_path is None:
                return targets, self.result.error_message or "拆分目标路径非法"
            target_file = str(target_path)
            target_norm = normcase(abspath(target_file))
            if target_norm == src_norm:
                return targets, (
                    f"拆分目标路径与源文件同路径: {target_file}"
                    "（产物写盘与源写回同路径互相覆盖，需拆分到新"
                    "文件）")
            content_error = self._target_content_error(target_path)
            if content_error:
                return targets, content_error
            if target_norm in seen:
                first_file, first_group = seen[target_norm]
                return targets, (
                    f"拆分目标路径冲突: {target_file} 与 {first_file} 归一"
                    f"为同一物理路径，同时承载组 {first_group!r} 与 "
                    f"{group_name!r}（target 模板需含 {{group}} 占位符"
                    "且各组目标互不同名）")
            seen[target_norm] = (target_file, group_name)
            targets[group_name] = target_file
        return targets, ""
    @staticmethod
    def _target_content_error(target_path: Path) -> str:
        if not target_path.exists():
            return ""
        existing, _fingerprint = read_source_with_fingerprint(str(target_path))
        if existing is None:
            return (f"拆分目标已存在但无法读取: {target_path}；"
                    "拒绝覆盖不可核验的既有目标")
        if existing.strip():
            return (f"拆分目标文件已存在且含实现: {target_path}；"
                    "拆分会整篇覆盖目标原有内容，请改用空文件或新路径，"
                    "或先人工合并目标实现")
        return ""
    def _preview_split(self, source_path: Path, src: str, target_tpl: str,
                       groups: dict, sym_table=_SYMTABLE_UNSET) -> None:
        error, _prepared = self._prepare_split(
            source_path, src, target_tpl, groups, sym_table)
        if error is not None:
            self._fail(str(error.get("message", "拆分预检失败")))
    def _prepare_split(self, source_path: Path, src: str,
                       target_tpl: str, groups: dict, sym_table=_SYMTABLE_UNSET) -> tuple:
        lines = physical_lines_keepends(src)
        _err, _payload = _split_header(source_path, src, lines)
        if _err is not None:
            return _err, None
        header, header_end, tree = _payload
        expanded_targets, conflict = self._expand_group_targets(
            target_tpl, groups, source_path)
        if conflict:
            return {"status": "error", "data": {}, "message": conflict}, None
        analysis = analyze_split_deps(
            source_path, src, tree, header_end, groups, lines, sym_table)
        blocked = list(analysis.blocked)
        unresolved = sorted(set(analysis.unresolved))
        if unresolved:
            blocked.append(
                "无法静态确认拆分产物的全局依赖可解析: "
                + ", ".join(unresolved)
                + "；名称可能由源模块运行期动态注入或星号导入提供，"
                "复制函数不会复制源模块后续动态注入，且无法证明产物中的"
                "全局解析等价；请改为显式导入/静态常量或调整拆分边界")
        if blocked:
            return ({"status": "error", "data": {},
                     "message": "拆分产物依赖不完整，拒绝落盘: "
                                + "; ".join(dict.fromkeys(blocked))},
                    None)
        for gate in (_relative_import_gate(
                         source_path, tree, header_end, analysis.group_segs,
                         expanded_targets, self.skill_dir),
                     _file_dunder_gate(
                         source_path, tree, header_end, analysis.group_segs,
                         analysis.group_const_segments, expanded_targets)):
            if gate is not None:
                return gate, None
        writes, all_syms = _build_split_writes(
            analysis.group_segs, analysis.group_const_blocks,
            header, lines, expanded_targets, _declared_export_names(tree))
        if not writes:
            return ({"status": "error", "data": {},
                     "message": "无可拆分的符号段"}, None)
        return None, (writes, all_syms)
    def _write_split_files(self, source_path: Path, src: str,
                           target_tpl: str, groups: dict[str, list[str]],
                           sym_table=_SYMTABLE_UNSET) -> dict:
        error, prepared = self._prepare_split(
            source_path, src, target_tpl, groups, sym_table)
        if error is not None:
            return error
        writes, all_syms = prepared
        return self._commit_split_writes(source_path, src, writes, all_syms)
    def _commit_split_writes(self, source_path: Path, src: str,
                             writes: list, all_syms: list) -> dict:
        shared_all_error = _shared_all_assignment_error(
            src, all_syms, str(source_path))
        if shared_all_error is not None:
            return shared_all_error
        new_src, removed = remove_symbols_from_source(src, all_syms)
        if removed:
            writes.append((str(source_path), new_src))
        outcome = commit_writes(writes, str(self.skill_dir))
        if outcome["status"] != "ok":
            return outcome
        outcome["data"]["source_trimmed_symbols"] = removed
        return outcome
def _all_drop_lines(tree, header_end: int) -> set[int]:
    drop: set[int] = set()
    for node in tree.body:
        if node.lineno > header_end:
            break
        if is_all_assignment(node):
            drop.update(range(node.lineno - 1, node.end_lineno))
    return drop
def _split_header(source_path: Path, src: str, lines: list):
    tree = parse_source_tree(src, str(source_path))
    if tree is None:
        return ({"status": "error", "data": {},
                 "message": "源文件语法异常，拒绝拆分落盘"}, None)
    header_end = _header_end_of(tree, lines)
    header_drop = _all_drop_lines(tree, header_end)
    _gate_err = _header_stmt_gate(tree, header_end, header_drop, source_path)
    if _gate_err is not None:
        return (_gate_err, None)
    header = "".join(
        ln for i, ln in enumerate(lines[:header_end])
        if i not in header_drop)
    return (None, (header, header_end, tree))
def _header_end_of(tree, lines: list) -> int:
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            return symbol_start_line(lines, node) - 1
    return len(lines)
def _uses_all_name_import_time(
    node, *, annotations_evaluated: bool = True,
) -> bool:
    return any(
        is_all_target(sub)
        for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated)
    )
def _is_static_all_stmt(node) -> bool:
    if _is_pure_all_annotation(node):
        return True
    return (is_all_assignment(node)
            and _is_foldable_all_declaration(node)
            and extract_all_names(node) is not None)
def _all_stmt_prunable(node) -> bool:
    return not (isinstance(node, ast.Assign) and len(node.targets) > 1)
def _shares_line_with_other_stmt(tree, node) -> bool:
    return any(
        other is not node
        and other.lineno <= node.end_lineno
        and other.end_lineno >= node.lineno
        for other in tree.body)
def _dynamic_all_error(node, source_path) -> dict:
    return {"status": "error", "data": {},
            "message": "源文件存在动态 __all__ 声明/引用，拆分产物会在"
            "生成 __all__ 声明之前执行该语句并 NameError，且源文件"
            "静态修剪无法保留其语义，拒绝落盘（静态 __all__ 赋值"
            f"可被剔除）: {source_path} 第 {node.lineno} 行"}
def _header_assignment_effect(node: ast.AST) -> ast.AST | None:
    if isinstance(node, ast.Assign):
        _names, plain = _assign_target_names(node)
        if not plain or not _split_pure_literal(node.value):
            return node
    elif isinstance(node, ast.AnnAssign):
        if not isinstance(node.target, ast.Name):
            return node
        if node.value is not None and not _split_pure_literal(node.value):
            return node
    elif isinstance(node, ast.AugAssign):
        return node
    return None
def _unbound_header_effect(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> ast.AST | None:
    for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated):
        if (isinstance(sub, ast.Expr)
                and not isinstance(sub.value, ast.Constant)):
            return sub
        effect = _header_assignment_effect(sub)
        if effect is not None:
            return effect
        if isinstance(sub, (ast.Call, ast.With, ast.AsyncWith)):
            return sub
    return None
def _is_state_mutating_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    return ((isinstance(node.func, ast.Attribute)
             and node.func.attr in _STATE_MUTATING_METHODS)
            or (isinstance(node.func, ast.Name)
                and node.func.id in _STATE_MUTATING_BUILTIN_CALLS))
def _retained_import_time_effect(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> ast.AST | None:
    return next(
        (sub for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated)
         if _is_state_mutating_call(sub)
         or (isinstance(sub, ast.Expr)
             and not isinstance(sub.value, ast.Constant))),
        None,
    )
def _header_effect_error(node: ast.AST, source_path) -> dict:
    return {"status": "error", "data": {},
            "message": "源文件 header 区含不可静态复制的导入期求值"
            "（动态初始化、调用或副作用表达式），拆分会在每个产物中"
            "重复求值并生成独立状态，拒绝落盘（请把动态初始化/副作用"
            "移到显式入口或独立初始化模块，header 仅保留导入和静态字面量）: "
            f"{source_path} 第 {node.lineno} 行"}
def _retained_effect_error(node: ast.AST, source_path) -> dict:
    return {"status": "error", "data": {},
            "message": "源文件首个顶层定义后含保留的导入期副作用表达式"
            "（状态变异调用或无绑定非字面量表达式语句），该副作用只留在源模块"
            "而不随产物迁移，产物会读取未初始化或不同的模块状态，拒绝"
            "落盘（请把副作用移到显式入口或独立初始化模块）: "
            f"{source_path} 第 {node.lineno} 行"}
def _header_stmt_gate(tree, header_end: int, header_drop: set,
                      source_path) -> dict | None:
    has_static_all_base = False
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    for node in tree.body:
        if is_all_assignment(node) or _is_pure_all_annotation(node):
            if not _is_static_all_stmt(node):
                return _dynamic_all_error(node, source_path)
            if is_all_assignment(node) and not _all_stmt_prunable(node):
                return {"status": "error", "data": {},
                        "message": "源文件 __all__ 采用多目标赋值，"
                        "静态修剪无法只重写 __all__，源文件会残留已迁走"
                        "符号，拒绝落盘（请先归一为单目标 __all__ 声明）: "
                        f"{source_path} 第 {node.lineno} 行"}
            if (is_all_assignment(node)
                    and _shares_line_with_other_stmt(tree, node)):
                return {"status": "error", "data": {},
                        "message": "源文件 __all__ 声明与其他语句同属单行多语句，"
                        "静态修剪整行重写会静默丢失同行语句，拒绝落盘"
                        f"（请先归一为多行形态）: {source_path} "
                        f"第 {node.lineno} 行"}
            if isinstance(node, ast.AugAssign) and not has_static_all_base:
                return _dynamic_all_error(node, source_path)
            if is_all_assignment(node) and not isinstance(node, ast.AugAssign):
                has_static_all_base = True
            continue
        if node.lineno <= header_end:
            if _uses_all_name_import_time(
                    node, annotations_evaluated=annotations_evaluated):
                return _dynamic_all_error(node, source_path)
            effect = _unbound_header_effect(
                node, annotations_evaluated=annotations_evaluated)
            if effect is not None:
                return _header_effect_error(effect, source_path)
            if any(ln in header_drop
                   for ln in range(node.lineno - 1, node.end_lineno)):
                return {"status": "error", "data": {},
                        "message": "源文件 header 区含单行多语句（__all__ 与"
                        "其他语句同行），整行剔除将静默丢失同行语句，拒绝落盘"
                        f"（请先归一为多行形态）: {source_path} "
                        f"第 {node.lineno} 行"}
            continue
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef))
                and _uses_all_name_import_time(
                    node, annotations_evaluated=annotations_evaluated)):
            return _dynamic_all_error(node, source_path)
        if _all_rebind_line(
                node, annotations_evaluated=annotations_evaluated) is not None:
            return _dynamic_all_error(node, source_path)
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
            effect = _retained_import_time_effect(
                node, annotations_evaluated=annotations_evaluated)
            if effect is not None:
                return _retained_effect_error(effect, source_path)
    return None
_DEFAULT_EOL = "\n"
def _ensure_trailing_newline(text: str) -> str:
    return (text if text.endswith(("\r", "\n"))
            else text + _DEFAULT_EOL)
def _group_product(header: str, const_block: str, segs: list,
                   lines: list) -> str:
    eol = _DEFAULT_EOL
    body = (eol * 3).join(
        "".join(lines[s - 1:e]).rstrip("\r\n") for s, e, _n in segs)
    prefix = header.rstrip("\r\n")
    const_block = const_block.rstrip("\r\n")
    if const_block:
        prefix = (prefix + eol * 3 + const_block) if prefix else const_block
    separator = eol * 3 if prefix else ""
    return _ensure_trailing_newline(prefix + separator + body)
def _declared_export_names(tree: ast.Module) -> list[str] | None:
    names: list[str] | None = None
    for node in tree.body:
        if is_all_assignment(node):
            elems = extract_all_names(node)
            if elems is None or not _is_foldable_all_declaration(node):
                return None
            if isinstance(node, ast.AugAssign):
                names = (names or []) + list(elems)
            else:
                names = list(elems)
    return names
def _all_declaration(segs: list, declared: list[str] | None = None) -> str:
    moved = [name for _s, _e, name in segs]
    if declared is None:
        group_syms = [name for name in moved if not name.startswith("_")]
    else:
        moved_set = set(moved)
        group_syms = [name for name in dict.fromkeys(declared)
                      if name in moved_set]
    return (_DEFAULT_EOL * 2 + "__all__ = "
            f"[{', '.join(repr(n) for n in group_syms)}]" + _DEFAULT_EOL)
def _build_split_writes(group_segs: dict, group_const_blocks: dict,
                        header: str, lines: list,
                        expanded_targets: dict,
                        declared: list[str] | None = None) -> tuple[list, list]:
    writes: list[tuple[str, str]] = []
    all_syms: list[str] = []
    for group_name, segs in group_segs.items():
        const_block = group_const_blocks.get(group_name, "").rstrip("\r\n")
        new_code = _group_product(header, const_block, segs, lines)
        new_code += _all_declaration(segs, declared)
        writes.append((expanded_targets[group_name], new_code))
        all_syms.extend(name for _s, _e, name in segs)
    return writes, all_syms
def _copied_ast_nodes(tree, header_end: int, segs,
                      const_segments=()) -> list:
    ranges = [(s, e) for s, e, _n in segs] + list(const_segments)
    return [node for node in walk_nodes(tree)
            if (lineno := getattr(node, "lineno", None)) is not None
            and (lineno <= header_end
                 or any(s <= lineno <= e for s, e in ranges))]
def _relative_import_gate(source_path: Path, tree, header_end: int,
                          group_segs: dict, expanded_targets: dict,
                          root: Path) -> dict | None:
    src_pkg = _package_parts(source_path, root)
    problems: list[str] = []
    for group_name, target in expanded_targets.items():
        tgt_pkg = _package_parts(target, root)
        if tgt_pkg == src_pkg:
            continue
        nodes = [
            node for node in _copied_ast_nodes(
                tree, header_end, group_segs.get(group_name, ()))
            if isinstance(node, ast.ImportFrom) and node.level > 0]
        broken: list[str] = []
        for node in nodes:
            src_mod = _resolve_relative_module(
                src_pkg, node.level, node.module)
            if src_mod is None:
                continue
            tgt_mod = _resolve_relative_module(
                tgt_pkg, node.level, node.module)
            if tgt_mod == src_mod:
                continue
            text = "." * node.level + (node.module or "")
            broken.append(
                f"第 {node.lineno} 行 from {text} import ..."
                f"（源解析 {_dotted_module(src_mod)}，"
                f"目标解析 {_dotted_module(tgt_mod)}")
        if broken:
            problems.append(f"组 {group_name!r} → {target}: "
                            + "；".join(broken))
    if not problems:
        return None
    return {"status": "error", "data": {},
            "message": "拆分目标改变了相对导入的包解析，产物将 ImportError，"
                       "拒绝落盘: " + "; ".join(problems)
                       + "。请改用绝对导入或保持产物与源文件同包"}
_FILE_IDENTITY_DUNDERS = frozenset({
    "__cached__", "__file__", "__loader__", "__name__", "__spec__",
})
_MODULE_IDENTITY_DUNDERS = _FILE_IDENTITY_DUNDERS | frozenset({"__package__"})
def _file_dunder_gate(source_path: Path, tree, header_end: int,
                      group_segs: dict, group_const_segments: dict,
                      expanded_targets: dict) -> dict | None:
    src_file = normcase(abspath(str(source_path)))
    src_dir = normcase(os.path.dirname(src_file))
    cross: list[str] = []
    lines: set[int] = set()
    names: set[str] = set()
    for group, target in expanded_targets.items():
        target_file = normcase(abspath(str(target)))
        if target_file == src_file:
            continue
        target_dir = normcase(os.path.dirname(target_file))
        nodes = [
            node for node in _copied_ast_nodes(
                tree, header_end, group_segs.get(group, ()),
                group_const_segments.get(group, ()))
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
            and node.id in _MODULE_IDENTITY_DUNDERS
            and (node.id in _FILE_IDENTITY_DUNDERS or target_dir != src_dir)]
        if not nodes:
            continue
        cross.append(f"组 {group!r} → {target}")
        lines.update(node.lineno for node in nodes)
        names.update(node.id for node in nodes)
    if not cross:
        return None
    lines_text = ", ".join(str(n) for n in sorted(lines))
    names_text = ", ".join(sorted(names))
    return {"status": "error", "data": {},
            "message": "拆分产物改变模块身份或包/资源上下文，但复制代码读取 "
                       f"{names_text}（第 {lines_text} 行）；模块名、文件身份或"
                       "包解析会变化且不可静态补偿，拒绝落盘: " + ", ".join(cross)
                       + "。请解除模块身份/资源路径耦合，改为显式参数或绝对"
                       "路径，或保留原模块边界"}
_CTRL_BLOCK_FUNC_NAMES = {
    "If": "_check_condition",
    "For": "_process_items",
    "AsyncFor": "_process_items",
    "While": "_loop_until",
    "Try": "_safe_execute",
    "TryStar": "_safe_execute",
    "With": "_manage_resource",
    "AsyncWith": "_manage_resource",
    "Match": "_match_cases",
}
def _rel_line(node: ast.AST, func: ast.AST, end: bool = False) -> int:
    line = (getattr(node, "end_lineno", None) or node.lineno) if end else node.lineno
    return line - func.lineno + 1
def _logical_block(start_rel: int, end_rel: int, rationale: str,
                   block_type: str, stmt_type: str = "") -> dict[str, Any]:
    block = {
        "start_rel": start_rel, "end_rel": end_rel,
        "lines": end_rel - start_rel + 1,
        "rationale": rationale, "type": block_type,
    }
    if stmt_type:
        block["stmt_type"] = stmt_type
    return block
def _unique_block_name(base_name: str, used_names: dict[str, int]) -> str:
    seen = used_names.get(base_name, 0)
    used_names[base_name] = seen + 1
    return base_name if not seen else f"{base_name}_{seen + 1}"
def _block_suggestion(block: dict[str, Any], suggested_name: str,
                      target: ast.FunctionDef | ast.AsyncFunctionDef) -> dict[str, Any]:
    return {
        "success": True,
        "operation": "extract_function",
        "suggested_name": suggested_name,
        "lines": block["lines"],
        "range": (f"L{target.lineno + block['start_rel'] - 1}"
                  f"-L{target.lineno + block['end_rel'] - 1}"),
        "rationale": block["rationale"],
    }
_DEFAULT_FUNCTION_NAME = ""
_DEFAULT_MIN_FUNC_LINES = 20
_DEFAULT_MIN_BLOCK_LINES = 5
_DEFAULT_MAX_BLOCK_LINES = 20
_MAX_DECOMPOSE_DEPTH = 5
def _norm_min_lines(value: object, default: int) -> int:
    return max(1, int_or(value, default))
class BigFunctionDecomposer:
    DEFAULT_MIN_FUNC_LINES = _DEFAULT_MIN_FUNC_LINES
    DEFAULT_MIN_BLOCK_LINES = _DEFAULT_MIN_BLOCK_LINES
    DEFAULT_MAX_BLOCK_LINES = _DEFAULT_MAX_BLOCK_LINES
    def __init__(self, min_func_lines: int | None = None,
                 min_block_lines: int | None = None) -> None:
        self.min_func_lines = _norm_min_lines(
            min_func_lines, self.DEFAULT_MIN_FUNC_LINES)
        self.min_block_lines = _norm_min_lines(
            min_block_lines, self.DEFAULT_MIN_BLOCK_LINES)
    def decompose(self, code: str, function_name: str = _DEFAULT_FUNCTION_NAME,
                  func_node: ast.FunctionDef | ast.AsyncFunctionDef | None = None
                  ) -> list[dict[str, Any]]:
        target, error = self._resolve_target(code, function_name, func_node)
        if error:
            return [{"success": False, "error": error}]
        func_lines = (target.end_lineno or target.lineno) - target.lineno + 1
        if func_lines < self.min_func_lines:
            return [{"success": False,
                     "error": f"函数足够小 (<{self.min_func_lines}行),无需分解"}]
        used_names: dict[str, int] = {}
        results: list[dict[str, Any]] = []
        for block in self._blocks_from_body(target.body, target):
            if block["lines"] < self.min_block_lines:
                continue
            suggested_name = _unique_block_name(
                self._generate_func_name(block, target), used_names)
            results.append(_block_suggestion(block, suggested_name, target))
        if not results:
            return [{"success": False,
                     "error": f"未找到 >= {self.min_block_lines} 行的可提取逻辑块"}]
        return results
    def _resolve_target(
        self, code: str, function_name: str,
        func_node: ast.FunctionDef | ast.AsyncFunctionDef | None,
    ) -> tuple[ast.FunctionDef | ast.AsyncFunctionDef | None, str]:
        if func_node is not None:
            if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return None, "func_node 须为 FunctionDef/AsyncFunctionDef AST 节点"
            return func_node, ""
        tree, parse_err = parse_ast_safely(code)
        if tree is None:
            return None, f"语法错误: {parse_err}"
        target = self._first_func(tree, function_name)
        if target is None:
            return None, f"未找到函数 '{function_name}'"
        return target, ""
    def decompose_recursive(
        self, code: str, function_name: str = _DEFAULT_FUNCTION_NAME,
        max_lines: int | None = None,
    ) -> list[dict[str, Any]]:
        max_lines = _norm_min_lines(max_lines, self.DEFAULT_MAX_BLOCK_LINES)
        target, error = self._resolve_target(code, function_name, None)
        if error:
            return [{"success": False, "error": error}]
        func_lines = (target.end_lineno or target.lineno) - target.lineno + 1
        if func_lines < self.min_func_lines:
            return [{"success": False,
                     "error": f"函数足够小 (<{self.min_func_lines}行),无需分解"}]
        all_results: list[dict[str, Any]] = []
        to_process: list[tuple[list[ast.stmt], int]] = [(target.body, 0)]
        used_names: dict[str, int] = {}
        while to_process:
            body, depth = to_process.pop(0)
            if depth > _MAX_DECOMPOSE_DEPTH:
                continue
            for block in self._blocks_from_body(body, target):
                if block["lines"] < self.min_block_lines:
                    continue
                suggested_name = _unique_block_name(
                    self._generate_func_name(block, target), used_names)
                r = _block_suggestion(block, suggested_name, target)
                all_results.append({**r, "depth": depth})
                node = block.get("node")
                if r["lines"] > max_lines and node is not None:
                    for child_body in _control_flow_child_bodies(node):
                        to_process.append((child_body, depth + 1))
        return all_results
    def _first_func(
        self, tree: ast.AST, name: str = _DEFAULT_FUNCTION_NAME
    ) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if not name or node.name == name:
                return node
        return None
    def _blocks_from_body(self, body: list[ast.stmt],
                          ref: ast.AST) -> list[dict[str, Any]]:
        if not body:
            return []
        blocks: list[dict[str, Any]] = []
        pending_start: int | None = None
        for index, stmt in enumerate(body):
            if not isinstance(stmt, NESTED_CTRL_TYPES):
                if pending_start is None:
                    pending_start = _rel_line(stmt, ref)
                continue
            if pending_start is not None:
                blocks.append(_logical_block(
                    pending_start, _rel_line(body[index - 1], ref, end=True),
                    "语句序列", "statements"))
                pending_start = None
            stmt_type = type(stmt).__name__
            block = _logical_block(
                _rel_line(stmt, ref), _rel_line(stmt, ref, end=True),
                f"{stmt_type} 控制流块", "control_flow", stmt_type)
            block["node"] = stmt
            blocks.append(block)
        if pending_start is not None:
            blocks.append(_logical_block(
                pending_start, _rel_line(body[-1], ref, end=True),
                "尾部语句序列", "statements"))
        return blocks
    def _generate_func_name(self, block: dict[str, Any],
                            func: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
        if block["type"] == "control_flow":
            return _CTRL_BLOCK_FUNC_NAMES.get(block["stmt_type"], "_execute_block")
        return f"_extracted_from_{func.name}"
def _oversized_node_suggestions(
        code: str, node: ast.FunctionDef | ast.AsyncFunctionDef,
        min_lines: int) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    decomposer = BigFunctionDecomposer(min_func_lines=min_lines)
    for suggestion in decomposer.decompose(
            code, node.name, func_node=node):
        if not suggestion.get("success"):
            continue
        suggestion["function"] = node.name
        suggestion["func_lines"] = (
            (node.end_lineno or node.lineno) - node.lineno + 1)
        hits.append(suggestion)
    return hits
def scan_oversized_functions(
        code: str,
        min_lines: int | None = None,
        ) -> list[dict[str, Any]]:
    min_lines = _norm_min_lines(min_lines, _DEFAULT_MIN_FUNC_LINES)
    tree, parse_err = parse_ast_safely(code)
    if tree is None:
        _log.warning("超大函数扫描跳过（语法错误）: %s", parse_err)
        return []
    suggestions: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            suggestions.extend(
                _oversized_node_suggestions(code, node, min_lines))
    return suggestions
def attach_function_decomposition(data: dict, code: str, func_min: int) -> None:
    data["function_decomposition"] = (
        scan_oversized_functions(code, min_lines=func_min)
        if int_or(func_min, 0) > 0 else [])
__all__ = [
    "BigFunctionDecomposer",
    "SplitAnalysis",
    "SplitExecutor",
    "analyze_split_deps",
    "attach_function_decomposition",
    "auto_group_defs",
    "hook_pinned_symbols",
    "scan_oversized_functions",
]

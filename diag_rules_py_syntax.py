from __future__ import annotations

import ast
import os
import threading
from typing import Any

from jwsgj.diag_shared_ast_bindings import (
    binding_names_of,
    build_scope_index,
    collect_shadow_bindings,
    enclosing_scope_binds,
    owner_scope,
)
from jwsgj.diag_shared_ast_nodes import (
    AST_MATCH_TYPES,
    BUILTIN_CALLABLES,
    COMP_SCOPE_NODES,
    TRY_STAR,
    build_node_parent_map,
    build_parent_map,
    collect_param_names,
    definition_time_exprs,
    get_call_name,
    import_alias_bound_names,
    is_overload_stub,
    is_star_import,
    iter_arg_nodes,
    iter_evaluation_scope_chain,
    iter_own_nodes,
    module_postpones_annotations,
    str_constant_value,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_ast_nodes import iter_scope_nodes as _shared_scope_nodes
from jwsgj.diag_shared_ast_nodes import scope_nodes_list as _scope_nodes_list
from jwsgj.diag_shared_source_core import (
    FRAME_BOUNDARY_NODES,
    physical_docstring_lines,
)
from jwsgj.diag_types_defs import finding_scan_exempt
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    PROJECT_ROOT_MARKERS,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import block_exits, walk_nodes
from jwsgj.runtime_scope import SYS_TMP_ROOT

logger = get_module_logger(__name__)
__all__ = [
    "check_PY01",
    "check_PY02",
    "check_PY03",
    "check_PY04",
    "check_PY05",
    "check_PY07",
    "collect_py01_enclosing_bindings",
]
logger.info("diag_rules_py_syntax 语法语义规则域已加载: %d 项导出",
            len(__all__))
def _py01_func_chain(func_spans, pos):
    return sorted(
        (s for s in func_spans
         if (s[0][0], s[0][1]) <= pos <= (s[0][2], s[0][3])),
        key=lambda s: s[0][:2])
def _py01_handler_scope_layout(handler):
    scope_nodes = list(walk_nodes(handler))
    func_spans = []
    for fn in scope_nodes:
        if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda, ast.ClassDef)):
            continue
        body = fn.body if isinstance(fn, ast.Lambda) else fn.body[0]
        func_spans.append((
            (fn.lineno, fn.col_offset, fn.end_lineno, fn.end_col_offset),
            isinstance(fn, ast.ClassDef),
            (body.lineno, body.col_offset),
        ))
    return scope_nodes, func_spans
def _py01_evaluation_chain(func_spans, pos):
    return [
        entry for entry in _py01_func_chain(func_spans, pos)
        if entry[2] <= pos
    ]
def _py01_chain_key(chain, own_scope: bool = True):
    if not chain:
        return None
    if own_scope:
        return chain[-1]
    return chain[-2] if len(chain) >= 2 else None
_PY01_BINDING_NODES = (
    ast.Name, ast.Import, ast.ImportFrom,
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
)
def _py01_match_bound_name(child) -> str:
    if isinstance(child, (_MATCH_AS, _MATCH_STAR)):
        return getattr(child, 'name', None) or ''
    if isinstance(child, _MATCH_MAPPING):
        return getattr(child, 'rest', None) or ''
    return ''
_PY01_BRANCH_SPECS = (
    ((ast.If, ast.IfExp), (
        ('body', 'body', False), ('orelse', 'else', False),
    )),
    ((ast.For, ast.AsyncFor, ast.While), (
        ('target', 'body', False), ('body', 'body', False),
        ('orelse', 'else', False),
    )),
    ((ast.Try, TRY_STAR), (
        ('body', 'body', False), ('handlers', 'handler', True),
        ('orelse', 'else', False),
    )),
)
def _py01_sequence_branch(parent, child, specs):
    for field_name, label, identify_child in specs:
        candidates = getattr(parent, field_name, ())
        if not isinstance(candidates, (list, tuple)):
            candidates = (candidates,)
        for candidate in candidates:
            if child is not candidate:
                continue
            marker = (id(parent), label)
            return marker + ((id(child),) if identify_child else ())
    return None
def _py01_indexed_branch(parent, child, nodes, label, start=0):
    for index, candidate in enumerate(nodes, start):
        if child is candidate:
            return (id(parent), label, index)
    return None
def _py01_conditional_child(parent, child):
    for node_types, specs in _PY01_BRANCH_SPECS:
        if isinstance(parent, node_types):
            return _py01_sequence_branch(parent, child, specs)
    if isinstance(parent, AST_MATCH_TYPES):
        return _py01_indexed_branch(parent, child, parent.cases, 'case')
    if isinstance(parent, ast.BoolOp):
        return _py01_indexed_branch(
            parent, child, parent.values[1:], 'value', start=1)
    return None
def _py01_execution_path(node, parent_map, handler) -> tuple:
    path = []
    cur = node
    while cur is not handler and cur in parent_map:
        parent = parent_map[cur]
        marker = _py01_conditional_child(parent, cur)
        if marker is not None:
            path.append(marker)
        cur = parent
    return tuple(reversed(path))
def _py01_binding_sites(child, variant: str, func_spans,
                        execution_path: tuple) -> list:
    captured = _py01_match_bound_name(child)
    if not (isinstance(child, _PY01_BINDING_NODES) or captured):
        return []
    pos = (child.lineno, child.col_offset)
    chain = _py01_func_chain(func_spans, pos)
    if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef, ast.Lambda)):
        chain = _py01_evaluation_chain(func_spans, pos)
    if isinstance(child, ast.Name):
        return _py01_name_binding(child, variant, chain, pos, execution_path)
    if isinstance(child, (ast.Import, ast.ImportFrom)):
        return _py01_import_binding(child, variant, chain, pos, execution_path)
    if isinstance(child, _PY01_BINDING_NODES):
        return _py01_definition_bindings(
            child, variant, chain, pos, execution_path)
    if captured != variant:
        return []
    return [(_py01_chain_key(chain), pos, execution_path)]
def _py01_name_binding(child, variant: str, chain, pos, path) -> list:
    if isinstance(child.ctx, ast.Store) and child.id == variant:
        return [(_py01_chain_key(chain), pos, path)]
    return []
def _py01_name_unbinding(child, variant: str, chain, pos, path) -> list:
    if isinstance(child.ctx, ast.Del) and child.id == variant:
        return [(_py01_chain_key(chain), pos, path)]
    return []
def _py01_unbinding_sites(child, variant: str, func_spans,
                          execution_path: tuple) -> list:
    if not isinstance(child, ast.Name):
        return []
    pos = (child.lineno, child.col_offset)
    chain = _py01_evaluation_chain(func_spans, pos)
    return _py01_name_unbinding(child, variant, chain, pos, execution_path)
def _py01_import_binding(child, variant: str, chain, pos, path) -> list:
    if variant in import_alias_bound_names(child):
        return [(_py01_chain_key(chain), pos, path)]
    return []
def _py01_definition_bindings(child, variant: str, chain, pos, path) -> list:
    sites = []
    if getattr(child, 'name', None) == variant:
        sites.append((_py01_chain_key(chain, own_scope=False), pos, path))
    if variant in collect_param_names(child):
        sites.append((_py01_chain_key(chain), pos, path))
    return sites
def _py01_comprehension_target_ids(scope_nodes, variant: str) -> set[int]:
    return {
        id(target)
        for comp in scope_nodes if isinstance(comp, COMP_SCOPE_NODES)
        for generator in comp.generators
        for target in walk_nodes(generator.target)
        if isinstance(target, ast.Name) and isinstance(target.ctx, ast.Store)
        and target.id == variant
    }


def _py01_valueless_annotation_target_ids(scope_nodes) -> set[int]:
    return {
        id(node.target) for node in scope_nodes
        if isinstance(node, ast.AnnAssign) and node.value is None
        and isinstance(node.target, ast.Name)
    }

def _py01_comp_target_visible(node: ast.Name, variant: str,
                              parent_map: dict) -> bool:
    child = node
    parent = parent_map.get(node)
    while parent is not None:
        if isinstance(parent, COMP_SCOPE_NODES):
            current_index = next(
                (index for index, generator in enumerate(parent.generators)
                 if generator is child), -1)
            for index, generator in enumerate(parent.generators):
                if variant not in binding_names_of(generator.target):
                    continue
                if current_index < 0 or current_index > index:
                    return True
                if (current_index == index
                        and not any(sub is node for sub in walk_nodes(generator.iter))):
                    return True
        child = parent
        parent = parent_map.get(parent)
    return False

def _py01_collect_variant_stores(scope_nodes, variant, func_spans,
                                 execution_paths,
                                 comprehension_target_ids) -> tuple[list, list]:
    stores = []
    unbindings = []
    valueless_annotation_ids = _py01_valueless_annotation_target_ids(
        scope_nodes)
    for child in scope_nodes:
        execution_path = execution_paths[id(child)]
        if (id(child) not in comprehension_target_ids
                and id(child) not in valueless_annotation_ids):
            stores.extend(_py01_binding_sites(
                child, variant, func_spans, execution_path))
        unbindings.extend(_py01_unbinding_sites(
            child, variant, func_spans, execution_path))
    return stores, unbindings
def _py01_deferred_after(store_key, load_chain) -> bool:
    start = load_chain.index(store_key) + 1 if store_key is not None else 0
    return any(not is_class for _span, is_class, _body in load_chain[start:])
def _py01_store_path_reaches_load(store_path: tuple,
                                   load_path: tuple) -> bool:
    if load_path[:len(store_path)] == store_path:
        return True
    if not store_path or len(load_path) < len(store_path):
        return False
    depth = len(store_path) - 1
    store_marker = store_path[depth]
    load_marker = load_path[depth]
    return (
        store_path[:depth] == load_path[:depth]
        and len(store_marker) == 3 and len(load_marker) == 3
        and store_marker[:2] == load_marker[:2]
        and store_marker[1] == 'value'
        and store_marker[2] < load_marker[2]
    )
def _py01_store_cleared_by_del(store_key, store_pos, store_path,
                               load_pos, load_path, unbindings) -> bool:
    for del_key, del_pos, del_path in unbindings:
        if del_key != store_key or not store_pos < del_pos < load_pos:
            continue
        if (_py01_store_path_reaches_load(store_path, del_path)
                and (_py01_store_path_reaches_load(del_path, load_path)
                     or _py01_store_path_reaches_load(load_path, del_path))):
            return True
    return False
def _py01_complete_branch_exempt(stores, load_key, load_pos, load_chain,
                                 load_path, unbindings, branch_ids) -> bool:
    depth = len(load_path)
    branches: dict[int, set[tuple]] = {}
    for _store_key, _store_pos, store_path in stores:
        if len(store_path) <= depth or store_path[:depth] != load_path:
            continue
        marker = store_path[depth]
        if marker and marker[0] in branch_ids:
            branches.setdefault(marker[0], set()).add(marker)
    for branch_id, markers in branches.items():
        body = (branch_id, 'body')
        orelse = (branch_id, 'else')
        if body not in markers or orelse not in markers:
            continue
        if all(_py01_load_exempt(
                stores, load_key, load_pos, load_chain,
                load_path + (marker,), unbindings, branch_ids)
               for marker in (body, orelse)):
            return True
    return False
def _py01_load_exempt(stores, load_key, load_pos, load_chain,
                      load_path, unbindings, branch_ids) -> bool:
    for store_key, store_pos, store_path in stores:
        if not _py01_store_path_reaches_load(store_path, load_path):
            continue
        if store_key == load_key:
            if store_pos < load_pos and not _py01_store_cleared_by_del(
                    store_key, store_pos, store_path,
                    load_pos, load_path, unbindings):
                return True
            continue
        if store_key is None:
            if (not _py01_deferred_after(None, load_chain)
                    and not store_pos < load_pos):
                continue
            return True
        if not store_key[1] and store_key in load_chain:
            if _py01_deferred_after(store_key, load_chain):
                return True
            return store_pos < load_pos
    return _py01_complete_branch_exempt(
        stores, load_key, load_pos, load_chain,
        load_path, unbindings, branch_ids)
def _py01_finding(child: Any, bound_name: str, filepath: Any) -> dict:
    return {
        "rule_id": "PY-01",
        "severity": "P0",
        "line": child.lineno,
        "file": filepath,
        "message": (
            f"PY-01: except块绑定变量'{bound_name}',"
            f"但块内引用'{child.id}'→NameError."
            f"多出现在批量替换/重命名后."
        ),
        "suggestion": (
            f"统一使用'{bound_name}'或修改except绑定为'{child.id}'"
        ),
        "rule_ref": "sc0581, NameError: name '_e' is not defined",
    }
def _py01_bindings_of_node(child: Any) -> set[str]:
    names = _py02_decl_binding(child)
    if isinstance(child, ast.Name) and isinstance(child.ctx, (ast.Store, ast.Del)):
        names.add(child.id)
    elif isinstance(child, (ast.Import, ast.ImportFrom)):
        names.update(import_alias_bound_names(child))
    return names
def _py01_value_bindings_of_node(child: Any) -> set[str]:
    if isinstance(child, (ast.Global, ast.Nonlocal)):
        return set()
    if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Del):
        return set()
    return _py01_bindings_of_node(child)

def _py01_expr_bound_names(expr: Any) -> set:
    if expr is None:
        return set()
    return {name for node in _shared_scope_nodes(expr)
            for name in _py01_value_bindings_of_node(node)}

def _py01_stmt_all_bound_names(stmt: ast.AST) -> set:
    return {name for node in _shared_scope_nodes(stmt)
            for name in _py01_value_bindings_of_node(node)}

def _py01_block_definite_bindings(stmts: list) -> set:
    names: set = set()
    for stmt in stmts:
        names |= _py01_stmt_definite_bindings(stmt)
    return names

def _py01_stmt_definite_bindings(stmt: ast.AST) -> set:
    """返回语句执行后**必然**已绑定的名字（分支取交集）。"""
    if isinstance(stmt, ast.If):
        test_names = _py01_expr_bound_names(stmt.test)
        body_names = _py01_block_definite_bindings(stmt.body)
        orelse_names = _py01_block_definite_bindings(stmt.orelse)
        body_exits = block_exits(stmt.body)
        orelse_exits = bool(stmt.orelse) and block_exits(stmt.orelse)
        if body_exits and orelse_exits:
            return test_names
        if body_exits:
            return test_names | orelse_names
        if orelse_exits:
            return test_names | body_names
        if not stmt.orelse:
            return test_names
        return test_names | (body_names & orelse_names)
    if isinstance(stmt, (ast.Try, TRY_STAR)):
        normal = (_py01_block_definite_bindings(stmt.body)
                  | _py01_block_definite_bindings(stmt.orelse))
        normal_reaches = (not block_exits(stmt.body)
                          and not (stmt.orelse and block_exits(stmt.orelse)))
        paths = [normal] if normal_reaches else []
        for handler in stmt.handlers:
            if block_exits(handler.body):
                continue
            paths.append(_py01_block_definite_bindings(handler.body))
        definite = set.intersection(*paths) if paths else set()
        return definite | _py01_block_definite_bindings(stmt.finalbody)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return _py01_expr_bound_names(stmt.iter)
    if isinstance(stmt, ast.While):
        return _py01_expr_bound_names(stmt.test)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        names: set = set()
        for item in stmt.items:
            names |= _py01_expr_bound_names(item.context_expr)
            if item.optional_vars is not None:
                names |= _py01_expr_bound_names(item.optional_vars)
        return names
    if isinstance(stmt, ast.Match):
        return _py01_expr_bound_names(stmt.subject)
    return _py01_stmt_all_bound_names(stmt)

def _py01_scope_bindings_before(scope: Any, anchor: Any,
                                parent_map: dict | None, *,
                                deferred: bool = False) -> set:
    """返回 ``scope`` 内在 ``anchor`` 之前可见的绑定名。

    ``deferred=True`` 表示 ``anchor`` 所在代码块延迟执行（位于函数体内），
    此时外层作用域在源码位置上晚于 ``anchor`` 的绑定在调用时同样可见，
    不能按源码位置与执行路径截断，否则会把合法的全局/闭包引用误判为未绑定。
    """
    names: set = set()
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        names |= collect_param_names(scope)
    anchor_pos = (None if deferred else (
        getattr(anchor, "lineno", 0), getattr(anchor, "col_offset", 0)))
    if anchor_pos is not None and parent_map is not None:
        # 先吸收 anchor 之前兄弟语句的“必然绑定”：if/else、try/except 等
        # 分支取交集，避免把两分支都初始化的名字误判为未绑定。
        for stmt in getattr(scope, "body", ()) or ():
            stmt_pos = (getattr(stmt, "lineno", 0),
                        getattr(stmt, "col_offset", 0))
            if stmt_pos >= anchor_pos:
                break
            if any(sub is anchor for sub in walk_nodes(stmt)):
                break
            names |= _py01_stmt_definite_bindings(stmt)
    anchor_path = (_py01_execution_path(anchor, parent_map, scope)
                   if parent_map is not None and not deferred else ())
    scope_nodes = list(_shared_scope_nodes(scope))
    valueless_annotation_ids = _py01_valueless_annotation_target_ids(
        scope_nodes)
    for child in scope_nodes:
        if anchor_pos is not None:
            pos = (getattr(child, "lineno", 0),
                   getattr(child, "col_offset", 0))
            if pos >= anchor_pos:
                continue
            if parent_map is not None:
                child_path = _py01_execution_path(child, parent_map, scope)
                if anchor_path[:len(child_path)] != child_path:
                    continue
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Del):
            names.discard(child.id)
            continue
        if id(child) not in valueless_annotation_ids:
            names |= _py01_value_bindings_of_node(child)
        if isinstance(child, FRAME_BOUNDARY_NODES):
            names |= enclosing_scope_binds(child)
    return names
def collect_py01_enclosing_bindings(parent_map: dict, handler: Any) -> set:
    names: set = set()
    seen_function = False
    seen_class = False
    child = handler
    while child in parent_map:
        parent = parent_map[child]
        # handler 一旦位于函数体内即延迟执行：再往外层走时，模块/外层函数在
        # handler 之后才发生的绑定在调用时同样可见，须纳入而不是按位置截断。
        deferred = seen_function
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
            names |= _py01_scope_bindings_before(
                parent, handler, parent_map, deferred=deferred)
            seen_function = True
        elif isinstance(parent, ast.Module):
            names |= _py01_scope_bindings_before(
                parent, handler, parent_map, deferred=deferred)
        elif isinstance(parent, ast.ClassDef):
            if not seen_function and not seen_class:
                names |= _py01_scope_bindings_before(parent, handler, parent_map)
            seen_class = True
        child = parent
    return names

def _py01_late_local_shadow(parent_map: dict, handler: Any,
                            variant: str) -> bool:
    scope = parent_map.get(handler)
    while scope is not None and not isinstance(
            scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        scope = parent_map.get(scope)
    if scope is None:
        return False
    scope_nodes = _scope_nodes_list(scope)
    if any(isinstance(child, (ast.Global, ast.Nonlocal))
           and variant in child.names for child in scope_nodes):
        return False
    bound_anywhere = variant in collect_param_names(scope) or any(
        variant in _py01_bindings_of_node(child) for child in scope_nodes)
    return bound_anywhere and variant not in _py01_scope_bindings_before(
        scope, handler, parent_map)

def _py01_non_runtime_annotation_ids(tree: ast.AST) -> set[int]:
    postponed = module_postpones_annotations(tree, require_absolute=True)
    skipped: set[int] = set()
    for scope in walk_nodes(tree):
        is_function = isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
        if not (is_function or isinstance(scope, (ast.Module, ast.ClassDef))):
            continue
        annotations = []
        if postponed and is_function:
            annotations.extend(arg.annotation for arg in iter_arg_nodes(scope.args))
            annotations.append(scope.returns)
        if is_function or postponed:
            annotations.extend(
                child.annotation for child in iter_own_nodes(scope)
                if isinstance(child, ast.AnnAssign))
        for annotation in annotations:
            if annotation is not None:
                skipped.update(id(child) for child in walk_nodes(annotation))
    return skipped
def _py01_unbound_load(child: Any, variant: str, func_spans,
                       stores, execution_paths, unbindings, branch_ids,
                       parent_map) -> bool:
    if not (isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load)
            and child.id == variant):
        return False
    if _py01_comp_target_visible(child, variant, parent_map):
        return False
    load_pos = (child.lineno, child.col_offset)
    load_chain = _py01_evaluation_chain(func_spans, load_pos)
    load_key = load_chain[-1] if load_chain else None
    return not _py01_load_exempt(
        stores, load_key, load_pos, load_chain, execution_paths[id(child)],
        unbindings, branch_ids)
def _py01_handler_issues(handler: Any, filepath: Any,
                         enclosing: set | None,
                         non_runtime_ids: set[int]) -> list:
    bound_name = handler.name
    if not bound_name:
        return []
    variant = "_" + bound_name
    scope_nodes, func_spans = _py01_handler_scope_layout(handler)
    parent_map = build_node_parent_map(handler)
    execution_paths = {
        id(child): _py01_execution_path(child, parent_map, handler)
        for child in scope_nodes
    }
    comprehension_target_ids = _py01_comprehension_target_ids(
        scope_nodes, variant)
    stores, unbindings = _py01_collect_variant_stores(
        scope_nodes, variant, func_spans, execution_paths,
        comprehension_target_ids)
    if enclosing and variant in enclosing:
        if not unbindings:
            return []
        stores.append((None, (-1, -1), ()))
    branch_ids = {
        id(child) for child in scope_nodes
        if isinstance(child, (ast.If, ast.IfExp))
    }
    return [
        _py01_finding(child, bound_name, filepath)
        for child in scope_nodes
        if id(child) not in non_runtime_ids
        and _py01_unbound_load(child, variant, func_spans, stores,
                               execution_paths, unbindings, branch_ids,
                               parent_map)
    ]
def _has_star_import_binding(tree: ast.AST) -> bool:
    return any(is_star_import(node) for node in walk_nodes(tree))
def check_PY01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None or _has_star_import_binding(tree):
        return issues
    parent_map = build_node_parent_map(tree)
    type_checking_ids = type_checking_body_node_ids(tree)
    non_runtime_ids = _py01_non_runtime_annotation_ids(tree)
    for node in walk_nodes(tree):
        if id(node) in type_checking_ids:
            continue
        if not isinstance(node, (ast.Try, TRY_STAR)):
            continue
        for handler in node.handlers:
            enclosing = collect_py01_enclosing_bindings(parent_map, handler)
            if handler.name and _py01_late_local_shadow(
                    parent_map, handler, "_" + handler.name):
                enclosing = set(enclosing)
                enclosing.discard("_" + handler.name)
            issues.extend(_py01_handler_issues(
                handler, filepath, enclosing, non_runtime_ids))
    return issues
def _py02_import_line_binding(stripped: str, rel: int) -> list:
    out = []
    body = stripped[len("import "):].strip()
    body = body.split("#", 1)[0].strip()
    for raw_part in body.split(","):
        part = raw_part.strip()
        if not part:
            continue
        name = part.split(" as ")[1].strip() if " as " in part else part.split(".")[0].strip()
        if name.isidentifier():
            out.append((name, "Import", body, rel))
    return out
def _py02_from_line_binding(stripped: str, rel: int) -> list:
    out = []
    body = stripped[len("from "):].split(" import ", maxsplit=1)[0].strip()
    after = stripped.split(" import ", 1)[1].split("#", 1)[0]
    for raw_part in after.split(","):
        part = raw_part.strip().strip("()")
        if not part or part == "*":
            continue
        name = part.split(" as ")[1].strip() if " as " in part else part
        if name.isidentifier():
            out.append((name, "ImportFrom", body, rel))
    return out
def _py02_has_bare_assign(stripped: str) -> bool:
    """判断一行是否可能构成 ``Assign`` / 带值的 ``AnnAssign``。

    必要条件：存在一个不属于 ``==`` / ``!=`` / ``<=`` / ``>=`` / ``:=``
    的裸 ``=`。文档字符串里绝大多数散文行（中文段落、标题、说明）没有裸
    ``=``，先用 O(行长) 的字符扫描挡掉，可省去逐行 ``ast.parse`` 以及随
    之而来的 ``SyntaxError`` 构造与回溯开销——两者都是每行重复付出，
    是 PY02 在长文档技能上的主要耗时来源。
    """
    index = stripped.find('=')
    while index != -1:
        prev = stripped[index - 1] if index else ''
        nxt = stripped[index + 1] if index + 1 < len(stripped) else ''
        if prev not in '=!<>:' and nxt != '=':
            return True
        index = stripped.find('=', index + 1)
    return False
def _py02_assign_line_binding(stripped: str, rel: int) -> list:
    if not _py02_has_bare_assign(stripped):
        return []
    try:
        _ptree = ast.parse(stripped)
    except PARSE_DEGRADE_EXC as _e:
        logger.debug("[PY02] docstring 散文行不可解析跳过: %s", _e)
        return []
    if not _ptree.body:
        return []
    targets = []
    for stmt in _ptree.body:
        if isinstance(stmt, ast.Assign):
            targets.extend(stmt.targets)
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            targets.append(stmt.target)
    names: set[str] = set()
    for target in targets:
        names |= binding_names_of(target)
    return [(name, "Assign", "赋值语句", rel) for name in sorted(names)]
_PY02_BUILTIN_NAMES = BUILTIN_CALLABLES
def _py02_global_line_binding(stripped: str, rel: int) -> list:
    out = []
    kw = "Global" if stripped.startswith("global ") else "Nonlocal"
    _names_part = stripped.split(" ", 1)[1].split("#", 1)[0]
    for raw_name in _names_part.split(","):
        name = raw_name.strip()
        if name.isidentifier():
            out.append((name, kw, name, rel))
    return out
def _py02_docstring_bindings(doc_text: str) -> list:
    out: list = []
    for _di, _dline in enumerate(doc_text.split("\n")):
        stripped = _dline.strip()
        if not stripped or stripped.startswith((">>> ", "... ")):
            continue
        if stripped.startswith("import "):
            out.extend(_py02_import_line_binding(stripped, _di))
        elif stripped.startswith("from ") and " import " in stripped:
            out.extend(_py02_from_line_binding(stripped, _di))
        elif stripped.startswith(("global ", "nonlocal ")):
            out.extend(_py02_global_line_binding(stripped, _di))
        else:
            out.extend(_py02_assign_line_binding(stripped, _di))
    return out
_MATCH_AS = getattr(ast, "MatchAs", ())
_MATCH_STAR = getattr(ast, "MatchStar", ())
_MATCH_MAPPING = getattr(ast, "MatchMapping", ())
def _py02_decl_binding(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.arg):
        return {node.arg}
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        return set(node.names)
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    _name = _py01_match_bound_name(node)
    return {_name} if _name else set()
def _py02_owner_docstring(node: Any, source_lines: Any) -> tuple[list[str], int, int] | None:
    body = getattr(node, "body", None)
    if not body or ast.get_docstring(node, clean=False) is None:
        return None
    first_stmt = body[0]
    doc_lines = physical_docstring_lines(source_lines, first_stmt)
    if doc_lines is None:
        return None
    doc_node = first_stmt.value
    ds_start = getattr(doc_node, "lineno", first_stmt.lineno)
    ds_end = getattr(doc_node, "end_lineno", ds_start) or ds_start
    return doc_lines, ds_start, ds_end
def _py02_finding(name: str, stmt_type: str, stmt_detail: str,
                  line: int, filepath: Any) -> dict:
    return {
        "rule_id": "PY-02",
        "severity": "P0",
        "line": line,
        "file": filepath,
        "message": (
            f"PY-02: 名字 '{name}' 仅在 docstring 内经 {stmt_type}"
            f"({stmt_detail})绑定，却被可执行代码引用且可执行代码未绑定"
            f"→运行期 NameError（疑为代码误写入 docstring）。"
        ),
        "suggestion": (
            f"将 '{name}' 的 {stmt_type} 移出 docstring（三引号外），"
            "或在可执行代码中完成绑定"
        ),
        "rule_ref": "1392 _tp_stages.py NameError: name 'logger' is not defined",
    }
def _py02_named_scope_paths(tree: ast.AST) -> dict[int, str]:
    scope_index = build_scope_index(tree)
    paths = {id(tree): ""}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
            continue
        outer = scope_index.get(id(node), "")
        paths[id(node)] = f"{outer}.{node.name}" if outer else node.name
    return paths
def _py02_reference_scope(node: ast.Name, name: str, parent_map: dict,
                          scope_paths: dict[int, str]) -> str | None:
    for scope in iter_evaluation_scope_chain(node, parent_map):
        if isinstance(scope, ast.Lambda):
            if name in collect_param_names(scope):
                return None
        elif id(scope) in scope_paths:
            return scope_paths[id(scope)]
    return ""
def _py02_global_redirect(scope: str, name: str, global_names: dict) -> bool:
    if not scope:
        return False
    parts = scope.split(".")
    return any(
        name in global_names.get(".".join(parts[:depth]), ())
        for depth in range(1, len(parts) + 1)
    )
def _py02_scope_references(tree: ast.AST,
                          type_checking_ids: set[int]) -> tuple[list, dict[int, str]]:
    parent_map = build_parent_map(tree)
    node_parent_map = build_node_parent_map(tree)
    scope_paths = _py02_named_scope_paths(tree)
    local_bindings, global_names, class_scopes = collect_shadow_bindings(tree)
    unresolved = []
    for node in walk_nodes(tree):
        if id(node) in type_checking_ids:
            continue
        if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
            continue
        # 目标可见性依赖 generator 位置及最外层 iter 特例，使用对象键父图。
        if _py01_comp_target_visible(node, node.id, node_parent_map):
            continue
        scope = _py02_reference_scope(node, node.id, parent_map, scope_paths)
        if scope is None:
            continue
        if owner_scope(scope, node.id, local_bindings, global_names,
                       class_scopes):
            continue
        if node.id in local_bindings.get("", ()):
            continue
        unresolved.append((
            node.id, scope,
            _py02_global_redirect(scope, node.id, global_names),
        ))
    return unresolved, scope_paths
def check_PY02(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None or _has_star_import_binding(tree):
        return issues
    excluded_ids = (type_checking_body_node_ids(tree)
                    | _py01_non_runtime_annotation_ids(tree))
    unresolved, scope_paths = _py02_scope_references(tree, excluded_ids)
    if not unresolved:
        return issues
    for node in walk_nodes(tree):
        if id(node) in excluded_ids:
            continue
        if not isinstance(node, (ast.Module, ast.FunctionDef,
                                 ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        doc_info = _py02_owner_docstring(node, source_lines)
        if doc_info is None:
            continue
        issues.extend(_py02_docstring_issues(
            doc_info, unresolved, scope_paths[id(node)], filepath))
    return issues
def _py02_docstring_issues(doc_info, unresolved: list, owner_path: str,
                           filepath: Any) -> list:
    issues = []
    doc_lines, ds_start, ds_end = doc_info
    doc_text = "\n".join(doc_lines)
    for name, stmt_type, stmt_detail, rel_line in _py02_docstring_bindings(doc_text):
        if name in _PY02_BUILTIN_NAMES:
            continue
        captured = any(
            ref_name == name
            and (
                not owner_path
                or (
                    not global_redirect
                    and (ref_scope == owner_path
                         or ref_scope.startswith(owner_path + "."))
                )
            )
            for ref_name, ref_scope, global_redirect in unresolved
        )
        if not captured:
            continue
        child_lineno = ds_start + rel_line
        if child_lineno > ds_end:
            continue
        issues.append(_py02_finding(
            name, stmt_type, stmt_detail, child_lineno, filepath))
    return issues
def _py03_param_annotations(args) -> list:
    if not isinstance(args, ast.arguments):
        return []
    return [arg.annotation for arg in iter_arg_nodes(args)
            if arg.annotation is not None]
def _py03_definition_time_exprs(node, with_annotations: bool) -> list:
    exprs = list(definition_time_exprs(node))
    if with_annotations:
        exprs.extend(_py03_param_annotations(getattr(node, 'args', None)))
        _returns = getattr(node, 'returns', None)
        if _returns is not None:
            exprs.append(_returns)
    exprs.extend(getattr(node, 'bases', ()) or ())
    exprs.extend(kw.value for kw in (getattr(node, 'keywords', ()) or ())
                 if getattr(kw, 'value', None) is not None)
    return exprs
def _py03_comprehension_bindings(node):
    for child in ast.iter_child_nodes(node):
        if isinstance(child, FRAME_BOUNDARY_NODES):
            continue
        if isinstance(child, ast.NamedExpr):
            yield child.target
        yield from _py03_comprehension_bindings(child)
def _py03_frame_walk(roots, with_annotations: bool):
    _nodes = list(roots)
    _idx = 0
    while _idx < len(_nodes):
        cur = _nodes[_idx]
        _idx += 1
        yield cur
        if isinstance(cur, FRAME_BOUNDARY_NODES):
            _nodes.extend(_py03_definition_time_exprs(cur, with_annotations))
            continue
        if isinstance(cur, COMP_SCOPE_NODES):
            _nodes.append(cur.generators[0].iter)
            _nodes.extend(generator.iter for generator in cur.generators[1:])
            for generator in cur.generators:
                _nodes.extend(generator.ifs)
            if isinstance(cur, ast.DictComp):
                _nodes.extend((cur.key, cur.value))
            else:
                _nodes.append(cur.elt)
            _nodes.extend(_py03_comprehension_bindings(cur))
            continue
        _nodes.extend(ast.iter_child_nodes(cur))
def _py03_scope_label(node):
    if isinstance(node, ast.Module):
        return "模块作用域"
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return f"函数 '{node.name}'"
    if isinstance(node, ast.ClassDef):
        return f"类 '{node.name}'"
    return None
def _py03_scope_bindings(node) -> list:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return [(node.name, node.lineno, node.col_offset)]
    if isinstance(node, ast.ExceptHandler):
        _name = node.name or ''
    else:
        _name = _py01_match_bound_name(node)
    if not _name:
        return []
    return [(_name, node.lineno, node.col_offset)]
def _py03_record_position(positions: dict, name: str, lineno: int,
                          col: int) -> None:
    _pos = (lineno, col)
    if name not in positions or _pos < positions[name]:
        positions[name] = _pos
def _py03_scope_params(node) -> dict:
    params: dict = {}
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        for arg in iter_arg_nodes(node.args):
            _py03_record_position(params, arg.arg, arg.lineno, arg.col_offset)
    return params
_PY03_DECL_KINDS = ((ast.Global, "global"), (ast.Nonlocal, "nonlocal"))
def _py03_decl_kind(node) -> str | None:
    for node_type, decl_kind in _PY03_DECL_KINDS:
        if isinstance(node, node_type):
            return decl_kind
    return None
def _py03_scope_declared_names(scope, node_type) -> set[str]:
    return {
        name
        for child in _py03_frame_walk(ast.iter_child_nodes(scope), False)
        if isinstance(child, node_type)
        for name in child.names
    }
def _py03_bound_names(scope, cache: dict[int, set[str]],
                       with_annotations: bool) -> set[str]:
    cached = cache.get(id(scope))
    if cached is not None:
        return cached
    names: set[str] = collect_param_names(scope)
    for child in _py03_frame_walk(getattr(scope, "body", ()),
                                 with_annotations):
        names |= _py01_bindings_of_node(child)
    names -= _py03_scope_declared_names(scope, ast.Global)
    names -= _py03_scope_declared_names(scope, ast.Nonlocal)
    cache[id(scope)] = names
    return names
def _py03_enclosing_function_scopes(node, parent_map: dict):
    cur = parent_map.get(id(node))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield cur
        cur = parent_map.get(id(cur))
def _py03_nonlocal_reason(name: str, node, parent_map: dict,
                          cache: dict[int, set[str]],
                          with_annotations: bool) -> str | None:
    if isinstance(node, ast.Module):
        return "nonlocal 声明不允许出现在模块作用域"
    for scope in _py03_enclosing_function_scopes(node, parent_map):
        if name in _py03_scope_declared_names(scope, ast.Global):
            break
        if name in _py03_bound_names(scope, cache, with_annotations):
            return None
    return f"nonlocal 名 '{name}' 在外层函数作用域内没有绑定"
def _py03_shadowed_by_comprehension(node: ast.Name,
                                    parent_map: dict) -> bool:
    cur = parent_map.get(id(node))
    while cur is not None:
        if isinstance(cur, COMP_SCOPE_NODES):
            first_iter = cur.generators[0].iter
            in_first_iter = any(
                sub is node for sub in walk_nodes(first_iter))
            if not in_first_iter:
                targets: set[str] = set()
                for generator in cur.generators:
                    targets |= binding_names_of(generator.target)
                if node.id in targets:
                    return True
        cur = parent_map.get(id(cur))
    return False
def _py03_in_annotation(node: ast.Name, parent_map: dict) -> bool:
    cur: ast.AST = node
    while id(cur) in parent_map:
        parent = parent_map[id(cur)]
        if isinstance(parent, ast.arg) and cur is parent.annotation:
            return True
        if isinstance(parent, ast.AnnAssign) and cur is parent.annotation:
            return True
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef))
                and cur is parent.returns):
            return True
        cur = parent
    return False
def _py03_collect_decls_and_uses(node, with_annotations: bool,
                                 parent_map: dict):
    declarations = []
    first_use: dict = {}
    annotated: dict = {}
    for child in _py03_frame_walk(getattr(node, "body", ()),
                                  with_annotations):
        decl_kind = _py03_decl_kind(child)
        if decl_kind is not None:
            for name in child.names:
                declarations.append(
                    (name, child.lineno, child.col_offset, decl_kind))
        elif isinstance(child, ast.AnnAssign) and isinstance(
                child.target, ast.Name):
            _py03_record_position(
                annotated, child.target.id,
                child.target.lineno, child.target.col_offset)
            _py03_record_position(
                first_use, child.target.id,
                child.target.lineno, child.target.col_offset)
        elif isinstance(child, ast.Name):
            # 仅当注解不参与运行期求值（from __future__ import annotations）时
            # 才能忽略注解内的名字；否则注解是定义期真实使用，先于 global/
            # nonlocal 声明即 SyntaxError。
            if (isinstance(child.ctx, ast.Load)
                    and not with_annotations
                    and _py03_in_annotation(child, parent_map)):
                continue
            if _py03_shadowed_by_comprehension(child, parent_map):
                continue
            _py03_record_position(
                first_use, child.id, child.lineno, child.col_offset)
        else:
            for name, lineno, col in _py03_scope_bindings(child):
                _py03_record_position(first_use, name, lineno, col)
    return declarations, first_use, _py03_scope_params(node), annotated
def _py03_finding(name: str, lineno: int, scope: str, filepath,
                  decl_kind: str,
                  repeated_from: int | None = None) -> dict:
    if repeated_from is None:
        message = (
            f"PY-03: {scope} 声明 {decl_kind} '{name}' (L{lineno})"
            f"前已存在引用/赋值."
            f"'used/assigned prior to {decl_kind} declaration' → SyntaxError."
        )
        suggestion = f"将 {decl_kind} 声明移至该名字首次使用/绑定之前"
    else:
        message = (
            f"PY-03: {scope} 重复声明 {decl_kind} '{name}' "
            f"(L{repeated_from}, L{lineno}),且声明前已存在引用/赋值."
            f"'used prior to {decl_kind} declaration' → SyntaxError."
        )
        suggestion = (
            f"删除重复的 {decl_kind} 声明,或合并到一个 {decl_kind} 语句中"
        )
    return {
        "rule_id": "PY-03",
        "severity": "P0",
        "line": lineno,
        "file": filepath,
        "message": message,
        "suggestion": suggestion,
        "rule_ref": (
            "L4-002682 SyntaxError: name 'x' is used prior to "
            f"{decl_kind} declaration"
        ),
    }
def _py03_ordering_issues(name: str, occurrences: list, first_use: dict,
                          scope: str, filepath,
                          decl_kind: str) -> list[dict]:
    issues: list[dict] = []
    anchor_line = occurrences[0][0]
    for index, (lineno, col, _kind) in enumerate(occurrences):
        if name not in first_use or not first_use[name] < (lineno, col):
            continue
        if index == 0:
            issues.append(_py03_finding(
                name, lineno, scope, filepath, decl_kind))
            break
        issues.append(_py03_finding(
            name, lineno, scope, filepath, decl_kind,
            repeated_from=anchor_line))
    return issues
def _py03_conflict_reason(name: str, node, params: dict, annotated: dict,
                          decl_pos: tuple[int, int],
                          decl_kind: str) -> str | None:
    if name in params:
        return f"参数 '{name}' 不能声明为 {decl_kind}"
    ann_pos = annotated.get(name)
    if ann_pos is None:
        return None
    if isinstance(node, ast.Module) and decl_pos < ann_pos:
        return None
    return f"注解名 '{name}' 不能声明为 {decl_kind}"
def _py03_conflict_finding(name: str, lineno: int, scope: str, filepath,
                           decl_kind: str, reason: str) -> dict:
    return {
        "rule_id": "PY-03",
        "severity": "P0",
        "line": lineno,
        "file": filepath,
        "message": (
            f"PY-03: {scope} 声明 {decl_kind} '{name}' (L{lineno})，{reason}"
            f" → SyntaxError."
        ),
        "suggestion": f"删除该 {decl_kind} 声明或重命名形参/注解名",
        "rule_ref": (
            f"SyntaxError: name '{name}' is parameter and {decl_kind} / "
            f"annotated name '{name}' can't be {decl_kind}"
        ),
    }
def _py03_scope_decl_issues(node, declarations: list, first_use: dict,
                            params: dict, annotated: dict, scope: str,
                            filepath, parent_map: dict,
                            with_annotations: bool) -> list[dict]:
    issues: list[dict] = []
    grouped: dict[str, list] = {}
    for name, lineno, col, decl_kind in declarations:
        grouped.setdefault(name, []).append((lineno, col, decl_kind))
    binding_cache: dict[int, set[str]] = {}
    for name, occurrences in grouped.items():
        if len({decl_kind for _l, _c, decl_kind in occurrences}) > 1:
            issues.append(_py03_conflict_finding(
                name, occurrences[-1][0], scope, filepath, "global/nonlocal",
                f"'{name}' 不能同时声明为 global 与 nonlocal"))
            continue
        decl_kind = occurrences[0][2]
        reason = _py03_conflict_reason(
            name, node, params, annotated, occurrences[0][:2], decl_kind)
        if reason is None and decl_kind == "nonlocal":
            reason = _py03_nonlocal_reason(
                name, node, parent_map, binding_cache, with_annotations)
        if reason is not None:
            issues.append(_py03_conflict_finding(
                name, occurrences[0][0], scope, filepath, decl_kind, reason))
            continue
        issues.extend(_py03_ordering_issues(
            name, occurrences, first_use, scope, filepath, decl_kind))
    return issues
def check_PY03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    _with_annotations = not module_postpones_annotations(tree, require_absolute=True)
    parent_map = build_parent_map(tree)
    for node in walk_nodes(tree):
        _scope = _py03_scope_label(node)
        if _scope is None:
            continue
        declarations, first_use, params, annotated = (
            _py03_collect_decls_and_uses(node, _with_annotations, parent_map))
        if not declarations:
            continue
        declarations.sort(key=lambda decl: (decl[1], decl[2]))
        issues.extend(_py03_scope_decl_issues(
            node, declarations, first_use, params, annotated, _scope,
            filepath, parent_map, _with_annotations))
    return issues
def _py04_normalized_path(path: str) -> str:
    return os.path.realpath(path).replace("\\", "/").lower().rstrip("/")
def _py04_project_root(filepath) -> str | None:
    text = str(filepath) if filepath else ""
    if not text:
        return None
    cur = os.path.dirname(os.path.abspath(text))
    temp_root = _py04_normalized_path(SYS_TMP_ROOT)
    while True:
        if _py04_normalized_path(cur) == temp_root:
            return None
        if _py04_is_project_root(cur):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            return None
        cur = parent
def _py04_is_project_root(path: str) -> bool:
    return any(os.path.exists(os.path.join(path, marker))
               for marker in PROJECT_ROOT_MARKERS)
def _py04_top_name_of(entry: Any) -> str | None:
    name = entry.name
    if name.startswith("."):
        return None
    if entry.is_file():
        is_module = name.lower().endswith(".py")
        return name[:-3] if is_module and name.lower() != "__init__.py" else None
    if not entry.is_dir() or name == "__pycache__":
        return None
    return name
def _py04_top_name_safe(entry: Any) -> str | None:
    try:
        return _py04_top_name_of(entry)
    except OSError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context='_py04_top_level_names:OSError')
        return None
def _py04_has_python_surface(path: str) -> bool:
    try:
        with os.scandir(path) as entries:
            for entry in entries:
                name = entry.name
                if name.startswith(".") or name == "__pycache__":
                    continue
                try:
                    if entry.is_file():
                        if name.lower().endswith(".py"):
                            return True
                        continue
                    if entry.is_dir() and os.path.isfile(
                            os.path.join(entry.path, "__init__.py")):
                        return True
                except OSError:
                    continue
    except OSError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context='_py04_has_python_surface:OSError')
    return False
def _py04_import_roots(project_root: str) -> list[str]:
    roots = [project_root]
    try:
        with os.scandir(project_root) as entries:
            for entry in entries:
                try:
                    is_dir = entry.is_dir()
                except OSError as _entry_exc:
                    log_swallowed(
                        __name__, _entry_exc,
                        context='_py04_import_roots:entry')
                    continue
                if (not is_dir or entry.name.startswith(".")
                        or entry.name == "__pycache__"):
                    continue
                if os.path.isfile(os.path.join(entry.path, "__init__.py")):
                    continue
                if _py04_has_python_surface(entry.path):
                    roots.append(entry.path)
    except OSError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context='_py04_import_roots:OSError')
    return roots
def _py04_top_level_names(project_root: str) -> set[str]:
    names: set[str] = set()
    for import_root in _py04_import_roots(project_root):
        try:
            with os.scandir(import_root) as entries:
                names.update(
                    name for name in map(_py04_top_name_safe, entries)
                    if name is not None)
        except OSError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context='_py04_top_level_names:OSError')
    return names
def _py04_sibling_names(container: str, own_name: str) -> set[str]:
    names: set[str] = set()
    try:
        with os.scandir(container) as entries:
            siblings = [entry for entry in entries
                        if entry.name != own_name
                        and not entry.name.startswith(".")]
    except OSError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context='_py04_sibling_top_names:OSError')
        return names
    for sibling in siblings:
        try:
            is_dir = sibling.is_dir()
        except OSError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context='_py04_sibling_top_names:OSError')
            continue
        if is_dir and _py04_is_project_root(sibling.path):
            names.update(_py04_top_level_names(sibling.path))
    return names
def _py04_sibling_top_names(project_root: str) -> frozenset[str]:
    container = os.path.dirname(project_root)
    if not container or container == project_root:
        return frozenset()
    return frozenset(
        _py04_sibling_names(container, os.path.basename(project_root)))
def _py04_import_top_names(tree,
                           type_checking_ids: set[int]) -> list[tuple[str, int]]:
    found: list[tuple[str, int]] = []
    for node in walk_nodes(tree):
        if id(node) in type_checking_ids:
            continue
        if isinstance(node, ast.Import):
            for alias in node.names:
                found.append((alias.name.split(".", 1)[0], node.lineno))
        elif (isinstance(node, ast.ImportFrom) and node.level == 0
              and node.module):
            found.append((node.module.split(".", 1)[0], node.lineno))
    return found
def check_PY04(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    project_root = _py04_project_root(filepath)
    if project_root is None:
        return issues
    sibling_names = _py04_sibling_top_names(project_root)
    if not sibling_names:
        return issues
    local_names = _py04_top_level_names(project_root)
    reported: set[str] = set()
    for top_name, lineno in _py04_import_top_names(
            tree, type_checking_body_node_ids(tree)):
        if (top_name in reported or top_name in local_names
                or top_name not in sibling_names):
            continue
        reported.add(top_name)
        issues.append({
            "rule_id": "PY-04",
            "severity": "P0",
            "line": lineno,
            "file": filepath,
            "message": (
                f"PY-04: 绝对导入 '{top_name}' 与兄弟项目中的同名顶层包"
                "冲突，共享 sys.path 时可能发生影子导入。"
            ),
            "suggestion": (
                f"重命名冲突的 '{top_name}' 包/模块，"
                "或用独立虚拟环境隔离项目搜索路径"
            ),
            "rule_ref": "跨项目同名顶层包影子导入",
        })
    return issues
def _py05_finding(name: str, scope_name: str, first_line: int,
                  line: int, filepath: Any) -> dict:
    return {
        "rule_id": "PY-05",
        "severity": "P0",
        "line": line,
        "file": filepath,
        "message": (
            f"PY-05: {scope_name} 内重复定义 '{name}' "
            f"(L{first_line}, L{line})."
            f"后者静默覆盖前者,前者逻辑完全失效."
        ),
        "suggestion": "合并或重命名重复定义",
        "rule_ref": "cs69_duplicate_func",
    }
_PY05_PROPERTY_ACCESSORS = frozenset({"setter", "getter", "deleter"})
def _py05_property_accessor(node: ast.AST) -> tuple[str, str]:
    for dec in getattr(node, "decorator_list", ()):
        target = dec.func if isinstance(dec, ast.Call) else dec
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and isinstance(target, ast.Name) and target.id == "property"):
            return node.name, "property"
        if (isinstance(target, ast.Attribute)
                and target.attr in _PY05_PROPERTY_ACCESSORS
                and isinstance(target.value, ast.Name)):
            return target.value.id, target.attr
    return "", ""
def _py05_scope_issues(scope_node: ast.AST, scope_name: str,
                       kinds: tuple, filepath: Any) -> list[dict]:
    issues: list[dict] = []
    seen: dict[str, int] = {}
    accessor_first_lines: dict[tuple[str, str], int] = {}
    for child in scope_node.body:
        if not isinstance(child, kinds):
            continue
        if is_overload_stub(child):
            continue
        accessor_target, accessor_kind = _py05_property_accessor(child)
        if accessor_target and accessor_target == child.name:
            if accessor_kind == "property":
                first_line = seen.get(child.name)
                if first_line is not None:
                    issues.append(_py05_finding(
                        child.name, scope_name, first_line,
                        child.lineno, filepath))
                else:
                    seen[child.name] = child.lineno
                for kind in _PY05_PROPERTY_ACCESSORS:
                    accessor_first_lines.pop((child.name, kind), None)
                accessor_first_lines[(child.name, "getter")] = child.lineno
                continue
            accessor_key = (child.name, accessor_kind)
            first_accessor_line = accessor_first_lines.get(accessor_key)
            if first_accessor_line is not None:
                issues.append(_py05_finding(
                    child.name, scope_name, first_accessor_line,
                    child.lineno, filepath))
            else:
                accessor_first_lines[accessor_key] = child.lineno
                seen.setdefault(child.name, child.lineno)
            continue
        first_line = seen.get(child.name)
        if first_line is None:
            seen[child.name] = child.lineno
            continue
        issues.append(_py05_finding(child.name, scope_name, first_line,
                                    child.lineno, filepath))
    return issues
def check_PY05(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict] = []
    if tree is None:
        return issues
    definition_kinds = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
    type_checking_ids = type_checking_body_node_ids(tree)
    for node in walk_nodes(tree):
        if id(node) in type_checking_ids:
            continue
        if isinstance(node, ast.Module):
            scope_name = "模块"
        elif isinstance(node, ast.ClassDef):
            scope_name = f"类 '{node.name}'"
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            scope_name = f"函数 '{node.name}'"
        else:
            continue
        issues.extend(_py05_scope_issues(
            node, scope_name, definition_kinds, filepath))
    return issues
def _py07_is_directory_path(value: str, filepath: Any) -> bool:
    if value.endswith(("/", "\\")):
        return True
    if os.path.isdir(value):
        return True
    if not filepath or os.path.isabs(value):
        return False
    source_dir = os.path.dirname(os.path.abspath(str(filepath)))
    return os.path.isdir(os.path.join(source_dir, value))
def _py07_dir_path_args(node, filepath: Any) -> list:
    values = []
    for arg in node.args[1:]:
        value = str_constant_value(arg)
        if value is not None:
            values.append(value)
    for kw in node.keywords:
        if kw.arg == "location":
            value = str_constant_value(kw.value)
            if value is not None:
                values.append(value)
    return [
        value for value in values
        if _py07_is_directory_path(value, filepath)
    ]
_PY07_SPEC_CALL = "importlib.util.spec_from_file_location"
#: ``_py07_scope_import_facts`` 的作用域级缓存。
#:
#: 实测 ``_py07_import_aliases`` 单文件被调 **1,929 次**，而作用域只有数百个
#: （复用度约 5.7×）；每次调用都要把整个作用域子树重扫一遍，只为按
#: ``call_pos`` 切一刀。这里把**与 call_pos 无关的事实**（绑定名全量集合、
#: 按源码位置的导入/遮蔽事件流）按作用域缓存一次，后续调用只做位置过滤。
#:
#: 键 ``(id(scope), id(parent_map))``，值里存二者强引用做身份校验。
_PY07_SCOPE_FACTS_CACHE: dict[tuple, tuple] = {}
_PY07_SCOPE_FACTS_LOCK = threading.Lock()
_PY07_SCOPE_FACTS_MAX = 2048


def _py07_scope_import_facts(scope, parent_map: dict) -> tuple[set, list]:
    """返回 ``(bound_anywhere, events)``——与 ``call_pos`` 无关的作用域事实。

    ``events`` 每项为 ``(pos, kind, payload)``：

    * ``("import", (target, is_from))`` —— 该位置发生一次导入绑定
    * ``("shadow", ())`` —— 该位置发生一次遮蔽

    顺序与 ``_scope_nodes_list(scope)`` 一致（即源码遍历序），
    因此按 ``pos < call_pos`` 过滤后的事件序列与原实现逐项相同。
    """
    key = (id(scope), id(parent_map))
    with _PY07_SCOPE_FACTS_LOCK:
        hit = _PY07_SCOPE_FACTS_CACHE.get(key)
    if (hit is not None and hit[0] is scope
            and hit[1] is parent_map):
        return hit[2], hit[3]
    bound_anywhere: set[str] = set()
    events: list = []
    for node in _scope_nodes_list(scope):
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and _py03_shadowed_by_comprehension(node, parent_map)):
            continue
        node_pos = (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
        if isinstance(node, ast.Import):
            bound_anywhere.update(import_alias_bound_names(node))
            for alias in node.names:
                local = alias.asname or alias.name.split(".", 1)[0]
                target = alias.name if alias.asname else local
                events.append((node_pos, "import", (local, target, False)))
        elif isinstance(node, ast.ImportFrom):
            bound = import_alias_bound_names(node)
            bound_anywhere.update(bound)
            if node.level == 0 and node.module:
                for alias in node.names:
                    if alias.name == "*":
                        continue
                    local = alias.asname or alias.name
                    events.append((node_pos, "import",
                                   (local, f"{node.module}.{alias.name}", True)))
            else:
                for name in bound:
                    events.append((node_pos, "shadow", name))
        elif not isinstance(node, (ast.Global, ast.Nonlocal)):
            bound = _py01_bindings_of_node(node)
            bound_anywhere.update(bound)
            for name in bound:
                events.append((node_pos, "shadow", name))
    with _PY07_SCOPE_FACTS_LOCK:
        _PY07_SCOPE_FACTS_CACHE[key] = (scope, parent_map, bound_anywhere, events)
        while len(_PY07_SCOPE_FACTS_CACHE) > _PY07_SCOPE_FACTS_MAX:
            _PY07_SCOPE_FACTS_CACHE.pop(
                next(iter(_PY07_SCOPE_FACTS_CACHE)), None)
    return bound_anywhere, events


def _py07_import_aliases(
        scope, parent_map: dict, call_pos: tuple[int, int]
) -> tuple[dict[str, str], dict[str, str], set[str], set[str]]:
    from_map: dict[str, str] = {}
    module_map: dict[str, str] = {}
    prior_imports: dict[str, tuple[tuple[int, int], str, bool]] = {}
    prior_shadows: dict[str, tuple[int, int]] = {}
    bound_anywhere, events = _py07_scope_import_facts(scope, parent_map)
    for node_pos, kind, payload in events:
        if node_pos >= call_pos:
            continue
        if kind == "import":
            local, target, is_from = payload
            prior_imports[local] = (node_pos, target, is_from)
        else:
            prior_shadows[payload] = node_pos
    for local, (import_pos, target, is_from) in prior_imports.items():
        if prior_shadows.get(local, (-1, -1)) > import_pos:
            continue
        (from_map if is_from else module_map)[local] = target
    prior_shadowed = {
        name for name, shadow_pos in prior_shadows.items()
        if name not in prior_imports
        or shadow_pos > prior_imports[name][0]
    }
    return from_map, module_map, prior_shadowed, bound_anywhere
def _py07_resolved_call_name(node: ast.Call, from_map: dict[str, str],
                             module_map: dict[str, str]) -> str:
    func = node.func
    if isinstance(func, ast.Name):
        return from_map.get(func.id, "")
    if isinstance(func, ast.Attribute):
        dotted = get_call_name(node) or ""
        head, _sep, tail = dotted.partition(".")
        base = module_map.get(head) or from_map.get(head)
        if not base:
            return ""
        return f"{base}.{tail}" if tail else base
    return ""
def _py07_scoped_call_name(node: ast.Call, parent_map: dict,
                           alias_cache: dict) -> str:
    func = node.func
    direct_name = isinstance(func, ast.Name)
    if direct_name:
        head_node = func
    elif isinstance(func, ast.Attribute):
        head_node = func
        while isinstance(head_node, ast.Attribute):
            head_node = head_node.value
        if not isinstance(head_node, ast.Name):
            return ""
    else:
        return ""
    head = head_node.id
    if _py03_shadowed_by_comprehension(head_node, parent_map):
        return ""
    call_pos = (node.lineno, node.col_offset)
    for scope in iter_evaluation_scope_chain(node, parent_map):
        scope_key = (id(scope), call_pos)
        if scope_key not in alias_cache:
            alias_cache[scope_key] = _py07_import_aliases(
                scope, parent_map, call_pos)
        from_map, module_map, prior_shadowed, bound_anywhere = alias_cache[scope_key]
        if head in prior_shadowed:
            return ""
        has_prior_import = (
            head in from_map if direct_name
            else head in module_map or head in from_map
        )
        if has_prior_import:
            return _py07_resolved_call_name(node, from_map, module_map)
        if head in bound_anywhere and not isinstance(scope, ast.ClassDef):
            return ""
    return ""
def check_PY07(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    parent_map = build_parent_map(tree)
    alias_cache: dict = {}
    type_checking_ids = type_checking_body_node_ids(tree)
    for node in walk_nodes(tree):
        if id(node) in type_checking_ids:
            continue
        if not isinstance(node, ast.Call):
            continue
        if not isinstance(node.func, (ast.Name, ast.Attribute)):
            continue
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr != "spec_from_file_location"):
            continue
        if _py07_scoped_call_name(
                node, parent_map, alias_cache) != _PY07_SPEC_CALL:
            continue
        _dir_paths = _py07_dir_path_args(node, filepath)
        if _dir_paths:
            issues.append(_py07_finding(_dir_paths, node.lineno, filepath))
    return issues
def _py07_finding(dir_paths: list, line: int, filepath: Any) -> dict:
    paths_text = ", ".join(f"'{p}'" for p in dir_paths)
    return {
        "rule_id": "PY-07",
        "severity": "P0",
        "line": line,
        "file": filepath,
        "message": (
            f"PY-07: spec_from_file_location 传入目录路径 {paths_text},"
            f"对包目录返回 None→module_from_spec(None) 异常."
        ),
        "suggestion": (
            "用 types.ModuleType 手动创建模块对象,"
            "通过 sys.modules.setdefault 注册"
        ),
        "rule_ref": "2630 Python importlib 已知行为",
    }
def wiring_declarations() -> dict:
    return {"catalogs": {"rule_bindings": {
        'PY01': check_PY01, 'PY02': check_PY02, 'PY03': check_PY03,
        'PY04': check_PY04, 'PY05': check_PY05, 'PY07': check_PY07,
    }}}

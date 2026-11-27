from __future__ import annotations

import ast
import logging
import os
from collections import deque
from collections.abc import Iterator
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    annassign_target_names,
    ast_name,
    augassign_target_names,
    iter_unpack_target_names,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    scope_import_tables,
)
from jwsgj.engine_d2_flow import (
    MUTATING_ATTRS,
    calls_by_lineno_cached,
    clear_call_scan_memos,
    clear_flow_memos,
    expr_reaches_param,
    fn_def_site_exprs,
    function_param_names,
    interpreter_option_consumes_value,
    iter_module_scope_stmts,
    load_sink_tree,
    match_capture_names,
    memo_clear,
    memo_hit,
    memo_store,
    shell_interpretation_open,
    sink_first_arg,
)
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger("jwsgj.engine_d2_verdict")
__all__ = [
    "E2_BRANCH_BOUNDARY",
    "GLOBAL_REBOUND_MARKER",
    "IMPORTED_NAME_MARKER",
    "SanitizeCtx",
    "argv_mutation_name_set",
    "clear_e2_scope_memos",
    "enclosing_class_assigns",
    "enclosing_class_dynamic_attrs",
    "enclosing_function",
    "enclosing_function_bound_names",
    "expr_is_sanitized",
    "function_rebound_param_names",
    "function_unmodeled_binding_names",
    "function_var_exprs",
    "is_harness_subprocess_call",
    "iter_own_nodes_with_def_sites",
    "lambda_own_walrus_targets",
    "module_assigns_outside",
    "module_multi_assigned_names",
    "module_var_map_cached",
    "mutation_alias_closure",
    "mutation_append_records",
    "mutation_positional_records",
    "nested_scope_bound_names",
    "nested_scope_node_bound_names",
    "resolve_bound_chain",
    "resolve_local_list_expr",
    "resolve_name_closure",
    "scope_bound_names",
    "sentinel_branch_reaches_param",
    "subprocess_sink_calls",
]
E2_BRANCH_BOUNDARY = "__E2_IFEXP_BRANCH_BOUNDARY__"
_DEFAULT_DEPTH = 0
_DASH_C_LITERALS = frozenset({"-c", "/c", "/k"})
_INTERPRETER_HEAD_HINTS = (
    "python", "pythonw", "pyw", "py", "pypy", "perl", "ruby", "node",
    "nodejs", "bash", "zsh", "sh", "shell", "dash", "ash", "ksh",
    "csh", "tcsh", "fish", "cmd", "powershell", "pwsh", "lua",
    "luajit", "php",
)
_HEAD_VERSION_SUFFIX_CHARS = frozenset("0123456789._-")
def _program_basename(value: str) -> str:
    _base = value.lower().replace("\\", "/").rsplit("/", 1)[-1]
    for _sfx in (".exe", ".bat", ".cmd", ".com"):
        if _base.endswith(_sfx):
            return _base[: -len(_sfx)]
    return _base
def _matches_interpreter_hint(base: str, hint: str) -> bool:
    if base == hint:
        return True
    return (base.startswith(hint)
            and all(_c in _HEAD_VERSION_SUFFIX_CHARS
                    for _c in base[len(hint):]))
def _is_sys_executable(node: ast.AST) -> bool:
    return (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == "sys" and node.attr == "executable")
def _is_interpreter_head(head: ast.AST) -> bool:
    if isinstance(head, ast.Attribute):
        return _is_sys_executable(head)
    if isinstance(head, ast.Constant) and isinstance(head.value, str):
        _base = _program_basename(head.value)
        return any(_matches_interpreter_hint(_base, _h)
                   for _h in _INTERPRETER_HEAD_HINTS)
    return False
def _is_interpreter_head_bound(head, ctx) -> bool:
    resolved = resolve_bound_chain(head, ctx.var_map)
    if _is_sys_executable(resolved):
        line = getattr(head, "lineno", -1)
        return ("sys" not in nested_scope_bound_names(ctx.tree, line)
                and _visible_sys_import_clear(ctx))
    return _is_interpreter_head(resolved)
def _interpreter_head_hint(head, ctx) -> str:
    resolved = resolve_bound_chain(head, ctx.var_map)
    if _is_sys_executable(resolved):
        return "python"
    if not (isinstance(resolved, ast.Constant)
            and isinstance(resolved.value, str)):
        return ""
    base = _program_basename(resolved.value)
    return next((hint for hint in _INTERPRETER_HEAD_HINTS
                 if _matches_interpreter_hint(base, hint)), "")
def _is_branch_boundary(e) -> bool:
    return (isinstance(e, ast.Constant) and isinstance(e.value, str)
            and e.value == E2_BRANCH_BOUNDARY)
def _split_branch_segments(elts: list) -> list[list]:
    segs: list[list] = [[]]
    for _e in elts:
        if _is_branch_boundary(_e):
            segs.append([])
        else:
            segs[-1].append(_e)
    return segs
def _advance_interp_states(states, values, program) -> frozenset[int]:
    advanced: set[int] = set()
    for state in states:
        for value in values:
            if state == 2:
                advanced.add(2)
            elif state == 3:
                advanced.add(0)
            elif state == 1:
                advanced.add(-1 if value.startswith("-") else 2)
            elif interpreter_option_consumes_value(
                    program, value.strip()):
                advanced.add(3)
            elif value == "-m":
                advanced.add(1)
            elif _option_value_closes(value):
                advanced.add(2)
            else:
                advanced.add(0)
    return frozenset(advanced)
def _interp_states_closed(states) -> bool:
    return bool(states) and all(state == 2 for state in states)
def _argv_head_is_fixed_program(head, var_map) -> bool:
    if _is_interpreter_head(head):
        return True
    resolved = resolve_bound_chain(head, var_map)
    return (isinstance(resolved, ast.Constant)
            and isinstance(resolved.value, str))
_HARNESS_TOOL_HEAD_HINTS = (
    "pytest", "py.test", "ruff", "mypy", "pyright", "pylint",
    "flake8", "bandit", "black", "isort", "coverage", "tox", "nox",
    "pre-commit", "unittest", "nose", "nose2",
)
def _is_harness_tool_head(head, var_map) -> bool:
    if not _argv_head_is_fixed_program(head, var_map):
        return False
    resolved = resolve_bound_chain(head, var_map)
    if _is_interpreter_head(resolved) or not isinstance(resolved.value, str):
        return False
    base = _program_basename(resolved.value)
    return any(_matches_interpreter_hint(base, hint)
               for hint in _HARNESS_TOOL_HEAD_HINTS)
def _merge_branch_faces(left: ast.AST, right: ast.AST) -> ast.List:
    _le = list(getattr(left, "elts", []))
    _re = list(getattr(right, "elts", []))
    _segs = _combine_branch_segments(
        _split_branch_segments(_le), _split_branch_segments(_re))
    _elts: list = []
    for _i, _seg in enumerate(_segs):
        if _i:
            _elts.append(ast.Constant(value=E2_BRANCH_BOUNDARY))
        _elts.extend(_seg)
    return ast.List(elts=_elts, ctx=ast.Load())
def _combine_branch_segments(lsegs: list, rsegs: list) -> list:
    # jwsgj:suppress large_list_alloc — 审计认可：分支段组合受表达式分支数约束，规模有界
    return [list(_ls) + list(_rs) for _ls in lsegs for _rs in rsegs]
def _is_add_binop(expr) -> bool:
    return isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add)
def resolve_local_list_expr(
    expr, var_map, _depth=_DEFAULT_DEPTH,
) -> ast.AST | None:
    if _depth > 5 or expr is None:
        return None
    if isinstance(expr, ast.List):
        return expr
    if isinstance(expr, ast.Name):
        return resolve_local_list_expr(var_map.get(expr.id), var_map, _depth + 1)
    if _is_add_binop(expr):
        return _resolve_binop_add(expr, var_map, _depth)
    if isinstance(expr, ast.IfExp):
        return _resolve_ifexp_branch(expr, var_map, _depth)
    return None
_COND_SCOPE_TYPES = tuple(t for t in (
    ast.If, ast.For, ast.AsyncFor, ast.While,
    ast.Try, getattr(ast, "TryStar", ast.Try),
    ast.With, ast.AsyncWith, getattr(ast, "Match", None),
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
    ast.IfExp, ast.BoolOp, ast.ListComp, ast.SetComp, ast.DictComp,
    ast.GeneratorExp,
) if t is not None)
def _resolve_binop_add(expr, var_map, _depth: int):
    left = resolve_local_list_expr(expr.left, var_map, _depth + 1)
    right = resolve_local_list_expr(expr.right, var_map, _depth + 1)
    if left is not None and right is not None:
        return _merge_branch_faces(left, right)
    return None
def _resolve_ifexp_branch(expr, var_map, _depth: int):
    body = resolve_local_list_expr(expr.body, var_map, _depth + 1)
    orelse = resolve_local_list_expr(expr.orelse, var_map, _depth + 1)
    if body is not None and orelse is not None:
        _sentinel = ast.Constant(value=E2_BRANCH_BOUNDARY)
        return ast.List(
            elts=(list(getattr(body, "elts", [])) + [_sentinel]
                  + list(getattr(orelse, "elts", []))),
            ctx=ast.Load())
    return None
def _parent_chain_index(root) -> dict:
    _parent: dict = {}
    _todo = deque([root])
    while _todo:
        _n = _todo.popleft()
        for _c in ast.iter_child_nodes(_n):
            _parent[id(_c)] = _n
            _todo.append(_c)
    return _parent
def _is_conditional_scope(node, fn, parent: dict) -> bool:
    _cur = parent.get(id(node))
    while _cur is not None and _cur is not fn:
        if isinstance(_cur, _COND_SCOPE_TYPES):
            return True
        _cur = parent.get(id(_cur))
    return False
def _aug_append_elts(node, var_name: str) -> list:
    if (isinstance(node, ast.AugAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id == var_name
            and isinstance(node.op, ast.Add)):
        v = node.value
        return v.elts if isinstance(v, ast.List) else [v]
    return []
def _is_method_call_on(node, var_name: str, attrs: frozenset) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in attrs
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == var_name)
def _tail_call_append_elts(node, var_name: str) -> list:
    if not _is_method_call_on(node, var_name, _TAIL_APPEND_ATTRS):
        return []
    _elts: list = []
    for a in node.args:
        _elts.extend(a.elts if isinstance(a, ast.List) else [a])
    return _elts
def _append_mutation_elts(node, var_name: str) -> list:
    _elts = _aug_append_elts(node, var_name)
    if _elts:
        return _elts
    return _tail_call_append_elts(node, var_name)
def _sort_records(records: list) -> list:
    records.sort(key=lambda r: (r[0], r[1]))
    return records
def _nested_scope_shadows_var(node, var_name: str,
                                outer_is_local: bool) -> bool:
    if var_name in _declared_names(node, ast.Nonlocal):
        return False
    if var_name in _declared_names(node, ast.Global):
        return outer_is_local
    return var_name in _scope_node_bound_names(node)
def _is_direct_scope_body_child(scope, child) -> bool:
    body = getattr(scope, "body", None)
    if isinstance(body, list):
        return any(stmt is child for stmt in body)
    return body is child
def _class_binding_flags(cls: ast.ClassDef) -> tuple[set, set, frozenset]:
    return (_declared_names(cls, ast.Nonlocal),
            _declared_names(cls, ast.Global), scope_bound_names(cls))
def _class_scope_shadows_node(node, scope, var_name: str,
                              outer_is_local: bool, parent: dict,
                              class_flags: dict) -> bool:
    cur = node
    while cur is not scope:
        up = parent.get(id(cur))
        if up is None:
            return False
        if (isinstance(up, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
                and _is_direct_scope_body_child(up, cur)):
            return False
        if (isinstance(up, ast.ClassDef)
                and not any(cur is site for site in _nested_definition_sites(up))):
            flags = class_flags.get(id(up))
            if flags is None:
                flags = _class_binding_flags(up)
                class_flags[id(up)] = flags
            nonlocals, globals_, bound = flags
            if var_name in nonlocals:
                return False
            if var_name in globals_:
                return outer_is_local
            if var_name in bound:
                return True
        cur = up
    return False
def _iter_var_scope_nodes(scope, var_name: str):
    _outer_is_local = (not isinstance(scope, ast.Module)
                       and var_name in scope_bound_names(scope))
    parent = _parent_chain_index(scope)
    class_flags: dict = {}
    stack = list(reversed(_scope_roots(scope)))
    while stack:
        node = stack.pop()
        if not _class_scope_shadows_node(
                node, scope, var_name, _outer_is_local, parent, class_flags):
            yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            stack.extend(reversed(fn_def_site_exprs(node)))
            if _nested_scope_shadows_var(node, var_name, _outer_is_local):
                continue
            stack.extend(reversed(_scope_roots(node)))
            continue
        if isinstance(node, ast.ClassDef):
            stack.extend(reversed(_nested_definition_sites(node)))
            stack.extend(reversed(node.body))
            continue
        if isinstance(node, _COMPREHENSION_TYPES):
            if _nested_scope_shadows_var(node, var_name, _outer_is_local):
                _generators = getattr(node, "generators", ())
                if _generators:
                    stack.append(_generators[0].iter)
                continue
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def mutation_append_records(var_name: str, fn: ast.AST) -> list:
    if fn is None:
        return []
    parent = _parent_chain_index(fn)
    records: list = []
    for node in _iter_var_scope_nodes(fn, var_name):
        _elts = _append_mutation_elts(node, var_name)
        if _elts:
            _cond = _is_conditional_scope(node, fn, parent)
            for e in _elts:
                records.append((getattr(node, "lineno", 0),
                                getattr(node, "col_offset", 0), _cond, e))
    _sort_records(records)
    return records
_TAIL_APPEND_ATTRS = frozenset({"extend", "append", "add", "__iadd__"})
_STRUCTURAL_MUTATE_ATTRS = frozenset(
    {"insert", "pop", "remove", "clear", "reverse", "sort",
     "__setitem__", "__delitem__"})
def _subscript_mutation_root_names(target) -> list[str]:
    if isinstance(target, (ast.Tuple, ast.List)):
        return [name for elt in target.elts
                for name in _subscript_mutation_root_names(elt)]
    if isinstance(target, ast.Starred):
        return _subscript_mutation_root_names(target.value)
    node = target
    has_subscript = False
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        has_subscript = has_subscript or isinstance(node, ast.Subscript)
        node = node.value
    return [node.id] if has_subscript and isinstance(node, ast.Name) else []
def _pos_mutation_target_hit(target, var_name: str) -> bool:
    return var_name in _subscript_mutation_root_names(target)
def _store_targets(node) -> list:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    if isinstance(node, ast.AugAssign):
        return [node.target]
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return [node.target]
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [it.optional_vars for it in node.items
                if it.optional_vars is not None]
    return []
def _structural_call_kind(node, var_name: str):
    if not _is_method_call_on(node, var_name, _STRUCTURAL_MUTATE_ATTRS):
        return None
    if node.func.attr == "insert":
        return "insert"
    if node.func.attr == "__setitem__":
        return "store"
    if node.func.attr == "__delitem__":
        return "del"
    return "reorder"
def _subscript_store_kind(node, var_name: str):
    if any(_pos_mutation_target_hit(_t, var_name)
           for _t in _store_targets(node)):
        return "store"
    return None
def _indirect_store_target(target) -> bool:
    if isinstance(target, (ast.Attribute, ast.Subscript)):
        return True
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_indirect_store_target(elt) for elt in target.elts)
    return (isinstance(target, ast.Starred)
            and _indirect_store_target(target.value))
def _alias_store_kind(node, var_name: str):
    if not (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign))
            and node.value is not None):
        return None
    targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
    if not any(_indirect_store_target(target) for target in targets):
        return None
    if any(isinstance(sub, ast.Name) and sub.id == var_name
           for sub in walk_nodes(node.value)):
        return "alias"
    return None
def _pos_mutation_kind(node, var_name: str):
    _kind = _structural_call_kind(node, var_name)
    if _kind is not None:
        return _kind
    _kind = _alias_store_kind(node, var_name)
    if _kind is not None:
        return _kind
    _kind = _subscript_store_kind(node, var_name)
    if _kind is not None:
        return _kind
    if isinstance(node, ast.Delete):
        for _t in node.targets:
            if _pos_mutation_target_hit(_t, var_name):
                return "del"
    return None
def mutation_positional_records(var_name: str, fn: ast.AST) -> list:
    if fn is None:
        return []
    records: list = []
    for node in _iter_var_scope_nodes(fn, var_name):
        _kind = _pos_mutation_kind(node, var_name)
        if _kind is not None:
            records.append((getattr(node, "lineno", 0),
                            getattr(node, "col_offset", 0), _kind))
    _sort_records(records)
    return records
def _closure_successors(cur, var_map, depth: int) -> list:
    if isinstance(cur, ast.Name):
        return [(var_map.get(cur.id), depth + 1)]
    if _is_add_binop(cur):
        return [(cur.left, depth + 1), (cur.right, depth + 1)]
    if isinstance(cur, ast.IfExp):
        return [(cur.body, depth + 1), (cur.orelse, depth + 1)]
    return [(_n, depth + 1) for _n in walk_nodes(cur)
            if isinstance(_n, ast.Name)]
def resolve_name_closure(expr, var_map) -> set:
    _out: set = set()
    _stack: list = [(expr, 0)]
    while _stack:
        _cur, _depth = _stack.pop()
        if _depth > 5 or _cur is None:
            continue
        if isinstance(_cur, ast.Name):
            if _cur.id in _out:
                continue
            _out.add(_cur.id)
        _stack.extend(_closure_successors(_cur, var_map, _depth))
    return _out
def argv_mutation_name_set(first, var_map, fn_vars=None) -> frozenset:
    _names = set(resolve_name_closure(first, var_map))
    _alias_map = {k: (v if isinstance(v, list) else [v])
                  for k, v in var_map.items()}
    if fn_vars:
        _alias_map.update(fn_vars)
    for _n in list(_names):
        _names |= mutation_alias_closure(_n, _alias_map)
    return frozenset(_names)
def resolve_bound_chain(expr: ast.AST, var_map) -> Any:
    _seen: set = set()
    while (isinstance(expr, ast.Name) and expr.id in var_map
           and expr.id not in _seen and len(_seen) < 5):
        _seen.add(expr.id)
        expr = var_map[expr.id]
    return expr
def sentinel_branch_reaches_param(elts, params, assigns) -> bool:
    for _i in range(1, len(elts)):
        if (isinstance(elts[_i - 1], ast.Constant)
                and getattr(elts[_i - 1], "value", None) == E2_BRANCH_BOUNDARY
                and expr_reaches_param(elts[_i], params, assigns)):
            return True
    return False
def _structural_alias_values(value) -> tuple:
    return tuple(value) if isinstance(value, frozenset) else (value,)
def _is_structural_subprocess_call(call, aliases) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        return any(isinstance(_value, str)
                   and _value.startswith("@subprocess.")
                   for _value in _structural_alias_values(
                       aliases.get(func.id, "")))
    return (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and "subprocess" in _structural_alias_values(
                aliases.get(func.value.id, func.value.id)))
def subprocess_sink_calls(path: str, tree: ast.Module, line: int):
    for call, params, assigns, aliases in calls_by_lineno_cached(
            path, tree).get(line, ()):
        if _is_structural_subprocess_call(call, aliases or {}):
            yield call, params, assigns
@dataclass(frozen=True)
class _HarnessJudgeCtx:
    var_map: dict
    fn_vars: dict
    tree: ast.Module
    path: str
    fn: object = None
def _import_binding_identity(binding) -> str:
    if not isinstance(binding, tuple) or not binding:
        return ""
    if binding[0] == "import" and len(binding) > 1:
        return binding[1] if isinstance(binding[1], str) else ""
    if binding[0] == "from" and len(binding) >= 3:
        module, member = binding[1], binding[2]
        if isinstance(module, str) and module and isinstance(member, str):
            return f"{module}.{member}"
    return ""
def _scope_has_non_import_binding(scope, name: str) -> bool:
    if (isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
            and name in function_param_names(scope)):
        return True
    return any(
        not isinstance(node, (ast.Import, ast.ImportFrom))
        and name in _scoped_node_bound_names(scope, node)
        for node in iter_own_nodes_with_def_sites(scope))
def _visible_sys_import_clear(ctx: _HarnessJudgeCtx) -> bool:
    tables = scope_import_tables(ctx.tree)
    if not tables or ctx.fn is None:
        return False
    parent = collect_lexical_scope_table(ctx.tree).parent
    chain = []
    current = ctx.fn
    while current is not None:
        if not isinstance(current, ast.ClassDef):
            chain.append(current)
        current = parent.get(current)
    identity = ""
    for scoped in reversed(chain):
        binding = (tables.get(scoped) or {}).get("sys")
        if binding is not None:
            identity = _import_binding_identity(binding)
        if _scope_has_non_import_binding(scoped, "sys"):
            identity = ""
    return identity == "sys"
def _harness_mutation_scope(name: str, ctx: _HarnessJudgeCtx):
    if ctx.fn is not None and name in scope_bound_names(ctx.fn):
        return ctx.fn
    return ctx.tree
def _harness_incremental_exprs(first, ctx: _HarnessJudgeCtx,
                               sink_pos: tuple[int, int]) -> list:
    records: list = []
    for _n in sorted(argv_mutation_name_set(
            first, ctx.var_map, ctx.fn_vars)):
        records.extend(mutation_append_records(
            _n, _harness_mutation_scope(_n, ctx)))
    records = [_r for _r in records if (_r[0], _r[1]) < sink_pos]
    _sort_records(records)
    return [e for _lo, _co, _cond, e in records]
def _dash_c_name_hit(_r, params, assigns, ctx: _HarnessJudgeCtx,
                     consts) -> bool:
    _fv = ctx.fn_vars.get(_r.id) or []
    if _fv:
        for _expr in _fv:
            _resolved = resolve_bound_chain(_expr, ctx.var_map)
            if isinstance(_resolved, ast.Name) and _resolved.id not in params:
                return True
            consts.update(_str_constants(_resolved))
        return bool(consts & _DASH_C_LITERALS)
    if not assigns.get(_r.id):
        return True
    return _dep_name_constants(_r, params, assigns, ctx, consts)
def _dep_name_constants(_r, params, assigns, ctx: _HarnessJudgeCtx,
                        consts) -> bool:
    for _dep in assigns.get(_r.id, ()):
        _dr = resolve_bound_chain(
            ast.Name(id=_dep, ctx=ast.Load()), ctx.var_map)
        if isinstance(_dr, ast.Name):
            if _dr.id in params:
                continue
            return True
        consts.update(_str_constants(_dr))
    return False
def _str_constants(*nodes) -> set:
    return {
        _n.value.lower()
        for node in nodes if node is not None
        for _n in walk_nodes(node)
        if isinstance(_n, ast.Constant) and isinstance(_n.value, str)
    }
def _static_option_constants(nodes, ctx) -> set[str]:
    return {
        value.lower()
        for node in nodes
        for value in (_static_option_values(node, ctx) or ())
    }
def _mod_multi_rebound(closure: set, ctx: _HarnessJudgeCtx) -> bool:
    mod_multi = module_multi_assigned_names(ctx.path, ctx.tree)
    return bool(mod_multi and any(
        _n in mod_multi and _n not in ctx.fn_vars for _n in closure))
def _harness_argv_has_dash_c(first, list_expr, params, assigns,
                             ctx: _HarnessJudgeCtx,
                             sink_pos: tuple[int, int]) -> bool:
    consts = _str_constants(first, list_expr)
    consts.update(_static_option_constants(
        getattr(list_expr, "elts", []), ctx))
    if _dash_c_elt_chain_hit(list_expr, params, assigns, ctx, consts):
        return True
    if consts & _DASH_C_LITERALS:
        return True
    _incremental_exprs = _harness_incremental_exprs(first, ctx, sink_pos)
    _incremental_consts = _str_constants(*_incremental_exprs)
    _incremental_consts.update(
        _static_option_constants(_incremental_exprs, ctx))
    if _incremental_consts & _DASH_C_LITERALS:
        return True
    return _mod_multi_rebound(
        resolve_name_closure(first, ctx.var_map), ctx)
def _dash_c_elt_chain_hit(list_expr, params, assigns,
                          ctx: _HarnessJudgeCtx, consts) -> bool:
    for _e in getattr(list_expr, "elts", []):
        _r = resolve_bound_chain(_e, ctx.var_map)
        if (isinstance(_r, ast.Name) and _r.id not in params
                and _dash_c_name_hit(_r, params, assigns, ctx, consts)):
            return True
        consts.update(_str_constants(_r))
    return False
def _merged_var_map(path, tree, fn, _fn_vars: dict, line: int) -> dict:
    var_map = dict(module_var_map_cached(path, tree))
    for _k, _exprs in _fn_vars.items():
        if len(_exprs) == 1:
            var_map[_k] = _exprs[0]
        else:
            var_map.pop(_k, None)
    _blocked: set = set()
    if fn is not None:
        _blocked |= function_unmodeled_binding_names(fn)
        _blocked |= enclosing_function_bound_names(tree, fn)
    _blocked.update(nested_scope_bound_names(tree, line))
    for _k in _blocked:
        var_map.pop(_k, None)
    return var_map
_STATIC_OPTION_VALUE_CAP = 64
def _option_values_from_exprs(exprs, ctx, depth, seen):
    values: set[str] = set()
    for _expr in exprs:
        _current = _static_option_values(_expr, ctx, depth + 1, seen)
        if not _current:
            return None
        values.update(_current)
        if len(values) > _STATIC_OPTION_VALUE_CAP:
            return None
    return frozenset(values)
def _static_name_values(expr, ctx, depth, seen):
    _seen = frozenset() if seen is None else seen
    if expr.id in _seen:
        return None
    _seen = _seen | {expr.id}
    _local = ctx.fn_vars.get(expr.id)
    if _local:
        return _option_values_from_exprs(_local, ctx, depth, _seen)
    _resolved = resolve_bound_chain(expr, ctx.var_map)
    if _resolved is expr:
        return None
    return _static_option_values(_resolved, ctx, depth + 1, _seen)
def _static_binop_values(expr, ctx, depth, seen):
    _left = _static_option_values(expr.left, ctx, depth + 1, seen)
    _right = _static_option_values(expr.right, ctx, depth + 1, seen)
    if (not _left or not _right
            or len(_left) * len(_right) > _STATIC_OPTION_VALUE_CAP):
        return None
    return frozenset(_l + _r for _l in _left for _r in _right)
def _static_option_values(expr, ctx, depth=_DEFAULT_DEPTH, seen=None):
    if depth > 6 or expr is None:
        return None
    if isinstance(expr, ast.Constant):
        if _is_branch_boundary(expr):
            return None
        return (frozenset({expr.value})
                if isinstance(expr.value, str) else None)
    if isinstance(expr, ast.Name):
        return _static_name_values(expr, ctx, depth, seen)
    if isinstance(expr, (ast.List, ast.Tuple, ast.Set)):
        return _option_values_from_exprs(expr.elts, ctx, depth, seen)
    if isinstance(expr, ast.IfExp):
        return _option_values_from_exprs(
            (expr.body, expr.orelse), ctx, depth, seen)
    if _is_add_binop(expr):
        return _static_binop_values(expr, ctx, depth, seen)
    return None
def _option_value_closes(value: str) -> bool:
    return value == "-m" or not value.startswith("-")
def _interp_option_zone_clear(seg, inc, ctx) -> bool:
    has_head = bool(seg and _is_interpreter_head_bound(seg[0], ctx))
    tail = seg[1:] if has_head else seg
    program = _interpreter_head_hint(seg[0], ctx) if has_head else ""
    states = frozenset({0})
    for expr in tail + inc:
        values = _static_option_values(expr, ctx)
        if values is None:
            return _interp_states_closed(states)
        states = _advance_interp_states(states, values, program)
    return _interp_states_closed(states)
def _argv_head_unsafe(elts, params, assigns) -> bool:
    return (not elts
            or expr_reaches_param(elts[0], params, assigns)
            or sentinel_branch_reaches_param(elts, params, assigns))
def _harness_call_prechecks(call, params, assigns,
                            ctx: _HarnessJudgeCtx):
    if shell_interpretation_open(call):
        return None
    first = sink_first_arg(call)
    list_expr = resolve_local_list_expr(first, ctx.var_map)
    if list_expr is None:
        return None
    sink_pos = _source_position(call)
    if any((_r[0], _r[1]) < sink_pos
           for _n in argv_mutation_name_set(first, ctx.var_map, ctx.fn_vars)
           for _r in mutation_positional_records(
               _n, _harness_mutation_scope(_n, ctx))):
        return None
    if _harness_argv_has_dash_c(
            first, list_expr, params, assigns, ctx, sink_pos):
        return None
    elts = getattr(list_expr, "elts", [])
    if _argv_head_unsafe(elts, params, assigns):
        return None
    return first, elts
def _harness_tool_incremental_clear(inc, ctx) -> bool:
    return all(_static_option_values(expr, ctx) is not None for expr in inc)
def _tail_segment_clear(_seg, inc, ctx) -> bool:
    if not _seg:
        return not inc
    if _is_interpreter_head_bound(_seg[0], ctx):
        return _interp_option_zone_clear(_seg, inc, ctx)
    return (_is_harness_tool_head(_seg[0], ctx.var_map)
            and _harness_tool_incremental_clear(inc, ctx))
def _harness_branch_segments_clear(elts, inc, ctx) -> bool:
    _segments = _split_branch_segments(elts[1:])
    _sentinel_head = _is_branch_boundary(elts[0])
    if _sentinel_head:
        _segments = [[]] + _segments
    if _is_interpreter_head_bound(elts[0], ctx):
        if _segments and not _interp_option_zone_clear(
                [elts[0], *_segments[0]], inc, ctx):
            return False
        _tails = _segments[1:]
    else:
        if (not _is_harness_tool_head(elts[0], ctx.var_map)
                or not _harness_tool_incremental_clear(inc, ctx)):
            return False
        _tails = _segments if _sentinel_head else _segments[1:]
    return all(_tail_segment_clear(seg, inc, ctx) for seg in _tails)
def _harness_single_call_clear(call, params, assigns,
                               ctx: _HarnessJudgeCtx) -> bool:
    _pre = _harness_call_prechecks(call, params, assigns, ctx)
    if _pre is None:
        return False
    first, elts = _pre
    _inc = _harness_incremental_exprs(
        first, ctx, _source_position(call))
    return _harness_branch_segments_clear(elts, _inc, ctx)
def is_harness_subprocess_call(
    skill_dir: str, rel_file: str, line: int, cache=None,
) -> bool:
    try:
        tree, path = load_sink_tree(skill_dir, rel_file, cache)
        if tree is None or enclosing_function(tree, line) is None:
            return False
        return _all_harness_calls_clear(
            path, tree, line, _build_harness_judge_ctx(tree, path, line))
    except Exception as e:  
        _log.debug("harness 判定异常，保守不判误报交 CV 仲裁: %s", e, exc_info=True)
        return False
def _fn_vars_before_line(fn_vars: dict, line: int) -> dict:
    return {
        name: [_e for _e in exprs if getattr(_e, "lineno", line) <= line]
        for name, exprs in fn_vars.items()
    }
def _build_harness_judge_ctx(tree, path, line) -> _HarnessJudgeCtx:
    _fn = enclosing_function(tree, line)
    _all_fn_vars = function_var_exprs(_fn) if _fn is not None else {}
    _fn_vars = _fn_vars_before_line(_all_fn_vars, line)
    return _HarnessJudgeCtx(
        var_map=_merged_var_map(path, tree, _fn, _fn_vars, line),
        fn_vars=_fn_vars, tree=tree, path=path, fn=_fn)
def _all_harness_calls_clear(path, tree, line, jctx: _HarnessJudgeCtx) -> bool:
    _matched = False
    for call, params, assigns in subprocess_sink_calls(path, tree, line):
        _matched = True
        if not _harness_single_call_clear(call, params, assigns, jctx):
            return False
    return _matched
def _is_chr_call(call) -> bool:
    return (isinstance(call, ast.Call)
            and isinstance(call.func, ast.Name)
            and call.func.id == "chr"
            and len(call.args) == 1)
def _is_chr_int_constant(expr) -> bool:
    return (_is_chr_call(expr)
            and isinstance(expr.args[0], ast.Constant)
            and isinstance(expr.args[0].value, int))
def _replace_old_new_args(expr: ast.Call):
    if len(expr.args) >= 2:
        return expr.args[0], expr.args[1]
    old = expr.args[0] if expr.args else _keyword_arg(expr, "old")
    return old, _keyword_arg(expr, "new")
def _keyword_arg(expr: ast.Call, name: str):
    for k in expr.keywords:
        if k.arg == name:
            return k.value
    return None
def _joinedstr_template_static(expr, mod_assigns, depth,
                               fn_bindings) -> bool:
    for v in expr.values:
        if isinstance(v, ast.Constant):
            continue
        if not _formatted_value_static(v, mod_assigns, depth, fn_bindings):
            return False
    return True
def _formatted_value_static(v, mod_assigns, depth, fn_bindings) -> bool:
    if not isinstance(v, ast.FormattedValue):
        return False
    _fs = getattr(v, "format_spec", None)
    if (_fs is not None
            and not _is_static_template(_fs, mod_assigns, depth + 1,
                                        fn_bindings)):
        return False
    return _is_static_template(v.value, mod_assigns, depth + 1, fn_bindings)
def _exprs_template_static(exprs, mod_assigns, depth, fn_bindings) -> bool:
    return bool(exprs) and all(
        _is_static_template(e, mod_assigns, depth + 1, fn_bindings)
        for e in exprs)
def _mod_assigns_template_static(exprs, mod_assigns, depth,
                               fn_bindings) -> bool:
    if any(e is IMPORTED_NAME_MARKER or e is GLOBAL_REBOUND_MARKER
           for e in exprs or []):
        return False
    return _exprs_template_static(exprs, mod_assigns, depth, fn_bindings)
def _name_template_static(expr, mod_assigns, depth, fn_bindings) -> bool:
    if fn_bindings is not None and expr.id in fn_bindings:
        return _exprs_template_static(
            fn_bindings.get(expr.id), mod_assigns, depth, fn_bindings)
    return _mod_assigns_template_static(
        mod_assigns.get(expr.id), mod_assigns, depth, fn_bindings)
def _is_static_template(
    expr, mod_assigns, depth=_DEFAULT_DEPTH, fn_bindings=None,
):
    if depth > 6 or expr is None:
        return False
    if isinstance(expr, ast.Constant):
        return True
    _handler = _TEMPLATE_DISPATCH.get(expr.__class__)
    if _handler is None:
        return False
    return _handler(expr, mod_assigns, depth, fn_bindings)
def _binop_template_static(expr, mod_assigns, depth, fn_bindings) -> bool:
    return (isinstance(expr.op, ast.Add)
            and _concat_template_static(expr, mod_assigns, depth, fn_bindings))
def _ifexp_template_static(expr, mod_assigns, depth, fn_bindings) -> bool:
    return (_is_static_template(expr.body, mod_assigns, depth + 1,
                                fn_bindings)
            and _is_static_template(expr.orelse, mod_assigns, depth + 1,
                                    fn_bindings))
_TEMPLATE_DISPATCH = {
    ast.JoinedStr: _joinedstr_template_static,
    ast.Name: _name_template_static,
    ast.BinOp: _binop_template_static,
    ast.IfExp: _ifexp_template_static,
}
def _concat_template_static(expr, mod_assigns, depth, fn_bindings) -> bool:
    return (_is_static_template(expr.left, mod_assigns, depth + 1, fn_bindings)
            and _is_static_template(expr.right, mod_assigns, depth + 1,
                                    fn_bindings))
def _function_reference_escapes(tree, fname, shadow_scopes) -> bool:
    parents = _parent_chain_index(tree)
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and node.id == fname):
            continue
        line = getattr(node, "lineno", -1)
        if _call_arg_shadowed(node, line, shadow_scopes):
            continue
        parent = parents.get(id(node))
        if isinstance(parent, ast.Call) and parent.func is node:
            continue
        return True
    return False
def _callsites_arg_static(tree, fname, arg_index, fn):
    mod_assigns = module_assigns_outside(tree, fn)
    _shadow_scopes = _collect_shadow_scopes(tree)
    if _function_reference_escapes(tree, fname, _shadow_scopes):
        return False
    found = False
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        _ok = _static_call_arg(node, fname, arg_index,
                               mod_assigns, _shadow_scopes)
        if _ok is None:
            continue
        found = True
        if not _ok:
            return False
    return found
def _static_call_arg(node: ast.Call, fname: str, arg_index: int,
                     mod_assigns: dict, shadow_scopes: list):
    if not isinstance(node.func, ast.Name) or node.func.id != fname:
        return None
    line = getattr(node, "lineno", -1)
    if _call_arg_shadowed(node.func, line, shadow_scopes):
        return None
    if arg_index >= len(node.args):
        return False
    if any(isinstance(a, ast.Starred)
           for a in node.args[:arg_index + 1]):
        return False
    _arg = node.args[arg_index]
    if _call_arg_shadowed(_arg, line, shadow_scopes):
        return False
    return _is_static_template(_arg, mod_assigns)
_SCOPE_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                     ast.ClassDef, ast.ListComp, ast.SetComp, ast.DictComp,
                     ast.GeneratorExp)
def _scope_node_bound_names(node) -> frozenset:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return scope_bound_names(node)
    return frozenset(nested_scope_node_bound_names(node))
def _nested_shadow_spans(node) -> tuple:
    if not isinstance(node, ast.ClassDef):
        return ()
    return tuple(
        _node_span(n) for n in walk_nodes(node)
        if n is not node and isinstance(n, _SCOPE_NODE_TYPES))
def _collect_shadow_scopes(tree) -> list:
    scopes = []
    for n in walk_nodes(tree):
        if isinstance(n, _SCOPE_NODE_TYPES):
            scopes.append((*_node_span(n), _scope_node_bound_names(n),
                           _nested_shadow_spans(n)))
    return scopes
def _call_arg_shadowed(arg, line: int, shadow_scopes) -> bool:
    _arg_names = {n.id for n in walk_nodes(arg) if isinstance(n, ast.Name)}
    for lo, hi, bounds, excluded_spans in shadow_scopes:
        if not (lo <= line <= hi
                and any(name in bounds for name in _arg_names)):
            continue
        if any(ex_lo <= line <= ex_hi for ex_lo, ex_hi in excluded_spans):
            continue
        return True
    return False
@dataclass(slots=True)
class SanitizeCtx:
    guards: object
    fn_vars: dict
    params: list
    tree: object
    fn: object
    mod_assigns: dict
    cls_assigns: object = None
    cls_name: str = ""
    cls_dynamic: object = None
    import_fims: object = None
    taint_funcs: object = None
    def __post_init__(self):
        if self.cls_assigns is None:
            self.cls_assigns = {}
        if self.cls_dynamic is None:
            self.cls_dynamic = frozenset()
        if self.import_fims is None:
            self.import_fims = {}
        if self.taint_funcs is None:
            self.taint_funcs = frozenset()
def _int_literal(node) -> int | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if not (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd, ast.Invert))):
        return None
    value = _int_literal(node.operand)
    if value is None:
        return None
    if isinstance(node.op, ast.USub):
        return -value
    return value if isinstance(node.op, ast.UAdd) else ~value
def _dict_literal_key(node) -> tuple[bool, object]:
    if isinstance(node, ast.Constant):
        return True, node.value
    value = _int_literal(node)
    return value is not None, value
def _literal_container_alias_values(
        container, index, fn_vars=None, depth=_DEFAULT_DEPTH,
        seen=frozenset()) -> tuple:
    if depth > 6:
        return ()
    if isinstance(container, ast.Name):
        if container.id in seen:
            return ()
        return tuple(
            value
            for binding in (fn_vars or {}).get(container.id, ())
            for value in _literal_container_alias_values(
                binding, index, fn_vars, depth + 1, seen | {container.id})
        )
    if isinstance(container, (ast.IfExp, ast.BoolOp, ast.NamedExpr)):
        if isinstance(container, ast.IfExp):
            branches = (container.body, container.orelse)
        elif isinstance(container, ast.BoolOp):
            branches = tuple(container.values)
        else:
            branches = (container.value,)
        return tuple(
            value
            for branch in branches
            for value in _literal_container_alias_values(
                branch, index, fn_vars, depth + 1, seen)
        )
    if isinstance(container, ast.Subscript):
        containers = _literal_container_alias_values(
            container.value, container.slice, fn_vars, depth + 1, seen)
        return tuple(
            value
            for inner in containers
            for value in _literal_container_alias_values(
                inner, index, fn_vars, depth + 1, seen)
        )
    if isinstance(index, ast.Slice):
        return ()
    if isinstance(container, (ast.List, ast.Tuple)):
        if any(isinstance(elt, ast.Starred) for elt in container.elts):
            return tuple(elt.value if isinstance(elt, ast.Starred) else elt
                         for elt in container.elts)
        index_value = _int_literal(index)
        if index_value is None:
            if isinstance(index, (ast.Constant, ast.UnaryOp)):
                return ()
            return tuple(container.elts)
        try:
            return (container.elts[index_value],)
        except IndexError:
            return ()
    if not isinstance(container, ast.Dict):
        return ()
    index_known, index_value = _dict_literal_key(index)
    values = []
    for key, value in zip(container.keys, container.values, strict=True):
        if key is None:
            return tuple(container.values)
        key_known, key_value = _dict_literal_key(key)
        if not key_known or not index_known:
            return tuple(container.values)
        if key_value == index_value:
            values.append(value)
    return tuple(values)
def _expr_may_alias(expr, holders, fn_vars=None) -> bool:
    stack = [expr]
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Name):
            if current.id in holders:
                return True
            continue
        if isinstance(current, ast.IfExp):
            stack.extend((current.body, current.orelse))
        elif isinstance(current, ast.BoolOp):
            stack.extend(current.values)
        elif isinstance(current, ast.NamedExpr):
            stack.append(current.value)
        elif isinstance(current, ast.Subscript):
            stack.extend(_literal_container_alias_values(
                current.value, current.slice, fn_vars))
    return False
def _extends_closure(name, exprs, closure, fn_vars=None) -> bool:
    return (name not in closure
            and any(_expr_may_alias(expr, closure, fn_vars)
                    for expr in exprs or ()))
def mutation_alias_closure(var: str, fn_vars: dict) -> frozenset:
    closure = {var}
    changed = True
    while changed:
        changed = False
        for name, exprs in (fn_vars or {}).items():
            if _extends_closure(name, exprs, closure, fn_vars):
                closure.add(name)
                changed = True
    return frozenset(closure)
def _close_alias_window(active: dict[str, tuple[int, int]],
                        windows: dict[str, list], name: str,
                        position: tuple[int, int]) -> None:
    if name in active:
        windows.setdefault(name, []).append((active.pop(name), position))
def _flush_alias_windows(active: dict[str, tuple[int, int]],
                         windows: dict[str, list]) -> None:
    for name, start in active.items():
        windows.setdefault(name, []).append((start, None))
def _source_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, 'lineno', -1), getattr(node, 'col_offset', -1))
def _binding_execution_scope(name, expr, fn, parents):
    owner = fn
    if id(expr) in parents:
        current = parents[id(expr)]
        while current is not None:
            if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.Lambda)):
                owner = current
                break
            current = parents.get(id(current))
    else:
        line = getattr(expr, 'lineno', -1)
        owner = max(
            (node for node in walk_nodes(fn)
             if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.Lambda))
             and (getattr(node, 'lineno', 0) or 0) <= line
             <= (getattr(node, 'end_lineno', 0) or 0)),
            key=lambda node: node.lineno,
            default=fn,
        )
    if owner is not fn and name in scope_bound_names(owner):
        return owner
    return fn
def _binding_expr_is_conditional(expr, name, fn, parents) -> bool:
    if fn is None:
        return False
    scope = _binding_execution_scope(name, expr, fn, parents)
    if id(expr) in parents:
        return _is_conditional_scope(expr, scope, parents)
    line = getattr(expr, 'lineno', -1)
    return any(
        node is not scope and isinstance(node, _COND_SCOPE_TYPES)
        and (getattr(node, 'lineno', 0) or 0) < line
        <= (getattr(node, 'end_lineno', 0) or 0)
        for node in walk_nodes(scope))
_ALIAS_UNPACK_GROUP_TYPES = (
    ast.Assign, ast.AnnAssign, ast.For, ast.AsyncFor,
)
def _alias_binding_group(expr, fn, parents) -> int:
    current = expr
    while id(current) in parents:
        current = parents[id(current)]
        if isinstance(current, _ALIAS_UNPACK_GROUP_TYPES):
            return id(current)
    position = _source_position(expr)
    candidates = []
    if fn is not None:
        for node in walk_nodes(fn):
            if not isinstance(node, _ALIAS_UNPACK_GROUP_TYPES):
                continue
            end = (getattr(node, 'end_lineno', -1),
                   getattr(node, 'end_col_offset', -1))
            if _source_position(node) <= position <= end:
                candidates.append(node)
    return id(max(candidates, key=_source_position)) if candidates else id(expr)
def _alias_events(fn_vars: dict, fn=None) -> list:
    parents = _parent_chain_index(fn) if fn is not None else {}
    events = [(getattr(expr, 'lineno', -1),
               getattr(expr, 'col_offset', -1), name, expr,
               _binding_expr_is_conditional(expr, name, fn, parents),
               _alias_binding_group(expr, fn, parents))
              for name, exprs in (fn_vars or {}).items()
              for expr in exprs or ()]
    events.sort(key=lambda item: (item[0], item[1], item[2]))
    return events
def _advance_alias_windows(
        events: list, var: str, fn_vars=None) -> dict[str, list]:
    holders = {var}
    active: dict[str, int] = {}
    windows: dict[str, list] = {}
    groups: dict[int, list] = {}
    for event in events:
        line, col, name, _expr, _conditional, group = event
        if name == var:
            continue
        groups.setdefault(group, []).append(event)
    for grouped in groups.values():
        may_aliases = [_expr_may_alias(event[3], holders, fn_vars)
                       for event in grouped]
        for event in grouped:
            line, col, name, _expr, conditional, _group = event
            if not conditional:
                _close_alias_window(
                    active, windows, name, (line, col))
        for event, may_alias in zip(grouped, may_aliases, strict=True):
            line, col, name, _expr, conditional, _group = event
            if may_alias:
                if name not in active:
                    active[name] = (line, col)
                holders.add(name)
            elif not conditional:
                holders.discard(name)
    _flush_alias_windows(active, windows)
    return windows
def _holds_at(name: str, position: tuple[int, int], windows: dict) -> bool:
    return any(start <= position and (end is None or position <= end)
               for start, end in windows.get(name, ()))
def _expr_holds_at(expr, position, windows, fn_vars) -> bool:
    holders = {name for name in windows if _holds_at(name, position, windows)}
    return _expr_may_alias(expr, holders, fn_vars)
def _is_alias_method_call(node, windows, fn_vars) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and _expr_holds_at(node.func.value, _source_position(node),
                               windows, fn_vars))
def _all_sanitized(items, ctx, depth) -> bool:
    return all(expr_is_sanitized(item, ctx, depth + 1) for item in items)
def _call_mutation_tainted(node, windows, ctx, depth) -> bool:
    if not _is_alias_method_call(node, windows, ctx.fn_vars):
        return False
    if node.func.attr not in _VALUE_MUTATING_ATTRS:
        return False
    return any(not expr_is_sanitized(a, ctx, depth + 1)
               for a in (*node.args, *(k.value for k in node.keywords)))
def _aug_mutation_tainted(node, windows, ctx, depth) -> bool:
    if not isinstance(node, ast.AugAssign):
        return False
    receivers = [node.target]
    if not isinstance(node.target, ast.Name):
        receivers.append(getattr(node.target, "value", None))
    return (any(_expr_holds_at(receiver, _source_position(node),
                               windows, ctx.fn_vars)
                for receiver in receivers if receiver is not None)
            and not expr_is_sanitized(node.value, ctx, depth + 1))
def _simple_assign_targets(node) -> list[ast.expr] | tuple[ast.expr, ...]:
    return node.targets if isinstance(node, ast.Assign) else (node.target,)
def _store_target_receivers(target):
    if isinstance(target, (ast.Tuple, ast.List, ast.Starred)):
        children = target.elts if hasattr(target, "elts") else (target.value,)
        for child in children:
            yield from _store_target_receivers(child)
    elif (isinstance(target, ast.Subscript)
          or (isinstance(target, ast.Attribute)
              and _subscript_mutation_root_names(target))):
        yield target.value
def _subscript_store_of_targets(targets, position, windows, fn_vars) -> bool:
    return any(
        _expr_holds_at(receiver, position, windows, fn_vars)
        for target in targets
        for receiver in _store_target_receivers(target))
def _store_mutation_tainted(node, windows, ctx, depth) -> bool:
    if not (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign))
            and node.value is not None):
        return False
    return (_subscript_store_of_targets(
                _simple_assign_targets(node), _source_position(node), windows,
                ctx.fn_vars)
            and not expr_is_sanitized(node.value, ctx, depth + 1))
def _target_store_mutation_tainted(node, windows, ctx, depth) -> bool:
    _position = _source_position(node)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return (_subscript_store_of_targets(
                    (node.target,), _position, windows, ctx.fn_vars)
                and not expr_is_sanitized(node.iter, ctx, depth + 1))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return any(
            item.optional_vars is not None
            and _subscript_store_of_targets(
                (item.optional_vars,), _position, windows, ctx.fn_vars)
            and not expr_is_sanitized(item.context_expr, ctx, depth + 1)
            for item in node.items)
    return False
_VALUE_MUTATING_ATTRS = MUTATING_ATTRS | frozenset({
    "setdefault", "symmetric_difference_update", "__setitem__",
    "__iadd__", "__ior__", "__ixor__"})
_MUTATION_CHANNELS = (
    _call_mutation_tainted,
    _aug_mutation_tainted,
    _store_mutation_tainted,
    _target_store_mutation_tainted,
)
def _mutation_stmts_tainted(windows, ctx, depth=_DEFAULT_DEPTH) -> bool:
    if ctx.fn is None or not windows:
        return False
    seen: set[int] = set()
    for name in windows:
        for node in _iter_var_scope_nodes(ctx.fn, name):
            if id(node) in seen:
                continue
            seen.add(id(node))
            if any(_channel(node, windows, ctx, depth)
                   for _channel in _MUTATION_CHANNELS):
                return True
    return False
def _builtin_shadowed(name: str, ctx) -> bool:
    if any(name in (_coll or ()) for _coll in (
            ctx.params,
            ctx.fn_vars,
            ctx.import_fims,
            ctx.mod_assigns,
            scope_bound_names(ctx.tree))):
        return True
    if ctx.fn is None:
        return False
    return (name in function_unmodeled_binding_names(ctx.fn)
            or name in enclosing_function_bound_names(ctx.tree, ctx.fn))
def _template_receiver_ok(call, ctx):
    recv = call.func.value
    if isinstance(recv, ast.Call):
        return False
    if _is_static_template(recv, ctx.mod_assigns,
                           fn_bindings=_fn_scope_bindings(ctx)):
        return True
    if isinstance(recv, ast.Name) and recv.id in ctx.params:
        return _param_receiver_callsites_static(recv.id, ctx)
    return False
def _fn_scope_bindings(ctx) -> dict:
    _bindings = dict(ctx.fn_vars or {})
    for _p in (ctx.params or ()):
        _bindings[_p] = []
    if ctx.fn is not None:
        for _n in function_unmodeled_binding_names(ctx.fn):
            _bindings[_n] = []
        for _n in enclosing_function_bound_names(ctx.tree, ctx.fn):
            _bindings[_n] = []
    return _bindings
def _param_receiver_callsites_static(recv_id: str, ctx) -> bool:
    fname = getattr(ctx.fn, "name", "")
    if not fname:
        return False
    if _owning_class(ctx.tree, ctx.fn) is not None:
        return False
    _a = ctx.fn.args
    _pos = [x.arg for x in list(_a.posonlyargs) + list(_a.args)]
    if recv_id not in _pos:
        return False
    return _callsites_arg_static(
        ctx.tree, fname, _pos.index(recv_id), ctx.fn)
def _list_binding_partition(fn_vars: dict, var: str) -> tuple[list, list]:
    _exprs = fn_vars.get(var, [])
    _inits = [e for e in _exprs if isinstance(e, (ast.List, ast.Tuple))]
    _others = [e for e in _exprs
               if not isinstance(e, (ast.List, ast.Tuple))]
    return _inits, _others
def _alias_closure_clean(name: str, ctx, depth) -> bool:
    alias_names = mutation_alias_closure(name, ctx.fn_vars)
    if any(record[2] == "alias" for alias in alias_names
           for record in mutation_positional_records(alias, ctx.fn)):
        return False
    _windows = _advance_alias_windows(
        _alias_events(ctx.fn_vars, ctx.fn), name, ctx.fn_vars)
    _windows.setdefault(name, []).append(((-1, -1), None))
    return not _mutation_stmts_tainted(_windows, ctx, depth)
def _list_name_binding_sanitized(var, ctx, depth) -> bool:
    if var in ctx.params:
        return var in ctx.guards
    if ctx.fn is not None and (
            var in function_unmodeled_binding_names(ctx.fn)
            or var in enclosing_function_bound_names(ctx.tree, ctx.fn)):
        return False
    inits, others = _list_binding_partition(ctx.fn_vars, var)
    if others or not inits:
        return False
    if not all(_all_sanitized(init.elts, ctx, depth) for init in inits):
        return False
    return _alias_closure_clean(var, ctx, depth)
def _list_expr_sanitized(expr, ctx, depth=_DEFAULT_DEPTH):
    if depth > 6 or expr is None:
        return False
    if isinstance(expr, (ast.List, ast.Tuple)):
        return _all_sanitized(expr.elts, ctx, depth)
    if isinstance(expr, ast.Name):
        return _list_name_binding_sanitized(expr.id, ctx, depth)
    return expr_is_sanitized(expr, ctx, depth + 1)
def _formatted_value_sanitized(expr, ctx, depth) -> bool:
    _fs = getattr(expr, "format_spec", None)
    if _fs is not None and not expr_is_sanitized(_fs, ctx, depth + 1):
        return False
    if expr.conversion == 114:
        return True
    return expr_is_sanitized(expr.value, ctx, depth + 1)
def _name_expr_sanitized(expr, ctx, depth) -> bool:
    if expr.id in ctx.guards:
        return True
    if expr.id in ctx.params:
        return False
    if ctx.fn is not None and (
            expr.id in function_unmodeled_binding_names(ctx.fn)
            or expr.id in enclosing_function_bound_names(ctx.tree, ctx.fn)):
        return False
    exprs = ctx.fn_vars.get(expr.id)
    if exprs:
        if not _all_sanitized(exprs, ctx, depth):
            return False
    elif not _is_static_template(expr, ctx.mod_assigns):
        return False
    return _alias_closure_clean(expr.id, ctx, depth)
_SELF_CLS_RECEIVERS = frozenset({"self", "cls"})
_ALL_CLASS_ATTRS = "*"
def _attr_receiver_rebound(recv: str, ctx) -> bool:
    if ctx.fn is None:
        return False
    unmodeled = (function_unmodeled_binding_names(ctx.fn)
                 - frozenset(ctx.params or ()))
    if recv in unmodeled or recv in function_rebound_param_names(ctx.fn):
        return True
    return recv in enclosing_function_bound_names(ctx.tree, ctx.fn)
def _decorator_is_staticmethod(dec) -> bool:
    if isinstance(dec, ast.Name):
        return dec.id == "staticmethod"
    return isinstance(dec, ast.Attribute) and dec.attr == "staticmethod"
def _is_staticmethod_fn(fn) -> bool:
    decorators = getattr(fn, "decorator_list", ()) or ()
    return any(_decorator_is_staticmethod(_d) for _d in decorators)
def _method_receiver_name(fn) -> str | None:
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    positional = [*fn.args.posonlyargs, *fn.args.args]
    return positional[0].arg if positional else None
def _implicit_receiver_ok(recv: str, ctx) -> bool:
    if _is_staticmethod_fn(ctx.fn):
        return False
    return _method_receiver_name(ctx.fn) == recv
def _attr_receiver_ok(recv: str, ctx) -> bool:
    if recv in _SELF_CLS_RECEIVERS:
        if not _implicit_receiver_ok(recv, ctx):
            return False
    elif ctx.cls_name and recv == ctx.cls_name:
        if recv in (ctx.params or ()):
            return False
    elif ctx.cls_name and recv == _method_receiver_name(ctx.fn):
        if not _implicit_receiver_ok(recv, ctx):
            return False
    else:
        return False
    if recv in (ctx.fn_vars or {}):
        return False
    return not _attr_receiver_rebound(recv, ctx)
def _attr_expr_sanitized(expr, ctx, depth) -> bool:
    if not isinstance(expr.value, ast.Name):
        return False
    if not _attr_receiver_ok(expr.value.id, ctx):
        return False
    if _ALL_CLASS_ATTRS in ctx.cls_dynamic or expr.attr in ctx.cls_dynamic:
        return False
    exprs = ctx.cls_assigns.get(expr.attr) or ()
    return bool(exprs) and _all_sanitized(exprs, ctx, depth)
_LITERAL_ATOM_FUNCS = frozenset({"repr", "chr"})
def _repr_chr_literal_ok(expr, f, ctx):
    if not (isinstance(f, ast.Name) and f.id in _LITERAL_ATOM_FUNCS):
        return None
    if _builtin_shadowed(f.id, ctx):
        return None
    if f.id == "chr":
        return _is_chr_int_constant(expr)
    return True
def _join_call_sanitized(expr, f, ctx, depth) -> bool:
    return (expr_is_sanitized(f.value, ctx, depth + 1)
            and _list_expr_sanitized(expr.args[0], ctx, depth + 1))
def _replace_call_sanitized(expr, ctx, depth):
    old, new = _replace_old_new_args(expr)
    if old is None or new is None:
        return None
    return (isinstance(old, ast.Constant)
            and expr_is_sanitized(new, ctx, depth + 1)
            and _template_receiver_ok(expr, ctx))
def _attr_call_form_sanitized(expr, f, ctx, depth):
    if f.attr == "join" and expr.args:
        return _join_call_sanitized(expr, f, ctx, depth)
    if f.attr == "replace":
        return _replace_call_sanitized(expr, ctx, depth)
    return None
def _call_expr_sanitized(expr, ctx, depth) -> bool:
    f = expr.func
    if ast_name(f) in ctx.taint_funcs:
        return False
    _rc = _repr_chr_literal_ok(expr, f, ctx)
    if _rc is not None:
        return _rc
    if isinstance(f, ast.Attribute):
        _form = _attr_call_form_sanitized(expr, f, ctx, depth)
        if _form is not None:
            return _form
    return False
def _container_child_parts(expr):
    if isinstance(expr, (ast.List, ast.Tuple, ast.Set)):
        return expr.elts
    if isinstance(expr, ast.Dict):
        return [part for part in (*expr.keys, *expr.values)
                if part is not None]
    if isinstance(expr, ast.JoinedStr):
        return expr.values
    return None
def expr_is_sanitized(expr: ast.AST, ctx, depth=_DEFAULT_DEPTH) -> bool:
    if depth > 8 or expr is None:
        return False
    if isinstance(expr, ast.Constant):
        return True
    _parts = _container_child_parts(expr)
    if _parts is not None:
        return _all_sanitized(_parts, ctx, depth)
    return _leaf_expr_sanitized(expr, ctx, depth)
_LEAF_DISPATCH = {
    ast.FormattedValue: _formatted_value_sanitized,
    ast.Name: _name_expr_sanitized,
    ast.Attribute: _attr_expr_sanitized,
    ast.Call: _call_expr_sanitized,
}
def _leaf_expr_sanitized(expr, ctx, depth):
    if _is_add_binop(expr):
        return _all_sanitized((expr.left, expr.right), ctx, depth)
    if isinstance(expr, ast.IfExp):
        return _all_sanitized((expr.body, expr.orelse), ctx, depth)
    handler = _LEAF_DISPATCH.get(expr.__class__)
    return handler(expr, ctx, depth) if handler is not None else False
def _unavailable_value(node: ast.AST) -> ast.expr:
    return ast.copy_location(ast.Constant(value=None), node)
_TRY_NODES: tuple = tuple(
    _t for _t in (ast.Try, getattr(ast, "TryStar", None))
    if isinstance(_t, type))
def _target_binding_entries(targets, value, line: int):
    for target in targets:
        for name in iter_unpack_target_names(target):
            yield name, value, line, False
def _sequence_unzip_pairs(targets, values):
    starred = [index for index, target in enumerate(targets)
               if isinstance(target, ast.Starred)]
    if not starred:
        return (tuple(zip(targets, values))
                if len(targets) == len(values) else None)
    if len(starred) != 1 or len(values) < len(targets) - 1:
        return None
    index = starred[0]
    tail_count = len(targets) - index - 1
    star_end = len(values) - tail_count
    starred_value = ast.copy_location(ast.List(
        elts=list(values[index:star_end]), ctx=ast.Load()), targets[index])
    return (
        *zip(targets[:index], values[:index]),
        (targets[index], starred_value),
        *zip(targets[index + 1:], values[star_end:]),
    )
def _target_value_pairs(target, value):
    if isinstance(target, ast.Name):
        yield target.id, value
        return
    if isinstance(target, ast.Starred):
        yield from _target_value_pairs(target.value, value)
        return
    if not isinstance(target, (ast.Tuple, ast.List)):
        return
    if isinstance(value, (ast.Tuple, ast.List)):
        pairs = _sequence_unzip_pairs(target.elts, value.elts)
        if pairs is not None:
            for child_target, child_value in pairs:
                yield from _target_value_pairs(child_target, child_value)
            return
    for child in target.elts:
        yield from _target_value_pairs(child, value)
def _iteration_values(value):
    return value.elts if isinstance(value, (ast.List, ast.Tuple, ast.Set)) else (value,)
def _assign_binding_entries(node):
    if node.value is None:
        return
    value = (GLOBAL_REBOUND_MARKER if isinstance(node, ast.AugAssign)
             else node.value)
    yield from _target_binding_entries(
        _assignment_targets(node), value, node.lineno)
def _for_binding_entries(node):
    for value in _iteration_values(node.iter):
        for name, bound_value in _target_value_pairs(node.target, value):
            yield name, bound_value, node.lineno, False
def _with_binding_entries(node):
    for item in node.items:
        if item.optional_vars is not None:
            yield from _target_binding_entries(
                (item.optional_vars,), item.context_expr, node.lineno)
def _try_binding_entries(node):
    for handler in node.handlers:
        if handler.name:
            yield (handler.name, _unavailable_value(handler),
                   handler.lineno, False)
def _definition_binding_entries(node):
    yield node.name, _unavailable_value(node), node.lineno, False
def _delete_binding_entries(node):
    for target in node.targets:
        for name in iter_unpack_target_names(target):
            yield name, _unavailable_value(node), node.lineno, False
def _match_binding_entries(node):
    for name in match_capture_names(node):
        yield name, node.subject, node.lineno, False
_MODULE_BINDING_HANDLERS = {
    ast.Assign: _assign_binding_entries,
    ast.AnnAssign: _assign_binding_entries,
    ast.AugAssign: _assign_binding_entries,
    ast.For: _for_binding_entries,
    ast.AsyncFor: _for_binding_entries,
    ast.With: _with_binding_entries,
    ast.AsyncWith: _with_binding_entries,
    ast.FunctionDef: _definition_binding_entries,
    ast.AsyncFunctionDef: _definition_binding_entries,
    ast.ClassDef: _definition_binding_entries,
    ast.Delete: _delete_binding_entries,
}
for _try_node_type in _TRY_NODES:
    _MODULE_BINDING_HANDLERS[_try_node_type] = _try_binding_entries
def _iter_module_binding_entries(tree: ast.Module):
    for node in iter_module_scope_stmts(tree):
        handler = _MODULE_BINDING_HANDLERS.get(
            node.__class__, _match_binding_entries)
        yield from handler(node)
def _walrus_target_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
        return node.target.id
    return None
def _iter_module_walrus_targets(tree: ast.Module):
    for sub in iter_own_nodes_with_def_sites(tree):
        _name = _walrus_target_name(sub)
        if _name is not None:
            yield _name, sub.value, getattr(sub, "lineno", 0)
def _iter_module_bindings(tree: ast.Module):
    entries = [
        (_line, getattr(_val, "col_offset", -1), _order, _name, _val)
        for _order, (_name, _val, _line, _exempt) in enumerate(
            _iter_module_binding_entries(tree))
    ]
    entries.extend(
        (_line, getattr(_val, "col_offset", -1), len(entries) + _order,
         _name, _val)
        for _order, (_name, _val, _line) in enumerate(
            _iter_module_walrus_targets(tree)))
    entries.sort(key=lambda item: item[:3])
    for _line, _col, _order, _name, _val in entries:
        yield _name, _val
_MODULE_VAR_MAP_MEMO: dict[str, tuple[ast.Module, dict[str, ast.AST]]] = {}
def module_var_map_cached(path: str, tree: ast.Module) -> dict[str, ast.AST]:
    key = os.path.abspath(path)
    hit = memo_hit(_MODULE_VAR_MAP_MEMO, key, tree)
    if hit is not None:
        return hit
    var_map: dict[str, ast.AST] = {}
    for _name, _val in _iter_module_bindings(tree):
        var_map.setdefault(_name, _val)
    memo_store(_MODULE_VAR_MAP_MEMO, key, tree, var_map)
    return var_map
def _module_has_star_import(tree: ast.Module) -> bool:
    return any(
        isinstance(node, ast.ImportFrom)
        and any(alias.name == "*" for alias in node.names)
        for node in iter_module_scope_stmts(tree))
def _module_assign_counts(tree: ast.Module) -> dict[str, int]:
    counts: dict[str, int] = {}
    for _name, _ in _iter_module_bindings(tree):
        counts[_name] = counts.get(_name, 0) + 1
    for node in iter_module_scope_stmts(tree):
        for _name in _import_bound_names(node):
            counts[_name] = counts.get(_name, 0) + 1
    return counts
_MODULE_MULTIASSIGN_MEMO: dict[str, tuple[ast.Module, frozenset]] = {}
def module_multi_assigned_names(path: str, tree: ast.Module) -> frozenset:
    key = os.path.abspath(path)
    hit = memo_hit(_MODULE_MULTIASSIGN_MEMO, key, tree)
    if hit is not None:
        return hit
    counts = _module_assign_counts(tree)
    unreliable = {n for n, c in counts.items() if c > 1}
    if _module_has_star_import(tree):
        unreliable.update(counts)
    unreliable.update(n for n in _global_rebound_names(tree)
                      if counts.get(n, 0) > 0)
    multi = frozenset(unreliable)
    memo_store(_MODULE_MULTIASSIGN_MEMO, key, tree, multi)
    return multi
IMPORTED_NAME_MARKER = ast.Constant(value="__imported_name__")
GLOBAL_REBOUND_MARKER = ast.Constant(value="__global_rebound__")
_MODULE_ASSIGNS_RAW_MEMO: dict[str, tuple[ast.Module, dict]] = {}
def _import_stmt_bound_names(node: ast.Import) -> list[str]:
    return [a.asname or a.name.split(".")[0] for a in node.names]
def _from_import_bound_names(node: ast.ImportFrom) -> list[str]:
    return [a.asname or a.name for a in node.names if a.name != "*"]
def _import_bound_names(node) -> list[str]:
    if isinstance(node, ast.Import):
        return _import_stmt_bound_names(node)
    if isinstance(node, ast.ImportFrom):
        return _from_import_bound_names(node)
    return []
def _register_module_import(node, imports: dict) -> None:
    for name in _import_bound_names(node):
        imports.setdefault(name, []).append(IMPORTED_NAME_MARKER)
def _collect_module_walrus_assigns(tree: ast.Module, assigns: dict) -> None:
    for _name, _val, _line in _iter_module_walrus_targets(tree):
        assigns.setdefault(_name, []).append((_val, _line, True))
def _global_rebound_names(tree: ast.Module) -> set:
    global_names: set[str] = set()
    for _n in walk_nodes(tree):
        if isinstance(_n, ast.Global):
            global_names.update(_n.names)
    return global_names
def _collect_module_assigns(tree: ast.Module) -> dict:
    assigns: dict[str, list] = {}
    imports: dict[str, list] = {}
    for name, value, line, exempt in _iter_module_binding_entries(tree):
        assigns.setdefault(name, []).append((value, line, exempt))
    for node in iter_module_scope_stmts(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _register_module_import(node, imports)
    _collect_module_walrus_assigns(tree, assigns)
    globals_rebound = _global_rebound_names(tree)
    if _module_has_star_import(tree):
        globals_rebound.update(assigns)
    return {"assigns": assigns, "imports": imports,
            "globals_rebound": globals_rebound}
def _module_assigns_raw(path: str, tree: ast.Module) -> dict:
    key = os.path.abspath(path)
    hit = memo_hit(_MODULE_ASSIGNS_RAW_MEMO, key, tree)
    if hit is not None:
        return hit
    raw = _collect_module_assigns(tree)
    memo_store(_MODULE_ASSIGNS_RAW_MEMO, key, tree, raw)
    return raw
def _assigns_outside_fn_range(assigns: dict, fn) -> dict:
    if fn is None:
        return {k: _entry_values(items) for k, items in assigns.items()}
    flo, fhi = _node_span(fn)
    m: dict[str, list] = {}
    for k, items in assigns.items():
        kept = _strip_within_fn_range(items, flo, fhi)
        if kept:
            m[k] = kept
    return m
def _entry_values(items: list) -> list:
    return [entry for entry, _line, _walrus in items]
def _strip_within_fn_range(items: list, flo: int, fhi: int) -> list:
    return [entry for entry, line, is_scope_exempt in items
            if is_scope_exempt or not (flo < line <= fhi)]
def module_assigns_outside(tree: ast.Module, fn, path=None) -> Any:
    raw = (_module_assigns_raw(path, tree) if path is not None
           else _collect_module_assigns(tree))
    m = _assigns_outside_fn_range(raw["assigns"], fn)
    _merge_import_bindings(m, raw["imports"])
    _mark_global_rebinds(m, raw.get("globals_rebound", ()))
    return m
def _merge_import_bindings(target: dict, imports: dict) -> None:
    for name, items in imports.items():
        target.setdefault(name, []).extend(items)
def _mark_global_rebinds(target: dict, rebound_names) -> None:
    for name in rebound_names:
        if name in target:
            target[name].append(GLOBAL_REBOUND_MARKER)
_FUNC_SPAN_MEMO: dict[int, tuple[ast.Module, list]] = {}
def enclosing_function(tree: ast.Module, line) -> Any:
    spans = memo_hit(_FUNC_SPAN_MEMO, id(tree), tree)
    if spans is None:
        spans = memo_store(_FUNC_SPAN_MEMO, id(tree), tree,
                            _function_spans(tree))
    if _inline_def_site_call_conflict(spans, line):
        return None
    return max(
        (node for _lo, _hi, node in spans
         if _line_in_definition_body(node, line)),
        key=lambda node: node.lineno, default=None)
def _node_span(node: ast.AST) -> tuple[int, int]:
    lo = getattr(node, "lineno", 0)
    hi = getattr(node, "end_lineno", lo) or lo
    return lo, hi
def _line_in_span(node: ast.AST, line: int) -> bool:
    lo, hi = _node_span(node)
    return lo <= line <= hi
def _function_spans(tree: ast.Module) -> list:
    return [
        (*_node_span(node), node)
        for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
def _inline_def_site_call_conflict(spans: list, line: int) -> bool:
    for _lo, _hi, node in spans:
        if node.lineno != line or not node.body:
            continue
        if node.body[0].lineno != line:
            continue
        if any(isinstance(call, ast.Call) and call.lineno == line
               for site in fn_def_site_exprs(node)
               for call in walk_nodes(site)):
            return True
    return False
_NESTED_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_COMPREHENSION_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                        ast.GeneratorExp)
def _scope_roots(scope):
    body = getattr(scope, "body", None)
    if isinstance(body, list):
        return list(body)
    return [body] if body is not None else []
def _nested_definition_sites(n):
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return fn_def_site_exprs(n)
    if isinstance(n, ast.ClassDef):
        _sites = [*n.decorator_list, *n.bases, *n.keywords]
        _sites.extend(getattr(n, "type_params", None) or ())
        return _sites
    return None
def iter_own_nodes_with_def_sites(scope: ast.AST) -> Iterator[ast.AST]:
    stack = list(reversed(_scope_roots(scope)))
    while stack:
        n = stack.pop()
        yield n
        _sites = _nested_definition_sites(n)
        if _sites is not None:
            stack.extend(reversed(_sites))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(n))))
def _iter_nested_scopes(scope):
    stack = list(reversed(_scope_roots(scope)))
    while stack:
        n = stack.pop()
        if isinstance(n, _NESTED_SCOPE_TYPES):
            yield n
            continue
        if isinstance(n, ast.ClassDef):
            stack.extend(reversed(list(n.body)))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(n))))
def _declared_names(scope, node_type) -> set:
    return {name for n in iter_own_nodes_with_def_sites(scope)
            if isinstance(n, node_type)
            for name in getattr(n, "names", ())}
def _assign_target_family_names(n: ast.Assign) -> set:
    return set().union(*(iter_unpack_target_names(t) for t in n.targets))
def _with_target_family_names(n) -> set:
    bound = set()
    for item in n.items:
        if item.optional_vars is not None:
            bound.update(iter_unpack_target_names(item.optional_vars))
    return bound
def _node_target_family_names(n):
    for types, extractor in _TARGET_FAMILY_EXTRACTORS:
        if isinstance(n, types):
            return extractor(n)
    return None
def _for_target_names(n) -> set:
    return set(iter_unpack_target_names(n.target))
_TARGET_FAMILY_EXTRACTORS = (
    (ast.Assign, _assign_target_family_names),
    (ast.AnnAssign, annassign_target_names),
    (ast.AugAssign, augassign_target_names),
    ((ast.For, ast.AsyncFor), _for_target_names),
    ((ast.With, ast.AsyncWith), _with_target_family_names),
)
def _node_special_bound_names(n) -> set:
    if isinstance(n, ast.ExceptHandler) and n.name:
        return {n.name}
    if isinstance(n, (ast.Import, ast.ImportFrom)):
        return set(_import_bound_names(n))
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {n.name}
    if isinstance(n, ast.Delete):
        return set().union(*(iter_unpack_target_names(t) for t in n.targets))
    _walrus = _walrus_target_name(n)
    if _walrus is not None:
        return {_walrus}
    return set(match_capture_names(n))
def _node_bound_names(n) -> set:
    _names = _node_target_family_names(n)
    if _names is not None:
        return _names
    return _node_special_bound_names(n)
def _scoped_node_bound_names(scope, n) -> set:
    if (isinstance(n, ast.AnnAssign)
            and isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))):
        return annassign_target_names(n, include_unassigned=True)
    return _node_bound_names(n)
def _binding_names(scope, nonlocals_decl) -> set:
    bound: set = set()
    a = getattr(scope, "args", None)
    if a is not None:
        bound.update(function_param_names(scope))
    for n in iter_own_nodes_with_def_sites(scope):
        bound.update(_scoped_node_bound_names(scope, n))
    return bound - nonlocals_decl
def _single_assign_pair(n):
    _walrus = _walrus_target_name(n)
    if _walrus is not None:
        return _walrus, n.value
    if (isinstance(n, ast.AnnAssign) and n.value is not None
            and isinstance(n.target, ast.Name)):
        return n.target.id, n.value
    return None
def _node_assign_pairs(n):
    if isinstance(n, ast.Assign):
        for target in n.targets:
            yield from _target_value_pairs(target, n.value)
        return
    if isinstance(n, (ast.For, ast.AsyncFor)):
        for value in _iteration_values(n.iter):
            yield from _target_value_pairs(n.target, value)
        return
    _pair = _single_assign_pair(n)
    if _pair is not None:
        yield _pair
def _assign_pairs(scope):
    for n in iter_own_nodes_with_def_sites(scope):
        yield from _node_assign_pairs(n)
def _visit_scope_assigns(scope, resolves, m: dict) -> None:
    _globals_d = _declared_names(scope, ast.Global)
    _nonlocals_d = _declared_names(scope, ast.Nonlocal)
    _local_binds = _binding_names(scope, _nonlocals_d) - _globals_d
    _collect = (None if resolves is None
                else _nonlocals_d & resolves)
    _visible = (set() if resolves is None else resolves - _local_binds)
    _local_aliases: set[str] = set()
    for _name, _val in _assign_pairs(scope):
        _collect_this = _collects_assignment(
            _name, _collect, _globals_d, _nonlocals_d)
        if (resolves is not None and not _collect_this
                and (_name in _local_aliases
                     or _expr_may_alias(_val, _visible))):
            _local_aliases.add(_name)
            _visible.add(_name)
            _collect_this = True
        if _collect_this:
            m.setdefault(_name, []).append(_val)
    _child = (_local_binds if resolves is None
              else (resolves - _local_binds) | _local_aliases)
    for nested in _iter_nested_scopes(scope):
        _visit_scope_assigns(nested, _child, m)
def _collects_assignment(name: str, collect: set | None,
                         globals_decl: set, nonlocals_decl: set) -> bool:
    if collect is None:
        return name not in globals_decl and name not in nonlocals_decl
    return name in collect
def function_var_exprs(fn: ast.AST) -> Any:
    m: dict[str, list] = {}
    _visit_scope_assigns(fn, None, m)
    return m
def scope_bound_names(scope) -> frozenset[str]:
    _nonlocals = _declared_names(scope, ast.Nonlocal)
    _globals = _declared_names(scope, ast.Global)
    return frozenset(_binding_names(scope, _nonlocals) - _globals)
def _unmodeled_binding_names(scope) -> set:
    names: set = set()
    append_targets: set = set()
    modeled: set = set()
    if getattr(scope, "args", None) is not None:
        names.update(function_param_names(scope))
    for _n in iter_own_nodes_with_def_sites(scope):
        _bound = _scoped_node_bound_names(scope, _n)
        if not _bound:
            continue
        _modeled = {name for name, _expr in _node_assign_pairs(_n)}
        modeled |= _modeled
        if (isinstance(_n, ast.AugAssign) and isinstance(_n.op, ast.Add)
                and isinstance(_n.target, ast.Name)):
            append_targets |= _bound
            continue
        names |= _bound - _modeled
    names |= append_targets - modeled
    return names - _declared_names(scope, ast.Nonlocal)
def function_unmodeled_binding_names(fn) -> frozenset[str]:
    return frozenset(_unmodeled_binding_names(fn)
                     - _declared_names(fn, ast.Global))
def function_rebound_param_names(fn) -> frozenset[str]:
    params = frozenset(function_param_names(fn))
    if not params:
        return frozenset()
    rebound: set = set()
    for _n in iter_own_nodes_with_def_sites(fn):
        rebound |= _scoped_node_bound_names(fn, _n)
    rebound -= _declared_names(fn, ast.Nonlocal)
    return frozenset(rebound & params)
def enclosing_function_bound_names(tree: ast.Module, fn) -> frozenset[str]:
    if fn is None:
        return frozenset()
    flo, fhi = _node_span(fn)
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, _NESTED_SCOPE_TYPES) or node is fn:
            continue
        lo, hi = _node_span(node)
        if lo <= flo and fhi <= hi:
            names |= scope_bound_names(node)
    return frozenset(names)
def lambda_own_walrus_targets(node) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    _todo: deque = deque([node.body])
    while _todo:
        cur = _todo.popleft()
        if isinstance(cur, ast.Lambda):
            _todo.extend(fn_def_site_exprs(cur))
            continue
        _name = _walrus_target_name(cur)
        if _name is not None and _name not in seen:
            seen.add(_name)
            out.append(_name)
        _todo.extend(ast.iter_child_nodes(cur))
    return out
def nested_scope_node_bound_names(node) -> list[str]:
    if isinstance(node, ast.Lambda):
        return [*function_param_names(node),
                *lambda_own_walrus_targets(node)]
    if isinstance(node, _COMPREHENSION_TYPES):
        return [name
                for _gen in node.generators
                for name in iter_unpack_target_names(_gen.target)]
    if isinstance(node, ast.ClassDef):
        return sorted(scope_bound_names(node))
    return []
def _line_in_definition_body(node, line: int) -> bool:
    body = getattr(node, "body", None)
    if isinstance(body, list):
        if not body:
            return False
        return _node_span(body[0])[0] <= line <= _node_span(body[-1])[1]
    return body is not None and _line_in_span(body, line)
def _line_in_class_execution(cls: ast.ClassDef, line: int) -> bool:
    for node in walk_nodes(cls):
        if node is cls:
            continue
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda, ast.ClassDef))
                and _line_in_definition_body(node, line)):
            return False
    return True
def nested_scope_bound_names(tree, line) -> list[str]:
    return list(dict.fromkeys(
        name
        for node in walk_nodes(tree)
        if isinstance(node, _SCOPE_NODE_TYPES)
        and _line_in_span(node, line)
        and (not isinstance(node, ast.ClassDef)
             or _line_in_class_execution(node, line))
        for name in nested_scope_node_bound_names(node)))
def _owning_class(tree: ast.Module, fn: ast.AST) -> ast.ClassDef | None:
    fn_id = id(fn)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ClassDef) and any(
                id(stmt) == fn_id for stmt in node.body
                if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)))):
            return node
    return None
def _assignment_targets(node: ast.AST) -> list[ast.expr]:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    if isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        return [node.target]
    return []
def _is_receiver_call(node, name: str, receivers) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name) and node.func.id == name
            and len(node.args) == 1 and not node.keywords
            and isinstance(node.args[0], ast.Name)
            and node.args[0].id in receivers)
def _self_cls_attr_root(target: ast.expr, receivers=None) -> str | None:
    _receivers = _SELF_CLS_RECEIVERS if receivers is None else receivers
    node = target
    while isinstance(node, (ast.Subscript, ast.Attribute, ast.Call)):
        if isinstance(node, ast.Call):
            if _is_receiver_call(node, "vars", _receivers):
                return "__dict__"
            if _is_receiver_call(node, "type", _receivers):
                return "__class__"
            if (isinstance(node.func, ast.Name)
                    and node.func.id == "getattr"
                    and not node.keywords and 2 <= len(node.args) <= 3
                    and isinstance(node.args[0], ast.Name)
                    and node.args[0].id in _receivers):
                return _attr_write_name(node.args[1])
            return None
        if isinstance(node, ast.Attribute):
            base = node.value
            if isinstance(base, ast.Name) and base.id in _receivers:
                return "__class__" if node.attr == "__class__" else node.attr
            node = base
            continue
        node = node.value
    return None
def _mutation_targets(node: ast.AST) -> list[ast.expr]:
    if isinstance(node, ast.Delete):
        return list(node.targets)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    if isinstance(node, ast.NamedExpr):
        return [node.target]
    return _assignment_targets(node)
_CONTAINER_MUTATE_ATTRS = _VALUE_MUTATING_ATTRS | frozenset({
    "pop", "remove", "clear", "sort", "reverse", "__delitem__",
    "__imul__", "__iand__", "__isub__"})
def _mut_call_receiver_root(node) -> ast.expr | None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _CONTAINER_MUTATE_ATTRS):
        return None
    return node.func.value
def _self_cls_mut_call_root(node, receivers=None) -> str | None:
    recv = _mut_call_receiver_root(node)
    if recv is None:
        return None
    return _self_cls_attr_root(recv, receivers)
def _plain_mut_call_root(node) -> str | None:
    if isinstance(node, ast.Expr):
        node = node.value
    recv = _mut_call_receiver_root(node)
    if recv is None:
        return None
    if isinstance(recv, ast.Name):
        return recv.id
    root = _self_cls_attr_root(recv)
    if root is not None:
        return root
    root_node = recv
    while isinstance(root_node, (ast.Subscript, ast.Attribute)):
        root_node = root_node.value
    return root_node.id if isinstance(root_node, ast.Name) else None
def _attr_write_name(attr_expr) -> str:
    if isinstance(attr_expr, ast.Constant) and isinstance(attr_expr.value, str):
        return attr_expr.value
    return _ALL_CLASS_ATTRS
def _is_super_call(expr) -> bool:
    return (isinstance(expr, ast.Call)
            and isinstance(expr.func, ast.Name) and expr.func.id == "super"
            and not expr.args and not expr.keywords)
def _dynamic_attr_receiver_root(receiver, receivers) -> str | None:
    if isinstance(receiver, ast.Name):
        return receiver.id if receiver.id in receivers else None
    root = _self_cls_attr_root(receiver, receivers)
    return root if root in ("__dict__", "__class__") else None
def _dynamic_attr_write(node, receivers) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    attr_expr = None
    receiver = None
    if isinstance(func, ast.Name) and func.id in {"setattr", "delattr"}:
        receiver = node.args[0] if node.args else _keyword_arg(node, "obj")
        attr_expr = (node.args[1] if len(node.args) > 1
                     else _keyword_arg(node, "name"))
    elif (isinstance(func, ast.Attribute)
          and func.attr in {"__setattr__", "__delattr__"}):
        if _is_super_call(func.value):
            return _attr_write_name(
                node.args[0] if node.args else _keyword_arg(node, "name"))
        if _dynamic_attr_receiver_root(func.value, receivers) is not None:
            receiver = func.value
            attr_expr = (node.args[0] if node.args
                         else _keyword_arg(node, "name"))
        elif node.args:
            receiver = node.args[0]
            attr_expr = (node.args[1] if len(node.args) > 1
                         else _keyword_arg(node, "name"))
    if _dynamic_attr_receiver_root(receiver, receivers) is None:
        return None
    return _attr_write_name(attr_expr)
def _method_attr_alias_bindings(method, receivers) -> tuple[dict, set[str]]:
    bindings: dict[str, list] = {}
    attr_roots: set[str] = set()
    for name, exprs in function_var_exprs(method).items():
        values = list(exprs)
        for expr in exprs:
            expr_roots = {
                root for node in walk_nodes(expr)
                if (root := _self_cls_attr_root(node, receivers)) is not None}
            values.extend(ast.Name(id=root, ctx=ast.Load())
                          for root in expr_roots)
            attr_roots.update(expr_roots)
        bindings[name] = values
    return bindings, attr_roots
def _method_mutated_names(method) -> set[str]:
    mutated: set[str] = set()
    for node in walk_nodes(method):
        root = _plain_mut_call_root(node)
        if root is not None:
            mutated.add(root)
        if (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)
                and isinstance(node.target, ast.Name)):
            mutated.add(node.target.id)
        for target in _mutation_targets(node):
            mutated.update(_subscript_mutation_root_names(target))
    return mutated
def _method_attr_bindings(method: ast.AST, receivers) -> set[str]:
    bound: set[str] = set()
    for node in walk_nodes(method):
        roots = [_self_cls_attr_root(target, receivers)
                 for target in _mutation_targets(node)]
        roots.extend((_self_cls_mut_call_root(node, receivers),
                      _dynamic_attr_write(node, receivers)))
        for root in roots:
            if root is not None:
                bound.add(_ALL_CLASS_ATTRS
                          if root in ("__dict__", "__class__") else root)
    alias_bindings, attr_roots = _method_attr_alias_bindings(method, receivers)
    if attr_roots:
        mutated = _method_mutated_names(method)
        for root in attr_roots:
            if mutation_alias_closure(root, alias_bindings) & mutated:
                bound.add(_ALL_CLASS_ATTRS
                          if root in ("__dict__", "__class__") else root)
    return bound
def _method_class_receivers(cls: ast.ClassDef, method) -> frozenset:
    receivers: set[str] = set()
    if not _is_staticmethod_fn(method):
        _receiver = _method_receiver_name(method)
        if _receiver is not None:
            receivers.add(_receiver)
    if cls.name not in scope_bound_names(method):
        receivers.add(cls.name)
    return frozenset(receivers)
def _class_method_bound_attrs(cls: ast.ClassDef) -> set[str]:
    bound: set[str] = set()
    for stmt in cls.body:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            bound |= _method_attr_bindings(
                stmt, _method_class_receivers(cls, stmt))
    return bound
_STORE_NAME = "name"
_STORE_UNPACK = "unpack"
_STORE_CONTAINER = "container"
_STORE_AUGMENTED = "augmented"
def _store_target_roots(target: ast.expr) -> list[tuple[str, str]]:
    if isinstance(target, ast.Name):
        return [(target.id, _STORE_NAME)]
    if isinstance(target, (ast.Tuple, ast.List)):
        return [(name, _STORE_UNPACK)
                for elt in target.elts
                for name, _kind in _store_target_roots(elt)]
    if isinstance(target, ast.Starred):
        return [(name, _STORE_UNPACK)
                for name, _kind in _store_target_roots(target.value)]
    node = target
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        node = node.value
    return [(node.id, _STORE_CONTAINER)] if isinstance(node, ast.Name) else []
def _class_body_store_pairs(cls: ast.ClassDef):
    for stmt in iter_own_nodes_with_def_sites(cls):
        value = getattr(stmt, "value", None)
        if value is None:
            continue
        _force_kind = (_STORE_AUGMENTED
                       if isinstance(stmt, ast.AugAssign) else None)
        for target in _assignment_targets(stmt):
            for name, kind in _store_target_roots(target):
                yield name, value, _force_kind or kind
def _class_body_name_assigns(cls: ast.ClassDef) -> dict[str, list[ast.expr]]:
    table: dict[str, list[ast.expr]] = {}
    for name, value, kind in _class_body_store_pairs(cls):
        if kind == _STORE_NAME:
            table.setdefault(name, []).append(value)
    return table
def _class_body_unstable_names(cls: ast.ClassDef) -> set[str]:
    names: set[str] = set()
    for stmt in iter_own_nodes_with_def_sites(cls):
        if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            _augmented = isinstance(stmt, ast.AugAssign)
            for target in _assignment_targets(stmt):
                names.update(
                    name for name, kind in _store_target_roots(target)
                    if _augmented or kind != _STORE_NAME)
            continue
        if isinstance(stmt, ast.Delete):
            for target in stmt.targets:
                names.update(name for name, _kind in _store_target_roots(target))
            continue
        names.update(_node_bound_names(stmt))
        _mut_root = _plain_mut_call_root(stmt)
        if _mut_root is not None:
            names.add(_ALL_CLASS_ATTRS
                      if _mut_root in ("__dict__", "__class__") else _mut_root)
    return names
def enclosing_class_dynamic_attrs(tree: ast.Module, fn: ast.AST) -> frozenset:
    cls = _owning_class(tree, fn)
    if cls is None:
        return frozenset()
    return frozenset(_class_method_bound_attrs(cls)
                     | _class_body_unstable_names(cls))
def enclosing_class_assigns(
    tree: ast.Module, fn: ast.AST,
) -> tuple[dict[str, list[ast.expr]], str]:
    cls = _owning_class(tree, fn)
    if cls is None:
        return {}, ""
    return _class_body_name_assigns(cls), cls.name
def clear_e2_scope_memos() -> int:
    n = memo_clear(_FUNC_SPAN_MEMO, _MODULE_VAR_MAP_MEMO,
                   _MODULE_MULTIASSIGN_MEMO, _MODULE_ASSIGNS_RAW_MEMO)
    return n + clear_call_scan_memos() + clear_flow_memos()

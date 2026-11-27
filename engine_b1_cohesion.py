from __future__ import annotations

import argparse
import ast
import json
import os
from collections import Counter, defaultdict, deque
from collections.abc import Iterator
from pathlib import Path
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_bindings import ScopeNameResolver, import_stmt_binds
from jwsgj.diag_shared_ast_nodes import is_dunder_name, main_guard_branch
from jwsgj.diag_shared_ast_surface import (
    collect_module_exports_state,
    is_all_assignment,
)
from jwsgj.diag_shared_ast_views import (
    parent_map,
    same_scope_dfs_nodes,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import count_lines
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    TEST_ARTIFACT_DIRS,
    is_pruned_scan_dir,
    is_scan_py_name,
    tarjan_scc,
)
from jwsgj.shared_cache import SharedCache, load_module_source

logger = get_module_logger(__name__, __file__)
__all__ = [
    "COHESION_RULE_IDS",
    "COHESION_RULE_META",
    "DEFAULT_MIN_LARGE_LINES",
    "CohesionAnalyzer",
    "ModuleInfo",
    "load_modules",
    "main",
    "render_markdown",
    "result_to_b1_findings",
    "scan_independent_blocks",
]
class _CohesionRuleMeta(NamedTuple):
    family: str
    severity: str
    confidence: float
    pattern_name: str
    switch: str
COHESION_RULE_META: dict[str, _CohesionRuleMeta] = {
    "CH01-HARD-CYCLE": _CohesionRuleMeta(
        "cohesion_cycle", "P1", 0.9, "hard_cycle", "hard"),
    "CH02-SOFT-CYCLE": _CohesionRuleMeta(
        "cohesion_cycle", "P3", 0.7, "soft_cycle", "soft"),
    "CH03-MISPLACED-SYMBOL": _CohesionRuleMeta(
        "cohesion_migration", "P3", 0.6, "misplaced_symbol", "migrate"),
    "CH04-MERGE-CANDIDATE": _CohesionRuleMeta(
        "cohesion_migration", "P3", 0.5, "merge_candidate", "merge"),
    "CH05-SPLIT-CANDIDATE": _CohesionRuleMeta(
        "cohesion_split", "P2", 0.75, "governance_candidate", "blocks"),
}
COHESION_RULE_IDS = frozenset(COHESION_RULE_META)
DEFAULT_MIN_LARGE_LINES = 3000
def _coerce_directory(directory) -> str:
    if directory is None or isinstance(directory, bool):
        return ""
    if not isinstance(directory, (str, bytes, os.PathLike)):
        return ""
    try:
        raw = os.fsdecode(os.fspath(directory)).strip()
    except (TypeError, ValueError, OSError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_coerce_directory:{type(_e).__name__}')
        return ""
    return os.path.abspath(raw) if raw else ""
def _coerce_min_lines(value) -> int:
    if value is None:
        return DEFAULT_MIN_LARGE_LINES
    if isinstance(value, bool):
        logger.warning("[Cohesion] min_large_lines 为布尔值，回落默认阈值: %r", value)
        return DEFAULT_MIN_LARGE_LINES
    if isinstance(value, float):
        if not value > 0:
            logger.warning("[Cohesion] min_large_lines 非法，回落默认阈值: %r", value)
            return DEFAULT_MIN_LARGE_LINES
        try:
            parsed = int(value)
        except (OverflowError, ValueError):
            logger.warning("[Cohesion] min_large_lines 非有限数，回落默认阈值: %r", value)
            return DEFAULT_MIN_LARGE_LINES
        return _coerce_min_lines(parsed)
    if isinstance(value, int):
        if value <= 0:
            logger.warning("[Cohesion] min_large_lines 非正，回落默认阈值: %r", value)
            return DEFAULT_MIN_LARGE_LINES
        return value
    if isinstance(value, str):
        try:
            parsed = int(value.strip())
        except ValueError:
            logger.warning("[Cohesion] min_large_lines 非数值，回落默认阈值: %r", value)
            return DEFAULT_MIN_LARGE_LINES
        return _coerce_min_lines(parsed)
    logger.warning("[Cohesion] min_large_lines 类型不支持，回落默认阈值: %r", value)
    return DEFAULT_MIN_LARGE_LINES
def _coerce_rule_set(active_rules) -> frozenset[str] | None:
    if active_rules is None:
        return None
    if isinstance(active_rules, str):
        return frozenset({active_rules})
    try:
        items = list(active_rules)
    except TypeError as _e:
        log_swallowed(__name__, _e,
                      context=f'_coerce_rule_set:{type(_e).__name__}')
        logger.warning("[Cohesion] active_rules 不可迭代，按全量规则分析: %r",
                       active_rules)
        return None
    return frozenset(item for item in items
                     if isinstance(item, str) and item)
def _last_dotted_segment(name: str) -> str:
    return name.rsplit(".", 1)[-1]
def _assign_target_names(target: ast.expr) -> list[ast.Name]:
    if isinstance(target, ast.Name):
        return [target]
    if isinstance(target, (ast.Tuple, ast.List)):
        out: list[ast.Name] = []
        for el in target.elts:
            out.extend(_assign_target_names(el))
        return out
    if isinstance(target, ast.Starred):
        return _assign_target_names(target.value)
    return []
def _assign_def_entries(node: ast.Assign) -> list[tuple[str, int, int]]:
    entries: list[tuple[str, int, int]] = []
    for t in node.targets:
        for nm in _assign_target_names(t):
            entries.append((nm.id, node.lineno, node.end_lineno))
    return entries
def _is_type_checking_test(test: ast.expr) -> bool:
    if isinstance(test, ast.Name):
        return test.id == "TYPE_CHECKING"
    if (isinstance(test, ast.Attribute)
            and isinstance(test.value, ast.Name)):
        return test.value.id == "typing" and test.attr == "TYPE_CHECKING"
    return False
def _type_checking_body_visible(test: ast.expr) -> bool | None:
    if _is_type_checking_test(test):
        return False
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        inner = _type_checking_body_visible(test.operand)
        return None if inner is None else not inner
    return None
def _module_level_body_visible(test: ast.expr) -> bool | None:
    type_checking = _type_checking_body_visible(test)
    if type_checking is not None:
        return type_checking
    negated = (isinstance(test, ast.UnaryOp)
               and isinstance(test.op, ast.Not))
    if negated:
        test = test.operand
    if isinstance(test, ast.Constant):
        condition = bool(test.value)
    else:
        main_branch = main_guard_branch(test)
        if main_branch is None:
            return None
        condition = not main_branch
    return not condition if negated else condition
def _plain_import_target(module_path: str,
                         pkg_name: str | None, *,
                         relative: bool = False) -> str | None:
    parts = [p for p in str(module_path or "").split(".") if p]
    if not parts:
        return None
    if relative:
        return parts[-1]
    pkg_parts = [p for p in str(pkg_name or "").split(".") if p]
    if not pkg_parts:
        return parts[0] if len(parts) == 1 else None
    if len(parts) > 1 and parts[0] == pkg_parts[0]:
        return parts[-1]
    return None
def _package_import_container(module_path: str,
                              pkg_name: str | None) -> bool:
    module_parts = [p for p in str(module_path or "").split(".") if p]
    pkg_parts = [p for p in str(pkg_name or "").split(".") if p]
    return bool(
        module_parts and pkg_parts
        and len(module_parts) <= len(pkg_parts)
        and pkg_parts[:len(module_parts)] == module_parts)
def _from_import_source_path(stmt: ast.ImportFrom,
                             pkg_name: str | None) -> str:
    module_parts = [p for p in str(stmt.module or "").split(".") if p]
    if not stmt.level:
        return ".".join(module_parts)
    pkg_parts = [p for p in str(pkg_name or "").split(".") if p]
    package_len = len(pkg_parts) - stmt.level + 1
    if package_len < 0:
        return ""
    return ".".join([*pkg_parts[:package_len], *module_parts])
def _from_import_package_container(stmt: ast.ImportFrom,
                                   pkg_name: str | None) -> bool:
    return _package_import_container(
        _from_import_source_path(stmt, pkg_name), pkg_name)
def _package_depth(pkg_name: str | None) -> int:
    return len([p for p in str(pkg_name or "").split(".") if p])
def _from_import_in_scope(stmt: ast.ImportFrom,
                          pkg_name: str | None) -> bool:
    if stmt.level:
        return stmt.level <= _package_depth(pkg_name)
    if _package_import_container(stmt.module, pkg_name):
        return True
    return _plain_import_target(stmt.module, pkg_name) is not None
def _import_names_target(module_path: str, self_name: str,
                         pkg_name: str | None, *,
                         relative: bool = False) -> bool:
    return (_plain_import_target(
        module_path, pkg_name, relative=relative) == self_name)
def _module_name_import_binds(
        names: list[ast.alias]) -> Iterator[tuple[str, str]]:
    for a in names:
        if a.name == "*":
            continue
        seg = _last_dotted_segment(a.name)
        yield a.asname or seg, seg
def _collect_submodule_targets(stmt: ast.ImportFrom,
                               top_from_mods: set[str]) -> None:
    for _bind, _seg in _module_name_import_binds(stmt.names):
        top_from_mods.add(_seg)
def _collect_plain_import_targets(stmt: ast.Import, top_from_mods: set[str],
                                  pkg_name: str | None) -> None:
    for a in stmt.names:
        seg = _plain_import_target(a.name, pkg_name)
        if seg is not None:
            top_from_mods.add(seg)
def _symbol_import_entries(stmt: ast.ImportFrom,
                           pkg_name: str | None) -> Iterator[tuple[str, str]]:
    if not _from_import_in_scope(stmt, pkg_name) or not stmt.module:
        return
    if _from_import_package_container(stmt, pkg_name):
        return
    modname = _last_dotted_segment(stmt.module)
    for a in stmt.names:
        if a.name != "*":
            yield a.name, modname
def _collect_import_from(stmt: ast.ImportFrom, top_from_mods: set[str],
                         symbol_imports: set[tuple[str, str]],
                         pkg_name: str | None) -> None:
    if not _from_import_in_scope(stmt, pkg_name):
        return
    if _from_import_package_container(stmt, pkg_name):
        _collect_submodule_targets(stmt, top_from_mods)
        return
    if stmt.module:
        top_from_mods.add(_last_dotted_segment(stmt.module))
        symbol_imports.update(_symbol_import_entries(stmt, pkg_name))
        return
    _collect_submodule_targets(stmt, top_from_mods)
def _collect_import_info(stmts: list[ast.stmt], top_from_mods: set[str],
                         symbol_imports: set[tuple[str, str]],
                         pkg_name: str | None) -> None:
    for stmt in _iter_module_level_stmts(stmts):
        if isinstance(stmt, ast.ClassDef):
            _collect_import_info(stmt.body, top_from_mods, symbol_imports,
                                 pkg_name=pkg_name)
            continue
        if isinstance(stmt, ast.ImportFrom):
            _collect_import_from(stmt, top_from_mods, symbol_imports, pkg_name)
            continue
        if isinstance(stmt, ast.Import):
            _collect_plain_import_targets(stmt, top_from_mods, pkg_name)
def _stmt_self_import(stmt: ast.AST, self_name: str,
                      pkg_name: str | None) -> bool:
    if isinstance(stmt, ast.Import):
        return any(_import_names_target(a.name, self_name, pkg_name)
                   for a in stmt.names)
    if isinstance(stmt, ast.ImportFrom):
        if not _from_import_in_scope(stmt, pkg_name):
            return False
        if stmt.module and _import_names_target(
                stmt.module, self_name, pkg_name, relative=bool(stmt.level)):
            return True
        return (_from_import_package_container(stmt, pkg_name)
                and any(a.name == self_name for a in stmt.names))
    return False
def _collect_self_import(stmts: list[ast.stmt], self_name: str,
                         pkg_name: str | None) -> bool:
    for stmt in _iter_module_level_stmts(stmts):
        if isinstance(stmt, ast.ClassDef):
            if _collect_self_import(stmt.body, self_name, pkg_name):
                return True
            continue
        if _stmt_self_import(stmt, self_name, pkg_name):
            return True
    return False
def _submodule_lazy_targets(stmt: ast.ImportFrom,
                            self_name: str) -> Iterator[str]:
    for _bind, _tgt in _module_name_import_binds(stmt.names):
        if _tgt != self_name:
            yield _tgt
def _lazy_import_edge_targets(node: ast.AST, self_name: str,
                              pkg_name: str | None) -> Iterator[str]:
    if isinstance(node, ast.ImportFrom):
        yield from _from_import_targets(node, self_name, pkg_name)
    elif isinstance(node, ast.Import):
        yield from _plain_import_targets(node, self_name, pkg_name)
def _from_import_targets(node: ast.ImportFrom, self_name: str,
                         pkg_name: str | None) -> Iterator[str]:
    if not _from_import_in_scope(node, pkg_name):
        return
    if _from_import_package_container(node, pkg_name):
        yield from _submodule_lazy_targets(node, self_name)
        return
    tgt = _last_dotted_segment(node.module)
    if tgt != self_name:
        yield tgt
def _plain_import_targets(node: ast.Import, self_name: str,
                          pkg_name: str | None) -> Iterator[str]:
    for a in node.names:
        tgt = _plain_import_target(a.name, pkg_name)
        if tgt is not None and tgt != self_name:
            yield tgt
_TRY_STMT_TYPES: tuple[type, ...] = (
    ast.Try, getattr(ast, "TryStar", ast.Try))
_WITH_STMT_TYPES: tuple[type, ...] = (ast.With, ast.AsyncWith)
_MATCH_STMT_TYPES: tuple[type, ...] = (
    (ast.Match,) if hasattr(ast, "Match") else ())
def _module_level_children(stmt: ast.stmt) -> list[ast.stmt]:
    if isinstance(stmt, ast.If):
        return _if_children(stmt)
    for _types, _extract in _COMPOUND_CHILD_EXTRACTORS:
        if isinstance(stmt, _types):
            return _extract(stmt)
    return []
def _if_children(stmt: ast.If) -> list[ast.stmt]:
    body_visible = _module_level_body_visible(stmt.test)
    if body_visible is not None:
        return list(stmt.body if body_visible else stmt.orelse)
    return [*stmt.body, *stmt.orelse]
def _match_case_children(stmt: ast.stmt) -> list[ast.stmt]:
    return [_b for _c in stmt.cases for _b in _c.body]
def _try_stmt_children(stmt: ast.stmt) -> list[ast.stmt]:
    children = [*stmt.body, *stmt.orelse, *stmt.finalbody]
    for _h in stmt.handlers:
        children.extend(_h.body)
    return children
def _with_stmt_children(stmt: ast.stmt) -> list[ast.stmt]:
    return list(stmt.body)
def _loop_stmt_children(stmt: ast.stmt) -> list[ast.stmt]:
    return [*stmt.body, *stmt.orelse]
_COMPOUND_CHILD_EXTRACTORS: tuple[tuple[tuple[type, ...], object], ...] = (
    (_MATCH_STMT_TYPES, _match_case_children),
    (_TRY_STMT_TYPES, _try_stmt_children),
    (_WITH_STMT_TYPES, _with_stmt_children),
    ((ast.For, ast.While), _loop_stmt_children),
)
def _iter_module_level_stmts(stmts: list[ast.stmt]) -> Iterator[ast.stmt]:
    queue: deque[ast.stmt] = deque(stmts)
    while queue:
        stmt = queue.popleft()
        yield stmt
        queue.extend(_module_level_children(stmt))
def _collect_top_level_defs(tree: ast.Module) -> list[tuple[str, int, int]]:
    entries = [entry for node in _iter_module_level_stmts(tree.body)
               for entry in _stmt_def_entries(node)]
    entries.sort(key=lambda entry: (entry[1], entry[0]))
    unique: dict[str, tuple[str, int, int]] = {}
    for entry in entries:
        unique.setdefault(entry[0], entry)
    return list(unique.values())
_TYPE_ALIAS_TYPES = (ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ()
def _stmt_def_entries(node: ast.stmt) -> list[tuple[str, int, int]]:
    entry = _definition_entry(node)
    if entry is not None:
        return [entry]
    if isinstance(node, _TYPE_ALIAS_TYPES):
        return [(node.name.id, node.lineno, node.end_lineno)]
    if isinstance(node, ast.Assign):
        return _assign_def_entries(node)
    if (isinstance(node, ast.AnnAssign)
            and node.value is not None
            and isinstance(node.target, ast.Name)):
        return [(node.target.id, node.lineno, node.end_lineno)]
    return []
def _definition_entry(node: ast.stmt) -> tuple[str, int, int] | None:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
        return None
    start = min([node.lineno, *(dec.lineno for dec in node.decorator_list)])
    return node.name, start, node.end_lineno
_MATCH_BIND_TYPES: tuple[type, ...] = tuple(
    _t for _t in (getattr(ast, "MatchAs", None),
                  getattr(ast, "MatchStar", None),
                  getattr(ast, "MatchMapping", None))
    if _t is not None)
_MATCH_MAPPING_TYPES: tuple[type, ...] = (
    (ast.MatchMapping,) if hasattr(ast, "MatchMapping") else ())
def _fn_binds_args(args: ast.arguments) -> set[str]:
    binds: set[str] = set()
    for arg in list(args.posonlyargs) + list(args.args) + list(args.kwonlyargs):
        binds.add(arg.arg)
    if args.vararg is not None:
        binds.add(args.vararg.arg)
    if args.kwarg is not None:
        binds.add(args.kwarg.arg)
    return binds
def _match_bind_name(n: ast.AST) -> str | None:
    _nm = n.rest if isinstance(n, _MATCH_MAPPING_TYPES) else n.name
    return _nm or None
def _is_comp_target(n: ast.Name, pm: dict) -> bool:
    _t = n
    _p = pm.get(_t)
    while isinstance(_p, (ast.Tuple, ast.List, ast.Starred)):
        _t = _p
        _p = pm.get(_t)
    return isinstance(_p, ast.comprehension) and _p.target is _t
def _binds_of_definition(n: ast.AST) -> set[str]:
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {n.name}
    if isinstance(n, ast.Nonlocal):
        return set(n.names)
    if isinstance(n, (ast.Import, ast.ImportFrom)):
        return import_stmt_binds(n)
    if isinstance(n, (ast.ExceptHandler, *_MATCH_BIND_TYPES)):
        return set(filter(None, (_optional_bind_name(n),)))
    return set()
def _optional_bind_name(n: ast.AST) -> str | None:
    if isinstance(n, ast.ExceptHandler):
        return n.name
    return _match_bind_name(n)
def _fn_scope_binds(fn: ast.AST, pm: dict) -> set[str]:
    binds: set[str] = _fn_binds_args(fn.args)
    globals_declared: set[str] = set()
    for n in same_scope_dfs_nodes(fn):
        if isinstance(n, ast.Global):
            globals_declared.update(n.names)
            continue
        if _is_local_binding_name(n, pm):
            binds.add(n.id)
            continue
        binds.update(_binds_of_definition(n))
    return binds - globals_declared
def _binding_first_lines(scope: ast.AST, pm: dict) -> dict[str, int]:
    lines: dict[str, int] = {}
    globals_declared: set[str] = set()
    for n in same_scope_dfs_nodes(scope):
        if isinstance(n, ast.Global):
            globals_declared.update(n.names)
            continue
        if _is_local_binding_name(n, pm):
            if _is_annotation_only_target(n, pm):
                # 类/模块作用域下 `x: int` 不绑定名字（只写 __annotations__），
                # 不能据此判定后续同名引用被遮蔽。
                continue
            names, line = (n.id,), n.lineno
        else:
            names, line = _binds_of_definition(n), getattr(n, "lineno", 0)
        for name in names:
            if name and (name not in lines or line < lines[name]):
                lines[name] = line
    return {name: line for name, line in lines.items()
            if name not in globals_declared}
def _is_local_binding_name(n: ast.AST, pm: dict) -> bool:
    return (isinstance(n, ast.Name) and not isinstance(n.ctx, ast.Load)
            and not _is_comp_target(n, pm))


def _is_annotation_only_target(n: ast.AST, pm: dict) -> bool:
    """判断 ``n`` 是否为「仅注解」赋值的目标。

    ``x: int``（无 value）在函数作用域会让 ``x`` 成为局部名，但在类体和模块
    作用域不会绑定该名字（只写 ``__annotations__``），因此不能当作类属性/
    模块状态绑定。
    """
    if not isinstance(n, ast.Name) or not isinstance(n.ctx, ast.Store):
        return False
    parent = pm.get(n)
    return (isinstance(parent, ast.AnnAssign)
            and parent.target is n and parent.value is None)
_FUNC_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_COMP_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_SCOPE_RESOLVER_KEY = "scope_name_resolver"
_SourcePosition = tuple[int, int]
_ImportEntry = tuple[_SourcePosition, str, bool]
_ScopedImports = dict[ast.AST, dict[str, set[_ImportEntry]]]
def _source_position(node: ast.AST) -> _SourcePosition:
    return (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
def _inside_function_scope(node: ast.AST, pm: dict) -> bool:
    cur = pm.get(node)
    while cur is not None and not isinstance(cur, ast.Module):
        if isinstance(cur, _FUNC_SCOPE_TYPES):
            return True
        cur = pm.get(cur)
    return False
def _inside_inactive_branch(node: ast.AST, pm: dict) -> bool:
    child = node
    cur = pm.get(node)
    while cur is not None:
        if isinstance(cur, ast.If):
            body_visible = _module_level_body_visible(cur.test)
            type_only_branch = (
                cur.body if body_visible is False
                else cur.orelse if body_visible is True else ())
            if any(statement is child for statement in type_only_branch):
                return True
        child, cur = cur, pm.get(cur)
    return False
def _comp_binds_through(comp: ast.AST, count: int) -> set[str]:
    binds: set[str] = set()
    for gen in comp.generators[:count]:
        for n in walk_nodes(gen.target):
            if isinstance(n, ast.Name):
                binds.add(n.id)
    return binds
def _in_first_iter_subtree(node: ast.AST, comp: ast.AST, pm: dict) -> bool:
    first_iter = comp.generators[0].iter
    p = node
    while p is not None and p is not comp:
        if p is first_iter:
            return True
        p = pm.get(p)
    return False
def _function_scope_shadows(name: str, fn: ast.AST, pm: dict,
                            binds_cache: dict[Any, Any]) -> bool:
    binds = binds_cache.get(id(fn))
    if binds is None:
        binds = binds_cache[id(fn)] = _fn_scope_binds(fn, pm)
    return name in binds
def _function_scope_globals(fn: ast.AST,
                            binds_cache: dict[Any, Any]) -> frozenset[str]:
    key = (id(fn), "global_declarations")
    names = binds_cache.get(key)
    if names is None:
        names = binds_cache[key] = frozenset(
            name for node in same_scope_dfs_nodes(fn)
            if isinstance(node, ast.Global) for name in node.names)
    return names
def _comp_visible_generator_count(node: ast.AST, comp: ast.AST,
                                  pm: dict) -> int:
    cur = node
    while cur is not comp:
        parent = pm.get(cur)
        if parent is None:
            break
        if isinstance(parent, ast.comprehension):
            for idx, gen in enumerate(comp.generators):
                if parent is not gen:
                    continue
                if cur is gen.iter:
                    return idx
                if any(cur is cond for cond in gen.ifs):
                    return idx + 1
        cur = parent
    return len(comp.generators)
def _comp_scope_shadows(name: str, comp: ast.AST, node: ast.AST, pm: dict,
                        binds_cache: dict[Any, Any]) -> bool:
    visible_count = _comp_visible_generator_count(node, comp, pm)
    if visible_count == 0:
        return False
    if visible_count < len(comp.generators):
        return name in _comp_binds_through(comp, visible_count)
    binds = binds_cache.get(id(comp))
    if binds is None:
        binds = binds_cache[id(comp)] = _comp_binds_through(
            comp, len(comp.generators))
    return name in binds
def _type_param_shadow_override(name: str, node: ast.AST, pm: dict,
                                binds_cache: dict[Any, Any]) -> bool:
    resolver = binds_cache.get(_SCOPE_RESOLVER_KEY)
    if resolver is None or not isinstance(node, ast.Name):
        return False
    cur = pm.get(node)
    while cur is not None:
        type_params = getattr(cur, "type_params", None) or ()
        if any(getattr(param, "name", None) == name
               for param in type_params):
            import_path = resolver.import_path(node)
            return bool(getattr(resolver, "_complete", False)) and import_path is None
        cur = pm.get(cur)
    return False
def _is_shadowed(name: str, node: ast.AST, pm: dict,
                 binds_cache: dict[Any, Any]) -> bool:
    if _type_param_shadow_override(name, node, pm, binds_cache):
        return True
    cur = pm.get(node)
    while cur is not None and not isinstance(cur, ast.Module):
        if (isinstance(cur, _FUNC_SCOPE_TYPES)
                and not _in_function_header(node, cur, pm)
                and name in _function_scope_globals(cur, binds_cache)):
            return False
        if _scope_shadows(name, cur, node, pm, binds_cache):
            return True
        cur = pm.get(cur)
    return False
def _in_function_header(node: ast.AST, fn: ast.AST, pm: dict) -> bool:
    child = node
    cur = pm.get(node)
    while cur is not None and cur is not fn:
        child = cur
        cur = pm.get(cur)
    if cur is not fn:
        return False
    if child is getattr(fn, "args", None):
        return True
    if child in (getattr(fn, "decorator_list", None) or ()):
        return True
    if child is getattr(fn, "returns", None):
        return True
    return child in (getattr(fn, "type_params", None) or ())
def _direct_child_under(node: ast.AST, cls: ast.ClassDef,
                        pm: dict) -> ast.AST | None:
    child = node
    cur = pm.get(node)
    while cur is not None and cur is not cls:
        child = cur
        cur = pm.get(cur)
    return child if cur is cls else None
def _in_class_header(node: ast.AST, cls: ast.ClassDef, pm: dict) -> bool:
    child = _direct_child_under(node, cls, pm)
    if child is None:
        return False
    if child in (cls.decorator_list or ()) or child in (cls.bases or ()):
        return True
    if child in (getattr(cls, "type_params", None) or ()):
        return True
    return child in (cls.keywords or ())
def _evaluates_in_class_body(node: ast.AST, cls: ast.ClassDef,
                             pm: dict) -> bool:
    cur = pm.get(node)
    while cur is not None and cur is not cls:
        if isinstance(cur, _FUNC_SCOPE_TYPES):
            if not _in_function_header(node, cur, pm):
                return False
        elif isinstance(cur, _COMP_TYPES):
            if not _in_first_iter_subtree(node, cur, pm):
                return False
        elif (isinstance(cur, ast.ClassDef)
              and not _in_class_header(node, cur, pm)):
            return False
        cur = pm.get(cur)
    return cur is cls
def _scope_shadows(name: str, scope: ast.AST, node: ast.AST, pm: dict,
                   binds_cache: dict[Any, Any]) -> bool:
    if isinstance(scope, _FUNC_SCOPE_TYPES):
        if _in_function_header(node, scope, pm):
            return False
        return _function_scope_shadows(name, scope, pm, binds_cache)
    if isinstance(scope, _COMP_TYPES):
        return _comp_scope_shadows(name, scope, node, pm, binds_cache)
    if isinstance(scope, ast.ClassDef):
        if not _evaluates_in_class_body(node, scope, pm):
            return False
        _key = (id(scope), "binding_first_lines")
        first_lines = binds_cache.get(_key)
        if first_lines is None:
            first_lines = binds_cache[_key] = _binding_first_lines(scope, pm)
        _line = first_lines.get(name)
        return _line is not None and _line <= getattr(node, "lineno", 0)
    return False
def _attr_root_name(node: ast.Attribute) -> ast.Name | None:
    root = node
    while isinstance(root, ast.Attribute):
        root = root.value
    return root if isinstance(root, ast.Name) else None
def _dotted_attr_parts(node: ast.AST) -> list[str] | None:
    parts: list[str] = []
    current = node
    while isinstance(current, ast.Attribute):
        parts.append(current.attr)
        current = current.value
    if not isinstance(current, ast.Name):
        return None
    parts.append(current.id)
    return list(reversed(parts))
def _current_package_attr_target(
        node: ast.Attribute, pkg_name: str | None, pm: dict,
        imports: _ScopedImports,
        binds_cache: dict[Any, Any]) -> tuple[str, str] | None:
    if not pkg_name:
        return None
    module_parts = _dotted_attr_parts(node.value)
    if not module_parts:
        return None
    module = _plain_import_target(".".join(module_parts), pkg_name)
    root = _attr_root_name(node.value)
    if module is None or root is None:
        return None
    visible = _visible_import_targets(
        root.id, root, pm, imports, binds_cache, dotted=True)
    return (module, node.attr) if module in visible else None
def _function_scope_nonlocals(fn: ast.AST,
                              binds_cache: dict[Any, Any]) -> frozenset[str]:
    key = (id(fn), "nonlocal_declarations")
    names = binds_cache.get(key)
    if names is None:
        names = binds_cache[key] = frozenset(
            name for node in same_scope_dfs_nodes(fn)
            if isinstance(node, ast.Nonlocal) for name in node.names)
    return names
def _direct_nonimport_rebind_position(
        stmt: ast.stmt, name: str) -> _SourcePosition | None:
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return _source_position(stmt) if stmt.name == name else None
    if isinstance(stmt, ast.Assign):
        targets = stmt.targets
    elif ((isinstance(stmt, ast.AnnAssign) and stmt.value is not None)
          or isinstance(stmt, ast.AugAssign)):
        targets = [stmt.target]
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        targets = [item.optional_vars for item in stmt.items
                   if item.optional_vars is not None]
    elif (isinstance(stmt, (ast.If, ast.While))
          and isinstance(stmt.test, ast.NamedExpr)):
        targets = [stmt.test.target]
    elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.NamedExpr):
        targets = [stmt.value.target]
    else:
        return None
    bound = any(nm.id == name for target in targets
                for nm in _assign_target_names(target))
    return _source_position(stmt) if bound else None
def _direct_import_rebind_position(
        stmt: ast.stmt, name: str) -> _SourcePosition | None:
    if isinstance(stmt, (ast.Import, ast.ImportFrom)) and name in import_stmt_binds(stmt):
        return _source_position(stmt)
    return None
def _containing_block_rebind_position(
        block: ast.AST, child: ast.stmt, name: str,
) -> _SourcePosition | None:
    body = getattr(block, "body", None)
    if not isinstance(body, list) or not any(stmt is child for stmt in body):
        return None
    if isinstance(block, (ast.For, ast.AsyncFor)):
        targets = [block.target]
    elif isinstance(block, (ast.With, ast.AsyncWith)):
        targets = [item.optional_vars for item in block.items
                   if item.optional_vars is not None]
    elif isinstance(block, ast.ExceptHandler):
        return _source_position(block) if block.name == name else None
    elif hasattr(ast, "match_case") and isinstance(block, ast.match_case):
        matched = any(name in _binds_of_definition(pattern_node)
                      for pattern_node in walk_nodes(block.pattern))
        return _source_position(block.pattern) if matched else None
    else:
        return None
    bound = any(nm.id == name for target in targets
                for nm in _assign_target_names(target))
    return _source_position(block) if bound else None
def _definite_rebind_position(
        name: str, node: ast.AST, scope: ast.AST, pm: dict, *,
        direct_rebind=_direct_nonimport_rebind_position,
) -> _SourcePosition | None:
    latest: _SourcePosition | None = None
    child = node
    cur = pm.get(node)
    nested_scope = False
    lexical_scopes = (ast.Module, ast.ClassDef, *_FUNC_SCOPE_TYPES)
    while cur is not None:
        if cur is scope:
            nested_scope = False
        elif isinstance(cur, lexical_scopes):
            nested_scope = True
        if not nested_scope and isinstance(child, ast.stmt):
            for field in ("body", "orelse", "finalbody"):
                statements = getattr(cur, field, None)
                if not isinstance(statements, list):
                    continue
                for index, statement in enumerate(statements):
                    if statement is not child:
                        continue
                    for previous in statements[:index]:
                        position = direct_rebind(previous, name)
                        if position is not None and (
                                latest is None or position > latest):
                            latest = position
                    position = _containing_block_rebind_position(
                        cur, child, name)
                    if position is not None and (
                            latest is None or position > latest):
                        latest = position
                    break
        if cur is scope:
            break
        child, cur = cur, pm.get(cur)
    return latest
def _scoped_module_imports(
        tree: ast.Module, pkg_name: str | None,
) -> _ScopedImports:
    pm = parent_map(tree)
    imports: _ScopedImports = {}
    for stmt in tree_nodes(tree):
        if not isinstance(stmt, (ast.Import, ast.ImportFrom)):
            continue
        scope = pm.get(stmt)
        while scope is not None and not isinstance(
                scope, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.ClassDef)):
            scope = pm.get(scope)
        if scope is None:
            continue
        entries: list[tuple[str, str, bool]] = []
        if isinstance(stmt, ast.Import):
            for a in stmt.names:
                target = _plain_import_target(a.name, pkg_name)
                if target is None:
                    continue
                if a.asname:
                    entries.append((a.asname, target, False))
                elif "." not in a.name:
                    entries.append((a.name, target, False))
                else:
                    entries.append((a.name.split(".", 1)[0], target, True))
        elif (_from_import_in_scope(stmt, pkg_name)
              and _from_import_package_container(stmt, pkg_name)):
            entries.extend((bind, target, False) for bind, target
                           in _module_name_import_binds(stmt.names))
        for bind, target, dotted in entries:
            imports.setdefault(scope, {}).setdefault(bind, set()).add(
                (_source_position(stmt), target, dotted))
    return imports
def _visible_import_targets(
        name: str, node: ast.AST, pm: dict,
        imports: _ScopedImports,
        binds_cache: dict[Any, Any], *, dotted: bool = False,
) -> set[str]:
    if _type_param_shadow_override(name, node, pm, binds_cache):
        return set()
    def scope_entries(scope: ast.AST) -> set[tuple[_SourcePosition, str]]:
        node_position = _source_position(node)
        entries = {(position, target) for position, target, is_dotted
                   in imports.get(scope, {}).get(name, set())
                   if is_dotted == dotted and position <= node_position}
        if not entries:
            return set()
        rebound = _definite_rebind_position(name, node, scope, pm)
        import_rebound = _definite_rebind_position(
            name, node, scope, pm,
            direct_rebind=_direct_import_rebind_position)
        return {(position, target) for position, target in entries
                if (rebound is None or position > rebound)
                and (import_rebound is None or position >= import_rebound)}
    cur = pm.get(node)
    global_only = False
    while cur is not None:
        if isinstance(cur, _FUNC_SCOPE_TYPES) and not global_only:
            if not _in_function_header(node, cur, pm):
                if name in _function_scope_globals(cur, binds_cache):
                    global_only = True
                elif name not in _function_scope_nonlocals(cur, binds_cache):
                    entries = scope_entries(cur)
                    if entries:
                        return {target for _position, target in entries}
                    if _function_scope_shadows(name, cur, pm, binds_cache):
                        return set()
        elif isinstance(cur, _COMP_TYPES) and not global_only:
            if _comp_scope_shadows(name, cur, node, pm, binds_cache):
                return set()
        elif isinstance(cur, ast.ClassDef) and not global_only:
            if _evaluates_in_class_body(node, cur, pm):
                key = (id(cur), "binding_first_lines")
                first_lines = binds_cache.get(key)
                if first_lines is None:
                    first_lines = binds_cache[key] = _binding_first_lines(cur, pm)
                first_line = first_lines.get(name)
                line = getattr(node, "lineno", 0)
                if first_line is not None and first_line <= line:
                    position = _source_position(node)
                    return {target for import_position, target in scope_entries(cur)
                            if import_position <= position}
        elif isinstance(cur, ast.Module):
            return {target for _position, target in scope_entries(cur)}
        cur = pm.get(cur)
    return set()
def _ref_entry(node: ast.AST, pm: dict,
               binds_cache: dict[Any, Any]) -> tuple[str, ast.AST] | None:
    if isinstance(node, ast.AugAssign):
        if (isinstance(node.target, ast.Name)
                and not _is_shadowed(node.target.id, node.target, pm,
                                     binds_cache)):
            return node.target.id, node.target
        return None
    return _load_ref_entry(node, pm, binds_cache)
def _load_ref_entry(node: ast.AST, pm: dict,
                    binds_cache: dict[Any, Any]) -> tuple[str, ast.AST] | None:
    if isinstance(node, ast.Name):
        target, report = node, node
    elif isinstance(node, ast.Attribute):
        target, report = _attr_root_name(node), node
    else:
        return None
    if _is_unshadowed_load(target, pm, binds_cache):
        return target.id, report
    return None
def _is_unshadowed_load(target: ast.AST, pm: dict,
                        binds_cache: dict[Any, Any]) -> bool:
    return (isinstance(target, ast.Name) and isinstance(target.ctx, ast.Load)
            and not _is_shadowed(target.id, target, pm, binds_cache))
def _module_state_bindings(tree: ast.Module) -> set[str]:
    pm = parent_map(tree)
    names: set[str] = set()
    for node in same_scope_dfs_nodes(tree):
        if isinstance(node, ast.Name):
            if (isinstance(node.ctx, ast.Store)
                    and not _is_comp_target(node, pm)
                    and not _is_annotation_only_target(node, pm)):
                names.add(node.id)
            continue
        names.update(_binds_of_definition(node))
    return names
def _declares_all(tree: ast.Module) -> bool:
    return any(is_all_assignment(node)
               for node in _iter_module_level_stmts(tree.body))
def _public_api_of(tree: ast.Module, declared: set[str], exact: bool,
                   top_defs: list[tuple[str, int, int]]) -> tuple[set[str], bool]:
    if declared or not exact or _declares_all(tree):
        return set(declared), bool(exact)
    return ({name for name, _start, _end in top_defs
             if not name.startswith("_")}, True)
class ModuleInfo:
    def __init__(self, name: str, path: str, src: str, tree: ast.Module,
                 pkg_name: str | None = None):
        self.name = name
        self.path = path
        self.src = src
        self.tree = tree
        self.pkg_name = pkg_name
        self.public_api: set[str] = set()
        self.public_api_exact = True
        self.top_defs: list[tuple[str, int, int]] = []
        self.ref_lines: dict[str, list[int]] = defaultdict(list)
        self.module_bindings: set[str] = set()
        self.lines = count_lines(src)
        self.top_from_mods: set[str] = set()
        self.symbol_imports: set[tuple[str, str]] = set()
        self.defs: set[str] = set()
        self.defs_lines: dict[str, int] = {}
        self.lazy_edges: set[tuple[str, str]] = set()
        self.attr_used: set[tuple[str, str]] = set()
        self.internal_usage: set[str] = set()
        self.self_import_hard = False
        self.self_import_lazy = False
        self._parse()
    def _parse_lazy_edges(self) -> None:
        pm = parent_map(self.tree)
        for node in tree_nodes(self.tree):
            if not isinstance(node, (ast.ImportFrom, ast.Import)):
                continue
            if (_inside_inactive_branch(node, pm)
                    or not _inside_function_scope(node, pm)):
                continue
            if _stmt_self_import(node, self.name, self.pkg_name):
                self.self_import_lazy = True
            if isinstance(node, ast.ImportFrom):
                self.symbol_imports.update(
                    _symbol_import_entries(node, self.pkg_name))
            for _lt in _lazy_import_edge_targets(
                    node, self.name, self.pkg_name):
                self.lazy_edges.add((self.name, _lt))
    def _parse_refs(self) -> None:
        pm = parent_map(self.tree)
        binds_cache: dict[Any, Any] = {}
        if any(getattr(node, "type_params", None)
               for node in tree_nodes(self.tree)):
            binds_cache[_SCOPE_RESOLVER_KEY] = ScopeNameResolver(
                self.src, self.path, self.tree, self.module_bindings)
        imports = _scoped_module_imports(self.tree, self.pkg_name)
        for node in tree_nodes(self.tree):
            if node is self.tree:
                continue
            entry = _ref_entry(node, pm, binds_cache)
            if entry is not None:
                ref_name, ref_node = entry
                self.internal_usage.add(ref_name)
                _line = getattr(ref_node, "lineno", 0)
                if _line:
                    self.ref_lines[ref_name].append(_line)
            if not isinstance(node, ast.Attribute):
                continue
            if isinstance(node.value, ast.Name):
                for target in _visible_import_targets(
                        node.value.id, node.value, pm, imports, binds_cache):
                    self.attr_used.add((target, node.attr))
                continue
            qualified = _current_package_attr_target(
                node, self.pkg_name, pm, imports, binds_cache)
            if qualified is not None:
                self.attr_used.add(qualified)
    def _parse(self) -> None:
        tree = self.tree
        declared_api, declared_exact = collect_module_exports_state(tree)
        self.self_import_hard = _collect_self_import(
            tree.body, self.name, self.pkg_name)
        _collect_import_info(tree.body, self.top_from_mods,
                             self.symbol_imports, pkg_name=self.pkg_name)
        self.top_defs = _collect_top_level_defs(tree)
        self.public_api, self.public_api_exact = _public_api_of(
            tree, declared_api, declared_exact, self.top_defs)
        self.defs = {name for name, _s, _e in self.top_defs}
        self.defs_lines = {name: s for name, s, _e in self.top_defs}
        self.module_bindings = _module_state_bindings(tree)
        self._parse_lazy_edges()
        self._parse_refs()
def _range_has_line(lines: list[int] | None, start: int, end: int) -> bool:
    return bool(lines) and any(start <= ln <= end for ln in lines)
def scan_independent_blocks(mod: ModuleInfo) -> list[dict]:
    all_defs = {name for name, _s, _e in mod.top_defs} | mod.module_bindings
    return [_block_entry(name, start, end, all_defs, mod.ref_lines)
            for name, start, end in mod.top_defs
            if not is_dunder_name(name)]
def _block_entry(name: str, start: int, end: int, all_defs: set[str],
                 ref_lines: dict[str, list[int]]) -> dict:
    internal = sorted(r for r in all_defs
                      if r != name
                      and _range_has_line(ref_lines.get(r), start, end))
    return {"name": name, "start": start, "end": end,
            "lines": end - start + 1, "internal_deps": internal}
def _package_name_for_directory(
        directory: str, source_root: str | Path | None = None) -> str | None:
    current = Path(os.path.abspath(directory))
    if source_root is not None:
        root = Path(os.path.abspath(source_root))
        if not (root / "__init__.py").is_file():
            if current == root:
                return None
            if current.is_relative_to(root):
                relative = current.relative_to(root)
                if all(part.isidentifier() for part in relative.parts):
                    return ".".join(relative.parts)
    if not (current / "__init__.py").is_file():
        return None
    parts = [current.name]
    while current.parent != current and (current.parent / "__init__.py").is_file():
        current = current.parent
        parts.append(current.name)
    return ".".join(reversed(parts))
_MODULE_DIR_SKIP_NAMES = frozenset(
    SCAN_COLLECT_PRUNE_DIRS_LOWER | TEST_ARTIFACT_DIRS | {
        "testing", "docs", "doc", "examples", "example", "scripts",
        "script", "temp", "tmp",
    }
)
_SOURCE_ROOT_NAMES = ("src", "lib", "python")
def _is_module_file_name(name: str) -> bool:
    if not is_scan_py_name(name):
        return False
    stem = Path(name).stem
    return stem != "__init__" and stem.isidentifier()
def _has_module_files(path: Path) -> bool:
    try:
        return any(item.is_file() and _is_module_file_name(item.name)
                   for item in path.iterdir())
    except OSError as exc:
        logger.debug("[Cohesion] 目录不可读 %s: %s", path, exc)
        return False
def _module_subdirs(path: Path) -> list[Path]:
    if not path.is_dir():
        return []
    try:
        children = sorted(path.iterdir())
    except OSError as exc:
        logger.debug("[Cohesion] 子目录枚举失败 %s: %s", path, exc)
        return []
    return [child for child in children
            if child.is_dir() and child.name.isidentifier()
            and not is_pruned_scan_dir(child.name, _MODULE_DIR_SKIP_NAMES)]
def _has_module_files_below(path: Path, depth: int = 3) -> bool:
    if _has_module_files(path):
        return True
    if depth <= 0:
        return False
    return any(_has_module_files_below(child, depth - 1)
               for child in _module_subdirs(path))
def _discover_module_root(directory: str) -> Path | None:
    root = Path(os.path.abspath(directory))
    if _has_module_files(root):
        return root
    for name in _SOURCE_ROOT_NAMES:
        candidate = root / name
        if _has_module_files_below(candidate):
            return candidate
    if any(_has_module_files_below(child) for child in _module_subdirs(root)):
        return root
    return None
def _module_files_of(root: Path) -> list[Path]:
    files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        current = Path(dirpath)
        dirnames[:] = sorted(
            name for name in dirnames
            if name.isidentifier()
            and not is_pruned_scan_dir(name, _MODULE_DIR_SKIP_NAMES))
        files.extend(current / name for name in sorted(filenames)
                     if _is_module_file_name(name))
    return files
def _resolve_source_root(source_root, requested: str) -> Path | None:
    if source_root is None or source_root == "":
        return _discover_module_root(requested)
    declared = _coerce_directory(source_root)
    if not declared:
        logger.warning("[Cohesion] source_root 非法，回退自动发现: %r",
                       source_root)
        return _discover_module_root(requested)
    root = Path(declared)
    if not root.is_dir():
        logger.warning("[Cohesion] source_root 不是目录，回退自动发现: %s",
                       declared)
        return _discover_module_root(requested)
    return root
def load_modules(directory: str,
                 cache: SharedCache | None = None,
                 *, source_root: str | Path | None = None
                 ) -> dict[str, ModuleInfo]:
    requested = _coerce_directory(directory)
    if not requested:
        logger.warning("[Cohesion] 分析目录为空或非法，跳过: %r", directory)
        return {}
    root = _resolve_source_root(source_root, requested)
    if root is None:
        logger.warning("[Cohesion] 未发现 Python 模块目录: %s", requested)
        return {}
    files = _module_files_of(root)
    pkg_cache: dict[Path, str | None] = {}
    mods: dict[str, ModuleInfo] = {}
    for f in files:
        if f.parent not in pkg_cache:
            pkg_cache[f.parent] = _package_name_for_directory(
                str(f.parent), source_root=root)
        pkg_name = pkg_cache[f.parent]
        name = f.stem
        if name in mods:
            logger.warning(
                "[Cohesion] 叶名重名跳过（无法仅凭导入末段区分）: %s 与 %s",
                mods[name].path, f)
            continue
        loaded = load_module_source(f, cache)
        if loaded is None:
            continue
        src, tree = loaded
        mods[name] = ModuleInfo(name, str(f), src, tree, pkg_name=pkg_name)
    return mods
def _sccs(edges: set[tuple[str, str]]) -> list[list[str]]:
    graph: dict[str, set[str]] = defaultdict(set)
    for source, target in edges:
        graph[source].add(target)
    return [sorted(component) for component in tarjan_scc(graph)
            if len(component) > 1]
def _empty_cycles() -> dict:
    return {"hard_sccs": [], "soft_sccs": [],
            "hard_count": 0, "soft_count": 0}
def _scc_membership(cycles: dict) -> dict[str, set[int]]:
    membership: dict[str, set[int]] = defaultdict(set)
    for idx, scc in enumerate(cycles["hard_sccs"] + cycles["soft_sccs"]):
        for node in scc:
            membership[node].add(idx)
    return membership
def _scc_node_names(sccs: list[list[str]]) -> set[str]:
    return {node for scc in sccs for node in scc}
def _uncovered_self_loops(self_loops: list[list[str]],
                          covered: set[str]) -> list[list[str]]:
    return [scc for scc in self_loops if scc[0] not in covered]
def _share_scc(membership: dict[str, set[int]], a: str, b: str) -> bool:
    own = membership.get(a)
    if not own:
        return False
    return bool(own & membership.get(b, set()))
def _normalized_sccs(sccs: list[list[str]]) -> list[list[str]]:
    norm = [sorted(s) for s in sccs]
    norm.sort(key=lambda s: (-len(s), s))
    return norm
class CohesionAnalyzer:
    def __init__(self, directory: str,
                 min_large_lines: int = DEFAULT_MIN_LARGE_LINES,
                 cache: SharedCache | None = None,
                 *, source_root: str | Path | None = None):
        self.directory = _coerce_directory(directory)
        self.min_large_lines = _coerce_min_lines(min_large_lines)
        self.mods: dict[str, ModuleInfo] = load_modules(
            self.directory, cache=cache, source_root=source_root)
        self.names = set(self.mods.keys())
        self.top_edges: set[tuple[str, str]] = set()
        self.lazy_edges: set[tuple[str, str]] = set()
        self.sym_consumers: dict[tuple[str, str], set[str]] = defaultdict(set)
        self.file_consumers: dict[str, set[str]] = defaultdict(set)
        self._src_consumer_syms: dict[tuple[str, str], set[str]] = defaultdict(set)
        self._build_graph()
    def _consume_top_and_lazy_edges(self) -> None:
        for m, mi in self.mods.items():
            for src in sorted(mi.top_from_mods):
                self._add_dependency_edge(self.top_edges, m, src)
            for _m, src in sorted(mi.lazy_edges):
                self._add_dependency_edge(self.lazy_edges, _m, src)
    def _add_dependency_edge(self, edges: set[tuple[str, str]],
                             m: str, src: str) -> None:
        if src in self.names and src != m:
            edges.add((m, src))
            self.file_consumers[src].add(m)
    def _consume_symbol_and_attr_edges(self) -> None:
        for m, mi in self.mods.items():
            for sym, src in sorted(mi.symbol_imports):
                self._add_symbol_consumer(m, src, sym)
            for src, attr in sorted(mi.attr_used):
                self._add_symbol_consumer(m, src, attr)
    def _add_symbol_consumer(self, m: str, src: str, sym: str) -> None:
        if src in self.names and src != m and sym in self.mods[src].defs:
            self.sym_consumers[(src, sym)].add(m)
            self.file_consumers[src].add(m)
            self._src_consumer_syms[(src, m)].add(sym)
    def _build_graph(self) -> None:
        self._consume_top_and_lazy_edges()
        self._consume_symbol_and_attr_edges()
    def _self_loop_sccs(self) -> tuple[list[list[str]], list[list[str]]]:
        hard: list[list[str]] = []
        soft: list[list[str]] = []
        for m, mi in sorted(self.mods.items()):
            if mi.self_import_hard:
                hard.append([m])
            elif mi.self_import_lazy:
                soft.append([m])
        return hard, soft
    def detect_cycles(self, include_soft: bool = True) -> dict:
        _self_hard, _self_soft = self._self_loop_sccs()
        hard = _sccs(self.top_edges)
        hard.extend(_uncovered_self_loops(
            _self_hard, _scc_node_names(hard)))
        if include_soft:
            soft = _sccs(self.top_edges | self.lazy_edges)
            _hard_sets = {frozenset(h) for h in hard}
            soft_only = [s for s in soft if frozenset(s) not in _hard_sets]
            soft_only.extend(_uncovered_self_loops(
                _self_soft,
                _scc_node_names(hard) | _scc_node_names(soft_only)))
        else:
            soft_only = []
        return {"hard_sccs": _normalized_sccs(hard),
                "soft_sccs": _normalized_sccs(soft_only),
                "hard_count": len(hard), "soft_count": len(soft_only)}
    def cycle_exempt_lazy_edges(self) -> set[tuple[str, str]]:
        cycles = self.detect_cycles()
        membership = _scc_membership(cycles)
        return {(m, t) for (m, t) in self.lazy_edges
                if _share_scc(membership, m, t)}
    def fan_metrics(self) -> dict:
        fan_in = Counter()
        fan_out = Counter()
        all_edges = self.top_edges | self.lazy_edges
        for a, b in all_edges:
            fan_in[b] += 1
            fan_out[a] += 1
        return {
            "fan_in": dict(sorted(fan_in.items(), key=lambda kv: (-kv[1], kv[0]))),
            "fan_out": dict(sorted(fan_out.items(), key=lambda kv: (-kv[1], kv[0]))),
        }
    def find_reorg_candidates(self, want_migrate: bool = True,
                              want_merge: bool = True) -> dict:
        migrate = self._migrate_candidates() if want_migrate else []
        merge = self._merge_candidates() if want_merge else []
        return {"migrate_candidates": migrate, "merge_candidates": merge}
    def _migrate_candidates(self) -> list:
        migrate = []
        for (src, sym), consumers in self.sym_consumers.items():
            cons = _single_consumer(consumers)
            if cons is None:
                continue
            if not self.mods[src].public_api_exact:
                continue
            if sym in self.mods[src].public_api:
                continue
            if sym not in self.mods[src].internal_usage:
                migrate.append({"src": src, "sym": sym, "consumer": cons,
                                "src_lines": self.mods[src].lines,
                                "sym_line": self.mods[src].defs_lines.get(sym, 0)})
        return migrate
    def _merge_candidates(self) -> list:
        merge = []
        for src, consumers in self.file_consumers.items():
            if not self.mods[src].public_api_exact:
                continue
            if self.mods[src].public_api:
                continue
            cons = _single_consumer(consumers)
            coverage = None if cons is None else self._coverage_of(src, cons)
            if coverage is None:
                continue
            merge.append({"src": src, "consumer": cons, "coverage": coverage,
                          "src_lines": self.mods[src].lines})
        return merge
    def _coverage_of(self, src: str, cons: str) -> float | None:
        total = len(self.mods[src].defs)
        if total < 3:
            return None
        coverage = len(self._src_consumer_syms[(src, cons)]) / total
        return coverage if coverage >= 0.5 else None
    def scan_large_blocks(self) -> list[dict]:
        results = []
        threshold = _coerce_min_lines(self.min_large_lines)
        for m, mi in self.mods.items():
            if mi.lines < threshold:
                continue
            independent = _independent_blocks(mi)
            if independent:
                results.append({"module": m, "lines": mi.lines,
                                "independent_blocks": independent})
        return results
    _RULE_WANT_MAP = tuple(
        (rule_id, meta.switch) for rule_id, meta in COHESION_RULE_META.items())
    def _wants(self, active_rules: frozenset | set | None) -> dict:
        _rules = _coerce_rule_set(active_rules)
        _full = _rules is None
        return {k: _full or rid in _rules for rid, k in self._RULE_WANT_MAP}
    def analyze(self, active_rules: frozenset | set | None = None) -> dict:
        want = self._wants(active_rules)
        return {
            "directory": self.directory,
            "module_count": len(self.mods),
            "total_lines": sum(m.lines for m in self.mods.values()),
            "cycles": self._cycles_section(want),
            "fan_metrics": self.fan_metrics(),
            "reorg_candidates": self._reorg_section(want),
            "large_blocks": self.scan_large_blocks() if want["blocks"] else [],
        }
    def _cycles_section(self, want: dict) -> dict:
        if not (want["hard"] or want["soft"]):
            return _empty_cycles()
        cycles = self.detect_cycles(include_soft=want["soft"])
        if want["hard"]:
            return cycles
        return {**_empty_cycles(), "soft_sccs": cycles["soft_sccs"],
                "soft_count": cycles["soft_count"]}
    def _reorg_section(self, want: dict) -> dict:
        if not (want["migrate"] or want["merge"]):
            return {"migrate_candidates": [], "merge_candidates": []}
        return self.find_reorg_candidates(
            want_migrate=want["migrate"], want_merge=want["merge"])
def _single_consumer(consumers: set) -> str | None:
    return next(iter(consumers)) if len(consumers) == 1 else None
def _independent_blocks(mi) -> list:
    return [b for b in scan_independent_blocks(mi) if not b["internal_deps"]]
def _section_dict(section, key: str) -> dict:
    if not isinstance(section, dict):
        return {}
    value = section.get(key)
    return value if isinstance(value, dict) else {}
def render_markdown(result: dict) -> str:
    result = result if isinstance(result, dict) else {}
    cycles = _section_dict(result, "cycles")
    lines = [f"# 上下文内聚分析报告 — {result.get('directory', '')}",
             (f"\n- 模块数: {result.get('module_count', 0)} | "
              f"总行数: {result.get('total_lines', 0)}"),
             (f"- 硬环(加载期): {cycles.get('hard_count', 0)} | "
              f"软环(lazy): {cycles.get('soft_count', 0)}")]
    lines.extend(_md_cycle_lines(cycles))
    lines.extend(_md_reorg_lines(_section_dict(result, "reorg_candidates")))
    lines.extend(_md_block_lines(_section_list(result, "large_blocks")))
    return "\n".join(lines)
def _md_cycle_lines(c: dict) -> list:
    lines = ["\n## 循环依赖"]
    hard_nodes = [_node_names(s) for s in _section_list(c, "hard_sccs")]
    soft_nodes = [_node_names(s) for s in _section_list(c, "soft_sccs")]
    for nodes in hard_nodes:
        if nodes:
            lines.append(f"- **硬环** 大小{len(nodes)}: {sorted(nodes)}")
    for nodes in soft_nodes:
        if nodes:
            lines.append(f"- 软环 大小{len(nodes)}: {sorted(nodes)}")
    if not any(hard_nodes) and not any(soft_nodes):
        lines.append("- 无循环依赖")
    return lines
def _md_reorg_lines(reorg: dict) -> list:
    _migrate = _dict_items(_section_list(reorg, "migrate_candidates"))
    _merge = _dict_items(_section_list(reorg, "merge_candidates"))
    lines = ["\n## 迁出候选(源模块内部0使用+单消费者)"]
    for m in _migrate[:30]:
        lines.append(f"- {m.get('src', '?')}.{m.get('sym', '?')} -> "
                     f"仅被 {m.get('consumer', '?')} 消费")
    if not _migrate:
        lines.append("- 无")
    lines.append("\n## 合并候选(单消费者+高覆盖)")
    for m in _merge[:30]:
        lines.append(f"- {m.get('src', '?')} -> {m.get('consumer', '?')} "
                     f"({_coverage_text(m):.0%})")
    if not _merge:
        lines.append("- 无")
    return lines
def _md_block_lines(large_blocks: list) -> list:
    lines = ["\n## 超大文件可拆独立块"]
    emitted = 0
    for lb in _dict_items(large_blocks):
        for b in _dict_items(_section_list(lb, "independent_blocks")):
            lines.append(f"- {lb.get('module', '?')}({lb.get('lines', '?')}行): "
                         f"独立块 {b.get('name', '?')} "
                         f"行{b.get('start', '?')}-{b.get('end', '?')} "
                         f"({b.get('lines', '?')}行)")
            emitted += 1
    if not emitted:
        lines.append("- 无")
    return lines
def _cohesion_finding(rule_id: str, file: str, line: int,
                      message: str) -> dict:
    meta = COHESION_RULE_META[rule_id]
    return {
        "rule_id": rule_id, "rule_family": meta.family,
        "severity": meta.severity, "confidence": meta.confidence,
        "file": file, "line": line, "message": message,
        "pattern_name": meta.pattern_name, "category": meta.family,
        "source": "B1",
    }
def _cycle_findings(cycles: dict, directory: str = "") -> list[dict]:
    findings = []
    for scc in _section_list(cycles, "hard_sccs"):
        _nodes = _node_names(scc)
        if not _nodes:
            continue
        findings.append(_cohesion_finding(
            "CH01-HARD-CYCLE", directory, 0,
            f"加载期硬环: {len(_nodes)} 模块循环依赖 {_nodes}"))
    for scc in _section_list(cycles, "soft_sccs"):
        _nodes = _node_names(scc)
        if not _nodes:
            continue
        findings.append(_cohesion_finding(
            "CH02-SOFT-CYCLE", directory, 0,
            f"运行时软环(lazy import): {len(_nodes)} 模块 {_nodes}"))
    return findings
def _migrate_findings(candidates: list) -> list[dict]:
    return [_cohesion_finding(
        "CH03-MISPLACED-SYMBOL",
        cand.get("src", "?"), cand.get("sym_line", 0),
        f"符号 {cand.get('sym', '?')} 源模块内部0使用、"
        f"仅被 {cand.get('consumer', '?')} 消费——迁移候选")
        for cand in _dict_items(candidates)]
def _coverage_text(cand) -> float:
    value = cand.get("coverage") if isinstance(cand, dict) else None
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 0.0
    return float(value)
def _merge_findings(candidates: list) -> list[dict]:
    return [_cohesion_finding(
        "CH04-MERGE-CANDIDATE",
        cand.get("src", "?"), 0,
        f"文件 {cand.get('src', '?')} 被 {cand.get('consumer', '?')} 消费 "
        f"{_coverage_text(cand):.0%} 定义——合并候选")
        for cand in _dict_items(candidates)]
def _split_findings(large_blocks: list) -> list[dict]:
    findings = []
    for lb in _dict_items(large_blocks):
        for b in _dict_items(_section_list(lb, "independent_blocks")):
            findings.append(_cohesion_finding(
                "CH05-SPLIT-CANDIDATE",
                lb.get("module", "?"), b.get("start", 0),
                f"超大文件 {lb.get('lines', '?')} 行内独立块 "
                f"{b.get('name', '?')}({b.get('lines', '?')}行)"
                "不依赖文件内其他定义——治理候选"
                "（禁止拆分文件，按简化/去重/收敛/迁移/"
                "提取私有实现处置）"))
    return findings
def _section_list(section, key: str) -> list:
    if not isinstance(section, dict):
        return []
    value = section.get(key)
    return value if isinstance(value, list) else []
def _dict_items(items) -> list[dict]:
    return [item for item in (items or []) if isinstance(item, dict)]
def _node_names(scc) -> list[str]:
    if not isinstance(scc, (list, tuple)):
        return []
    return list(dict.fromkeys(
        node for node in scc if isinstance(node, str) and node))
def result_to_b1_findings(result: dict) -> list[dict]:
    if not isinstance(result, dict):
        return []
    _directory = str(result.get("directory") or "")
    _reorg = result.get("reorg_candidates")
    return [
        *_cycle_findings(result.get("cycles"), _directory),
        *_migrate_findings(_section_list(_reorg, "migrate_candidates")),
        *_merge_findings(_section_list(_reorg, "merge_candidates")),
        *_split_findings(_section_list(result, "large_blocks")),
    ]
def _build_arg_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description="上下文内聚重组分析工具")
    ap.add_argument("directory", help="待分析的 Python 代码目录")
    ap.add_argument("-o", "--output", help="输出 markdown 报告路径")
    ap.add_argument("--json", dest="out_json", help="输出 JSON 报告路径")
    ap.add_argument("--min-lines", type=int, default=DEFAULT_MIN_LARGE_LINES,
                    help=f"超大文件阈值(默认{DEFAULT_MIN_LARGE_LINES})")
    ap.add_argument("--b1-findings", dest="b1",
                    help="输出 B1 兼容 finding 的 JSON 路径")
    return ap
def _validate_cli_paths(ap: argparse.ArgumentParser,
                        args: argparse.Namespace) -> None:
    if not str(args.directory or "").strip():
        ap.error("待分析目录不能为空")
    if not Path(args.directory).is_dir():
        ap.error(f"待分析目录不存在或非目录: {args.directory}")
    for opt_val in (args.output, args.out_json, args.b1):
        _validate_output_path(ap, opt_val)
def _validate_output_path(ap: argparse.ArgumentParser, opt_val: str | None) -> None:
    if not opt_val:
        return
    opt_path = Path(opt_val)
    if opt_path.is_dir():
        ap.error(f"输出路径是目录（应为文件）: {opt_val}")
    if not opt_path.parent.is_dir():
        ap.error(f"输出路径的父目录不存在: {opt_val}")
def _write_reports(md: str, result: dict, args: argparse.Namespace) -> None:
    if args.output:
        Path(args.output).write_text(md, encoding="utf-8")
        logger.info("[engine_b1 CLI] markdown 报告已写入: %s", args.output)
        print(f"\n[markdown 报告已写入] {args.output}")
    if args.out_json:
        _write_json_report(args.out_json, result)
        logger.info("[engine_b1 CLI] json 报告已写入: %s", args.out_json)
        print(f"[json 报告已写入] {args.out_json}")
    if args.b1:
        _write_json_report(args.b1, result_to_b1_findings(result))
        logger.info("[engine_b1 CLI] B1 findings 已写入: %s", args.b1)
        print(f"[B1 findings 已写入] {args.b1}")
def _write_json_report(path: str, payload) -> None:
    Path(path).write_text(
        json.dumps(payload, ensure_ascii=False, indent=2, default=str),
        encoding="utf-8")
def main() -> None:
    ap = _build_arg_parser()
    args = ap.parse_args()
    _validate_cli_paths(ap, args)
    logger.info("[engine_b1 CLI] 内聚分析启动: directory=%s min_lines=%s",
                args.directory, args.min_lines)
    result = CohesionAnalyzer(args.directory, args.min_lines).analyze()
    md = render_markdown(result)
    print(md)
    _write_reports(md, result, args)
    logger.info("[engine_b1 CLI] 内聚分析完成: directory=%s", args.directory)
if __name__ == "__main__":
    main()

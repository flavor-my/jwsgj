from __future__ import annotations

import ast
import hashlib
import logging
import os
import re
import sys
import threading
import time
import weakref
from collections import deque
from dataclasses import dataclass, field
from importlib import machinery, util

from jwsgj.diag_shared_ast_bindings import binding_names_of
from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    build_parent_map,
    definition_time_exprs,
    dotted_name,
    is_main_check,
    is_type_checking_guard,
    iter_module_stmt_blocks,
    module_imports_test_framework,
    pattern_capture_name,
)
from jwsgj.diag_shared_source_core import (
    read_source_tree,
    read_source_with_fingerprint,
)
from jwsgj.diag_testing_source import scope_direct_bindings
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    TEST_ARTIFACT_DIRS,
    TEST_DIR_CANDIDATES_LOWER,
    is_test_dir_candidate,
    is_test_source_basename,
)

_log = logging.getLogger(__name__)
__all__ = [
    'PytestSummaryResult',
    'QualityRun',
    'TestQualityVisitor',
    'build_test_index',
    'clear_index_memo',
    'collect_test_entries',
    'collect_test_findings',
    'detect_test_smells',
    'finalize_test_quality',
    'imp_internal_target',
    'is_collectable_test_class',
    'is_test_function_name',
    'is_test_function_node',
    'is_unittest_testcase_class',
    'iter_collectable_test_functions',
    'load_test_ast',
    'parse_pytest_summary',
    'release_e_group_caches',
    'summary_line_nodeid',
    'tree_collectable_test_classes',
    'tree_unittest_classes',
]
def is_test_function_name(name: str) -> bool:
    return isinstance(name, str) and name.startswith('test')
_UNITTEST_CASE_BASES = frozenset({"TestCase", "IsolatedAsyncioTestCase"})
_READ_DEGRADE_EXC = (OSError, *PARSE_DEGRADE_EXC)
def is_test_function_node(node: ast.AST) -> bool:
    return (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and is_test_function_name(node.name))
def is_unittest_testcase_class(node: ast.ClassDef) -> bool:
    return any(
        (isinstance(base, ast.Name) and base.id in _UNITTEST_CASE_BASES)
        or (isinstance(base, ast.Attribute) and base.attr in _UNITTEST_CASE_BASES)
        for base in node.bases
    )
def is_collectable_test_class(node: ast.ClassDef) -> bool:
    if is_unittest_testcase_class(node):
        return True
    if not node.name.startswith("Test"):
        return False
    return not any(
        isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef))
        and member.name in {"__init__", "__new__"}
        for member in node.body
    )
def _is_imported_unittest_base(base, import_loads: dict) -> bool:
    if isinstance(base, ast.Name):
        record = import_loads.get(id(base))
        sources = record[1] if record is not None else frozenset()
        return any(
            kind == "from"
            and (module == "unittest" or module.startswith("unittest."))
            and name in _UNITTEST_CASE_BASES
            for kind, module, name in sources)
    if not (isinstance(base, ast.Attribute)
            and base.attr in _UNITTEST_CASE_BASES):
        return False
    root = base.value
    while isinstance(root, ast.Attribute):
        root = root.value
    record = import_loads.get(id(root))
    sources = record[1] if record is not None else frozenset()
    return any(
        (kind == "module"
         and (module == "unittest" or module.startswith("unittest.")))
        or (kind == "from" and module == "unittest"
            and _name in {"case", "async_case"})
        for kind, module, _name in sources)
_CLASS_LEXICAL_SCOPES = (
    ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef,
)
def _class_scope_index(tree: ast.AST):
    parents = build_parent_map(tree)
    classes = [node for node in walk_nodes(tree)
               if isinstance(node, ast.ClassDef)]
    scope_by_class: dict[int, ast.AST] = {}
    classes_by_scope: dict[int, list[ast.ClassDef]] = {}
    for node in classes:
        scope = parents.get(id(node))
        while scope is not None and not isinstance(scope, _CLASS_LEXICAL_SCOPES):
            scope = parents.get(id(scope))
        scope = scope or tree
        scope_by_class[id(node)] = scope
        classes_by_scope.setdefault(id(scope), []).append(node)
    return classes, parents, scope_by_class, classes_by_scope
def _outer_lexical_scope(scope: ast.AST, parents: dict[int, ast.AST]):
    scope = parents.get(id(scope))
    while scope is not None and not isinstance(scope, _CLASS_LEXICAL_SCOPES):
        scope = parents.get(id(scope))
    return scope
def _named_base_classes(node: ast.ClassDef, name: str, parents,
                        scope_by_class, classes_by_scope) -> list[ast.ClassDef]:
    scope = scope_by_class.get(id(node))
    while scope is not None:
        matches = [candidate for candidate in classes_by_scope.get(id(scope), ())
                   if candidate.name == name]
        if matches:
            position = _source_position(node)
            if position == (0, 0):
                return matches[-1:]
            preceding = [
                candidate for candidate in matches
                if _source_position(candidate) < position]
            if preceding:
                return [max(preceding, key=_source_position)]
            if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return []
        if isinstance(scope, ast.Module):
            break
        scope = _outer_lexical_scope(scope, parents)
    return []
def tree_unittest_classes(tree: ast.AST) -> set[ast.ClassDef]:
    return _unittest_classes_from_index(tree, _class_scope_index(tree))
def _unittest_classes_from_index(tree: ast.AST, index) -> set[ast.ClassDef]:
    """按已建好的作用域索引收集 unittest 测试类。

    与 ``tree_collectable_test_classes`` 共用同一份索引：两者原先各自
    调用一次 ``_class_scope_index``，同一棵树被重复建索引两遍。
    """
    import_loads = _ImportLoadSiteResolver.collect(tree)
    classes, parents, scope_by_class, classes_by_scope = index
    collected: set[ast.ClassDef] = set()
    changed = True
    while changed:
        changed = False
        for node in classes:
            if node in collected:
                continue
            direct = any(
                _is_imported_unittest_base(base, import_loads)
                for base in node.bases)
            inherited = any(
                isinstance(base, ast.Name) and any(
                    parent in collected
                    for parent in _named_base_classes(
                        node, base.id, parents, scope_by_class, classes_by_scope))
                for base in node.bases)
            if direct or inherited:
                collected.add(node)
                changed = True
    return collected
_COLLECTABLE_CLASSES_CACHE: weakref.WeakKeyDictionary = (
    weakref.WeakKeyDictionary())
_COLLECTABLE_CLASSES_CACHE_MAX = 64
def tree_collectable_test_classes(tree: ast.AST) -> set[ast.ClassDef]:
    """收集可运行测试类；同一棵树多轮消费复用结果，避免重复建索引。"""
    try:
        cached = _COLLECTABLE_CLASSES_CACHE.get(tree)
    except TypeError:
        cached = None
    if cached is not None:
        return set(cached)
    index = _class_scope_index(tree)
    unittest_classes = _unittest_classes_from_index(tree, index)
    classes, parents, scope_by_class, classes_by_scope = index
    constructor_memo: dict[int, bool] = {}
    def has_custom_constructor(node: ast.ClassDef, active: set[int]) -> bool:
        key = id(node)
        if key in constructor_memo:
            return constructor_memo[key]
        if key in active:
            return False
        if any(isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef))
               and member.name in {"__init__", "__new__"}
               for member in node.body):
            constructor_memo[key] = True
            return True
        active.add(key)
        inherited = any(
            isinstance(base, ast.Name) and any(
                has_custom_constructor(parent, active)
                for parent in _named_base_classes(
                    node, base.id, parents, scope_by_class, classes_by_scope))
            for base in node.bases)
        active.remove(key)
        constructor_memo[key] = inherited
        return inherited
    result = unittest_classes | {
        node for node in classes
        if node.name.startswith("Test")
        and not has_custom_constructor(node, set())
    }
    visible_classes = {
        node for scope in (tree, *classes)
        for node in _visible_scoped_definitions(getattr(scope, 'body', ()))
        if isinstance(node, ast.ClassDef)
    }
    result.intersection_update(visible_classes)
    try:
        _COLLECTABLE_CLASSES_CACHE[tree] = frozenset(result)
    except TypeError:
        return result
    while len(_COLLECTABLE_CLASSES_CACHE) > _COLLECTABLE_CLASSES_CACHE_MAX:
        _COLLECTABLE_CLASSES_CACHE.pop(
            next(iter(_COLLECTABLE_CLASSES_CACHE)))
    return result
def _import_time_branch_blocks(node: ast.If) -> list[list]:
    test = node.test
    negated = isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
    inner = test.operand if negated else test
    if is_main_check(inner) or is_type_checking_guard(inner):
        return [node.body if negated else node.orelse]
    if isinstance(test, ast.Constant):
        return [node.body if test.value else node.orelse]
    return [node.body, node.orelse]
def _iter_scope_stmts_in_source_order(stmts: list):
    for stmt in stmts:
        yield stmt
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        if isinstance(stmt, ast.If):
            for block in _import_time_branch_blocks(stmt):
                yield from _iter_scope_stmts_in_source_order(block)
            continue
        for block in iter_module_stmt_blocks(stmt):
            yield from _iter_scope_stmts_in_source_order(block)
def _visible_scoped_definitions(stmts: list):
    definitions = [
        node for node in _iter_scope_stmts_in_source_order(stmts)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))]
    latest = {node.name: index for index, node in enumerate(definitions)}
    return [node for index, node in enumerate(definitions)
            if latest[node.name] == index]
def iter_collectable_test_functions(
        tree: ast.AST,
        collectable_classes: set[ast.ClassDef] | frozenset[ast.ClassDef] | None = None):
    if not isinstance(tree, ast.Module):
        return
    if collectable_classes is None:
        collectable_classes = tree_collectable_test_classes(tree)
    def from_class(class_node: ast.ClassDef):
        for member in _visible_scoped_definitions(class_node.body):
            if is_test_function_node(member):
                yield member
            elif (isinstance(member, ast.ClassDef)
                  and member in collectable_classes):
                yield from from_class(member)
    for node in _visible_scoped_definitions(tree.body):
        if is_test_function_node(node):
            yield node
        elif (isinstance(node, ast.ClassDef)
              and node in collectable_classes):
            yield from from_class(node)
def _read_test_source(filepath: str, caller: str,
                      max_size: int | None) -> str | None:
    try:
        filepath = os.fsdecode(filepath)
    except (TypeError, ValueError):
        _log.warning("[TestSuite] %s 非法文件路径(%s)，跳过",
                     caller, type(filepath).__name__)
        return None
    try:
        if max_size is not None:
            size = os.path.getsize(filepath)
            if size > max_size:
                _log.warning(
                    "[TestSuite] %s 扫描超限跳过 (%d > %d bytes): %s",
                    caller, size, max_size, filepath)
                return None
        source, _fingerprint = read_source_with_fingerprint(filepath)
        if source is None:
            _log.warning("[TestSuite] %s 读取失败: %s", caller, filepath)
        return source
    except _READ_DEGRADE_EXC:
        _log.warning("[TestSuite] %s 读取失败: %s", caller, filepath,
                     exc_info=True)
        return None
def load_test_ast(
    filepath: str,
    source: str | None,
    tree: ast.AST | None,
    caller: str,
    max_size: int | None = None,
) -> tuple[str | None, ast.AST | None]:
    if tree is not None:
        if isinstance(tree, ast.AST):
            return source, tree
        _log.warning("[TestSuite] %s 忽略非法 tree 形态(%s): %s",
                     caller, type(tree).__name__, filepath)
    if source is None:
        source = _read_test_source(filepath, caller, max_size)
        if source is None:
            return None, None
    try:
        return source, ast.parse(source, filename=filepath)
    except PARSE_DEGRADE_EXC:
        _log.warning("[TestSuite] %s AST 解析失败: %s", caller, filepath,
                     exc_info=True)
        return None, None
_INDEX_MEMO: dict[str, tuple[list, dict]] = {}
_INDEX_MEMO_MAX = 4096
_TI_SCHEMA_KEYS = frozenset({
    "imports", "called_names_with_assert",
    "has_assert_global", "module_keys", "name_to_mods",
    "module_aliases", "star_modules", "asserted_attr_chains",
    "from_pkg_binds", "from_bind_pkgs", "local_bind_names",
})
_MATCH_BIND_CLS = tuple(
    _c for _c in (getattr(ast, "MatchAs", None),
                  getattr(ast, "MatchStar", None),
                  getattr(ast, "MatchMapping", None))
    if _c is not None)
_TYPE_ALIAS_CLS = getattr(ast, "TypeAlias", None)
def _match_bind_name(node) -> str:
    return getattr(node, "name", None) or getattr(node, "rest", None) or ""
def _cached_source_and_tree(test_file: str, cache) -> tuple[str | None, ast.AST | None]:
    if cache is None:
        return None, None
    try:
        return cache.get_source(test_file), cache.get_ast(test_file)
    except Exception as _e:  
        log_swallowed(__name__, _e,
                      context=f'_cached_source_and_tree:{type(_e).__name__}')
        return None, None
def _parse_tree_or_none(content: str, test_file: str,
                        caller: str) -> ast.AST | None:
    try:
        return ast.parse(content, filename=test_file)
    except PARSE_DEGRADE_EXC as e:
        _log.warning(
            "[%s] 构建测试索引解析失败,跳过: %s (%s)", caller, test_file, e)
        return None
def _build_missing_entry(test_file: str, cache, bn: str,
                         fp: list) -> dict | None:
    content, tree = _cached_source_and_tree(test_file, cache)
    if tree is None:
        if content is None:
            content = _read_test_source(test_file, "build_test_index", None)
            if content is None:
                return None
        tree = _parse_tree_or_none(content, test_file, "build_test_index")
        if tree is None:
            return None
    _ti = _index_one_test_file(tree)
    if fp[0] != -1:
        _INDEX_MEMO[bn] = (fp, _ti)
    return _ti
def _submodule_exists(skill_dir: str, pkg_bn: str, pkg: str, name: str) -> bool:
    root = _package_root(skill_dir, pkg_bn, pkg)
    return machinery.PathFinder.find_spec(name, [root]) is not None
def _package_root(skill_dir: str, pkg_bn: str, pkg: str) -> str:
    segs = pkg.split(".")
    relative_segs = segs[1:] if segs[0] == pkg_bn else segs
    root = os.path.join(skill_dir, *relative_segs)
    flat_root = os.path.join(skill_dir, *segs)
    src_root = os.path.join(skill_dir, "src", *segs)
    root_is_package = os.path.isfile(os.path.join(root, "__init__.py"))
    if os.path.isdir(src_root) and (not os.path.isdir(root) or not root_is_package):
        return src_root
    if (flat_root != root
            and os.path.isfile(os.path.join(flat_root, "__init__.py"))):
        return flat_root
    return root
def _is_symbol_reexport(name: str, reexport: dict) -> bool:
    target = reexport.get(name)
    return target is not None and target != name
def _with_bind_names(node) -> set:
    return set().union(*(
        binding_names_of(i.optional_vars) for i in node.items
        if i.optional_vars is not None)) if node.items else set()
def _bind_names_assign(node) -> set:
    return set().union(*(binding_names_of(t) for t in node.targets))
def _bind_names_annassign(node) -> set:
    return binding_names_of(node.target) if node.value is not None else set()
def _bind_names_target(node) -> set:
    return binding_names_of(node.target)
def _bind_names_type_alias(node) -> set:
    return binding_names_of(node.name)
def _bind_names_except(node) -> set:
    return {node.name} if node.name else set()
def _bind_names_match(node) -> set:
    name = _match_bind_name(node)
    return {name} if name else set()
_BIND_NAME_COLLECTORS = {
    ast.Assign: _bind_names_assign,
    ast.AnnAssign: _bind_names_annassign,
    ast.AugAssign: _bind_names_target,
    ast.For: _bind_names_target,
    ast.AsyncFor: _bind_names_target,
    ast.With: _with_bind_names,
    ast.AsyncWith: _with_bind_names,
    ast.NamedExpr: _bind_names_target,
    ast.ExceptHandler: _bind_names_except,
    **({_TYPE_ALIAS_CLS: _bind_names_type_alias}
        if _TYPE_ALIAS_CLS is not None else {}),
    **dict.fromkeys(_MATCH_BIND_CLS, _bind_names_match),
}
def _node_bind_names(node) -> set:
    collector = _BIND_NAME_COLLECTORS.get(node.__class__)
    return collector(node) if collector is not None else set()
def _definition_binding_exprs(node) -> list:
    exprs = list(definition_time_exprs(node))
    args = getattr(node, "args", None)
    if isinstance(args, ast.arguments):
        parameters = (*args.posonlyargs, *args.args, *args.kwonlyargs,
                      args.vararg, args.kwarg)
        exprs.extend(parameter.annotation for parameter in parameters
                     if parameter is not None and parameter.annotation is not None)
    returns = getattr(node, "returns", None)
    if returns is not None:
        exprs.append(returns)
    if isinstance(node, ast.ClassDef):
        exprs.extend(node.bases)
        exprs.extend(keyword.value for keyword in node.keywords)
    return exprs
def _source_position(node) -> tuple[int, int]:
    return (getattr(node, 'lineno', 0) or 0,
            getattr(node, 'col_offset', 0) or 0)
def _record_binding_names(out: set, names, node, binding_sites) -> None:
    out.update(names)
    if binding_sites is None:
        return
    position = _source_position(node)
    for name in names:
        binding_sites.setdefault(name, []).append(position)
def _module_level_bind_names(tree, binding_sites=None) -> set:
    out: set = set()
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            _record_binding_names(
                out, {node.name}, node, binding_sites)
            stack.extend(_definition_binding_exprs(node))
            continue
        if isinstance(node, ast.Lambda):
            stack.extend(_definition_binding_exprs(node))
            continue
        _record_binding_names(
            out, _node_bind_names(node), node, binding_sites)
        stack.extend(ast.iter_child_nodes(node))
    return out
def _pkg_import_shadow_names(tree, pkg: str) -> set[str]:
    names: set[str] = set()
    if not isinstance(tree, ast.Module):
        return names
    prefix = f"{pkg}."
    for node in _iter_scope_stmts_in_source_order(tree.body):
        if isinstance(node, ast.Import):
            for alias in node.names:
                bind = alias.asname or alias.name.split(".", 1)[0]
                actual = alias.name if alias.asname else alias.name.split(".", 1)[0]
                if actual != f"{prefix}{bind}":
                    names.add(bind)
        elif isinstance(node, ast.ImportFrom):
            direct_submodule_source = (
                (not node.level and node.module == pkg)
                or (node.level == 1 and node.module is None)
            )
            for alias in node.names:
                if alias.name == "*":
                    continue
                bind = alias.asname or alias.name
                if not (direct_submodule_source and alias.name == bind):
                    names.add(bind)
    return names
def _pkg_shadow_names(pkg_root: str, cache, memo: dict,
                      pkg: str) -> frozenset:
    key = (os.path.normcase(pkg_root), pkg)
    cached = memo.get(key)
    if cached is not None:
        return cached
    names: frozenset = frozenset()
    init_path = os.path.join(pkg_root, "__init__.py")
    if os.path.isfile(init_path):
        tree = read_source_tree(init_path, cache)
        if tree is not None:
            names = frozenset(
                _module_level_bind_names(tree)
                | _pkg_import_shadow_names(tree, pkg))
    memo[key] = names
    return names
def _exists_in_any_pkg(skill_dir: str, pkg_bn: str, pkgs, name: str,
                       cache, memo: dict) -> bool:
    shadow_memo = memo
    for _p in pkgs:
        root = _package_root(skill_dir, pkg_bn, _p)
        if name in _pkg_shadow_names(root, cache, shadow_memo, _p):
            continue
        if _submodule_exists(skill_dir, pkg_bn, _p, name):
            return True
    return False
def _compute_submodule_binds(index: list, reexport: dict, skill_dir: str,
                             cache) -> set:
    _sub_binds: set = set()
    _pkg_bn = os.path.basename(os.path.normpath(skill_dir))
    _shadow_memo: dict = {}
    for _ti in index:
        for _x, _pkgs in (_ti.get("from_bind_pkgs") or {}).items():
            if _x in _sub_binds or _is_symbol_reexport(_x, reexport):
                continue
            if _exists_in_any_pkg(skill_dir, _pkg_bn, _pkgs, _x,
                                  cache=cache, memo=_shadow_memo):
                _sub_binds.add(_x)
    return _sub_binds
def _coerce_test_files(test_files) -> list[str]:
    try:
        items = list(test_files)
    except TypeError as _e:
        log_swallowed(__name__, _e,
                      context=f'_coerce_test_files:{type(_e).__name__}')
        return []
    paths: list[str] = []
    skipped = 0
    for item in items:
        try:
            path = os.fsdecode(item)
        except (TypeError, ValueError):
            skipped += 1
            continue
        if not path or "\0" in path:
            skipped += 1
            continue
        paths.append(path)
    if skipped:
        _log.warning("[F2] 测试索引跳过 %d/%d 个非法路径条目",
                     skipped, len(items))
    return paths
def build_test_index(test_files: list[str], cache, skill_dir: str,
                      reexport: dict) -> tuple[list, set]:
    if not skill_dir:
        raise ValueError(f"无效的技能目录: {skill_dir!r}")
    test_files = _coerce_test_files(test_files)
    if len(_INDEX_MEMO) >= _INDEX_MEMO_MAX:
        _INDEX_MEMO.clear()
    index: list = []
    hits = 0
    for test_file in test_files:
        _bn = _cache_key(test_file, skill_dir)
        _fp = _file_fingerprint(test_file)
        _ti = _memo_hit_entry(_INDEX_MEMO.get(_bn), _fp)
        if _ti is not None:
            hits += 1
        else:
            _ti = _build_missing_entry(test_file, cache, _bn, _fp)
        if _ti is not None:
            index.append(_ti)
    if hits:
        _log.info(
            "[F2] 测试索引缓存命中 %d/%d 文件（per-file 指纹，内存 memo）",
            hits, len(test_files))
    return index, _compute_submodule_binds(index, reexport,
                                                skill_dir, cache)
def _file_fingerprint(test_file: str) -> list:
    try:
        with open(test_file, "rb") as handle:
            st = os.fstat(handle.fileno())
            content = handle.read()
        digest = hashlib.sha256(content).hexdigest()
        return [st.st_mtime_ns, st.st_size, digest]
    except (OSError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_file_fingerprint:{type(_e).__name__}')
        return [-1, -1, ""]
def _memo_hit_entry(entry, fp: list):
    if not (isinstance(entry, tuple) and len(entry) == 2
            and isinstance(entry[1], dict)):
        return None
    _m_fp, _m_ti = entry
    if _m_fp == fp and _m_ti.keys() >= _TI_SCHEMA_KEYS:
        return _m_ti
    return None
def clear_index_memo() -> None:
    _INDEX_MEMO.clear()
def _cache_key(test_file: str, skill_dir: str | None) -> str:
    _root_abs = os.path.abspath(skill_dir) if skill_dir else ""
    _test_abs = os.path.abspath(test_file)
    if _root_abs:
        _root = os.path.normcase(os.path.normpath(_root_abs)).replace("\\", "/")
        try:
            _rel = os.path.normcase(
                os.path.relpath(_test_abs, _root_abs)).replace("\\", "/")
            return f"{_root}|{_rel}"
        except ValueError:
            _absolute = os.path.normcase(_test_abs).replace("\\", "/")
            _log.debug(
                "[F2] 缓存键 relpath 不可计算（跨盘符形态），"
                "回退根路径与绝对文件路径: %s", test_file)
            return f"{_root}|{_absolute}"
    return os.path.normcase(_test_abs).replace("\\", "/")
@dataclass(slots=True)
class _IndexState:
    imports: dict = field(default_factory=dict)
    has_assert_global: bool = False
    module_keys: set = field(default_factory=set)
    name_to_mods: dict = field(default_factory=dict)
    module_aliases: dict = field(default_factory=dict)
    from_pkg_binds: dict = field(default_factory=dict)
    from_bind_pkgs: dict[str, set] = field(default_factory=dict)
    from_bind_records: list = field(default_factory=list)
    star_modules: set = field(default_factory=set)
    func_nodes: list = field(default_factory=list)
    infos: list[dict] = field(default_factory=list)
    local_binds: set = field(default_factory=set)
    assert_sites: list = field(default_factory=list)
    dynamic_import_sites: list = field(default_factory=list)
def _register_module(state: _IndexState, mod_name: str) -> None:
    for part in mod_name.split("."):
        state.imports.setdefault(part, set()).add(mod_name)
        state.module_keys.add(part)
def _bind_params(state: _IndexState, a: ast.arguments) -> None:
    for _p in a.posonlyargs + a.args + a.kwonlyargs:
        state.local_binds.add(_p.arg)
    if a.vararg is not None:
        state.local_binds.add(a.vararg.arg)
    if a.kwarg is not None:
        state.local_binds.add(a.kwarg.arg)
def _load_has_source(node: ast.AST, import_loads: dict,
                     expected: tuple[str, str, str]) -> bool:
    record = import_loads.get(id(node))
    sources = record[1] if record is not None else frozenset()
    return len(sources) == 1 and expected in sources
_PYTEST_ASSERTION_CALLS = frozenset({"raises", "fail"})
_PYTEST_RAISES_CALL = "raises"
_SELF_ASSERTION_METHODS = frozenset({"fail"})
def _is_assert_call(f: ast.expr, _fcls: type,
                    import_loads: dict) -> bool:
    if _fcls is ast.Name:
        return any(
            _load_has_source(f, import_loads, ("from", "pytest", name))
            for name in _PYTEST_ASSERTION_CALLS)
    if _fcls is ast.Attribute:
        if (f.attr.startswith("assert_")
                or (f.attr.startswith("assert") and len(f.attr) > 6
                    and f.attr[6].isupper())):
            return True
        if (f.attr in _SELF_ASSERTION_METHODS
                and isinstance(f.value, ast.Name)
                and f.value.id == "self"):
            return True
        return (f.attr in _PYTEST_ASSERTION_CALLS
                and _load_has_source(
                    f.value, import_loads, ("module", "pytest", "")))
    return False
def _register_from_alias(state: _IndexState, module: str, alias,
                         *, dotted: bool) -> None:
    base = module.rsplit(".", maxsplit=1)[-1]
    if alias.name == "*":
        state.star_modules.add(base)
        return
    bind = alias.asname or alias.name
    state.name_to_mods.setdefault(bind, set()).add(base)
    state.from_pkg_binds[bind] = alias.name
    state.from_bind_records.append((bind, alias.name, module if dotted else base))
def _handle_import_from(state: _IndexState, node) -> None:
    if not (node.module and not node.level):
        return
    _register_module(state, node.module)
    dotted = "." in node.module
    for alias in node.names:
        _register_from_alias(state, node.module, alias, dotted=dotted)
def _is_import_module_ref(func: ast.expr,
                          cls: type, import_loads: dict) -> bool:
    if cls is ast.Attribute:
        return (func.attr == "import_module"
                and _load_has_source(
                    func.value, import_loads, ("module", "importlib", "")))
    if cls is ast.Name:
        return _load_has_source(
            func, import_loads, ("from", "importlib", "import_module"))
    return False
def _literal_string(node) -> str | None:
    if (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and node.value):
        return node.value
    return None
def _call_keyword_value(call: ast.Call, name: str):
    return next((keyword.value for keyword in call.keywords
                 if keyword.arg == name), None)
def _dynamic_import_name(call: ast.Call) -> str | None:
    name_node = (call.args[0] if call.args
                 else _call_keyword_value(call, "name"))
    module_name = _literal_string(name_node)
    if module_name is None or not module_name.startswith("."):
        return module_name
    package_node = (call.args[1] if len(call.args) > 1
                    else _call_keyword_value(call, "package"))
    package = _literal_string(package_node)
    if package is None:
        return None
    try:
        return util.resolve_name(module_name, package)
    except (ImportError, ValueError) as exc:
        _log.debug(
            "[ExtraAnalyzers] 动态导入相对模块无法解析,跳过: %s (%s)",
            module_name, exc)
        return None
def _register_dynamic_import(state: _IndexState, call: ast.Call) -> None:
    module_name = _dynamic_import_name(call)
    if module_name is None:
        return
    stdlib_names = getattr(sys, "stdlib_module_names", ())
    root_name = module_name.split(".", 1)[0]
    if root_name not in stdlib_names:
        _register_module(state, module_name)
def _handle_call(state: _IndexState, node, _chain) -> None:
    f = node.func
    _fcls = f.__class__
    state.dynamic_import_sites.append((f, _fcls, node))
    state.assert_sites.append((f, _fcls, _chain))
    _record_call_in_funcs(state, f, _fcls, _chain)
def _record_call_in_funcs(state: _IndexState, f, _fcls, _chain) -> None:
    if not _chain:
        return
    infos = [state.infos[i] for i in _chain]
    if _fcls is ast.Name:
        for fi in infos:
            fi["called"].add(f.id)
            fi["called_names"].add(f.id)
        return
    if _fcls is not ast.Attribute:
        return
    for fi in infos:
        fi["called"].add(f.attr)
    chain = dotted_name(f)
    if chain:
        for fi in infos:
            fi["chains"].add(chain)
def _propagate_asserts(state: _IndexState) -> None:
    by_name: dict[str, list] = {}
    for fi in state.infos:
        by_name.setdefault(fi["name"], []).append(fi)
    changed = True
    while changed:
        changed = False
        for fi in state.infos:
            if fi["has_assert"]:
                continue
            for callee in fi["called"]:
                if not _callee_is_asserted(callee, by_name):
                    continue
                fi["has_assert"] = True
                changed = True
                break
def _callee_is_asserted(callee: str, by_name: dict) -> bool:
    helpers = by_name.get(callee)
    return bool(helpers) and all(h["has_assert"] for h in helpers)
def _handle_import(state: _IndexState, node) -> None:
    for alias in node.names:
        _register_module(state, alias.name)
        if alias.asname:
            state.module_aliases[alias.asname] = alias.name.split(".")[-1]
        else:
            _first = alias.name.split(".")[0]
            state.module_aliases[_first] = _first
def _append_scope_info(state: _IndexState, node, name: str,
                       is_test: bool) -> tuple:
    state.func_nodes.append(node)
    state.infos.append({"name": name, "called": set(),
                        "called_names": set(), "is_test": is_test,
                        "has_assert": False, "chains": set()})
    return (len(state.func_nodes) - 1,)
def _register_func(state: _IndexState, node, _chain) -> tuple:
    state.local_binds.add(node.name)
    _bind_params(state, node.args)
    return _append_scope_info(
        state, node, node.name, is_test_function_name(node.name))
def _mark_class_bind(state: _IndexState, node) -> None:
    state.local_binds.add(node.name)
def _register_lambda(state: _IndexState, node, _chain) -> tuple:
    _bind_params(state, node.args)
    return _append_scope_info(state, node, "<lambda>", False)
def _mark_store_name(state: _IndexState, node) -> None:
    if isinstance(node.ctx, ast.Store):
        state.local_binds.add(node.id)
def _mark_except_name(state: _IndexState, node) -> None:
    if node.name:
        state.local_binds.add(node.name)
def _mark_match_bind(state: _IndexState, node) -> None:
    _mn = _match_bind_name(node)
    if _mn:
        state.local_binds.add(_mn)
_BIND_COLLECTORS = {
    ast.Import: _handle_import,
    ast.ImportFrom: _handle_import_from,
    ast.ClassDef: _mark_class_bind,
    ast.Name: _mark_store_name,
    ast.ExceptHandler: _mark_except_name,
    **dict.fromkeys(_MATCH_BIND_CLS, _mark_match_bind),
}
def _mark_assert_in_scope(state: _IndexState, chain) -> None:
    if not chain:
        state.has_assert_global = True
    for _i in chain:
        state.infos[_i]["has_assert"] = True
def _visit(state: _IndexState, node, _chain) -> tuple:
    _cls = node.__class__
    if _cls is ast.Call:
        _handle_call(state, node, _chain)
    elif _cls is ast.Assert:
        _mark_assert_in_scope(state, _chain)
    elif _cls is ast.FunctionDef or _cls is ast.AsyncFunctionDef:
        return _register_func(state, node, _chain)
    elif _cls is ast.Lambda:
        return _register_lambda(state, node, _chain)
    else:
        _collector = _BIND_COLLECTORS.get(_cls)
        if _collector is not None:
            _collector(state, node)
    return _chain
def _test_reachable_assert_infos(state: _IndexState) -> list:
    by_name: dict[str, list] = {}
    for fi in state.infos:
        by_name.setdefault(fi["name"], []).append(fi)
    index_by_id = {id(fi): i for i, fi in enumerate(state.infos)}
    reachable: set[int] = set()
    todo = deque(
        i for i, fi in enumerate(state.infos)
        if fi["is_test"] and fi["has_assert"])
    while todo:
        index = todo.popleft()
        if index in reachable:
            continue
        reachable.add(index)
        for callee in state.infos[index]["called"]:
            if not _callee_is_asserted(callee, by_name):
                continue
            for helper in by_name[callee]:
                todo.append(index_by_id[id(helper)])
    return [state.infos[i] for i in sorted(reachable)]
def _postprocess_assert_evidence(state: _IndexState,
                                 import_loads: dict) -> tuple[set, set]:
    for _f, _fcls, _ch in state.assert_sites:
        if _is_assert_call(_f, _fcls, import_loads):
            _mark_assert_in_scope(state, _ch)
    _propagate_asserts(state)
    reachable = _test_reachable_assert_infos(state)
    if reachable:
        state.has_assert_global = True
    _chains: set = set()
    _called: set = set()
    for fi in reachable:
        _called.update(fi.get("called_names", ()))
        _chains.update(fi.get("chains", ()))
    return _called, _chains
def _rebuild_from_bind_pkgs(state: _IndexState,
                            shadowed_binds: set[str]) -> None:
    by_bind: dict[str, set[tuple[str, str]]] = {}
    for bind, orig, source in state.from_bind_records:
        if bind in shadowed_binds:
            continue
        by_bind.setdefault(bind, set()).add((orig, source))
    state.from_bind_pkgs.clear()
    state.from_pkg_binds = {
        bind: next(iter(pairs))[0]
        for bind, pairs in by_bind.items() if len(pairs) == 1}
    for pairs in by_bind.values():
        if len(pairs) != 1:
            continue
        orig, source = next(iter(pairs))
        state.from_bind_pkgs.setdefault(orig, set()).add(source)
_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
_SCOPE_AUX_MEMO: weakref.WeakKeyDictionary = weakref.WeakKeyDictionary()
_SCOPE_AUX_LOCK = threading.Lock()
_SCOPE_AUX_CAP = 8192
def _scope_aux_cached(node, build, label: str):
    """按 AST 节点身份缓存「节点子树」导出的只读结果。

    `_scope_import_binding_sources` / `_scope_resolution_details` 都是
    「对某个作用域节点的整棵子树做一次遍历」的纯函数，而 `_ImportLoadSiteResolver`
    每个规则、每个作用域节点各调一次：实测 6,544 次调用只对应 709 个不同
    节点（去重率 89.2%），`_scope_resolution_details` 更占墙钟 2.33 s。

    返回值被调用方只读消费（`**details` 浅拷贝 + `.get`/`in`），故共享实例
    安全；与 `build_parent_map` 的「共享只读」契约定一致。
    """
    with _SCOPE_AUX_LOCK:
        cached = _SCOPE_AUX_MEMO.get(node)
    if cached is not None and cached[0] == label:
        return cached[1]
    result = build(node)
    with _SCOPE_AUX_LOCK:
        if len(_SCOPE_AUX_MEMO) >= _SCOPE_AUX_CAP:
            _SCOPE_AUX_MEMO.clear()
        _SCOPE_AUX_MEMO[node] = (label, result)
    return result
def _scope_import_binding_sources(node) -> dict[str, set[tuple[str, str, str]]]:
    return _scope_aux_cached(node, _build_scope_import_binding_sources,
                             "imports")
def _build_scope_import_binding_sources(node) -> dict[str, set[tuple[str, str, str]]]:
    imports: dict[str, set[tuple[str, str, str]]] = {}
    stack = list(ast.iter_child_nodes(node))
    while stack:
        child = stack.pop()
        if isinstance(child, _SCOPE_TYPES):
            continue
        if isinstance(child, ast.Import):
            for alias in child.names:
                bind = alias.asname or alias.name.split(".")[0]
                module = alias.name if alias.asname else bind
                imports.setdefault(bind, set()).add(("module", module, ""))
        elif isinstance(child, ast.ImportFrom):
            kind = "relative" if child.level else "from"
            for alias in child.names:
                if alias.name == "*":
                    continue
                bind = alias.asname or alias.name
                imports.setdefault(bind, set()).add(
                    (kind, child.module or "", alias.name))
        stack.extend(ast.iter_child_nodes(child))
    return imports
def _scope_resolution_details(node) -> dict:
    return _scope_aux_cached(node, _build_scope_resolution_details, "details")
def _build_scope_resolution_details(node) -> dict:
    globals_declared: set[str] = set()
    nonlocals: set[str] = set()
    # 作用域内直接绑定的名字（含 global 声明后的赋值）。`other` 由
    # `scope_direct_bindings` 产出，已剔除 global/nonlocal 声明名，故
    # 「声明 global 且确实被赋值」必须在此单独求交集。
    assigned: set[str] = set()
    stack = list(ast.iter_child_nodes(node))
    while stack:
        child = stack.pop()
        if isinstance(child, _SCOPE_TYPES):
            continue
        directive = _scope_directive_names(child)
        if directive is not None:
            globals_declared.update(directive[0])
            nonlocals.update(directive[1])
            continue
        bound = _binding_name_of(child)
        if bound is not None:
            assigned.add(bound)
        stack.extend(ast.iter_child_nodes(child))
    imports = _scope_import_binding_sources(node)
    non_import_bound = scope_direct_bindings(node) | _bound_param_names(node)
    binding_sites = {}
    if isinstance(node, ast.ClassDef):
        class_view = ast.Module(body=list(node.body), type_ignores=[])
        _module_level_bind_names(class_view, binding_sites)
    return {"globals": globals_declared, "nonlocals": nonlocals,
            "globals_bound": globals_declared & assigned,
            "imports": imports, "other": non_import_bound - nonlocals,
            "other_sites": binding_sites}
def _module_rebound_names(tree: ast.AST, binding_sites=None) -> set[str]:
    names = _module_level_bind_names(tree, binding_sites)
    for node in walk_nodes(tree):
        if isinstance(node, _SCOPE_TYPES):
            details = _scope_resolution_details(node)
            names.update(details["globals_bound"])
    return names
class _ImportLoadSiteResolver:
    def __init__(self, tree: ast.AST) -> None:
        module_binding_sites = {}
        module_rebounds = _module_rebound_names(tree, module_binding_sites)
        self.scopes = [{"kind": "module", "globals": set(), "nonlocals": set(),
                        "imports": _scope_import_binding_sources(tree),
                        "other": module_rebounds,
                        "other_sites": module_binding_sites}]
        self.loads: dict[int, tuple[str, frozenset]] = {}
    @classmethod
    def collect(cls, tree: ast.AST) -> dict[int, tuple[str, frozenset]]:
        resolver = cls(tree)
        resolver._visit(tree)
        return resolver.loads
    @staticmethod
    def _rebound_before_load(scope, name: str, position) -> bool:
        sites = scope.get("other_sites", {}).get(name)
        if not sites:
            return True
        return any(site <= position for site in sites)
    def _resolve_import_sources(self, name: str, position) -> frozenset:
        crossed_function = False
        for scope in reversed(self.scopes):
            kind = scope["kind"]
            if kind == "class" and crossed_function:
                continue
            if kind == "function":
                crossed_function = True
            if name in scope["globals"]:
                if name in self.scopes[0]["other"]:
                    return frozenset()
                return frozenset(self.scopes[0]["imports"].get(name, ()))
            if name in scope["nonlocals"]:
                continue
            if name in scope["other"]:
                if (kind not in {"module", "class"}
                        or (kind == "module" and crossed_function)
                        or self._rebound_before_load(scope, name, position)):
                    return frozenset()
            if name in scope["imports"]:
                return frozenset(scope["imports"][name])
        return frozenset()
    def _visit_scoped_body(self, node, kind: str, body: list) -> None:
        details = _scope_resolution_details(node)
        self.scopes.append({"kind": kind, **details})
        for stmt in body:
            self._visit(stmt)
        self.scopes.pop()
    def _visit_function(self, node) -> None:
        for decorator in node.decorator_list:
            self._visit(decorator)
        self._visit(node.args)
        if node.returns is not None:
            self._visit(node.returns)
        for type_param in getattr(node, "type_params", ()):
            self._visit(type_param)
        self._visit_scoped_body(node, "function", node.body)
    def _visit_class(self, node: ast.ClassDef) -> None:
        for decorator in node.decorator_list:
            self._visit(decorator)
        for base in node.bases:
            self._visit(base)
        for keyword in node.keywords:
            self._visit(keyword.value)
        for type_param in getattr(node, "type_params", ()):
            self._visit(type_param)
        self._visit_scoped_body(node, "class", node.body)
    def _visit_lambda(self, node: ast.Lambda) -> None:
        self._visit(node.args)
        self._visit_scoped_body(node, "function", [node.body])
    def _visit(self, node) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self._visit_function(node)
            return
        if isinstance(node, ast.ClassDef):
            self._visit_class(node)
            return
        if isinstance(node, ast.Lambda):
            self._visit_lambda(node)
            return
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            sources = self._resolve_import_sources(
                node.id, _source_position(node))
            if sources:
                self.loads[id(node)] = (node.id, sources)
        for child in ast.iter_child_nodes(node):
            self._visit(child)
def _index_children_with_scope(node, outer_chain, body_chain):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        for decorator in node.decorator_list:
            yield decorator, outer_chain
        yield node.args, outer_chain
        if node.returns is not None:
            yield node.returns, outer_chain
        for type_param in getattr(node, "type_params", ()):
            yield type_param, outer_chain
        for stmt in node.body:
            yield stmt, body_chain
        return
    if isinstance(node, ast.Lambda):
        yield node.args, outer_chain
        yield node.body, body_chain
        return
    for child in ast.iter_child_nodes(node):
        yield child, body_chain
def _index_one_test_file(tree: ast.AST):
    state = _IndexState()
    _todo = deque([(tree, ())])
    _pop = _todo.popleft
    while _todo:
        node, _chain = _pop()
        _child_chain = _visit(state, node, _chain)
        for _child, _scope in _index_children_with_scope(
                node, _chain, _child_chain):
            _todo.append((_child, _scope))
    import_loads = _ImportLoadSiteResolver.collect(tree)
    imported_names = {name for name, _sources in import_loads.values()}
    shadowed_binds = state.local_binds - imported_names
    for _n in shadowed_binds:
        state.name_to_mods.pop(_n, None)
        state.from_pkg_binds.pop(_n, None)
        state.module_aliases.pop(_n, None)
    _rebuild_from_bind_pkgs(state, shadowed_binds)
    for _f, _fcls, _call in state.dynamic_import_sites:
        if _is_import_module_ref(_f, _fcls, import_loads):
            _register_dynamic_import(state, _call)
    collectable_tests = frozenset(iter_collectable_test_functions(tree))
    for func_node, info in zip(state.func_nodes, state.infos, strict=True):
        info["is_test"] = func_node in collectable_tests
    called_names_with_assert, asserted_chains = _postprocess_assert_evidence(
        state, import_loads)
    _entry = {
        "imports": state.imports,
        "called_names_with_assert": called_names_with_assert,
        "has_assert_global": state.has_assert_global,
        "module_keys": state.module_keys,
        "name_to_mods": state.name_to_mods,
        "module_aliases": state.module_aliases,
        "star_modules": state.star_modules,
        "asserted_attr_chains": asserted_chains,
        "from_pkg_binds": state.from_pkg_binds,
        "from_bind_pkgs": state.from_bind_pkgs,
        "local_bind_names": shadowed_binds,
    }
    if _entry.keys() != _TI_SCHEMA_KEYS:
        raise RuntimeError(
            "测试索引条目键集与 _TI_SCHEMA_KEYS 漂移: "
            f"多={sorted(_entry.keys() - _TI_SCHEMA_KEYS)} "
            f"缺={sorted(_TI_SCHEMA_KEYS - _entry.keys())}")
    return _entry
def release_e_group_caches() -> dict:
    clear_index_memo()
    return {"e2_index_memo": True}
def _internal_package_roots(cache) -> frozenset[str]:
    roots: set[str] = set()
    for entry in (getattr(cache, 'valid_entries', None) or ()):
        rel_path = getattr(entry, 'rel_path', '')
        if not isinstance(rel_path, str):
            continue
        normalized = rel_path.replace('\\', '/')
        parts = [part for part in normalized.split('/') if part]
        if normalized == '__init__.py':
            skill_dir = getattr(cache, 'skill_dir', '')
            if skill_dir:
                roots.add(os.path.basename(os.path.normpath(skill_dir)))
        if len(parts) <= 1:
            continue
        roots.add(parts[1] if parts[0] == 'src' and len(parts) > 2
                  else parts[0])
    return frozenset(roots)
def imp_internal_target(imp: dict, internal_mods: set,
                        internal_roots: frozenset[str] | set[str] = frozenset()
                        ) -> str:
    if not isinstance(imp, dict):
        return ''
    _dep = imp.get('dep')
    if isinstance(_dep, str) and _dep in internal_mods:
        return _dep
    mod = imp.get('module')
    name = imp.get('name')
    mod = mod if isinstance(mod, str) else ''
    name = name if isinstance(name, str) else ''
    for dotted in (mod, name):
        if '.' not in dotted:
            continue
        root, _last = dotted.split('.', 1)[0], dotted.rsplit('.', 1)[-1]
        if root not in internal_roots:
            return ''
        if _last in internal_mods:
            return _last
    return _alias_in_internal(name, internal_mods)
def _alias_in_internal(name: str, internal_mods: set) -> str:
    if not name:
        return ''
    alias = name.rsplit('.', maxsplit=1)[-1]
    return alias if alias in internal_mods else ''
_SKIP_DECORATORS = frozenset({
    'skip', 'skipif', 'skipunless', 'expectedfailure', 'skiptest', 'xfail',
})
_SETUP_METHOD_NAMES = frozenset({
    'setUp', 'setup', 'setUpClass', 'setup_method', 'setup_class',
})
_TEARDOWN_METHOD_NAMES = frozenset({
    'tearDown', 'teardown', 'tearDownClass', 'teardown_method',
    'teardown_class',
})
_IN_PLACE_MUTATORS = frozenset({
    'append', 'extend', 'insert', 'remove', 'pop', 'popitem', 'clear',
    'update', 'add', 'discard', 'setdefault', 'sort', 'reverse',
    'appendleft', 'extendleft', 'popleft', 'rotate',
    'difference_update', 'intersection_update', 'symmetric_difference_update',
})
_CONTAINER_FACTORY_NAMES = frozenset({
    'list', 'dict', 'set', 'bytearray', 'deque', 'defaultdict', 'Counter',
    'OrderedDict',
})
def _collect_scope_bindings(func_node) -> tuple[set[str], set[str]]:
    globals_declared: set[str] = set()
    bound: set[str] = _bound_param_names(func_node)
    _collect_binding_names(func_node, bound, globals_declared)
    return globals_declared, bound
def _scope_directive_names(node) -> tuple[set[str], set[str]] | None:
    if isinstance(node, ast.Global):
        return set(node.names), set()
    if isinstance(node, ast.Nonlocal):
        return set(), set(node.names)
    return None
def _binding_name_of(node) -> str | None:
    if isinstance(node, ast.Name) and isinstance(
            node.ctx, (ast.Store, ast.Del)):
        return node.id
    if isinstance(node, ast.alias):
        return node.asname or node.name.split('.')[0]
    return pattern_capture_name(node)
def _collect_definition_time_bindings(node, bound: set[str],
                                      globals_declared: set[str]) -> None:
    for expr in _definition_binding_exprs(node):
        if isinstance(expr, ast.Lambda):
            _collect_definition_time_bindings(expr, bound, globals_declared)
            continue
        bound.update(_node_bind_names(expr))
        _collect_binding_names(expr, bound, globals_declared)
def _collect_binding_names(node, bound: set[str],
                           globals_declared: set[str]) -> None:
    for child in ast.iter_child_nodes(node):
        if _bind_scope_owner(child, bound, globals_declared):
            continue
        if child.__class__ is ast.Lambda:
            _collect_definition_time_bindings(child, bound, globals_declared)
            continue
        if _bind_scope_directive(child, bound, globals_declared):
            continue
        if _is_bare_annotation(child):
            _collect_binding_names(child.annotation, bound, globals_declared)
            continue
        _bind_child_name(child, bound)
        _collect_binding_names(child, bound, globals_declared)
def _bind_scope_owner(child, bound: set[str],
                      globals_declared: set[str]) -> bool:
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        bound.add(child.name)
        _collect_definition_time_bindings(child, bound, globals_declared)
        return True
    return False
def _bind_scope_directive(child, bound: set[str],
                          globals_declared: set[str]) -> bool:
    directive = _scope_directive_names(child)
    if directive is None:
        return False
    globals_declared.update(directive[0])
    bound.update(directive[1])
    return True
def _is_bare_annotation(child) -> bool:
    return isinstance(child, ast.AnnAssign) and child.value is None
def _bind_child_name(child, bound: set[str]) -> None:
    bound_name = _binding_name_of(child)
    if bound_name is not None:
        bound.add(bound_name)
def _decorator_tail_name(dec) -> str:
    if isinstance(dec, ast.Call):
        return _decorator_call_name(dec.func)
    return ast_name(dec)
def _parametrize_names_node(decorator: ast.Call):
    if decorator.args:
        return decorator.args[0]
    return next((keyword.value for keyword in decorator.keywords
                 if keyword.arg == 'argnames'), None)
def _parametrize_arg_names(decorator_list) -> set[str]:
    names: set[str] = set()
    for _dec in decorator_list:
        if not isinstance(_dec, ast.Call):
            continue
        if 'parametrize' not in _decorator_tail_name(_dec).lower():
            continue
        _first = _parametrize_names_node(_dec)
        if _first is None:
            continue
        if isinstance(_first, ast.Constant) and isinstance(_first.value, str):
            names.update(_p.strip()
                         for _p in _first.value.split(',') if _p.strip())
        elif isinstance(_first, (ast.List, ast.Tuple)):
            names.update(
                _elt.value.strip() for _elt in _first.elts
                if isinstance(_elt, ast.Constant)
                and isinstance(_elt.value, str) and _elt.value.strip())
    return names
def _injected_fixture_params(args, excluded: set[str]) -> bool:
    for _arg in [*args.posonlyargs, *args.args, *args.kwonlyargs]:
        if _arg.arg.startswith('_'):
            continue
        if _arg.arg in excluded:
            continue
        return True
    return False
def _decorator_call_name(func) -> str:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        root = func.value
        root_name = (root.id if isinstance(root, ast.Name)
                     else (root.attr if isinstance(root, ast.Attribute) else ''))
        return f"{root_name}.{func.attr}" if root_name else func.attr
    return ''
def _is_mock_module_name(module_name: str) -> bool:
    return 'mock' in module_name.split('.')
class TestQualityVisitor(ast.NodeVisitor):
    def __init__(self, rel_path: str):
        self.rel_path = rel_path
        self.test_classes = 0
        self.test_functions = 0
        self.assertions = 0
        self.has_assertion_evidence = False
        self.uses_setUp = False
        self.uses_tearDown = False
        self.uses_mock = False
        self.uses_skip = False
        self.uses_fixture = False
        self.naming_violations = []
        self.bare_assert_count = 0
        self.specific_assert_count = 0
        self.parameterized_count = 0
        self.subtest_count = 0
        self._ml_mutable_names: set[str] = set()
        self._module_mutable_names: set[str] = set()
        self._visited_ml_mutable_names: set[str] = set()
        self._mutated_names: set[str] = set()
        self._deferred_execution_depth = 0
        self._func_depth = 0
        self._in_test_func = False
        self._func_stack = []
        self._scope_globals_stack: list[set[str]] = []
        self._scope_bound_stack: list[set[str]] = []
        self._scope_kind_stack: list[str] = []
        self._class_collectable_stack: list[bool] = []
        self._class_parametrize_stack: list[set[str]] = []
        self._import_loads: dict = {}
        self._collectable_classes: set[ast.ClassDef] = set()
        self._collectable_functions: set[ast.AST] = set()
    @property
    def shared_mutable_refs(self) -> int:
        return len(self._ml_mutable_names & self._mutated_names)
    def _is_autouse_fixture_decorator(self, decorator) -> bool:
        """仅 `@pytest.fixture(autouse=True)`：对作用域内全部测试自动生效。

        普通 `@pytest.fixture` 只是声明夹具，不代表测试请求了它。
        """
        if not isinstance(decorator, ast.Call):
            return False
        if not any(keyword.arg == 'autouse'
                   and isinstance(keyword.value, ast.Constant)
                   and keyword.value.value is True
                   for keyword in decorator.keywords):
            return False
        func = decorator.func
        return ((_decorator_tail_name(decorator).rsplit('.', 1)[-1].lower()
                 == 'fixture')
                or any(_load_has_source(
                    func, self._import_loads, ('from', module, 'fixture'))
                    for module in ('pytest', 'pytest_asyncio')))
    @staticmethod
    def _is_usefixtures_decorator(decorator) -> bool:
        return (_decorator_tail_name(decorator).rsplit('.', 1)[-1].lower()
                == 'usefixtures')
    def _has_skip_decorator(self, decorator_list) -> bool:
        for dec in decorator_list:
            dn = _decorator_tail_name(dec).lower()
            if dn in _SKIP_DECORATORS or dn.rsplit('.', 1)[-1] in _SKIP_DECORATORS:
                return True
        return False
    def _count_parametrized(self, decorator_list) -> int:
        count = 0
        for dec in decorator_list:
            tokens = _decorator_tail_name(dec).lower()
            if isinstance(dec, ast.Call) and isinstance(dec.func, ast.Attribute):
                tokens += ' ' + self._root_name(dec.func).lower()
            if 'parametrize' in tokens or 'parameterized' in tokens:
                count += 1
        return count
    def visit_Module(self, node: ast.Module) -> None:
        _all_names, _module_level_names = _mutable_container_name_sets(node)
        self._ml_mutable_names.update(_all_names)
        self._module_mutable_names = _module_level_names
        self._collectable_classes = tree_collectable_test_classes(node)
        self._collectable_functions = set(iter_collectable_test_functions(node))
        self._import_loads = _ImportLoadSiteResolver.collect(node)
        self.generic_visit(node)
        self.has_assertion_evidence = self.assertions > 0
        if self.test_functions > 0 and not self.has_assertion_evidence:
            _evidence = _index_one_test_file(node)
            self.has_assertion_evidence = bool(
                _evidence['called_names_with_assert']
                or _evidence['asserted_attr_chains'])
    def _is_tracked_mutable(self, name: str) -> bool:
        names = (self._ml_mutable_names if self._deferred_execution_depth
                 else self._visited_ml_mutable_names)
        return name in names
    def _visit_deferred_body(self, body) -> None:
        self._deferred_execution_depth += 1
        try:
            for stmt in body:
                self.visit(stmt)
        finally:
            self._deferred_execution_depth -= 1
    def _visit_signature_exprs(self, node) -> None:
        for decorator in getattr(node, 'decorator_list', ()):
            self.visit(decorator)
        self.visit(node.args)
        if getattr(node, 'returns', None) is not None:
            self.visit(node.returns)
        for type_param in getattr(node, 'type_params', ()):
            self.visit(type_param)
    def visit_ClassDef(self, node):
        _collectable = (self._func_depth == 0
                        and node in self._collectable_classes
                        and all(self._class_collectable_stack))
        if _collectable and any(
                m in self._collectable_functions
                for m in _iter_scope_stmts_in_source_order(node.body)):
            self.test_classes += 1
        if self._has_skip_decorator(node.decorator_list):
            self.uses_skip = True
        if _collectable and any(
                self._is_usefixtures_decorator(dec)
                for dec in node.decorator_list):
            self.uses_fixture = True
        self._visit_definition_time_exprs(node)
        self._class_parametrize_stack.append(
            _parametrize_arg_names(node.decorator_list) if _collectable
            else set())
        try:
            self._visit_class_body_framescoped(node, _collectable)
        finally:
            self._class_parametrize_stack.pop()
    def _visit_definition_time_exprs(self, node) -> None:
        for dec in node.decorator_list:
            self.visit(dec)
        for base in node.bases:
            self.visit(base)
        for kw in node.keywords:
            self.visit(kw.value)
        for _tp in getattr(node, 'type_params', ()):
            self.visit(_tp)
    def _visit_class_body_framescoped(self, node: ast.ClassDef,
                                     collectable: bool) -> None:
        _pushed = False
        if self._func_depth > 0:
            _cls_globals, _cls_bound = _collect_scope_bindings(node)
            self._scope_globals_stack.append(_cls_globals)
            self._scope_bound_stack.append(_cls_bound)
            self._scope_kind_stack.append('class')
            _pushed = True
        self._class_collectable_stack.append(collectable)
        try:
            for stmt in node.body:
                self.visit(stmt)
        finally:
            self._class_collectable_stack.pop()
            if _pushed:
                self._scope_globals_stack.pop()
                self._scope_bound_stack.pop()
                self._scope_kind_stack.pop()
    def _handle_function(self, node):
        collectable_scope = (
            self._func_depth == 0
            and (not self._class_collectable_stack
                 or self._class_collectable_stack[-1]))
        is_test = node in self._collectable_functions
        self._visit_signature_exprs(node)
        self._func_stack.append(self._in_test_func)
        self._in_test_func = is_test
        self._func_depth += 1
        _globals_declared, _bound = _collect_scope_bindings(node)
        self._scope_globals_stack.append(_globals_declared)
        self._scope_bound_stack.append(_bound)
        self._scope_kind_stack.append('function')
        if is_test:
            self.test_functions += 1
            excluded = _parametrize_arg_names(node.decorator_list)
            excluded.update(*self._class_parametrize_stack)
            if self._class_collectable_stack:
                is_static = any(
                    _decorator_tail_name(dec).rsplit('.', 1)[-1]
                    == 'staticmethod'
                    for dec in node.decorator_list)
                parameters = (*node.args.posonlyargs, *node.args.args)
                if parameters and not is_static:
                    excluded.add(parameters[0].arg)
            if _injected_fixture_params(node.args, excluded):
                self.uses_fixture = True
        # setUp/tearDown 及其别名都是类方法名，模块级同名函数不是钩子。
        in_test_class = collectable_scope and bool(self._class_collectable_stack)
        if in_test_class and node.name in _SETUP_METHOD_NAMES:
            self.uses_setUp = True
        if in_test_class and node.name in _TEARDOWN_METHOD_NAMES:
            self.uses_tearDown = True
        if is_test and any(self._is_usefixtures_decorator(dec)
                           for dec in node.decorator_list):
            self.uses_fixture = True
        if collectable_scope and any(
                self._is_autouse_fixture_decorator(dec)
                for dec in node.decorator_list):
            self.uses_fixture = True
        if is_test and not re.match(r'^test_[A-Za-z0-9_]+$', node.name):
            self.naming_violations.append({
                'file': self.rel_path, 'function': node.name,
                'type': 'naming_violation', 'severity': 'low',
                'message': f"测试函数 {node.name} 不符合 test_* 命名规范",
            })
        if self._has_skip_decorator(node.decorator_list):
            self.uses_skip = True
        if is_test:
            self.parameterized_count += self._count_parametrized(
                node.decorator_list) + (1 if any(self._class_parametrize_stack)
                                       else 0)
        self._visit_deferred_body(node.body)
        self._in_test_func = self._func_stack.pop()
        self._func_depth -= 1
        self._scope_globals_stack.pop()
        self._scope_bound_stack.pop()
        self._scope_kind_stack.pop()
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._handle_function(node)
    def visit_AsyncFunctionDef(self, node):
        self._handle_function(node)
    def visit_If(self, node: ast.If) -> None:
        self.visit(node.test)
        blocks = ((node.body, node.orelse) if self._func_depth
                  else _import_time_branch_blocks(node))
        for block in blocks:
            for stmt in block:
                self.visit(stmt)
    def visit_Lambda(self, node: ast.Lambda) -> None:
        self._visit_signature_exprs(node)
        self._func_stack.append(self._in_test_func)
        self._in_test_func = False
        self._func_depth += 1
        _globals_declared, _bound = _collect_scope_bindings(node)
        self._scope_globals_stack.append(_globals_declared)
        self._scope_bound_stack.append(_bound)
        self._scope_kind_stack.append('function')
        self._visit_deferred_body([node.body])
        self._in_test_func = self._func_stack.pop()
        self._func_depth -= 1
        self._scope_globals_stack.pop()
        self._scope_bound_stack.pop()
        self._scope_kind_stack.pop()
    def visit_Assert(self, node):
        if self._in_test_func:
            self.bare_assert_count += 1
            self.assertions += 1
        self.generic_visit(node)
    def visit_Call(self, node: ast.Call) -> None:
        self._mark_inplace_mutation(node)
        self._count_assertion_call(node)
        self._count_subtest_call(node)
        self.generic_visit(node)
    def _count_assertion_call(self, node: ast.Call) -> None:
        func_name = ast_name(node.func)
        _specific = ((func_name.startswith('assert') and func_name != 'assert_')
                     or self._is_pytest_call(node.func, 'raises'))
        if _specific and self._in_test_func:
            self.specific_assert_count += 1
        _fail = func_name == 'fail' or self._is_pytest_call(node.func, 'fail')
        if self._in_test_func and (
                _specific or _fail or func_name in ('expect', 'should')):
            self.assertions += 1
    def _is_pytest_call(self, func, name: str) -> bool:
        if isinstance(func, ast.Attribute):
            return (func.attr == name
                    and _load_has_source(
                        func.value, self._import_loads, ("module", "pytest", "")))
        return _load_has_source(
            func, self._import_loads, ("from", "pytest", name))
    def _count_subtest_call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Attribute) and node.func.attr == 'subTest':
            self.subtest_count += 1
    def visit_ImportFrom(self, node):
        if ((node.module and _is_mock_module_name(node.module))
                or any(a.name == 'mock' for a in node.names)):
            self.uses_mock = True
        self.generic_visit(node)
    def visit_Import(self, node: ast.Import) -> None:
        if any(_is_mock_module_name(a.name) for a in node.names):
            self.uses_mock = True
        self.generic_visit(node)
    def _mark_inplace_mutation(self, node: ast.Call) -> None:
        func = node.func
        if (isinstance(func, ast.Attribute)
                and func.attr in _IN_PLACE_MUTATORS):
            root = self._root_name(func.value)
            if (self._is_tracked_mutable(root)
                    and self._content_write_targets_module(root)):
                self._mutated_names.add(root)
    def _mark_name_target_write(self, name: str, value) -> None:
        if value is None:
            return
        if self._func_depth == 0 and _is_mutable_container_value(value):
            self._ml_mutable_names.add(name)
            self._visited_ml_mutable_names.add(name)
        elif (self._is_tracked_mutable(name)
                and self._rebind_targets_module(name)):
            self._mutated_names.add(name)
    def _mark_content_write(self, target) -> None:
        root = self._root_name(target)
        if (self._is_tracked_mutable(root)
                and self._content_write_targets_module(root)):
            self._mutated_names.add(root)
    @staticmethod
    def _root_name(expr) -> str:
        while isinstance(expr, (ast.Subscript, ast.Attribute)):
            expr = expr.value
        return expr.id if isinstance(expr, ast.Name) else ''
    def _rebind_targets_module(self, name: str) -> bool:
        if not self._scope_globals_stack:
            return True
        if name not in self._module_mutable_names:
            return False
        return name in self._scope_globals_stack[-1]
    def _visible_bound_layers(self) -> list[set[str]]:
        _kinds = self._scope_kind_stack
        _visible = [b for b, k in zip(self._scope_bound_stack, _kinds, strict=True)
                    if k != 'class']
        if _kinds and _kinds[-1] == 'class':
            _idx = len(_kinds) - 1 - _kinds[::-1].index('class')
            _visible.append(self._scope_bound_stack[_idx])
        return _visible
    def _content_write_targets_module(self, name: str) -> bool:
        if not self._scope_globals_stack:
            return True
        if name not in self._module_mutable_names:
            return False
        if name in self._scope_globals_stack[-1]:
            return True
        return not any(name in _bound for _bound in self._visible_bound_layers())
    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            for subtarget, value in _iter_target_value_pairs(
                    target, node.value):
                if isinstance(subtarget, ast.Name):
                    self._mark_name_target_write(subtarget.id, value)
                else:
                    self._mark_content_write(subtarget)
        self.generic_visit(node)
    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        _root = self._root_name(node.target)
        if self._is_tracked_mutable(_root):
            _targets_module = (
                self._rebind_targets_module(_root)
                if isinstance(node.target, ast.Name)
                else self._content_write_targets_module(_root)
            )
            if _targets_module:
                self._mutated_names.add(_root)
        self.generic_visit(node)
    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        target = node.target
        if isinstance(target, ast.Name):
            self._mark_name_target_write(target.id, node.value)
        elif node.value is not None:
            self._mark_content_write(target)
        self.generic_visit(node)
    def visit_Delete(self, node: ast.Delete) -> None:
        for target in node.targets:
            if isinstance(target, ast.Name):
                if (self._is_tracked_mutable(target.id)
                        and self._rebind_targets_module(target.id)):
                    self._mutated_names.add(target.id)
            else:
                self._mark_content_write(target)
        self.generic_visit(node)
_MUTABLE_COMPREHENSIONS = (ast.ListComp, ast.DictComp, ast.SetComp)
def _is_mutable_container_value(value) -> bool:
    if isinstance(value, (ast.List, ast.Dict, ast.Set,
                         *_MUTABLE_COMPREHENSIONS)):
        return True
    if isinstance(value, ast.Call):
        return ast_name(value.func) in _CONTAINER_FACTORY_NAMES
    return False
def _iter_target_value_pairs(target, value):
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(item, ast.Starred) for item in target.elts)):
        for subtarget, subvalue in zip(target.elts, value.elts):
            yield from _iter_target_value_pairs(subtarget, subvalue)
        return
    yield target, value
def _assigned_mutable_names(node) -> set[str]:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, ast.AnnAssign):
        targets = (node.target,)
    else:
        return set()
    return {
        subtarget.id
        for target in targets
        for subtarget, value in _iter_target_value_pairs(target, node.value)
        if isinstance(subtarget, ast.Name) and _is_mutable_container_value(value)
    }
def _mutable_container_name_sets(tree: ast.Module) -> tuple[set[str], set[str]]:
    all_names: set[str] = set()
    module_level: set[str] = set()
    stack: list[tuple[ast.AST, bool]] = [(tree, False)]
    while stack:
        current, in_class = stack.pop()
        if current is not tree and isinstance(
                current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if isinstance(current, ast.ClassDef):
            stack.extend((child, True)
                         for child in ast.iter_child_nodes(current))
            continue
        names = _assigned_mutable_names(current)
        if names:
            all_names.update(names)
            if not in_class:
                module_level.update(names)
        stack.extend((child, in_class)
                     for child in ast.iter_child_nodes(current))
    return all_names, module_level
def _bound_param_names(func_node) -> set[str]:
    _args = getattr(func_node, 'args', None)
    if _args is None:
        return set()
    names: set[str] = set()
    for _a in (_args.posonlyargs + _args.args + _args.kwonlyargs):
        names.add(_a.arg)
    if _args.vararg:
        names.add(_args.vararg.arg)
    if _args.kwarg:
        names.add(_args.kwarg.arg)
    return names
def _assertion_density_score(fstat) -> float:
    n_funcs = max(fstat["test_functions"], 1)
    return min(max(fstat["assertions"], 0) / (n_funcs * 3.0), 1.0)
def _assertion_quality_score(visitor) -> float:
    bare = getattr(visitor, 'bare_assert_count', 0)
    specific = getattr(visitor, 'specific_assert_count', 0)
    total = bare + specific
    return specific / total if total > 0 else 0.5
_FIXTURE_FLAG_FIELDS = ('uses_setUp', 'uses_tearDown', 'uses_fixture')
def _flag_value(source, name: str) -> bool:
    if isinstance(source, dict):
        return bool(source.get(name))
    return bool(getattr(source, name, False))
def _has_fixture(source) -> bool:
    return any(_flag_value(source, name) for name in _FIXTURE_FLAG_FIELDS)
def _isolation_score(visitor) -> float:
    return 1.0 if _has_fixture(visitor) else 0.3
def _naming_score(fstat, naming_violations) -> float:
    penalty = sum(1 for nv in naming_violations
                  if nv.get("file") == fstat["file"])
    return max(0, 1.0 - penalty / max(fstat["test_functions"], 1))
def _parametrization_score(fstat, visitor) -> float:
    return min(getattr(visitor, 'parameterized_count', 0)
               / max(fstat["test_functions"], 1), 1.0)
def _shared_state_score(visitor) -> float:
    if _has_fixture(visitor):
        return 1.0
    return max(0, 1.0 - getattr(visitor, 'shared_mutable_refs', 0) * 0.1)
def _score_per_file_quality(per_file_stats, visitor_results,
                            naming_violations) -> dict:
    per_file_quality = {}
    for fstat in per_file_stats:
        fname = fstat["file"]
        visitor = visitor_results.get(fname)
        components = (
            (_assertion_density_score(fstat), 0.25),
            (_assertion_quality_score(visitor), 0.20),
            (_isolation_score(visitor), 0.15),
            (_naming_score(fstat, naming_violations), 0.15),
            (_parametrization_score(fstat, visitor), 0.10),
            (_shared_state_score(visitor), 0.15),
        )
        weighted = sum(score * weight for score, weight in components)
        per_file_quality[fname] = round(max(0.0, min(1.0, weighted)), 3)
    return per_file_quality
_TEST_FRAMEWORK_MODULE_NAMES = frozenset({'pytest', 'mock'})
_STDLIB_OR_FRAMEWORK_NAMES = (
    frozenset(getattr(sys, 'stdlib_module_names', ()))
    | _TEST_FRAMEWORK_MODULE_NAMES
)
_AGGREGATE_FLAG_FIELDS = ('uses_setUp', 'uses_tearDown', 'uses_mock',
                           'uses_skip', 'uses_fixture')
_AGGREGATE_COUNTER_FIELDS = (
    'bare_assert_count', 'specific_assert_count', 'parameterized_count',
    'subtest_count', 'shared_mutable_refs',
)
def _aggregate_visitor_metrics(visitor_results) -> dict:
    visitors = tuple(visitor_results.values())
    agg = {name: any(getattr(v, name) for v in visitors)
           for name in _AGGREGATE_FLAG_FIELDS}
    agg.update({name: sum(getattr(v, name) for v in visitors)
                for name in _AGGREGATE_COUNTER_FIELDS})
    agg['naming_violations'] = [
        violation for v in visitors for violation in v.naming_violations]
    return agg
def _apply_structure_metrics(result, agg, test_entries,
                             internal_mods: set,
                             internal_roots: frozenset[str]) -> None:
    test_categories = _classify_test_categories(
        test_entries, internal_mods, internal_roots)
    naming_violations = agg['naming_violations']
    result.findings.extend(naming_violations[:10])
    result.metrics['uses_setUp'] = agg['uses_setUp']
    result.metrics['uses_tearDown'] = agg['uses_tearDown']
    result.metrics['uses_mock'] = agg['uses_mock']
    result.metrics['uses_skip'] = agg['uses_skip']
    result.metrics['uses_fixture'] = agg['uses_fixture']
    result.metrics['test_categories'] = test_categories
    result.metrics['naming_violations'] = len(naming_violations)
    result.metrics['has_isolation'] = _has_fixture(agg)
def _apply_assertion_metrics(result, agg) -> None:
    bare = agg['bare_assert_count']
    specific = agg['specific_assert_count']
    total = bare + specific
    result.metrics['bare_assertions'] = bare
    result.metrics['specific_assertions'] = specific
    result.metrics['assertion_quality_pct'] = round(
        specific / total * 100 if total > 0 else 0, 1)
def _apply_size_metrics(result, test_entries, valid_entries) -> None:
    test_loc = sum(getattr(te, 'lines', 0) or 0 for te in test_entries)
    source_loc = sum(getattr(e, 'lines', 0) or 0 for e in valid_entries
                     if not getattr(e, 'is_test', False))
    result.metrics['test_loc'] = test_loc
    result.metrics['source_loc'] = source_loc
    result.metrics['test_to_code_ratio'] = round(
        test_loc / max(source_loc, 1), 2)
def _apply_shared_state_finding(result, agg, visitor_results) -> None:
    shared_refs = agg['shared_mutable_refs']
    for rel_path, visitor in visitor_results.items():
        file_refs = getattr(visitor, 'shared_mutable_refs', 0)
        if file_refs <= 0 or _has_fixture(visitor):
            continue
        result.findings.append({
            'type': 'shared_mutable_state', 'severity': 'medium',
            'file': rel_path, 'count': file_refs,
            'message': (f'{rel_path}: {file_refs} 个模块级可变对象但无夹具'
                        '(setUp/tearDown/fixture)，可能存在测试间状态泄漏'),
        })
    result.metrics['shared_mutable_refs'] = shared_refs
@dataclass
class QualityRun:
    result: object
    visitor_results: dict
    test_entries: list
    cache: object
    per_file_stats: list
    test_result: object
    test_smells: list
    assertion_density: float
    passed: int
    started_at: float
def finalize_test_quality(run: QualityRun) -> None:
    result = run.result
    agg = _aggregate_visitor_metrics(run.visitor_results)
    _apply_structure_metrics(
        result, agg, run.test_entries,
        getattr(run.cache, 'internal_mods', None) or set(),
        _internal_package_roots(run.cache))
    _apply_assertion_metrics(result, agg)
    _apply_size_metrics(result, run.test_entries,
                        getattr(run.cache, 'valid_entries', None) or ())
    result.metrics['parameterized_tests'] = agg['parameterized_count']
    result.metrics['subtest_uses'] = agg['subtest_count']
    _apply_shared_state_finding(result, agg, run.visitor_results)
    _finalize_execution_verdict(run)
    _apply_quality_grade(result, _score_per_file_quality(
        run.per_file_stats, run.visitor_results, agg['naming_violations']))
    result.elapsed_ms = (time.perf_counter() - run.started_at) * 1000
def _classify_test_categories(test_entries, internal_mods: set,
                              internal_roots: frozenset[str]) -> dict:
    test_categories = {'unit': 0, 'integration': 0, 'e2e': 0}
    for te in test_entries:
        category = _classify_one_test_entry(
            te, internal_mods, internal_roots)
        test_categories[category] += 1
    return test_categories
_TEST_CATEGORY_BY_IMPORT_FLAGS = {
    (False, False): 'unit',
    (True, False): 'integration',
    (False, True): 'e2e',
    (True, True): 'e2e',
}
def _relative_import_lines(tree) -> set:
    if tree is None:
        return set()
    return {node.lineno for node in walk_nodes(tree)
            if isinstance(node, ast.ImportFrom) and node.level}
def _classify_one_test_entry(te, internal_mods: set,
                             internal_roots: frozenset[str]) -> str:
    _relative_lines = _relative_import_lines(getattr(te, 'tree', None))
    has_internal_imports = False
    has_external_imports = False
    for imp in (getattr(te, 'imports', None) or ()):
        if not isinstance(imp, dict):
            continue
        if (imp_internal_target(imp, internal_mods, internal_roots)
                or imp.get('line') in _relative_lines):
            has_internal_imports = True
        elif imp.get('dep', '') not in _STDLIB_OR_FRAMEWORK_NAMES:
            has_external_imports = True
        if has_internal_imports and has_external_imports:
            break
    return _TEST_CATEGORY_BY_IMPORT_FLAGS[
        (has_internal_imports, has_external_imports)]
def _collection_error_count(test_result) -> int:
    return len(getattr(test_result, 'collection_errors', None) or ())
def _finalize_execution_verdict(run: QualityRun) -> None:
    test_result = run.test_result
    total = max(test_result.testsRun or 0, 0)
    if total == 0:
        _verdict_zero_run(run, total)
        return
    _degraded = getattr(test_result, "degraded_reason", None)
    if _degraded:
        _verdict_partial_degraded(run, total, _degraded)
        return
    if (len(test_result.failures) == 0 and len(test_result.errors) == 0
            and _collection_error_count(test_result) == 0):
        _verdict_all_clean(run, total)
        return
    _verdict_with_failures(run, total)
def _verdict_zero_run(run: QualityRun, total: int) -> None:
    run.result.status = "warn"
    run.result.score = 30
    _collection_n = _collection_error_count(run.test_result)
    if _collection_n:
        run.result.summary = (
            f"发现 {len(run.test_entries)} 个测试文件但 {total} 个测试用例执行，"
            f"{_collection_n} 个文件采集失败（收集期导入错误），须先修复采集失败")
        return
    run.result.summary = (
        f"发现 {len(run.test_entries)} 个测试文件但 {total} 个测试用例执行")
def _verdict_partial_degraded(run: QualityRun, total: int,
                              degraded_reason: str) -> None:
    test_result = run.test_result
    _failed = (len(test_result.failures) + len(test_result.errors)
               + _collection_error_count(test_result))
    run.result.status = "warn"
    run.result.score = 60
    run.result.summary = (
        f"{run.passed}/{total} 通过（仅已完成批次），"
        f"部分批次未完成（{degraded_reason}）"
        + (f"，{_failed} 失败/错误" if _failed else "")
        + "；测试证据不完整，须在源码稳定窗口复跑确认")
def _verdict_all_clean(run: QualityRun, total: int) -> None:
    test_result = run.test_result
    _skipped_n = getattr(
        test_result, 'skipped_method_count', len(test_result.skipped))
    _partial_skipped = getattr(test_result, 'partial_subtest_skips', 0)
    if _skipped_n >= total and not _partial_skipped:
        run.result.status = "warn"
        run.result.score = 30
        run.result.summary = (f"{total} 个测试全部被跳过（skipped），"
                              "无实际执行证据，须排查 skip 成因")
        return
    run.result.status = "pass"
    run.result.score = 90 if run.test_smells else 100
    _executed_n = total - _skipped_n
    _passed_n = max(0, min(run.passed, _executed_n))
    _expected_n = max(0, _executed_n - _passed_n)
    _skip_note = f", {_skipped_n} 个跳过" if _skipped_n else ""
    if _partial_skipped:
        _skip_note += f"（含 {_partial_skipped} 个部分 subTest 跳过）"
    _expected_note = (
        f", {_expected_n} 个预期失败/意外通过(xfail/xpass)"
        if _expected_n else "")
    run.result.summary = (
        f"{_passed_n}/{total} 个测试通过{_skip_note}{_expected_note} "
        f"({len(run.test_entries)} 文件, 断言密度 {run.assertion_density:.1f})")
def _verdict_with_failures(run: QualityRun, total: int) -> None:
    test_result = run.test_result
    _collection_n = _collection_error_count(test_result)
    _failed_n = getattr(
        test_result, 'failed_method_count', len(test_result.failures))
    _error_n = getattr(
        test_result, 'error_method_count', len(test_result.errors))
    _failed_or_error_n = getattr(
        test_result, 'failed_or_error_method_count', _failed_n + _error_n)
    fail_rate = (_failed_or_error_n + _collection_n) / total
    run.result.status = "warn"
    run.result.score = max(0, int(100 * (1 - fail_rate)))
    run.result.summary = (f"{run.passed}/{total} 通过, "
                          f"{_failed_n} 失败, {_error_n} 错误")
    if _collection_n:
        run.result.summary += f", {_collection_n} 个文件采集失败"
def _apply_quality_grade(result, per_file_quality: dict) -> None:
    avg_quality = sum(per_file_quality.values()) / max(len(per_file_quality), 1)
    result.metrics['test_quality_score'] = round(avg_quality, 3)
    quality_grade = "high" if avg_quality >= 0.80 else ("medium" if avg_quality >= 0.50 else "low")
    result.metrics['test_quality_grade'] = quality_grade
    result.metrics['test_quality_per_file'] = per_file_quality
    result.metrics['test_quality_summary'] = (
        f"test quality: {round(avg_quality*100,1)}% "
        f"(grade={quality_grade}), {len(per_file_quality)} files")
    if quality_grade == "low" and result.status == "pass":
        result.score = max(result.score - 15, 50)
        result.summary += f" [quality_low({round(avg_quality*100,1)}%)]"
    elif quality_grade == "medium" and result.status == "pass":
        result.score = max(result.score - 5, 70)
        result.summary += f" [quality_med({round(avg_quality*100,1)}%)]"
def _entry_path_key(path: str) -> str:
    return os.path.normcase(os.path.abspath(path))
def collect_test_entries(cache) -> list:
    test_entries = []
    for e in (getattr(cache, 'entries', None) or ()):
        if e.is_test and e.tree is not None:
            test_entries.append(e)
    _seen_paths = {_entry_path_key(e.path) for e in test_entries}
    for entry in (getattr(cache, 'test_dir_entries', None) or ()):
        _key = _entry_path_key(entry.path)
        if _key not in _seen_paths and entry.tree is not None:
            test_entries.append(entry)
            _seen_paths.add(_key)
    return test_entries
_TEST_INFRA_BASENAMES = frozenset({"conftest.py", "__init__.py"})
_TEST_DATA_DIRNAMES = frozenset(TEST_ARTIFACT_DIRS - TEST_DIR_CANDIDATES_LOWER)


def _is_test_infra_file(file_path: str) -> bool:
    """测试基础设施与测试数据文件不是测试用例文件。

    ``conftest.py`` 的职责是会话级夹具与生命周期钩子
    （``pytest_sessionfinish`` 等）；``__init__.py`` 仅为包标记；``fixtures``
    目录承载测试数据。三者按 pytest 收集规则均不会被收集为用例，按「空测试
    文件」上报会误伤标准布局（含测试目录内的包标记与夹具源码），压低测试
    质量分并掩盖真正该拆分的空套件。
    """
    segments = str(file_path or "").replace("\\", "/").split("/")
    if segments[-1].lower() in _TEST_INFRA_BASENAMES:
        return True
    return any(_seg.lower() in _TEST_DATA_DIRNAMES for _seg in segments[:-1])


def _has_test_intent(file_path: str, skill_dir: str | None = None) -> bool:
    norm = str(file_path or "").replace("\\", "/")
    if not norm:
        return False
    segments = norm.split("/")
    if any(is_test_dir_candidate(_seg) for _seg in segments[:-1]):
        return True
    if is_test_source_basename(segments[-1]):
        return True
    _open_path = file_path
    if skill_dir and not os.path.isabs(file_path):
        _open_path = os.path.join(skill_dir, file_path)
    _source = _read_test_source(_open_path, '_has_test_intent', None)
    if _source is None:
        return False
    tree = _parse_tree_or_none(_source, _open_path, '_has_test_intent')
    return tree is not None and module_imports_test_framework(tree)
def detect_test_smells(per_file_stats: list, skill_dir: str | None = None) -> list:
    test_smells = []
    for fstat in per_file_stats:
        if (fstat["test_functions"] > 0 and fstat["assertions"] == 0
                and not fstat.get("has_assertion_evidence", False)):
            test_smells.append({
                "file": fstat["file"],
                "type": "no_assertions",
                "severity": "high",
                "message": f"{fstat['file']}: {fstat['test_functions']} 个测试函数但 0 个断言",
            })
        if (fstat["test_functions"] == 0 and fstat["test_classes"] == 0
                and not _is_test_infra_file(fstat["file"])
                and _has_test_intent(fstat["file"], skill_dir)):
            test_smells.append({
                "file": fstat["file"],
                "type": "empty_test_file",
                "severity": "medium",
                "message": f"{fstat['file']}: 测试文件中无任何测试函数或测试类",
            })
    return test_smells
def _is_summary_nodeid_candidate(candidate: str) -> bool:
    file_key, separator, test_id = candidate.partition('::')
    if not separator:
        return candidate.endswith('.py')
    return (file_key.endswith('.py')
            and ('[' not in test_id or candidate.endswith(']')))
def _separator_head(body: str) -> str | None:
    _depth = 0
    for _idx, _char in enumerate(body):
        if _char == '[':
            _depth += 1
        elif _char == ']':
            _depth = max(0, _depth - 1)
        elif _depth == 0 and body.startswith(' - ', _idx):
            return body[:_idx].strip()
    if _depth > 0:
        for _match in re.finditer(r' - ', body):
            _candidate = body[:_match.start()].strip()
            if _is_summary_nodeid_candidate(_candidate):
                return _candidate
    return None
def _file_path_from_body(body: str) -> str:
    _head = _separator_head(body)
    if _head is not None and _head.endswith('.py'):
        return _head
    _text = body.strip()
    if _text.endswith('.py'):
        return _text
    return body.split(' - ', 1)[0].strip()
def _summary_body(_s: str) -> str:
    return (_s.split(' ', 1)[1]
            if _s.startswith(('FAILED ', 'ERROR ')) and ' ' in _s else _s)
def summary_line_nodeid(_s: str) -> str:
    _body = _summary_body(_s)
    _head = _separator_head(_body)
    if _head is not None:
        return _head
    if '::' not in _body:
        return _file_path_from_body(_body)
    return _body.strip()
_TB_TEXT_LIMIT = 500
_MAX_FINDINGS_PER_SOURCE = 20
_TB_SECTION_RE = re.compile(r'^_{3,}\s*(.+?)\s*_{3,}$')
# 计数令牌与 pytest 终端汇总 KNOWN_TYPES 对齐：reruns? 为 pytest-rerunfailures
# 计数令牌，subtests passed/failed/skipped 为 pytest 9 原生 subTest 计数令牌。
# 任一令牌缺失都会使整行不匹配，parse_pytest_summary 返回 None，执行证据
# 整批降级为 parse_failed。
_PYTEST_SUMMARY_LINE_RE = re.compile(
    r'^\s*(?:=+\s+)?'
    r'(?:(?:no tests ran|'
    r'[\d,]+ (?:passed|failed|errors?|skipped|xfailed|xpassed|warnings?|deselected'
    r'|reruns?|subtests (?:passed|failed|skipped)))'
    r'[,; ]*)+'
    r'in \d[\d.]*s')
_PYTEST_THOUSANDS_SEP_RE = re.compile(r'(?<=\d),(?=\d)')
def _is_failures_errors_header(line: str) -> bool:
    return line.startswith('====') and ('FAILURES' in line or 'ERRORS' in line)
def _is_short_summary_header(line: str) -> bool:
    return line.startswith('====') and 'short test summary info' in line
def _pytest_output_zone(out: str, is_header, *, skip_repeated_headers=False,
                        fallback: str = '') -> str:
    lines = out.split('\n')
    start = next((i for i, line in enumerate(lines) if is_header(line)), None)
    if start is None:
        return fallback
    zone: list[str] = []
    for line in lines[start + 1:]:
        if line.startswith('===='):
            if skip_repeated_headers and is_header(line):
                continue
            break
        zone.append(line)
    return '\n'.join(zone)
def _extract_pytest_traceback_sections(out: str) -> dict:
    zone = _pytest_output_zone(
        out, _is_failures_errors_header, skip_repeated_headers=True)
    sections: dict[str, list[str]] = {}
    for name, body in _split_tb_sections(zone):
        sections.setdefault(name, []).append(body.strip()[:_TB_TEXT_LIMIT])
    return sections
def _split_tb_sections(zone: str):
    name = None
    buf: list[str] = []
    for line in zone.split('\n'):
        line = line.rstrip('\r')
        match = _TB_SECTION_RE.match(line)
        if match:
            if name is not None:
                yield name, '\n'.join(buf)
            name, buf = match.group(1).strip(), []
        elif name is not None:
            buf.append(line)
    if name is not None:
        yield name, '\n'.join(buf)
def _lookup_pytest_traceback(tb_sections: dict | None, nodeid: str,
                             fallback: str) -> str:
    if not tb_sections or '::' not in nodeid:
        return fallback
    candidates = _traceback_candidates(nodeid)
    hit = _first_present_section(tb_sections, candidates, nodeid)
    if hit is not None:
        return hit
    wrapped = _first_present_section(
        tb_sections, _wrapped_tb_names(candidates), nodeid)
    return wrapped if wrapped is not None else fallback
def _nodeid_parts(nodeid: str) -> list[str]:
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(nodeid):
        char = nodeid[index]
        if char == '[':
            depth += 1
        elif char == ']':
            depth = max(0, depth - 1)
        elif depth == 0 and nodeid.startswith('::', index):
            parts.append(nodeid[start:index])
            index += 2
            start = index
            continue
        index += 1
    parts.append(nodeid[start:])
    return parts
def _traceback_candidates(nodeid: str) -> list[str]:
    parts = _nodeid_parts(nodeid)
    return ['.'.join(parts[1:]), parts[-1]]
_ERROR_AT_SETUP_OF = 'ERROR at setup of '
_ERROR_AT_TEARDOWN_OF = 'ERROR at teardown of '
def _wrapped_tb_names(candidates) -> list[str]:
    return [prefix + cand
            for cand in candidates
            for prefix in (_ERROR_AT_SETUP_OF, _ERROR_AT_TEARDOWN_OF)]
def _unwrapped_tb_name(name: str) -> str:
    for prefix in (_ERROR_AT_SETUP_OF, _ERROR_AT_TEARDOWN_OF):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name
def _summary_nodeid_with_sections(_s: str, tb_sections: dict | None) -> str:
    if not tb_sections:
        return summary_line_nodeid(_s)
    body = _summary_body(_s).strip()
    marker = body.find('::')
    if marker < 0:
        return summary_line_nodeid(_s)
    file_key = body[:marker].strip()
    matches: list[str] = []
    for raw_name in tb_sections:
        name = _unwrapped_tb_name(raw_name)
        name_pattern = re.escape(name).replace(r'\.', r'(?:::|\.)')
        match = re.match(
            rf'{re.escape(file_key)}::{name_pattern}(?= - |$)', body)
        if match is not None:
            matches.append(match.group(0))
    return max(matches, key=len) if matches else summary_line_nodeid(_s)
def _teardown_error_count(tb_sections: dict | None) -> int:
    if not tb_sections:
        return 0
    return sum(
        len(bodies) for name, bodies in tb_sections.items()
        if name.startswith(_ERROR_AT_TEARDOWN_OF))
def _select_traceback_body(bodies: list[str], nodeid: str) -> str | None:
    if len(bodies) == 1:
        return bodies[0]
    file_key = nodeid.split('::', 1)[0].strip().replace('\\', '/')
    if not file_key:
        return None
    matches = [body for body in bodies
               if file_key in body.replace('\\', '/')]
    return matches[0] if len(matches) == 1 else None
def _first_present_section(sections: dict, names, nodeid: str):
    for name in names:
        bodies = sections.get(name)
        if not bodies:
            continue
        hit = _select_traceback_body(bodies, nodeid)
        if hit is not None:
            return hit
    return None
def _collect_pytest_summary_lines(out: str, prefix: str, count_limit: int,
                                  bucket: list, seen_nodes: set,
                                  tb_sections: dict | None) -> None:
    for _line in out.split('\n'):
        _s = _line.rstrip()
        if not _s.startswith(prefix):
            continue
        _node = _summary_nodeid_with_sections(_s, tb_sections)
        if '::' not in _node:
            continue
        if len(bucket) < count_limit and _node not in seen_nodes:
            _tb = _lookup_pytest_traceback(
                tb_sections, _node, _s[:_TB_TEXT_LIMIT])
            bucket.append((_s, _tb))
            seen_nodes.add(_node)
@dataclass(frozen=True)
class _PytestLineScope:
    failed_count: int
    error_count: int
    tb_sections: dict | None = None
def _collect_pytest_collection_errors(zone: str, test_result) -> None:
    for line in zone.split('\n'):
        text = line.rstrip()
        if not text.startswith('ERROR '):
            continue
        node_id = summary_line_nodeid(text)
        if not node_id or '::' in node_id or not node_id.endswith('.py'):
            continue
        if node_id not in test_result.collection_errors:
            test_result.collection_errors.append(node_id)
def _collect_pytest_fail_err_lines(out: str, test_result,
                                   scope: _PytestLineScope) -> None:
    _collect_pytest_summary_lines(out, 'FAILED ', scope.failed_count,
                                  test_result.failures, set(),
                                  scope.tb_sections)
    _collect_pytest_summary_lines(out, 'ERROR ', scope.error_count,
                                  test_result.errors, set(),
                                  scope.tb_sections)
class PytestSummaryResult:
    def __init__(self, total: int, skipped: int):
        self.testsRun = total
        self.failures = []
        self.errors = []
        self.skipped = [None] * skipped
        self.collection_errors: list[str] = []
def parse_pytest_summary(out: str):
    _counts = _extract_summary_counts(_select_summary_scope(out))
    if _counts is None:
        return None
    _passed, _failed, _errors, _skipped, _xfailed, _xpassed = _counts
    test_result = PytestSummaryResult(0, _skipped)
    _tb_sections = _extract_pytest_traceback_sections(out)
    _short_zone = _pytest_output_zone(
        out, _is_short_summary_header, fallback=out)
    _collect_pytest_fail_err_lines(
        _short_zone, test_result,
        _PytestLineScope(_failed, _errors, _tb_sections))
    _collect_pytest_collection_errors(_short_zone, test_result)
    case_level_errors = max(_errors - len(test_result.collection_errors), 0)
    _pad_missing_fail_err(test_result, out, _failed, case_level_errors)
    independent_errors = max(
        case_level_errors - _teardown_error_count(_tb_sections), 0)
    test_result.testsRun = (
        _passed + _failed + independent_errors + _skipped + _xfailed + _xpassed)
    return test_result, _passed
def _select_summary_scope(out: str) -> str:
    _summary_lines = [ln for ln in out.split('\n')
                      if _PYTEST_SUMMARY_LINE_RE.match(ln)]
    return _summary_lines[-1] if _summary_lines else ''
_SUMMARY_COUNT_PATTERNS: tuple = (
    ('passed', r'(\d+) passed'),
    ('failed', r'(\d+) failed'),
    ('errors', r'(\d+) errors?'),
    ('skipped', r'(\d+) skipped'),
    ('xfailed', r'(\d+) xfailed'),
    ('xpassed', r'(\d+) xpassed'),
)
def _extract_summary_counts(summary_scope: str):
    scope = _PYTEST_THOUSANDS_SEP_RE.sub('', summary_scope)
    counts: dict[str, int] = {}
    _any_count_matched = False
    for _name, _pat in _SUMMARY_COUNT_PATTERNS:
        _m = re.search(_pat, scope)
        if _m is not None:
            _any_count_matched = True
            counts[_name] = int(_m.group(1))
        else:
            counts[_name] = 0
    if not (_any_count_matched
            or re.search(r'(\d+) deselected', scope)
            or re.search(r'no tests ran', scope)):
        return None
    return (counts['passed'], counts['failed'], counts['errors'],
            counts['skipped'], counts['xfailed'], counts['xpassed'])
def _pad_missing_fail_err(test_result, out: str, failed: int, errors: int) -> None:
    _err_ctx = '\n'.join([_l for _l in out.split('\n')
                          if 'ERROR' in _l or 'Traceback' in _l
                          or _l.startswith('E ')][-8:])
    if not _err_ctx:
        _err_ctx = '\n'.join(out.strip().split('\n')[-8:])
    _pad_entries(test_result.errors, errors,
                 "pytest error (no per-test line)", _err_ctx)
    _pad_entries(test_result.failures, failed,
                 "pytest failed (no per-test line)", _err_ctx)
def _pad_entries(entries: list, target: int, label: str, context: str) -> None:
    while len(entries) < target:
        entries.append((label, context[:_TB_TEXT_LIMIT]))
def _parse_test_file(tc_text: str) -> str:
    _text = str(tc_text)
    if _text.startswith(('FAILED ', 'ERROR ')):
        _nodeid = summary_line_nodeid(_text)
        if '::' in _nodeid:
            _candidate = _nodeid.split('::', 1)[0].strip()
            if _candidate.endswith('.py'):
                return _candidate
    for tok in _text.split()[:3]:
        if "::" in tok and ".py" in tok:
            return tok.split("::")[0]
    return ""
def collect_test_findings(result, test_result, test_smells: list) -> None:
    _failures = getattr(test_result, 'failures', None) or ()
    _errors = getattr(test_result, 'errors', None) or ()
    if _failures:
        for tc, tb in _failures[:_MAX_FINDINGS_PER_SOURCE]:
            result.findings.append({
                "type": "test_failure",
                "file": _parse_test_file(tc),
                "test": str(tc),
                "traceback": str(tb)[:_TB_TEXT_LIMIT],
            })
    if _errors:
        for tc, tb in _errors[:_MAX_FINDINGS_PER_SOURCE]:
            result.findings.append({
                "type": "test_error",
                "file": _parse_test_file(tc),
                "test": str(tc),
                "traceback": str(tb)[:_TB_TEXT_LIMIT],
            })
    _collection_errors = getattr(test_result, 'collection_errors', None) or ()
    for _path in _collection_errors[:_MAX_FINDINGS_PER_SOURCE]:
        result.findings.append({
            "type": "test_error",
            "file": str(_path),
            "test": str(_path),
            "traceback": "pytest 收集期导入失败，该文件的用例未执行",
        })
    result.findings.extend(test_smells[:_MAX_FINDINGS_PER_SOURCE])

from __future__ import annotations

__all__ = [
    "GENERIC_PROJECT_PRUNE_DIRS",
    "dynamic_module_binding_names",
    "extract_all_surface",
    "is_main_guard_if",
    "iter_match_capture_names",
    "iter_module_level_imports_tc",
    "iter_module_level_nodes",
    "iter_module_level_nodes_tc",
    "iter_static_edge_nodes",
    "iter_target_py_files",
    "iter_walrus_expr_bindings",
    "layout_of",
    "package_roots_for",
    "project_package_root",
    "prune_target_dirs",
    "relative_import_base",
    "resolve_namespace_dir",
    "run_api_integrity_checks",
    "static_all_declarations",
    "static_all_names",
    "static_seq_bindings",
    "strip_root_prefix",
]
import ast
import importlib.util
import os
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NamedTuple, Protocol

from jwsgj.diag_shared_ast_bindings import (
    collect_binding_names,
    exec_scope_declarations,
    import_stmt_binds,
)
from jwsgj.diag_shared_ast_nodes import (
    TYPE_ALIAS_NODES,
    assign_targets_value,
    is_constant_expr_stmt,
    is_main_check,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_surface import (
    EXPORT_BRANCH_ASSUME,
    _import_time_loop_visibility,
    _is_globals_call,
    import_time_branch_visibility,
    replay_export_surface,
    resolve_export_elts,
)
from jwsgj.diag_shared_source_core import (
    guard_tree,
    is_consolidated_code,
    load_source_tree,
)
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    import_key,
    is_backup_snapshot_dir,
    is_test_file_path,
)
from jwsgj.skill_profile import (
    detect_layout,
)

logger = get_module_logger(__name__)
class _AstCache(Protocol):
    def get_ast(self, filepath: str) -> ast.AST | None: ...
_SEQUENCE_MUTATION_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear", "sort",
    "reverse", "update", "add", "discard", "difference_update",
    "intersection_update", "symmetric_difference_update",
})
_SEQUENCE_READONLY_METHODS = frozenset({"count", "index", "copy"})
_SEQUENCE_READONLY_CALLS = frozenset({
    "all", "any", "bool", "format", "frozenset", "getattr", "hasattr",
    "isinstance", "issubclass", "iter", "len", "list", "max", "min",
    "print", "repr", "reversed", "set", "sorted", "str", "sum",
    "tuple", "type",
})
_TRY_TYPES = (ast.Try,) + ((ast.TryStar,) if hasattr(ast, "TryStar") else ())
class _AllSurface(NamedTuple):
    names: list[str]
    complete: bool
    ordered: bool = True
def _replay_module_exports(tree: ast.Module):
    return replay_export_surface(
        tree, branches=EXPORT_BRANCH_ASSUME,
        bindings=static_seq_bindings(tree),
        _side_effect_calls=_called_all_mutation_call_ids(tree))
def extract_all_surface(tree: ast.Module) -> _AllSurface | None:
    replay = _replay_module_exports(tree)
    if not replay.declared:
        return None
    return _AllSurface(replay.names, replay.exact, replay.ordered)
def _tc_flagged(stmts, flag: bool) -> list[tuple[ast.stmt, bool]]:
    return [(n, flag) for n in stmts]
def _tc_if_blocks(node: ast.If, under_tc: bool,
                  typing_aliases: set[str] | None,
                  type_checking_names: set[str] | None
                  ) -> list[tuple[ast.stmt, bool]]:
    if isinstance(node.test, ast.Constant):
        body_visible = bool(node.test.value)
        return (_tc_flagged(node.body, under_tc or not body_visible)
                + _tc_flagged(node.orelse, under_tc or body_visible))
    body_visible = import_time_branch_visibility(
        node.test, typing_aliases, type_checking_names)
    blocks = _tc_flagged(
        node.body, under_tc or body_visible is False)
    blocks += _tc_flagged(
        node.orelse, under_tc or body_visible is True)
    return blocks
def _tc_loop_blocks(node: ast.stmt, under_tc: bool, *,
                    typing_aliases: set[str] | None,
                    type_checking_names: set[str] | None
                    ) -> list[tuple[ast.stmt, bool]]:
    body_visible, else_visible = _import_time_loop_visibility(
        node, typing_aliases, type_checking_names)
    return (_tc_flagged(node.body, under_tc or body_visible is False)
            + _tc_flagged(node.orelse, under_tc or else_visible is False))


def _tc_try_blocks(node, under_tc: bool) -> list[tuple[ast.stmt, bool]]:
    blocks = _tc_flagged(node.body, under_tc)
    for _h in node.handlers:
        blocks += _tc_flagged(_h.body, under_tc)
    blocks += _tc_flagged(node.orelse, under_tc)
    blocks += _tc_flagged(node.finalbody, under_tc)
    return blocks
def _tc_match_blocks(node: ast.stmt, under_tc: bool) -> list[tuple[ast.stmt, bool]]:
    blocks: list[tuple[ast.stmt, bool]] = []
    for _case in getattr(node, "cases", None) or ():
        blocks.extend(_tc_flagged(getattr(_case, "body", None) or [], under_tc))
    return blocks
def _tc_child_blocks(node: ast.stmt, under_tc: bool, *,
                     include_class_body: bool,
                     typing_aliases: set[str] | None,
                     type_checking_names: set[str] | None
                     ) -> list[tuple[ast.stmt, bool]]:
    if isinstance(node, ast.If):
        return _tc_if_blocks(
            node, under_tc, typing_aliases, type_checking_names)
    if isinstance(node, _TRY_TYPES):
        return _tc_try_blocks(node, under_tc)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        return _tc_loop_blocks(
            node, under_tc, typing_aliases=typing_aliases,
            type_checking_names=type_checking_names)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return _tc_flagged(node.body, under_tc)
    if isinstance(node, ast.ClassDef):
        return _tc_flagged(node.body, under_tc) if include_class_body else []
    return _tc_match_blocks(node, under_tc)
def iter_module_level_nodes_tc(tree: ast.Module, *,
                                include_class_body: bool = True):
    typing_aliases = typing_guard_aliases(tree)
    type_checking_names = typing_type_checking_names(tree) or None
    stack = [(node, False) for node in reversed(tree.body)]
    while stack:
        node, under_tc = stack.pop()
        yield node, under_tc
        stack.extend(reversed(_tc_child_blocks(
            node, under_tc, include_class_body=include_class_body,
            typing_aliases=typing_aliases,
            type_checking_names=type_checking_names)))
def iter_module_level_imports_tc(tree: ast.Module):
    for node, under_tc in iter_module_level_nodes_tc(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)) and not under_tc:
            yield node
def _iter_import_time_nodes(tree: ast.AST):
    if not getattr(tree, "body", None):
        return
    for node, under_tc in iter_module_level_nodes_tc(
            tree, include_class_body=False):
        if not under_tc:
            yield node
_LAYOUT_CACHE_LIMIT = 64
_LAYOUT_STATE_FILES = frozenset({
    "__init__.py", "SKILL.md", "pyproject.toml", "setup.py", "setup.cfg",
    "requirements.txt",
})
def _layout_dir_signature(base: str, rel: str) -> tuple[tuple[str, tuple], ...]:
    try:
        with os.scandir(base) as entries:
            state: list[tuple[str, tuple]] = []
            nested: list[tuple[str, tuple]] = []
            for entry in entries:
                if entry.name.startswith('.'):
                    continue
                path = os.path.join(rel, entry.name) if rel else entry.name
                is_dir = entry.is_dir(follow_symlinks=False)
                mtime = size = 0
                if entry.name in _LAYOUT_STATE_FILES:
                    stat = entry.stat(follow_symlinks=False)
                    mtime, size = int(stat.st_mtime_ns), int(stat.st_size)
                state.append((path, (is_dir, mtime, size)))
                if (is_dir and not is_backup_snapshot_dir(entry.name)
                        and entry.name.lower() not in GENERIC_PROJECT_PRUNE_DIRS):
                    nested.extend(
                        _layout_dir_signature(
                            os.path.join(base, entry.name), path))
            state.extend(nested)
            return tuple(state)
    except OSError as exc:
        log_swallowed(__name__, exc, context='_layout_dir_signature:OSError')
        return (("__error__", (type(exc).__name__,)),)
def _layout_state_signature(skill_dir: str) -> tuple[tuple[str, tuple], ...]:
    return _layout_dir_signature(skill_dir, "")
_layout_cache: dict[tuple[str, tuple[tuple[str, tuple], ...]], Any] = {}
def layout_of(skill_dir: str | os.PathLike[str]) -> Any:
    root = os.path.abspath(os.fspath(skill_dir))
    signature = _layout_state_signature(root)
    key = (os.path.normcase(root), signature)
    if key not in _layout_cache:
        if len(_layout_cache) >= _LAYOUT_CACHE_LIMIT:
            _layout_cache.clear()
        _layout_cache[key] = detect_layout(root)
    return _layout_cache[key]
def project_package_root(project_root: str | os.PathLike[str]) -> str:
    raw = os.fspath(project_root)
    layout = layout_of(raw)
    if layout.is_package and layout.package_root:
        return os.path.abspath(layout.package_root)
    return os.path.abspath(raw)
def _declared_package_dir(skill_dir: str, package_name: str,
                          layout: Any = None) -> str | None:
    layout = layout if layout is not None else layout_of(skill_dir)
    if layout.is_package and layout.package_name == package_name:
        return layout.package_root
    return None
def resolve_namespace_dir(project_root: Path, module_name: str) -> Path | None:
    source_root = Path(project_package_root(project_root))
    parts = strip_root_prefix(project_root, module_name)
    if not parts:
        return None if (source_root / '__init__.py').exists() else source_root
    ns_dir = source_root / '/'.join(parts)
    if ns_dir.is_dir() and not (ns_dir / '__init__.py').exists():
        return ns_dir
    return None
def strip_root_prefix(project_root: Path, module_name: str) -> list[str]:
    parts = module_name.split('.')
    layout = layout_of(project_root)
    root_names = {import_key(project_root.name)}
    if layout.is_package:
        root_names.add(import_key(layout.package_name))
    return parts[1:] if parts and import_key(parts[0]) in root_names else parts
def _has_module_getattr(tree: ast.AST) -> bool:
    return any(
        isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
        and n.name == "__getattr__"
        for n in _iter_import_time_nodes(tree)
    )
def _tree_and_getattr(module_path, cache: _AstCache | None = None) -> tuple:
    if module_path is None:
        return None, False
    if cache is not None:
        try:
            _tree = cache.get_ast(str(module_path))
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e, context='_tree_and_getattr:cache')
            _tree = None
        if _tree is not None:
            return _tree, _has_module_getattr(_tree)
    loaded = load_source_tree(str(module_path))
    if loaded is None:
        logger.warning("[符号解析] 跳过 %s: 源码不可读取或语法错误", module_path)
        return None, False
    _source, tree = loaded
    return tree, _has_module_getattr(tree)
_MODULE_FLOW_TYPES = tuple(t for t in (
    ast.If, ast.Try, ast.With, ast.AsyncWith, ast.For, ast.AsyncFor,
    ast.While, ast.ExceptHandler,
    getattr(ast, "TryStar", None)) if t is not None)
_IMPORT_FALLBACK_NAMES = frozenset(
    ("ImportError", "ModuleNotFoundError", "Exception", "BaseException"))
_GUARD_TRY_TYPES = (ast.Try, getattr(ast, "TryStar", ast.Try))
_MATCH_TYPES = tuple(t for t in (getattr(ast, "Match", None),) if t is not None)
_MATCH_AS_TYPE = getattr(ast, "MatchAs", None)
_MATCH_STAR_TYPE = getattr(ast, "MatchStar", None)
_MATCH_SEQUENCE_TYPE = getattr(ast, "MatchSequence", None)
_MATCH_MAPPING_TYPE = getattr(ast, "MatchMapping", None)
_MATCH_CLASS_TYPE = getattr(ast, "MatchClass", None)
_MATCH_OR_TYPE = getattr(ast, "MatchOr", None)
_MATCH_NAME_TYPES = tuple(t for t in (_MATCH_AS_TYPE, _MATCH_STAR_TYPE)
                          if t is not None)
_MATCH_CHILD_ATTRS = {
    t: ("patterns",)
    for t in (_MATCH_SEQUENCE_TYPE, _MATCH_MAPPING_TYPE, _MATCH_OR_TYPE)
    if t is not None
}
if _MATCH_CLASS_TYPE is not None:
    _MATCH_CHILD_ATTRS[_MATCH_CLASS_TYPE] = ("patterns", "kwd_patterns")
def _match_own_capture_name(pattern: ast.AST) -> str | None:
    if _MATCH_NAME_TYPES and isinstance(pattern, _MATCH_NAME_TYPES):
        return pattern.name
    return None
def _match_child_patterns(pattern: ast.AST) -> tuple:
    if _MATCH_AS_TYPE is not None and isinstance(pattern, _MATCH_AS_TYPE):
        return (pattern.pattern,) if pattern.pattern is not None else ()
    children: list = []
    for attr in _MATCH_CHILD_ATTRS.get(type(pattern), ()):
        children.extend(getattr(pattern, attr, ()))
    return tuple(children)
def iter_match_capture_names(pattern: ast.AST | None):
    if pattern is None or _MATCH_AS_TYPE is None:
        return
    own_name = _match_own_capture_name(pattern)
    if own_name:
        yield own_name
    rest_name = _match_rest_name(pattern)
    if rest_name:
        yield rest_name
    for sub in _match_child_patterns(pattern):
        yield from iter_match_capture_names(sub)
def _match_rest_name(pattern: ast.AST) -> str | None:
    if _MATCH_MAPPING_TYPE is not None and isinstance(
            pattern, _MATCH_MAPPING_TYPE):
        return getattr(pattern, "rest", None)
    return None
def iter_module_level_nodes(tree: ast.Module | list[ast.stmt]):
    stmts = getattr(tree, "body", tree)
    stack: list[ast.stmt] = list(reversed(stmts))
    while stack:
        node = stack.pop()
        yield node
        stack.extend(reversed(list(_module_level_children(node))))
def _module_level_children(node: ast.AST):
    if isinstance(node, _MODULE_FLOW_TYPES):
        yield from ast.iter_child_nodes(node)
        return
    if _MATCH_TYPES and isinstance(node, _MATCH_TYPES):
        for case in node.cases:
            yield from case.body
def is_main_guard_if(node: ast.AST) -> bool:
    return isinstance(node, ast.If) and is_main_check(node.test)
def dynamic_module_binding_names(node: ast.AST) -> set[str]:
    """``globals()['x'] = v`` / ``globals().update({...})`` 等动态绑定的模块级名字。

    这些写法在运行期真实创建模块属性，但 AST 上不是 ``Name`` 绑定目标；
    各分析器（门面包导出面、符号链、API 契约）须共用同一份识别口径，
    否则同一名字在一处算「已定义」、在另一处算「幽灵导出」。
    既接受语句节点（``Expr`` 包裹的调用），也接受裸调用节点。
    """
    if isinstance(node, ast.Expr):
        node = node.value
    targets = (node.targets if isinstance(node, ast.Assign)
               else [node.target] if isinstance(node, ast.AnnAssign) else [])
    names = {
        target.slice.value
        for target in targets
        if isinstance(target, ast.Subscript) and _is_globals_call(target.value)
        and isinstance(target.slice, ast.Constant)
        and isinstance(target.slice.value, str)
    }
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and _is_globals_call(node.func.value)):
        return names
    method = node.func.attr
    if method in {'setdefault', '__setitem__'}:
        if (node.args and isinstance(node.args[0], ast.Constant)
                and isinstance(node.args[0].value, str)):
            names.add(node.args[0].value)
    elif method == 'update':
        for arg in node.args:
            if isinstance(arg, ast.Dict):
                names.update(
                    key.value for key in arg.keys
                    if isinstance(key, ast.Constant) and isinstance(key.value, str))
        names.update(keyword.arg for keyword in node.keywords if keyword.arg)
    return names
def iter_static_edge_nodes(tree: ast.AST):
    """产出运行期可达的节点，供静态依赖边与动态导入调用扫描共用。

    ``import`` 时永不执行的分支——``if TYPE_CHECKING:`` 体、``__main__`` 守卫体、
    静态假循环体——其中的 ``import`` / ``importlib.import_module`` 不构成
    运行期依赖边；``else`` 分支与函数体内的延迟导入仍照常产出。
    """
    excluded: set[int] = set()
    for node, under_tc in iter_module_level_nodes_tc(tree):
        if under_tc:
            excluded.update(id(child) for child in walk_nodes(node))
    stack: list[ast.AST] = [tree]
    while stack:
        node = stack.pop()
        if id(node) in excluded:
            continue
        if is_main_guard_if(node):
            stack.append(node.test)
            stack.extend(node.orelse)
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _regular_package_root(base: Path, root: Path) -> Path | None:
    current = base
    while not (current / '__init__.py').is_file():
        if current == root:
            return None
        current = current.parent
    package_root = current
    while current != root:
        parent = current.parent
        if parent == current or not (parent / '__init__.py').is_file():
            break
        package_root = current = parent
    return package_root
def _namespace_package_base(base: Path, root: Path) -> Path | None:
    if (base / '__init__.py').exists():
        return None
    layout = layout_of(root)
    if layout.is_package:
        package_root = Path(layout.package_root)
        if ((package_root / '__init__.py').exists()
                or not base.is_relative_to(package_root)):
            return None
        return package_root
    return base if base == root else None
def relative_import_base(fpath: str | os.PathLike, level: int,
                         root: str | os.PathLike) -> Path | None:
    if level <= 0:
        return None
    root_path = Path(os.path.abspath(str(root)))
    base = Path(os.path.abspath(str(fpath))).parent
    try:
        rel_dir = base.relative_to(root_path)
    except ValueError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='relative_import_base:ValueError')
        return None
    depth = 0 if str(rel_dir) == "." else len(rel_dir.parts)
    if level - 1 > depth:
        return None
    package_root = (_regular_package_root(base, root_path)
                    or _namespace_package_base(base, root_path))
    for _ in range(level - 1):
        base = base.parent
    if package_root is not None and base.is_relative_to(package_root):
        return base
    if not (root_path / '__init__.py').exists():
        return base
    return None
def _iter_walrus_exprs(node: ast.AST):
    if isinstance(node, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)):
        for expr in _outer_scope_exprs(node):
            yield from _iter_walrus_exprs(expr)
        return
    if isinstance(node, ast.ClassDef):
        for expr in (*node.decorator_list, *node.bases,
                     *(kw.value for kw in node.keywords)):
            yield from _iter_walrus_exprs(expr)
        return
    if isinstance(node, ast.NamedExpr):
        yield node
    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.stmt):
            continue
        yield from _iter_walrus_exprs(child)
def iter_walrus_expr_bindings(node: ast.AST):
    for expr in _iter_walrus_exprs(node):
        yield expr.target.id
def _outer_scope_exprs(node):
    args = node.args
    yield from getattr(node, 'decorator_list', ())
    yield from args.defaults
    yield from (d for d in args.kw_defaults if d is not None)
    for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs,
                args.vararg, args.kwarg):
        if arg is not None and arg.annotation is not None:
            yield arg.annotation
    returns = getattr(node, 'returns', None)
    if returns is not None:
        yield returns
_CACHE_MISSING = object()
_WALRUS_NAMES_ATTR = "_jwsgj_walrus_names"
_GLOBAL_NAMES_ATTR = "_jwsgj_global_names"
_IMPORT_TIME_SCOPES_ATTR = "_jwsgj_import_time_scopes"
_IMPORT_TIME_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
def _tree_import_time_scopes(tree: ast.AST) -> tuple[ast.AST, ...]:
    cached = getattr(tree, _IMPORT_TIME_SCOPES_ATTR, _CACHE_MISSING)
    if cached is _CACHE_MISSING:
        by_id: dict[int, ast.AST] = {}
        for node in _iter_import_time_nodes(tree):
            if not isinstance(node, _IMPORT_TIME_SCOPE_TYPES):
                continue
            for scope in walk_nodes(node):
                if isinstance(scope, _IMPORT_TIME_SCOPE_TYPES):
                    by_id[id(scope)] = scope
        cached = tuple(by_id.values())
        setattr(tree, _IMPORT_TIME_SCOPES_ATTR, cached)
    return cached
def _tree_global_names(tree: ast.AST) -> frozenset[str]:
    cached = getattr(tree, _GLOBAL_NAMES_ATTR, _CACHE_MISSING)
    if cached is _CACHE_MISSING:
        names: set[str] = set()
        for scope in _tree_import_time_scopes(tree):
            for node in iter_module_level_nodes(scope.body):
                if isinstance(node, ast.Global):
                    names.update(node.names)
        cached = frozenset(names)
        setattr(tree, _GLOBAL_NAMES_ATTR, cached)
    return cached
def _tree_walrus_names(tree: ast.AST) -> frozenset[str]:
    cached = getattr(tree, _WALRUS_NAMES_ATTR, _CACHE_MISSING)
    if cached is _CACHE_MISSING:
        names: set[str] = set()
        for stmt in _iter_import_time_nodes(tree):
            names.update(iter_walrus_expr_bindings(stmt))
        cached = frozenset(names)
        setattr(tree, _WALRUS_NAMES_ATTR, cached)
    return cached
GENERIC_PROJECT_PRUNE_DIRS = frozenset({
    "__pycache__", "__pypackages__", "node_modules", "site-packages",
    "venv", "env", "env3", "dist", "build", "htmlcov",
    "Temp", "zhenduan", "htm", "_cache", "_intermediate",
})
_TEST_PROJECT_PRUNE_DIRS = frozenset({"tests", "test", "fixtures", "test_tmp"})
_DEFAULT_INCLUDE_TESTS = True
def prune_target_dirs(dirnames: list[str], *,
                      include_tests: bool = _DEFAULT_INCLUDE_TESTS) -> None:
    excluded = {name.lower() for name in GENERIC_PROJECT_PRUNE_DIRS}
    if not include_tests:
        excluded.update(_TEST_PROJECT_PRUNE_DIRS)
    dirnames[:] = sorted(
        name for name in dirnames
        if (name and not name.startswith(".")
            and name.lower() not in excluded
            and (include_tests or not name.lower().endswith("_tests"))
            and not is_backup_snapshot_dir(name))
    )
def iter_target_py_files(root_dir, *,
                         include_tests: bool = _DEFAULT_INCLUDE_TESTS):
    try:
        raw_root = os.fsdecode(os.fspath(root_dir))
    except (TypeError, ValueError, OSError):
        return
    if not raw_root or not os.path.isdir(raw_root):
        return
    for dirpath, dirnames, filenames in os.walk(raw_root):
        prune_target_dirs(dirnames, include_tests=include_tests)
        for filename in sorted(filenames):
            if (filename.startswith((".", "._"))
                    or not filename.lower().endswith(".py")):
                continue
            if not include_tests and is_test_file_path(filename):
                continue
            yield Path(dirpath) / filename
def package_roots_for(skill_dir: str) -> set[str]:
    root = os.path.abspath(skill_dir)
    roots = {import_key(os.path.basename(os.path.normpath(root)))}
    layout = layout_of(root)
    if layout.is_package:
        roots.add(import_key(layout.package_name))
    try:
        for name in os.listdir(root):
            if os.path.isfile(os.path.join(root, name, "__init__.py")):
                roots.add(import_key(name))
    except OSError as exc:
        log_swallowed(__name__, exc, context="package_roots_for:OSError")
    return roots
def _importable_package_dir(pkg_root_name: str) -> str | None:
    try:
        spec = importlib.util.find_spec(pkg_root_name)
    except (ImportError, ValueError) as exc:
        log_swallowed(__name__, exc,
                      context="_importable_package_dir:ImportError")
        return None
    except Exception as exc:  # noqa: BLE001 — 导入钩子可能执行任意包代码
        logger.warning("[包根解析] find_spec(%s) 失败: %s", pkg_root_name, exc)
        return None
    if spec is None or spec.submodule_search_locations is None:
        return None
    locations = sorted(os.path.abspath(path)
                       for path in spec.submodule_search_locations)
    return locations[0] if locations else None
def _pkg_root_base_dir(pkg_root_name: str, real_pkg_root: str,
                       skill_dir: str, *, layout: Any = None) -> str | None:
    if pkg_root_name == real_pkg_root:
        if os.path.isfile(os.path.join(skill_dir, "__init__.py")):
            return skill_dir
        declared = _declared_package_dir(skill_dir, pkg_root_name, layout)
        return declared if declared is not None else skill_dir
    sub = os.path.join(skill_dir, pkg_root_name)
    if os.path.isdir(sub):
        return sub
    declared = _declared_package_dir(skill_dir, pkg_root_name, layout)
    if declared is not None:
        return declared
    return _importable_package_dir(pkg_root_name)
_STATIC_ALL_MAX_DEPTH = 32
class _StaticAll(NamedTuple):
    names: list[str]
    complete: bool
def _static_seq_target(stmt: ast.stmt) -> str | None:
    if isinstance(stmt, ast.Assign):
        if len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            return stmt.targets[0].id
        return None
    if (isinstance(stmt, ast.AnnAssign) and stmt.value is not None
            and isinstance(stmt.target, ast.Name)):
        return stmt.target.id
    return None
def _mutated_target_names(target: ast.expr) -> set[str]:
    if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name):
        return {target.value.id}
    return set(iter_unpack_target_names(target))
def _deleted_names(node: ast.Delete) -> set[str]:
    return {name for target in node.targets
            for name in _mutated_target_names(target)}
def _subscript_assignment_names(node: ast.Assign | ast.AnnAssign) -> set[str]:
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    return {target.value.id for target in targets
            if isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Name)}
def _loaded_names(*nodes: ast.AST) -> set[str]:
    return {child.id for node in nodes for child in walk_nodes(node)
            if isinstance(child, ast.Name)}
def _opaque_call_mutation_names(node: ast.Call) -> set[str]:
    func = node.func
    if ((isinstance(func, ast.Name) and func.id in _SEQUENCE_READONLY_CALLS)
            or (isinstance(func, ast.Attribute)
                and func.attr in _SEQUENCE_READONLY_METHODS)):
        return set()
    names = _loaded_names(
        *node.args, *(keyword.value for keyword in node.keywords))
    if not isinstance(func, ast.Name):
        names.update(_loaded_names(func))
    return names
def _mutation_call_names(node: ast.Call) -> set[str]:
    func = node.func
    if (isinstance(func, ast.Attribute)
            and func.attr in _SEQUENCE_MUTATION_METHODS):
        return ({func.value.id} if isinstance(func.value, ast.Name) else set())
    return _opaque_call_mutation_names(node)
_SEQ_MUTATION_EXTRACTORS = {
    ast.AugAssign: lambda node: _mutated_target_names(node.target),
    ast.Delete: _deleted_names,
    ast.Assign: _subscript_assignment_names,
    ast.AnnAssign: _subscript_assignment_names,
    ast.Call: _mutation_call_names,
    ast.NamedExpr: lambda node: (
        {node.target.id} if isinstance(node.target, ast.Name) else set()),
}
def _iter_seq_mutation_nodes(tree: ast.AST):
    stack = [tree]
    while stack:
        node = stack.pop()
        yield node
        children = (_outer_scope_exprs(node)
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                         ast.Lambda))
                    else ast.iter_child_nodes(node))
        stack.extend(children)
def _iter_import_time_seq_mutation_nodes(tree: ast.AST):
    excluded: set[int] = set()
    for node, under_tc in iter_module_level_nodes_tc(tree):
        if under_tc:
            excluded.update(id(child) for child in walk_nodes(node))
    for node in _iter_seq_mutation_nodes(tree):
        if id(node) not in excluded:
            yield node
def _iter_function_execution_nodes(scope: ast.FunctionDef):
    stack = list(scope.body)
    while stack:
        node = stack.pop()
        yield node
        children = (_outer_scope_exprs(node)
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                         ast.Lambda))
                    else ast.iter_child_nodes(node))
        stack.extend(children)
def _name_alias_pairs(nodes: Iterable[ast.AST]) -> set[tuple[str, str]]:
    pairs: set[tuple[str, str]] = set()
    for node in nodes:
        normalized = (assign_targets_value(node)
                      if isinstance(node, (ast.Assign, ast.AnnAssign))
                      else None)
        if normalized is not None:
            targets, value = normalized
            if isinstance(value, ast.Name):
                pairs.update(
                    (target.id, value.id) for target in targets
                    if isinstance(target, ast.Name) and target.id != value.id)
        if (isinstance(node, ast.NamedExpr)
                and isinstance(node.value, ast.Name)
                and node.target.id != node.value.id):
            pairs.add((node.target.id, node.value.id))
    return pairs
def _expand_alias_sources(names: Iterable[str],
                          pairs: set[tuple[str, str]]) -> set[str]:
    resolved = set(names)
    while True:
        sources = {source for alias, source in pairs if alias in resolved}
        if sources <= resolved:
            return resolved
        resolved.update(sources)
def _function_mutation_effects(
    scope: ast.FunctionDef,
    _visited: set[int] | None = None,
    _inherited: dict[str, list[ast.FunctionDef]] | None = None,
):
    visited = set() if _visited is None else _visited
    inherited = {} if _inherited is None else _inherited
    if id(scope) in visited:
        return set(), set()
    visited.add(id(scope))
    local, global_names = exec_scope_declarations(scope)
    def is_module_name(name: str) -> bool:
        return name not in local or name in global_names
    execution_nodes = tuple(_iter_function_execution_nodes(scope))
    alias_pairs = _name_alias_pairs(execution_nodes)
    nested_definitions: dict[str, list[ast.FunctionDef]] = {}
    for node in execution_nodes:
        if isinstance(node, ast.FunctionDef):
            nested_definitions.setdefault(node.name, []).append(node)
    visible_nested = {**inherited, **nested_definitions}
    mutated: set[str] = set()
    called: set[str] = set()
    for node in execution_nodes:
        if global_names:
            rebound: set[str] = set()
            collect_binding_names(node, rebound)
            mutated.update(rebound & global_names)
        extractor = _SEQ_MUTATION_EXTRACTORS.get(type(node))
        if extractor is not None:
            expanded = _expand_alias_sources(extractor(node), alias_pairs)
            mutated.update(name for name in expanded if is_module_name(name))
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)):
            continue
        for name in _expand_alias_sources({node.func.id}, alias_pairs):
            nested = nested_definitions.get(name)
            if nested is None and name not in local and name not in global_names:
                nested = inherited.get(name)
            if nested is not None:
                for nested_scope in nested:
                    nested_mutated, nested_called = _function_mutation_effects(
                        nested_scope, visited, visible_nested)
                    expanded_mutated = _expand_alias_sources(
                        nested_mutated, alias_pairs)
                    mutated.update(
                        name for name in expanded_mutated
                        if is_module_name(name))
                    expanded_called = _expand_alias_sources(
                        nested_called, alias_pairs)
                    called.update(
                        name for name in expanded_called
                        if is_module_name(name))
                continue
            if is_module_name(name):
                called.add(name)
    return mutated, called
def _function_call_mutates_all(
    scope: ast.FunctionDef, definitions: dict[str, list[ast.FunctionDef]],
    aliases: set[tuple[str, str]], _visited: set[str] | None = None,
) -> bool:
    direct, called = _function_mutation_effects(scope)
    if "__all__" in _expand_alias_sources(direct, aliases):
        return True
    visited = set() if _visited is None else _visited
    for called_name in called:
        for name in _expand_alias_sources({called_name}, aliases):
            if name in visited:
                continue
            visited.add(name)
            if any(_function_call_mutates_all(
                    nested, definitions, aliases, visited)
                   for nested in definitions.get(name, ())):
                return True
    return False


def _called_all_mutation_call_ids(tree: ast.AST) -> frozenset[int]:
    definitions: dict[str, list[ast.FunctionDef]] = {}
    for stmt in _iter_import_time_nodes(tree):
        if isinstance(stmt, ast.FunctionDef):
            definitions.setdefault(stmt.name, []).append(stmt)
    if not definitions:
        return frozenset()
    aliases = _sequence_alias_pairs(tree)
    call_ids: set[int] = set()
    for node in _iter_import_time_seq_mutation_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)):
            continue
        names = _expand_alias_sources({node.func.id}, aliases)
        if any(_function_call_mutates_all(scope, definitions, aliases)
               for name in names for scope in definitions.get(name, ())):
            call_ids.add(id(node))
    return frozenset(call_ids)


def _called_function_mutated_names(tree: ast.AST) -> set[str]:
    definitions: dict[str, list[ast.FunctionDef]] = {}
    for stmt in _iter_import_time_nodes(tree):
        if isinstance(stmt, ast.FunctionDef):
            definitions.setdefault(stmt.name, []).append(stmt)
    if not definitions:
        return set()
    aliases = _sequence_alias_pairs(tree)
    pending: set[str] = set()
    for node in _iter_import_time_seq_mutation_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)):
            continue
        pending.update(
            _expand_alias_sources({node.func.id}, aliases)
            & definitions.keys())
    visited: set[str] = set()
    mutated: set[str] = set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        for scope in definitions[name]:
            direct, called = _function_mutation_effects(scope)
            mutated.update(direct)
            for called_name in called:
                pending.update(
                    (_expand_alias_sources({called_name}, aliases)
                     & definitions.keys()) - visited)
    return mutated
def _sequence_alias_pairs(tree: ast.AST) -> set[tuple[str, str]]:
    return _name_alias_pairs(_iter_import_time_seq_mutation_nodes(tree))
def _class_global_rebound_names(tree: ast.AST) -> set[str]:
    rebound: set[str] = set()
    for scope in _iter_import_time_seq_mutation_nodes(tree):
        if not isinstance(scope, ast.ClassDef):
            continue
        _local, global_names = exec_scope_declarations(scope)
        if not global_names:
            continue
        for node in iter_module_level_nodes(scope.body):
            bound: set[str] = set()
            _collect_stmt_bindings(node, bound)
            if isinstance(node, ast.ExceptHandler) and node.name:
                bound.add(node.name)
            rebound.update(bound & global_names)
    return rebound
def _seq_mutated_names(tree: ast.AST) -> set[str]:
    mutated = _called_function_mutated_names(tree)
    mutated.update(_class_global_rebound_names(tree))
    for node in _iter_import_time_seq_mutation_nodes(tree):
        extractor = _SEQ_MUTATION_EXTRACTORS.get(type(node))
        if extractor is not None:
            mutated.update(extractor(node))
    aliases = _sequence_alias_pairs(tree)
    while True:
        indirect = {source for alias, source in aliases if alias in mutated}
        if indirect <= mutated:
            return mutated
        mutated.update(indirect)
def _module_rebound_names(tree: ast.AST) -> set[str]:
    body = getattr(tree, "body", None) or ()
    top_level_ids = {id(stmt) for stmt in body}
    rebound: set[str] = set()
    for stmt in _iter_import_time_nodes(tree):
        if isinstance(stmt, _GUARD_TRY_TYPES):
            rebound.update(
                handler.name for handler in stmt.handlers if handler.name)
        if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
            if id(stmt) not in top_level_ids:
                normalized = assign_targets_value(stmt)
                if normalized is not None:
                    for target in normalized[0]:
                        rebound.update(iter_unpack_target_names(target))
            continue
        if id(stmt) in top_level_ids and isinstance(stmt, _DEF_STMTS):
            rebound.add(stmt.name)
            continue
        names: set[str] = set()
        _collect_stmt_bindings(stmt, names)
        rebound.update(names)
    rebound.discard("__all__")
    return rebound
def static_seq_bindings(tree: ast.AST) -> dict[str, ast.AST]:
    mutated = _seq_mutated_names(tree)
    rebound = _module_rebound_names(tree)
    counts: dict[str, int] = {}
    values: dict[str, ast.AST] = {}
    for stmt in getattr(tree, "body", None) or ():
        name = _static_seq_target(stmt)
        if (name is None or name == "__all__"
                or name in mutated or name in rebound):
            continue
        counts[name] = counts.get(name, 0) + 1
        values[name] = getattr(stmt, "value", None)
    return {name: values[name] for name, count in counts.items() if count == 1}
def static_all_names(value: ast.AST,
                     bindings: dict[str, ast.AST],
                     _seen: frozenset[str] = frozenset(),
                     _depth: int = 0) -> _StaticAll:
    resolved = resolve_export_elts(value, bindings, _seen, _depth)
    if resolved is None:
        return _StaticAll([], False)
    names, exact = resolved
    return _StaticAll(names, exact)
_FUNC_DEF_STMTS = (ast.FunctionDef, ast.AsyncFunctionDef)
_DEF_STMTS = (*_FUNC_DEF_STMTS, ast.ClassDef)
_LOOP_STMTS = (ast.For, ast.AsyncFor, ast.While)
_FOR_STMTS = (ast.For, ast.AsyncFor)
_WITH_STMTS = (ast.With, ast.AsyncWith)
def _module_name(rel: Path) -> str:
    parts = list(rel.with_suffix("").parts)
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts) if parts else "__root__"
def _collect_stmt_bindings(stmt: ast.stmt, symbols: set[str]) -> None:
    symbols.update(iter_walrus_expr_bindings(stmt))
    # ``globals()['x'] = v`` / ``globals().update({...})`` 同样是模块级绑定，
    # 符号宇宙（_top_level_symbols）与绑定判定须同口径。
    symbols.update(dynamic_module_binding_names(stmt))
    if isinstance(stmt, _DEF_STMTS):
        symbols.add(stmt.name)
    elif isinstance(stmt, (ast.Assign, ast.AnnAssign)):
        symbols.update(_assigned_names(stmt))
    elif isinstance(stmt, (ast.Import, ast.ImportFrom)):
        _collect_import_bindings(stmt, symbols)
    else:
        _collect_header_bindings(stmt, symbols)
def _import_alias(alias: ast.alias) -> str:
    return alias.asname or alias.name.split(".")[0]
def _from_alias(alias: ast.alias) -> str | None:
    if alias.name == "*":
        return None
    return alias.asname or alias.name
def _is_future_import(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.ImportFrom) and stmt.level == 0
            and stmt.module == "__future__")
def _collect_import_bindings(stmt: ast.stmt, symbols: set[str]) -> None:
    if _is_future_import(stmt):
        return
    if isinstance(stmt, ast.ImportFrom):
        symbols.update(filter(None, map(_from_alias, stmt.names)))
    else:
        symbols.update(map(_import_alias, stmt.names))
class _BlockFamily(NamedTuple):
    types: tuple[type, ...]
    bodies: Callable[[ast.stmt], Iterable[ast.stmt]]
    header: Callable[[ast.stmt], set[str]]
def _body_and_orelse(stmt: ast.stmt) -> Iterable[ast.stmt]:
    yield from stmt.body
    yield from stmt.orelse
def _try_bodies(stmt: ast.stmt) -> Iterable[ast.stmt]:
    yield from stmt.body
    for handler in stmt.handlers:
        yield from handler.body
    yield from stmt.orelse
    yield from stmt.finalbody
def _with_bodies(stmt: ast.stmt) -> Iterable[ast.stmt]:
    yield from stmt.body
def _match_bodies(stmt: ast.stmt) -> Iterable[ast.stmt]:
    for case in stmt.cases:
        yield from case.body
def _type_alias_bodies(_stmt: ast.stmt) -> Iterable[ast.stmt]:
    return ()
def _no_header(_stmt: ast.stmt) -> set[str]:
    return set()
def _for_header(stmt: ast.stmt) -> set[str]:
    names: set[str] = set()
    if (isinstance(stmt, _FOR_STMTS)
            and _import_time_loop_visibility(stmt)[0] is not False):
        names.update(iter_unpack_target_names(stmt.target))
    return names
def _with_header(stmt: ast.stmt) -> set[str]:
    names: set[str] = set()
    for item in stmt.items:
        if item.optional_vars is not None:
            names.update(iter_unpack_target_names(item.optional_vars))
    return names
def _match_header(stmt: ast.stmt) -> set[str]:
    names: set[str] = set()
    for case in stmt.cases:
        names.update(iter_pattern_capture_names(case.pattern))
    return names
def _type_alias_header(stmt: ast.stmt) -> set[str]:
    return {stmt.name.id}
_BLOCK_FAMILIES: tuple[_BlockFamily, ...] = (
    _BlockFamily((ast.If,), _body_and_orelse, _no_header),
    _BlockFamily(_GUARD_TRY_TYPES, _try_bodies, _no_header),
    _BlockFamily(_LOOP_STMTS, _body_and_orelse, _for_header),
    _BlockFamily(_WITH_STMTS, _with_bodies, _with_header),
    _BlockFamily(_MATCH_TYPES, _match_bodies, _match_header),
    _BlockFamily(TYPE_ALIAS_NODES, _type_alias_bodies, _type_alias_header),
)
def _block_family(stmt: ast.stmt) -> _BlockFamily | None:
    for family in _BLOCK_FAMILIES:
        if isinstance(stmt, family.types):
            return family
    return None
def _collect_header_bindings(stmt: ast.stmt, symbols: set[str]) -> None:
    family = _block_family(stmt)
    if family is not None:
        symbols.update(family.header(stmt))
def _top_level_symbols(tree: ast.Module) -> set[str]:
    symbols: set[str] = set()
    for stmt in _iter_import_time_nodes(tree):
        _collect_stmt_bindings(stmt, symbols)
    return symbols
def _assigned_names(node: ast.stmt) -> set[str]:
    names: set[str] = set()
    if isinstance(node, ast.Assign):
        for t in node.targets:
            names.update(iter_unpack_target_names(t))
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        names.update(iter_unpack_target_names(node.target))
    return names
def _iter_block_bodies(stmt: ast.stmt) -> Iterable[ast.stmt]:
    family = _block_family(stmt)
    if family is not None:
        yield from family.bodies(stmt)
def _iter_module_level_stmts(stmts):
    for stmt in stmts:
        yield stmt
        if isinstance(stmt, _DEF_STMTS):
            continue
        yield from _iter_module_level_stmts(_iter_block_bodies(stmt))
def _extract_all(tree: ast.Module) -> _StaticAll | None:
    replay = _replay_module_exports(tree)
    if not replay.declared:
        return None
    return _StaticAll(replay.names, replay.exact)
def static_all_declarations(tree: ast.AST) -> tuple[set[str], bool]:
    surface = _extract_all(tree)
    if surface is None:
        return set(), False
    return set(surface.names), not surface.complete
@dataclass
class _ExportEvidence:
    public_func_count: int
    all_list: list
    empty_all_nodes: list
    all_augmented: bool
    has_computed_all: bool
def _count_visibility(tree: Any) -> tuple[int, int]:
    private_count = 0
    public_count = 0
    for node in _iter_import_time_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name.startswith("_"):
                private_count += 1
            else:
                public_count += 1
    return private_count, public_count
_STUB_EXEMPT_DECORATORS = frozenset({
    "abstractmethod", "abstractclassmethod", "abstractstaticmethod", "overload",
})
_PROTOCOL_BASE_NAME = "Protocol"
_TYPING_PROTOCOL_MODULES = frozenset({"typing", "typing_extensions"})
_STUB_DESIGN_INTENT_KEYWORDS = (
    "已切除", "已废弃", "已移除", "已删除", "已禁用", "已停用",
    "鲁棒", "回退", "兼容", "占位", "默认", "等效", "不可", "无法",
    "委托", "未实现", "待实现", "预留", "当前返回", "表示未", "暂未",
    "尚未", "deprecated", "removed", "disabled", "fallback", "robust",
    "compatibility", "placeholder", "default", "equivalent", "unsupported",
    "unavailable", "delegated", "not implemented", "reserved", "not yet",
)
def _stub_docstring(func_node: Any) -> str:
    if not func_node.body:
        return ""
    first_stmt = func_node.body[0]
    if is_constant_expr_stmt(first_stmt):
        val = first_stmt.value.value
        if isinstance(val, str):
            return val
    return ""
def _stub_effective_stmts(func_node: Any) -> list:
    effective = []
    for stmt in func_node.body:
        if is_constant_expr_stmt(stmt):
            continue
        if isinstance(stmt, ast.Pass):
            continue
        effective.append(stmt)
    return effective
def _stub_is_design_exempt(effective: list, docstring_text: str) -> bool:
    if not docstring_text:
        return False
    if len(effective) != 1 or not isinstance(effective[0], ast.Return):
        return False
    normalized_doc = docstring_text.casefold()
    return any(kw.casefold() in normalized_doc
               for kw in _STUB_DESIGN_INTENT_KEYWORDS)
def _stub_trivial_constant(cv: Any) -> bool:
    return (cv is None or isinstance(cv, bool)
            or (isinstance(cv, (int, float, complex)) and cv == 0)
            or (isinstance(cv, str) and cv == ""))
def _stub_empty_literal(rv: Any) -> bool:
    if isinstance(rv, ast.Dict):
        return not rv.keys
    return isinstance(rv, (ast.List, ast.Set, ast.Tuple)) and not rv.elts
def _stub_is_trivial_return(stmt: Any) -> bool:
    if not isinstance(stmt, ast.Return):
        return False
    rv = stmt.value
    if rv is None:
        return True
    if isinstance(rv, ast.Constant):
        return _stub_trivial_constant(rv.value)
    return _stub_empty_literal(rv)
def _stub_has_exempt_decorator(node: Any) -> bool:
    for decorator in node.decorator_list:
        if isinstance(decorator, ast.Name):
            name = decorator.id
        elif isinstance(decorator, ast.Attribute):
            name = decorator.attr
        else:
            name = None
        if name in _STUB_EXEMPT_DECORATORS:
            return True
    return False
def _protocol_base_names(tree: Any) -> frozenset[str]:
    names = {_PROTOCOL_BASE_NAME}
    for stmt in _iter_module_level_stmts(getattr(tree, "body", []) or []):
        if (isinstance(stmt, ast.ImportFrom)
                and stmt.module in _TYPING_PROTOCOL_MODULES):
            names.update(
                alias.asname or alias.name for alias in stmt.names
                if alias.name == _PROTOCOL_BASE_NAME)
    return frozenset(names)
def _base_is_protocol(base: ast.expr, names: frozenset[str]) -> bool:
    if isinstance(base, ast.Subscript):
        return _base_is_protocol(base.value, names)
    if isinstance(base, ast.Name):
        return base.id in names
    if isinstance(base, ast.Attribute):
        return base.attr == _PROTOCOL_BASE_NAME
    return False
def _protocol_member_ids(tree: Any) -> set[int]:
    names = _protocol_base_names(tree)
    member_ids: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        if not any(_base_is_protocol(base, names) for base in node.bases):
            continue
        member_ids.update(
            id(item) for item in node.body
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)))
    return member_ids
def _stub_is_func_stub(node: Any, *,
                       protocol_member: bool = False) -> bool:
    if protocol_member or _stub_has_exempt_decorator(node):
        return False
    if not node.body:
        return False
    docstring_text = _stub_docstring(node)
    effective = _stub_effective_stmts(node)
    if _stub_is_design_exempt(effective, docstring_text):
        return False
    return all(_stub_is_trivial_return(stmt) for stmt in effective)
def _count_stub_functions(tree: Any) -> tuple[int, int]:
    protocol_ids = _protocol_member_ids(tree)
    stub_count = 0
    total_funcs = 0
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            total_funcs += 1
            if _stub_is_func_stub(
                    node, protocol_member=id(node) in protocol_ids):
                stub_count += 1
    return stub_count, total_funcs
def _stub_collapse_issue(stub_count: int, total_funcs: int,
                         stub_ratio: float) -> dict[str, Any]:
    return {
        "rule_id": "GF-15",
        "severity": "P1",
        "line": 1,
        "message": (f"Stub collapse: {stub_count}/{total_funcs} "
                    f"({stub_ratio:.0%}) functions are stubs "
                    "(empty body or trivial return). Block threshold: 40%."),
        "category": "stub_detection",
        "stub_ratio": stub_ratio,
        "stub_count": stub_count,
        "total_funcs": total_funcs,
    }
def _check_stub_collapse(
    code: Any, tree: Any = None
) -> list[dict[str, Any]]:
    if is_consolidated_code(code):
        return []
    tree = guard_tree(code, tree, strict=True)
    if tree is None:
        return []
    issues: list[dict[str, Any]] = []
    stub_count, total_funcs = _count_stub_functions(tree)
    if total_funcs > 5:
        stub_ratio = stub_count / total_funcs
        if stub_ratio > 0.4:
            issues.append(_stub_collapse_issue(
                stub_count, total_funcs, stub_ratio))
    return issues
class _ExportScanner:
    __slots__ = ()
    def scan(self, tree: Any) -> _ExportEvidence:
        replay = _replay_module_exports(tree)
        _, public_func_count = _count_visibility(tree)
        return _ExportEvidence(
            public_func_count=public_func_count,
            all_list=list(replay.names),
            empty_all_nodes=(
                [replay.empty_node] if replay.empty_node is not None else []),
            all_augmented=replay.augmented,
            has_computed_all=replay.computed or not replay.exact,
        )
def _pkg_init_binding_evidence(top: Any) -> tuple[bool, bool]:
    star_import = any(alias.name == "*" for alias in top.names)
    bound = import_stmt_binds(top)
    return (star_import or any(not name.startswith("_") for name in bound),
            star_import or bool(bound))
def _name_evidence_from_names(names: Iterable[str]) -> tuple[bool, bool]:
    has_public_assign = False
    has_module_level_data = False
    for name in names:
        if name == "__all__":
            continue
        has_module_level_data = True
        if not name.startswith("_"):
            has_public_assign = True
    return has_public_assign, has_module_level_data
def _scan_data_evidence(tree: Any, fname: str) -> tuple[bool, bool]:
    has_public_assign = False
    has_module_level_data = False
    _is_pkg_init = (fname and
                    os.path.basename(fname) == "__init__.py")
    for top in _iter_import_time_nodes(tree):
        if isinstance(top, (ast.Import, ast.ImportFrom)):
            if not _is_pkg_init or _is_future_import(top):
                continue
            _pub_inc, _data_inc = _pkg_init_binding_evidence(top)
        else:
            bound: set[str] = set()
            _collect_stmt_bindings(top, bound)
            if isinstance(top, _DEF_STMTS):
                bound.discard(top.name)
            _pub_inc, _data_inc = _name_evidence_from_names(bound)
        has_public_assign = has_public_assign or _pub_inc
        has_module_level_data = has_module_level_data or _data_inc
    return has_public_assign, has_module_level_data
def _gf13_no_export_evidence(evidence: _ExportEvidence) -> bool:
    return (evidence.public_func_count == 0 and not evidence.all_list
            and not evidence.empty_all_nodes
            and not evidence.all_augmented
            and not evidence.has_computed_all)
def _no_public_api_issue(tree: Any, fname: str,
                         evidence: _ExportEvidence
                         ) -> list[dict[str, Any]]:
    if not _gf13_no_export_evidence(evidence):
        return []
    has_classes = any(isinstance(n, ast.ClassDef)
                      and not n.name.startswith("_")
                      for n in _iter_import_time_nodes(tree))
    has_public_assign, has_module_level_data = _scan_data_evidence(
        tree, fname)
    if not has_classes and not has_module_level_data:
        return [{
            "rule_id": "GF-13",
            "severity": "P0",
            "line": 1,
            "message": (
                "No public functions or __all__ exports found. "
                "May indicate API loss during refactoring."),
            "category": "api_preservation",
        }]
    if not has_classes and has_module_level_data and not has_public_assign:
        return [{
            "rule_id": "GF-13",
            "severity": "P2",
            "line": 1,
            "message": (
                "Module only contains private module-level data (no public API). "
                "Registry/data module by design — verify it has consumers."),
            "category": "api_preservation",
        }]
    return []
def _empty_all_loss_issues(
    evidence: _ExportEvidence
) -> list[dict[str, Any]]:
    if (evidence.all_list or not evidence.empty_all_nodes
            or evidence.all_augmented or evidence.has_computed_all):
        return []
    return [{
        "rule_id": "GF-13",
        "severity": "P0",
        "line": node.lineno,
        "message": (
            "__all__ is empty — all public API may have been "
            "removed during refactoring."),
        "category": "api_preservation",
    } for node in evidence.empty_all_nodes]
def _is_package_marker_init(tree: Any, fname: str) -> bool:
    if not fname or os.path.basename(fname) != "__init__.py":
        return False
    body = tree.body
    return all(
        isinstance(stmt, ast.Pass)
        or (isinstance(stmt, ast.ImportFrom) and stmt.module == "__future__")
        or (
            is_constant_expr_stmt(stmt)
            and isinstance(stmt.value.value, (str, type(Ellipsis)))
        )
        for stmt in body)
def _check_api_loss(
    code: Any, tree: Any = None, filepath: Any = None
) -> list[dict[str, Any]]:
    if is_consolidated_code(code):
        return []
    tree = guard_tree(code, tree)
    if tree is None:
        return []
    issues: list[dict[str, Any]] = []
    evidence = _ExportScanner().scan(tree)
    _fname = str(filepath) if filepath else ""
    if _fname and os.path.basename(_fname) == "__main__.py":
        return issues
    if _is_package_marker_init(tree, _fname):
        return issues
    issues.extend(_no_public_api_issue(tree, _fname, evidence))
    issues.extend(_empty_all_loss_issues(evidence))
    return issues
def _has_module_all(tree: Any) -> bool:
    return replay_export_surface(tree).declared
def _coverage_issue(tree: Any, private_count: int,
                    public_count: int) -> dict[str, Any] | None:
    total = private_count + public_count
    if total <= 5 or public_count == 0:
        return None
    ratio = public_count / total
    if ratio >= 0.2 or _has_module_all(tree):
        return None
    return {
        "rule_id": "GF-14",
        "severity": "P1",
        "line": 1,
        "message": (
            f"API coverage low: only {public_count}/{total} ({ratio:.0%}) "
            "functions are public. Refactoring may have hidden public APIs."),
        "category": "api_coverage",
    }
def _check_api_coverage(
    code: Any, tree: Any = None
) -> list[dict[str, Any]]:
    tree = guard_tree(code, tree)
    if tree is None:
        return []
    if is_consolidated_code(code):
        return []
    private_count, public_count = _count_visibility(tree)
    issue = _coverage_issue(tree, private_count, public_count)
    return [issue] if issue is not None else []
def run_api_integrity_checks(code: Any, *, tree: Any = None,
                             filepath: str = "", is_excluded: Any = None
                             ) -> list[dict[str, Any]]:
    if is_consolidated_code(code):
        return []
    skip = is_excluded if callable(is_excluded) else lambda _rule: False
    issues: list[dict[str, Any]] = []
    if not is_test_file_path(filepath) and not skip("GF-13"):
        issues.extend(_check_api_loss(code, tree=tree, filepath=filepath))
    if not skip("GF-14"):
        issues.extend(_check_api_coverage(code, tree=tree))
    if not skip("GF-15"):
        issues.extend(_check_stub_collapse(code, tree=tree))
    return issues

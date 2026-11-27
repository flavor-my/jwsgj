# ruff: noqa: I001
from __future__ import annotations
import ast
import math
import os
import sys
from collections.abc import Iterator, Mapping
from typing import Any
from jwsgj.diag_shared_ast_bindings import (
    ScopeNameResolver,
    import_bound_names,
    module_binding_names,
)
from jwsgj.diag_shared_ast_nodes import (
    _PROTOCOL_BASE_NAME as _PROTOCOL_BASE_NAME,
    _TYPING_PROTOCOL_MODULES as _TYPING_PROTOCOL_MODULES,
    _base_is_protocol as _base_is_protocol,
    _protocol_base_names as _protocol_base_names,
    _protocol_member_ids,
)
from jwsgj.diag_shared_ast_nodes import (
    attr_chain_key,
    build_parent_map,
    is_broad_except,
    is_docstring_stmt,
    is_dunder_name,
    is_type_checking_guard,
    iter_module_level_stmts,
)
from jwsgj.diag_shared_ast_nodes import (
    is_mutable_default as _is_mutable_default,
)
from jwsgj.diag_shared_ast_surface import (
    collect_all_export_names,
    collect_module_exports_state,
)
from jwsgj.diag_shared_source_core import (
    ASTUtils,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_normalize import int_or
from jwsgj.diag_types_vocab import (
    RULE_MUTABLE_DEFAULT,
    RULE_UNREACHABLE_CODE,
)
from jwsgj.runtime_scope import is_test_source_basename
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    'DeadCodeEliminator',
    'DegradationEliminator',
    'DynamicImportConverter',
    'FacadeOptimizer',
    'LazyImportEliminator',
    'PassthroughLayerDetector',
    'StubEliminator',
    'count_facade_entries',
    'default_param_sites',
    'fallback_scan_file',
    'parse_tree',
    'tally_shape_node',
]
_FALLBACK_SEVERITY: dict[str, str] = {
    "function_inner_import": "low",
    "bare_except_pass": "medium",
    "dynamic_import": "low",
    RULE_MUTABLE_DEFAULT: "high",
}
_TRY_TYPES = tuple(
    t for t in (ast.Try, getattr(ast, "TryStar", None)) if t is not None)
_TYPING_MODULES = frozenset({"typing", "typing_extensions"})
def _coerce_source_path(filepath: object) -> str | None:
    if isinstance(filepath, str):
        return filepath or None
    if isinstance(filepath, bytes):
        try:
            return os.fsdecode(filepath) or None
        except (TypeError, ValueError):
            return None
    if isinstance(filepath, os.PathLike):
        try:
            raw = os.fspath(filepath)
        except (TypeError, ValueError, OSError):
            return None
        if isinstance(raw, bytes):
            try:
                raw = os.fsdecode(raw)
            except (TypeError, ValueError):
                return None
        return raw or None
    return None
def _type_checking_guard_context(tree: ast.Module) -> tuple[set[str], set[str]]:
    names = {"TYPE_CHECKING"}
    aliases = set(_TYPING_MODULES)
    for stmt in iter_module_level_stmts(tree):
        if isinstance(stmt, ast.ImportFrom) and stmt.module in _TYPING_MODULES:
            names.update(
                alias.asname or alias.name for alias in stmt.names
                if alias.name == "TYPE_CHECKING")
        elif isinstance(stmt, ast.Import):
            aliases.update(
                alias.asname for alias in stmt.names
                if alias.name in _TYPING_MODULES and alias.asname)
    return names, aliases
def _type_checking_guard_polarity(
    test: ast.expr, names: set[str], aliases: set[str],
) -> bool | None:
    if is_type_checking_guard(
            test, typing_aliases=aliases, type_checking_names=names):
        return True
    if (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
            and is_type_checking_guard(
                test.operand, typing_aliases=aliases,
                type_checking_names=names)):
        return False
    return None
def _type_checking_scope_ids(tree: ast.Module) -> set[int]:
    names, aliases = _type_checking_guard_context(tree)
    ids: set[int] = set()
    stack: list[ast.AST] = [tree]
    while stack:
        node = stack.pop()
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.If):
                polarity = _type_checking_guard_polarity(
                    child.test, names, aliases)
                if polarity is not None:
                    type_only = child.body if polarity else child.orelse
                    runtime = child.orelse if polarity else child.body
                    for stmt in type_only:
                        ids.update(id(sub) for sub in walk_nodes(stmt))
                    stack.extend(runtime)
                    continue
            stack.append(child)
    return ids
def parse_tree(filepath: str) -> ast.Module | None:
    path = _coerce_source_path(filepath)
    if path is None:
        return None
    result = ASTUtils.parse_file(path)
    return None if result is None else result[0]
def _load_suppressions(filepath: str) -> dict:
    source = read_source(filepath)
    if source is None:
        return {}
    return parse_suppressions(source)
def _iter_scope_nodes(scope_node: ast.AST) -> Iterator[ast.AST]:
    stack = list(reversed(list(ast.iter_child_nodes(scope_node))))
    while stack:
        n = stack.pop()
        yield n
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(n))))
_STDLIB_MODULE_NAMES = frozenset(getattr(sys, "stdlib_module_names", ()))
def _regular_package_candidates(filepath: str) -> frozenset[str]:
    parent = os.path.dirname(os.path.abspath(filepath))
    parts: list[str] = []
    while os.path.isfile(os.path.join(parent, "__init__.py")):
        name = os.path.basename(parent)
        if not name.isidentifier():
            break
        parts.append(name)
        next_parent = os.path.dirname(parent)
        if next_parent == parent:
            break
        parent = next_parent
    parts.reverse()
    return frozenset(
        ".".join(parts[start:end])
        for start in range(len(parts))
        for end in range(start + 1, len(parts) + 1)
    )
def skill_pkg_candidates(filepath: str) -> frozenset[str]:
    path = _coerce_source_path(filepath)
    if path is None:
        return frozenset()
    parts = os.path.normpath(
        os.path.abspath(path)).replace(os.sep, "/").split("/")
    candidates: set[str] = set()
    candidates.update(_regular_package_candidates(path))
    for depth in range(2, min(4, len(parts)) + 1):
        segments = parts[-depth:-1]
        if not all(seg.isidentifier() for seg in segments):
            continue
        for end in range(1, len(segments) + 1):
            candidates.add(".".join(segments[:end]))
    return frozenset(
        name for name in candidates
        if name.split(".")[0] not in _STDLIB_MODULE_NAMES)
_OPTIONAL_HEAVY_MODULES = frozenset({
    'z3', 'matplotlib', 'numpy', 'pandas',
    'torch', 'tensorflow', 'cv2', 'PIL', 'sklearn',
    'scipy', 'sympy', 'networkx', 'graphviz',
    'yaml', 'toml', 'tomllib', 'requests', 'psutil', 'colorama',
    'aiohttp', 'httpx', 'websockets', 'uvicorn',
    'redis', 'pymongo', 'psycopg2', 'MySQLdb',
    'Crypto', 'bcrypt', 'cryptography',
    'lxml', 'bs4', 'html5lib',
    'pytest', 'hypothesis', 'coverage',
    'numba', 'cupy', 'jax', 'dask', 'pyspark', 'ray',
    'nltk', 'spacy', 'transformers', 'opencv',
})
def import_member_offenders(names: list,
                            pkg_candidates: frozenset[str] | None
                            ) -> list[tuple[str, str | None]]:
    return [
        (a.name, a.asname) for a in names
        if a.name.split('.')[0] not in _OPTIONAL_HEAVY_MODULES
        and a.name.split('.')[0] not in (pkg_candidates or frozenset())
    ]
def _is_exempt_import_from(
    node: ast.ImportFrom, pkg_candidates: frozenset[str] | None,
) -> bool:
    module = node.module or "?"
    if node.level > 0 or module.split('.')[0] in _OPTIONAL_HEAVY_MODULES:
        return True
    return bool(pkg_candidates) and any(
        module == pkg or module.startswith(pkg + ".")
        for pkg in pkg_candidates
    )
def import_from_offenders(node: ast.ImportFrom,
                          pkg_candidates: frozenset[str] | None
                          ) -> list[tuple[str, str | None]]:
    if _is_exempt_import_from(node, pkg_candidates):
        return []
    return [(a.name, a.asname) for a in node.names]
_IMPORT_ERROR_EXC_NAMES = frozenset({'ImportError', 'ModuleNotFoundError'})
def _is_builtin_name(dotted: str | None, names: frozenset[str]) -> bool:
    if not dotted:
        return False
    if dotted in names:
        return True
    return (dotted.startswith("builtins.")
            and dotted[len("builtins."):] in names)
def _import_error_handler_name(handler: ast.ExceptHandler) -> str | None:
    exc = handler.type
    if isinstance(exc, ast.Tuple):
        candidates = exc.elts
    elif exc is None:
        candidates = ()
    else:
        candidates = (exc,)
    for node in candidates:
        dotted = attr_chain_key(node)
        if _is_builtin_name(dotted, _IMPORT_ERROR_EXC_NAMES):
            return dotted
    return None
def count_facade_entries(tree: ast.Module) -> int:
    type_only_ids = _type_checking_scope_ids(tree)
    return sum(
        1 for node in iter_module_level_stmts(tree)
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef))
            and id(node) not in type_only_ids)
    )
class FacadeOptimizer:
    MAX_FACADE = 9
    def __init__(self, max_facade: int | None = None):
        default_limit = int_or(
            type(self).MAX_FACADE, FacadeOptimizer.MAX_FACADE)
        self.MAX_FACADE = max(0, int_or(max_facade, default_limit))
    def _facade_result(self, facade_count: int, filepath: str,
                       error: str | None = None) -> dict:
        result = {
            "ok": facade_count <= self.MAX_FACADE,
            "facade_count": facade_count,
            "max_facade": self.MAX_FACADE,
            "filepath": filepath,
        }
        if error is not None:
            result.update(ok=False, error=error)
        return result
    def check(self, filepath: str) -> dict:
        path = _coerce_source_path(filepath)
        if path is None:
            return self._facade_result(0, "", error="非法源码路径")
        if path.replace('\\', '/').rsplit('/', 1)[-1].lower() != '__init__.py':
            return self._facade_result(0, path)
        tree = parse_tree(path)
        if tree is None:
            return self._facade_result(
                0, path, error="无法读取或解析 __init__.py")
        return self._facade_result(count_facade_entries(tree), path)
def _import_node_ids(stmts, *, include_deferred: bool = False) -> set[int]:
    ids: set[int] = set()
    stack = list(stmts)
    while stack:
        node = stack.pop()
        if (not include_deferred
                and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.Lambda))):
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            ids.add(id(node))
            continue
        stack.extend(ast.iter_child_nodes(node))
    return ids
def _exempt_stmt_groups(tree: ast.Module) -> Iterator[tuple]:
    guard_names, typing_aliases = _type_checking_guard_context(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.If):
            polarity = _type_checking_guard_polarity(
                node.test, guard_names, typing_aliases)
            if polarity is not None:
                yield tuple(node.body if polarity else node.orelse), True
        elif (isinstance(node, _TRY_TYPES)
              and any(_import_error_handler_name(h) for h in node.handlers)):
            yield _try_scope_stmts(node), False
def _try_scope_stmts(node) -> tuple:
    return (
        *node.body,
        *(s for h in node.handlers if _import_error_handler_name(h)
          for s in h.body),
    )
def _collect_exempt_import_ids(tree: ast.Module) -> set[int]:
    ids: set[int] = set()
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.ClassDef):
            ids.update(_import_node_ids(node.body))
    for group, include_deferred in _exempt_stmt_groups(tree):
        ids.update(_import_node_ids(
            group, include_deferred=include_deferred))
    return ids
class LazyImportEliminator:
    def detect(self, filepath: str) -> list[dict]:
        path = _coerce_source_path(filepath)
        if path is None:
            return []
        tree = parse_tree(path)
        if tree is None:
            return []
        _exempt_ids = _collect_exempt_import_ids(tree)
        _pkg_cands = skill_pkg_candidates(path)
        violations = self._collect_func_scope_imports(
            tree, path, _exempt_ids, _pkg_cands)
        violations.sort(key=lambda v: (
            v.get("line", 0), v.get("function", ""),
            v.get("type", ""), v.get("module", "")))
        return violations
    @staticmethod
    def _judge_scope_node(child, node, filepath: str, exempt_ids: set,
                          pkg_cands: frozenset) -> dict | None:
        if id(child) in exempt_ids:
            return None
        if isinstance(child, ast.Import):
            return LazyImportEliminator._judge_func_import(
                child, node, filepath, pkg_cands)
        if isinstance(child, ast.ImportFrom):
            return LazyImportEliminator._judge_func_import_from(
                child, node, filepath, pkg_cands)
        return None
    @staticmethod
    def _collect_func_scope_imports(tree, filepath: str,
                                    exempt_ids: set,
                                    pkg_cands: frozenset) -> list[dict]:
        violations: list[dict] = []
        seen: set[int] = set()
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                     ast.ClassDef)):
                continue
            for child in _iter_scope_nodes(node):
                if id(child) in seen:
                    continue
                seen.add(id(child))
                violation = LazyImportEliminator._judge_scope_node(
                    child, node, filepath, exempt_ids, pkg_cands)
                if violation is not None:
                    violations.append(violation)
        return violations
    @staticmethod
    def _judge_func_import(child: ast.Import, node, filepath: str,
                           pkg_cands) -> dict | None:
        offenders = import_member_offenders(child.names, pkg_cands)
        if not offenders:
            return None
        return {
            "file": filepath,
            "line": child.lineno,
            "function": node.name,
            "type": "import",
            "module": ", ".join(m[0] for m in offenders),
            "modules": offenders,
        }
    @staticmethod
    def _judge_func_import_from(child: ast.ImportFrom, node, filepath: str,
                                pkg_cands) -> dict | None:
        offenders = import_from_offenders(child, pkg_cands)
        if not offenders:
            return None
        return {
            "file": filepath,
            "line": child.lineno,
            "function": node.name,
            "type": "import_from",
            "module": child.module or "?",
            "symbols": offenders,
        }
def _is_ellipsis_expr(node: ast.AST) -> bool:
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
            and node.value.value is Ellipsis)
def _is_noop_stmt(stmt: ast.AST) -> bool:
    return isinstance(stmt, ast.Pass) or (
        isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant))
def _is_rule_suppressed(
        suppressions: dict, lineno: int, rule: str, category: str = "") -> bool:
    if not suppressions:
        return False
    if is_suppressed(suppressions, lineno, rule):
        return True
    return bool(category) and is_suppressed(suppressions, lineno, category)
def is_pass_only_body(body: list) -> bool:
    return all(_is_noop_stmt(stmt) for stmt in body)
def _none_assignment_names(stmt: ast.stmt) -> list[str]:
    if not isinstance(stmt, (ast.Assign, ast.AnnAssign)):
        return []
    if not (isinstance(stmt.value, ast.Constant) and stmt.value.value is None):
        return []
    targets = stmt.targets if isinstance(stmt, ast.Assign) else (stmt.target,)
    return [t.id for t in targets if isinstance(t, ast.Name)]
class DegradationEliminator:
    def detect(self, filepath: str) -> list[dict]:
        path = _coerce_source_path(filepath)
        if path is None:
            return []
        tree = parse_tree(path)
        if tree is None:
            return []
        type_only_ids = _type_checking_scope_ids(tree)
        violations = []
        for node in walk_nodes(tree):
            if isinstance(node, _TRY_TYPES) and id(node) not in type_only_ids:
                for handler in node.handlers:
                    violations.extend(
                        self._collect_c4_violations(handler, path))
                    _c5 = self._collect_c5_violation(handler, path)
                    if _c5 is not None:
                        violations.append(_c5)
        violations.sort(key=lambda v: (
            v.get("line", 0), v.get("type", ""),
            v.get("variable", ""), v.get("value", "")))
        return violations
    @staticmethod
    def _collect_c4_violations(handler: ast.ExceptHandler, filepath: str) -> list[dict]:
        _exc_name = _import_error_handler_name(handler)
        if not _exc_name:
            return []
        violations: list[dict] = []
        for stmt in handler.body:
            for target in _none_assignment_names(stmt):
                violations.append({
                    "file": filepath,
                    "line": stmt.lineno,
                    "type": "regression",
                    "variable": target,
                    "pattern": (
                        f"except {ast.unparse(handler.type)}: "
                        f"{target} = None"),
                })
        return violations
    @staticmethod
    def _collect_c5_violation(handler: ast.ExceptHandler, filepath: str) -> dict | None:
        if not _is_bare_except_pass(handler):
            return None
        return {
            "file": filepath,
            "line": handler.lineno,
            "type": "fallback",
            "value": "pass",
            "pattern": _except_pattern(handler),
        }
def _is_bare_except_pass(handler: ast.ExceptHandler) -> bool:
    return is_broad_except(handler) and is_pass_only_body(handler.body)
def _except_pattern(handler: ast.ExceptHandler) -> str:
    if handler.type is None:
        return "except: pass"
    return f"except {ast.unparse(handler.type)}: pass"
_PROTOCOL_STUB_IMPORT_PATHS = frozenset({
    'abc.abstractmethod', 'typing.overload', 'typing_extensions.overload',
})
def _decorator_import_path(
        decorator: ast.AST, resolver: ScopeNameResolver,
) -> str | None:
    parts: list[str] = []
    root = decorator
    while isinstance(root, ast.Attribute):
        parts.append(root.attr)
        root = root.value
    if not isinstance(root, ast.Name):
        return None
    import_path = resolver.import_path(root)
    if import_path is None:
        return None
    for part in reversed(parts):
        import_path += f".{part}"
    return import_path
def _is_protocol_stub(
        func_node: ast.AST, resolver: ScopeNameResolver | None = None,
) -> bool:
    for decorator in func_node.decorator_list:
        if resolver is not None:
            if (_decorator_import_path(decorator, resolver)
                    in _PROTOCOL_STUB_IMPORT_PATHS):
                return True
            continue
        if (isinstance(decorator, ast.Attribute)
                and decorator.attr in ('abstractmethod', 'overload')):
            return True
        if (isinstance(decorator, ast.Name)
                and decorator.id in ('abstractmethod', 'overload')):
            return True
    return False
def _non_docstring_body(body: list) -> list:
    return [stmt for stmt in body if not is_docstring_stmt(stmt)]
def _is_visitor_noop(node: ast.AST, kind: str | None = None) -> bool:
    if not str(getattr(node, "name", "")).startswith("visit_"):
        return False
    if kind is None:
        kind = _bare_stub_kind(getattr(node, "body", []))
    if kind is not None:
        return True
    stmts = [
        stmt for stmt in _non_docstring_body(getattr(node, "body", []))
        if not _is_noop_stmt(stmt)]
    if len(stmts) != 1 or not isinstance(stmts[0], ast.Return):
        return False
    value = stmts[0].value
    return (value is None
            or (isinstance(value, ast.Constant) and value.value is None))
def _bare_stub_kind(body: list) -> str | None:
    stmts = _non_docstring_body(body)
    if not stmts:
        return "pass"
    if all(_is_noop_stmt(stmt) for stmt in stmts):
        if any(isinstance(stmt, ast.Pass) for stmt in stmts):
            return "pass"
        if any(_is_ellipsis_expr(stmt) for stmt in stmts):
            return "ellipsis"
        return "pass"
    return None
_BLOCK_TERMINATOR_NODES = (ast.Return, ast.Raise, ast.Break, ast.Continue)
class DeadCodeEliminator:
    def detect(self, filepath: str) -> list[dict]:
        path = _coerce_source_path(filepath)
        if path is None:
            return []
        tree = parse_tree(path)
        if tree is None:
            return []
        violations = []
        _pmap = build_parent_map(tree)
        _protocol_ids = _protocol_member_ids(tree)
        _type_only_ids = _type_checking_scope_ids(tree)
        _suppressions = _load_suppressions(path)
        _resolver = _source_name_resolver(tree, path)
        for node in walk_nodes(tree):
            if id(node) in _type_only_ids:
                continue
            if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and id(node) not in _protocol_ids):
                _v = self._judge_empty_body_violation(
                    node, path, _suppressions, _resolver)
                if _v is not None:
                    violations.append(_v)
            _vf = self._judge_if_false_violation(
                node, path, _suppressions)
            if _vf is not None:
                violations.append(_vf)
            if isinstance(node, _BLOCK_TERMINATOR_NODES):
                _v = self._judge_unreachable_violation(
                    node, _pmap, path, _suppressions)
                if _v is not None:
                    violations.append(_v)
        violations.sort(key=lambda v: (
            v.get("line", 0), v.get("type", ""), v.get("name", "")))
        return violations
    def _judge_empty_body_violation(
            self, node, filepath: str, suppressions: dict,
            resolver: ScopeNameResolver | None = None) -> dict | None:
        if _is_protocol_stub(node, resolver):
            return None
        kind = _bare_stub_kind(node.body)
        if kind is None:
            return None
        if _is_visitor_noop(node, kind):
            return None
        _rule = "empty_function" if kind == "pass" else "stub_function"
        if _is_rule_suppressed(
                suppressions, node.lineno, _rule, "C8_dead_code"):
            return None
        return {
            "file": filepath,
            "line": node.lineno,
            "type": _rule,
            "name": node.name,
        }
    @staticmethod
    def _judge_if_false_violation(node, filepath: str,
                                  suppressions: dict
                                  ) -> dict | None:
        if not isinstance(node, ast.If):
            return None
        is_literal, literal_value = _literal_default_value(node.test)
        if not is_literal or literal_value:
            return None
        if _is_rule_suppressed(
                suppressions, node.lineno, "if_false_block", "C8_dead_code"):
            return None
        return {
            "file": filepath,
            "line": node.lineno,
            "type": "if_false_block",
        }
    def _judge_unreachable_violation(self, node, pmap: dict, filepath: str,
                                     suppressions: dict
                                     ) -> dict | None:
        parent_body = DeadCodeEliminator._find_parent_body(node, pmap)
        if parent_body is None:
            return None
        idx = parent_body.index(node)
        if idx >= len(parent_body) - 1:
            return None
        _next = parent_body[idx + 1]
        _line = _next.lineno if hasattr(_next, 'lineno') else node.lineno
        if _is_rule_suppressed(
                suppressions, _line, RULE_UNREACHABLE_CODE, "C8_dead_code"):
            return None
        return {
            "file": filepath,
            "line": _line,
            "type": RULE_UNREACHABLE_CODE,
        }
    @staticmethod
    def _find_parent_body(target: ast.AST, pmap: dict) -> list | None:
        parent = pmap.get(id(target))
        if parent is None:
            return None
        for _field_name, field_value in ast.iter_fields(parent):
            if isinstance(field_value, list) and target in field_value:
                return field_value
        return None
def _assign_target_names(node: ast.AST) -> set:
    if isinstance(node, ast.Assign):
        assignment_targets = node.targets
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        assignment_targets = (node.target,)
    else:
        return set()
    targets = set()
    pending = list(assignment_targets)
    while pending:
        target = pending.pop()
        if isinstance(target, (ast.Tuple, ast.List)):
            pending.extend(target.elts)
        elif isinstance(target, ast.Starred):
            pending.append(target.value)
        elif isinstance(target, ast.Name):
            targets.add(target.id)
        elif isinstance(target, ast.Attribute):
            targets.add(target.attr)
    return targets
_SHAPE_COUNT_KINDS: tuple[tuple[tuple[type, ...], str], ...] = (
    ((ast.Return,), "returns"),
    ((ast.If, ast.IfExp), "branches"),
    ((ast.For, ast.While, ast.AsyncFor), "loops"),
)
def tally_shape_node(node: ast.AST, counts: dict, calls: set,
                      assign_targets: set) -> None:
    if isinstance(node, ast.Call):
        call_name = ASTUtils.resolve_call_name(node)
        if call_name:
            calls.add(call_name)
        return
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        assign_targets.update(
            _assign_target_names(node))
        return
    for kinds, key in _SHAPE_COUNT_KINDS:
        if isinstance(node, kinds):
            counts[key] = counts.get(key, 0) + 1
            return
_PASSTHROUGH_SKIP_FILES = frozenset({
    "__init__.py", "__main__.py", "setup.py", "conftest.py",
})
_PASSTHROUGH_EXEMPT_NAMES = frozenset({"main", "cli"})
_PASSTHROUGH_COMPAT_SUFFIXES = ("_compat", "_alias", "_deprecated", "_legacy")
_PASSTHROUGH_COMPAT_MARKERS = (
    "兼容", "别名", "alias", "deprecated", "compat",
    "re-export", "reexport", "转发", "delegat",
)
_NON_CONFIG_NUMERIC_DEFAULTS = frozenset({0, 1, -1, 2})
_NON_CONFIG_STR_DEFAULTS = frozenset({
    "utf-8", "utf8", "ascii", "latin-1", "r", "w", "a", "rb", "wb",
    "ab", "r+", "w+", "a+", "strict", "ignore", "replace",
    "backslashreplace", "surrogateescape", "newline", "json", "text",
    "none", "null", "true", "false",
    "get", "post", "put", "delete", "head", "options", "patch",
})
def _literal_default_value(node: ast.AST) -> tuple[bool, Any]:
    if isinstance(node, ast.Constant):
        return True, node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        is_literal, value = _literal_default_value(node.operand)
        if is_literal and type(value) in (int, float, complex):
            return True, -value if isinstance(node.op, ast.USub) else value
    return False, None
def _default_value_key(value: Any) -> tuple[str, Any] | None:
    if isinstance(value, bool) or value is None:
        return None
    if type(value) is int:
        return None if value in _NON_CONFIG_NUMERIC_DEFAULTS else ("int", value)
    if type(value) is float:
        if math.isnan(value) or math.isinf(value):
            return None
        return None if value in _NON_CONFIG_NUMERIC_DEFAULTS else ("float", value)
    if type(value) is str:
        stripped = value.strip()
        if len(stripped) < 3:
            return None
        return (None if stripped.lower() in _NON_CONFIG_STR_DEFAULTS
                else ("str", value))
    return None
def _function_default_sites(
        node: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
        fpath: str) -> list[tuple[tuple, dict]]:
    sites: list[tuple[tuple, dict]] = []
    for arg, default in _default_param_bindings(node):
        if arg.arg in ("self", "cls") or arg.arg.startswith("_"):
            continue
        is_literal, literal_value = _literal_default_value(default)
        if not is_literal:
            continue
        key = _default_value_key(literal_value)
        if key is None:
            continue
        sites.append(((arg.arg, *key), {
            "file": fpath,
            "line": default.lineno,
            "function": getattr(node, "name", "<lambda>"),
        }))
    return sites
def default_param_sites(tree: ast.Module,
                         fpath: str) -> list[tuple[tuple, dict]]:
    if not isinstance(tree, ast.AST):
        return []
    fpath = _coerce_source_path(fpath) or ""
    type_only_ids = (_type_checking_scope_ids(tree)
                     if isinstance(tree, ast.Module) else set())
    sites: list[tuple[tuple, dict]] = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
            continue
        if id(node) in type_only_ids:
            continue
        sites.extend(_function_default_sites(node, fpath))
    return sites
def _forwarded_positional(
        call_args: list[ast.expr],
        vararg: str | None) -> tuple[list[str], bool] | None:
    names: list[str] = []
    star_forwarded = False
    for arg in call_args:
        if isinstance(arg, ast.Name):
            names.append(arg.id)
            continue
        if not (isinstance(arg, ast.Starred) and isinstance(arg.value, ast.Name)
                and vararg is not None and arg.value.id == vararg):
            return None
        names.append(vararg)
        star_forwarded = True
    return names, star_forwarded
def _forwarded_keywords(
        call_keywords: list[ast.keyword], kwarg: str | None,
) -> tuple[list[str], bool] | None:
    names: list[str] = []
    double_star_forwarded = False
    for keyword in call_keywords:
        if keyword.arg is None:
            if (kwarg is None or not isinstance(keyword.value, ast.Name)
                    or keyword.value.id != kwarg):
                return None
            names.append(kwarg)
            double_star_forwarded = True
            continue
        if (not isinstance(keyword.value, ast.Name)
                or keyword.value.id != keyword.arg):
            return None
        names.append(keyword.arg)
    return names, double_star_forwarded
def _declared_params(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[list[str], str | None, str | None]:
    args = node.args
    positional = [a.arg for a in (*args.posonlyargs, *args.args)]
    vararg = args.vararg.arg if args.vararg is not None else None
    kwarg = args.kwarg.arg if args.kwarg is not None else None
    return positional, vararg, kwarg
def _forwards_all_params(node: ast.FunctionDef | ast.AsyncFunctionDef,
                         call: ast.Call) -> bool:
    positional, vararg, kwarg = _declared_params(node)
    keyword_only = [a.arg for a in node.args.kwonlyargs]
    found_positional = _forwarded_positional(call.args, vararg)
    found_keywords = _forwarded_keywords(call.keywords, kwarg)
    if found_positional is None or found_keywords is None:
        return False
    positional_only = {arg.arg for arg in node.args.posonlyargs}
    if any(keyword.arg in positional_only for keyword in call.keywords):
        return False
    forwarded_positional, star_forwarded = found_positional
    forwarded_keywords, double_star_forwarded = found_keywords
    if kwarg is not None and not double_star_forwarded:
        return False
    forwarded = forwarded_positional + forwarded_keywords
    declared = [*positional, *keyword_only]
    if vararg is not None:
        declared.append(vararg)
    if kwarg is not None:
        declared.append(kwarg)
    if len(forwarded) != len(set(forwarded)):
        return False
    if set(forwarded) != set(declared):
        return False
    if star_forwarded and forwarded_positional[-1] != vararg:
        return False
    plain_positional = [name for name in forwarded_positional
                        if not (star_forwarded and name == vararg)]
    return plain_positional == positional[:len(plain_positional)]
def _passthrough_exempt(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    if node.decorator_list or node.name in _PASSTHROUGH_EXEMPT_NAMES:
        return True
    if node.name.endswith(_PASSTHROUGH_COMPAT_SUFFIXES):
        return True
    doc = (ast.get_docstring(node) or "").lower()
    return any(marker in doc for marker in _PASSTHROUGH_COMPAT_MARKERS)
def _forward_return_call(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> ast.Call | None:
    body = _non_docstring_body(node.body)
    if len(body) != 1 or not isinstance(body[0], ast.Return):
        return None
    value = body[0].value
    if isinstance(value, ast.Await):
        if not isinstance(node, ast.AsyncFunctionDef):
            return None
        value = value.value
    elif isinstance(node, ast.AsyncFunctionDef):
        return None
    return value if isinstance(value, ast.Call) else None
def _function_call_contract(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> tuple | None:
    args = node.args
    defaults = (
        *args.defaults,
        *(default for default in args.kw_defaults if default is not None),
    )
    if any(not _literal_default_value(default)[0] for default in defaults):
        return None
    return (
        tuple(arg.arg for arg in args.posonlyargs),
        tuple(arg.arg for arg in args.args),
        tuple(ast.unparse(default) for default in args.defaults),
        args.vararg.arg if args.vararg is not None else None,
        tuple(arg.arg for arg in args.kwonlyargs),
        tuple(ast.unparse(default) if default is not None else None
              for default in args.kw_defaults),
        args.kwarg.arg if args.kwarg is not None else None,
    )
def _pure_forward_callee(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        definitions: dict[str, ast.FunctionDef | ast.AsyncFunctionDef],
) -> str | None:
    if _passthrough_exempt(node):
        return None
    call = _forward_return_call(node)
    if call is None or not isinstance(call.func, ast.Name):
        return None
    callee = call.func.id
    if callee == node.name or callee[:1].isupper():
        return None
    if not _forwards_all_params(node, call):
        return None
    target = definitions.get(callee)
    if target is None or target.decorator_list:
        return None
    contract = _function_call_contract(node)
    if contract is None or contract != _function_call_contract(target):
        return None
    if (isinstance(node, ast.AsyncFunctionDef)
            and not isinstance(target, ast.AsyncFunctionDef)):
        return None
    return callee
def _module_public_names(
        tree: ast.Module, statements: list,
        type_only_ids: set[int] | None = None) -> set[str] | None:
    type_only_ids = type_only_ids or set()
    statements = [node for node in statements
                  if id(node) not in type_only_ids]
    exports, exact = collect_module_exports_state(tree)
    has_all = bool(exports) or not exact or any(
        collect_all_export_names(node)[0] for node in statements)
    if has_all:
        return set(exports) if exact else None
    if any(isinstance(node, ast.ImportFrom)
           and any(alias.name == "*" for alias in node.names)
           for node in statements):
        return None
    names = import_bound_names(statements)
    for node in statements:
        names.update(module_binding_names(node))
    return {name for name in names if not name.startswith("_")}
def _module_forwarders(
        tree: ast.Module) -> tuple[int, list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, str]]]:
    type_only_ids = _type_checking_scope_ids(tree)
    statements = [node for node in iter_module_level_stmts(tree)
                  if id(node) not in type_only_ids]
    public_names = _module_public_names(tree, statements, type_only_ids)
    if public_names is None:
        return 0, []
    definitions = {}
    ambiguous_names: set[str] = {
        name
        for node in statements
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        for name in module_binding_names(node) | import_bound_names([node])
    }
    for node in statements:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name in definitions:
            ambiguous_names.add(node.name)
            definitions.pop(node.name, None)
        elif node.name not in ambiguous_names:
            definitions[node.name] = node
    wrappers: list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, str]] = []
    for node in statements:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name in ambiguous_names or node.name not in public_names:
            continue
        callee = _pure_forward_callee(node, definitions)
        if callee is not None:
            wrappers.append((node, callee))
    forwarding = {node.name: callee for node, callee in wrappers}
    def terminates_at_implementation(name: str) -> bool:
        seen: set[str] = set()
        while name in forwarding:
            if name in seen:
                return False
            seen.add(name)
            name = forwarding[name]
        return True
    wrappers = [
        (node, callee) for node, callee in wrappers
        if terminates_at_implementation(node.name)
    ]
    return len(public_names), wrappers
def _forwarder_preview(
        wrappers: list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, str]]) -> str:
    preview = "、".join(f"{node.name}()→{callee}()"
                       for node, callee in wrappers[:5])
    if len(wrappers) > 5:
        preview += f" 等 {len(wrappers)} 个"
    return preview
class PassthroughLayerDetector:
    MIN_WRAPPERS = 3
    MIN_RATIO = 0.5
    def detect(self, filepath: str) -> list[dict]:
        path = _coerce_source_path(filepath)
        if path is None:
            return []
        basename = os.path.basename(path).lower()
        if (basename in _PASSTHROUGH_SKIP_FILES
                or is_test_source_basename(basename)):
            return []
        tree = parse_tree(path)
        if tree is None:
            return []
        public_count, wrappers = _module_forwarders(tree)
        if len(wrappers) < self.MIN_WRAPPERS or not public_count:
            return []
        if len(wrappers) / public_count < self.MIN_RATIO:
            return []
        wrappers.sort(key=lambda item: item[0].lineno)
        detail = (
            f"纯转发层：模块公开面 {len(wrappers)}/{public_count} 个符号中，"
            f"这些函数仅原样转发（{_forwarder_preview(wrappers)}），"
            f"缺少校验/转换/副作用"
        )
        return [{
            "file": path,
            "line": wrappers[0][0].lineno,
            "count": len(wrappers),
            "public_count": public_count,
            "functions": [node.name for node, _callee in wrappers],
            "detail": detail,
            "message": detail,
            "suggestion": (
                "删除包装层让调用方直连目标，或为包装层补充真实职责"
                "（校验/转换/缓存/默认值收敛）；不要复制目标函数的默认参数"
            ),
        }]
class StubEliminator:
    def detect(self, filepath: str) -> list[dict]:
        path = _coerce_source_path(filepath)
        if path is None:
            return []
        tree = parse_tree(path)
        if tree is None:
            return []
        violations = []
        _protocol_ids = _protocol_member_ids(tree)
        _type_only_ids = _type_checking_scope_ids(tree)
        _suppressions = _load_suppressions(path)
        _resolver = _source_name_resolver(tree, path)
        for node in walk_nodes(tree):
            if (not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    or id(node) in _protocol_ids
                    or id(node) in _type_only_ids
                    or _is_protocol_stub(node, _resolver)):
                continue
            stub_stmt = self._stub_statement(node)
            if stub_stmt is None or _is_visitor_noop(node):
                continue
            if self._is_suppressed_stub(_suppressions, node):
                continue
            violations.append({
                "file": path,
                "line": node.lineno,
                "name": node.name,
                "type": "stub_function",
                "body": ast.unparse(stub_stmt),
            })
        violations.sort(key=lambda v: (v.get("line", 0), v.get("name", "")))
        return violations
    @staticmethod
    def _is_suppressed_stub(suppressions: dict, func_node: ast.AST) -> bool:
        if not suppressions:
            return False
        return any(
            _is_rule_suppressed(
                suppressions, func_node.lineno, rule, "C16_stubs")
            for rule in ("stub_function", "empty_function"))
    @staticmethod
    def _stub_statement(
            func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> ast.stmt | None:
        if is_dunder_name(func_node.name):
            return None
        stmts = [
            stmt for stmt in _non_docstring_body(func_node.body)
            if not _is_noop_stmt(stmt)]
        if len(stmts) != 1 or not isinstance(stmts[0], ast.Return):
            return None
        stmt = stmts[0]
        if not StubEliminator._is_stub_return_value(stmt.value):
            return None
        return stmt
    @staticmethod
    def _is_stub_return_value(value) -> bool:
        if value is None:
            return True
        is_literal, literal_value = _literal_default_value(value)
        if is_literal:
            return StubEliminator._is_zero_constant(literal_value)
        return ((isinstance(value, (ast.List, ast.Set, ast.Tuple))
                 and not value.elts)
                or (isinstance(value, ast.Dict) and not value.keys))
    @staticmethod
    def _is_zero_constant(value) -> bool:
        return (value is None or value is False
                or (isinstance(value, (int, float, complex))
                    and not isinstance(value, bool) and value == 0)
                or (isinstance(value, (str, bytes)) and not value))
def _source_name_resolver(
        tree: ast.Module, path: str) -> ScopeNameResolver | None:
    source = read_source(path)
    if source is None:
        return None
    return ScopeNameResolver(source, path, tree, set())
class DynamicImportConverter:
    DYNAMIC_PATTERNS = (
        'importlib.import_module',
        'import_module',
        '__import__',
    )
    def detect(self, filepath: str) -> list[dict]:
        path = _coerce_source_path(filepath)
        if path is None:
            return []
        tree = parse_tree(path)
        if tree is None:
            return []
        violations = []
        type_only_ids = _type_checking_scope_ids(tree)
        resolver = _source_name_resolver(tree, path)
        for node in walk_nodes(tree):
            if id(node) in type_only_ids:
                continue
            offense = _dynamic_import_offense(
                node, self.DYNAMIC_PATTERNS, resolver)
            if offense is None:
                continue
            call_name, module_name = offense
            violations.append({
                "file": path,
                "line": node.lineno,
                "type": "dynamic_import",
                "function": call_name,
                "module": module_name,
            })
        violations.sort(key=lambda v: (
            v.get("line", 0), v.get("module", ""),
            v.get("function", "")))
        return violations
    @staticmethod
    def _dynamic_import_module_name(node: ast.Call) -> str:
        arg = node.args[0] if node.args else None
        if arg is None:
            arg = next((kw.value for kw in node.keywords
                        if kw.arg == 'name'), None)
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            return arg.value
        if isinstance(arg, ast.Name):
            return f"<variable: {arg.id}>"
        return "?"
    def suggest_static_import(self, violation: dict) -> str:
        if not isinstance(violation, Mapping):
            return "# 无法自动转换动态导入: 未知模块"
        module = violation.get("module", "")
        if not isinstance(module, str):
            return "# 无法自动转换动态导入: 未知模块"
        if module.startswith('<') or not module or module == "?":
            return f"# 无法自动转换动态导入: {module or '未知模块'}"
        if not all(seg.isidentifier() for seg in module.split('.')):
            return f"# 无法自动转换动态导入: {module}"
        return f"import {module}  # 替换动态导入 (原行 {violation.get('line', 0)})"
def _canonical_dynamic_import_name(
    call_name: str, accepted: tuple[str, ...] | frozenset[str],
) -> str | None:
    if call_name in accepted:
        return call_name
    _stripped = call_name[len("builtins."):]
    if call_name.startswith("builtins.") and _stripped in accepted:
        return _stripped
    return None
def _dynamic_import_offense(
    node: ast.AST, patterns: tuple[str, ...] | frozenset[str],
    resolver: ScopeNameResolver | None,
) -> tuple[str, str] | None:
    if not isinstance(node, ast.Call):
        return None
    call_name = ASTUtils.resolve_call_name(node)
    resolved_name = call_name
    if resolver is not None:
        root = node.func
        while isinstance(root, ast.Attribute):
            root = root.value
        if isinstance(root, ast.Name):
            import_path = resolver.import_path(root)
            if import_path is not None:
                suffix = (call_name[len(root.id):]
                          if call_name.startswith(root.id) else "")
                resolved_name = import_path + suffix
            elif resolver.is_bound(root):
                return None
    canonical_name = _canonical_dynamic_import_name(resolved_name, patterns)
    if canonical_name is None:
        return None
    display_name = (call_name if resolved_name != call_name
                    else canonical_name)
    return display_name, DynamicImportConverter._dynamic_import_module_name(node)
def _import_signature(node: ast.AST) -> tuple | None:
    if isinstance(node, ast.Import):
        return ("import", node.lineno, tuple(sorted(a.name for a in node.names)))
    if isinstance(node, ast.ImportFrom):
        return ("from", node.lineno, node.level, node.module or "",
                tuple(sorted(a.name for a in node.names)))
    return None
def _toplevel_import_sigs(tree: ast.Module) -> frozenset[tuple]:
    sigs: set[tuple] = set()
    for n in iter_module_level_stmts(tree):
        s = _import_signature(n)
        if s is not None:
            sigs.add(s)
    return frozenset(sigs)
def _is_toplevel_import(node: ast.AST, toplevel_sigs: frozenset[tuple]) -> bool:
    sig = _import_signature(node)
    return sig is not None and sig in toplevel_sigs
def _scan_import_in_function(node: ast.AST, fpath: str,
                             toplevel_sigs: frozenset[tuple],
                             pkg_candidates: frozenset[str],
                             exempt_ids: set[int]) -> list:
    if not isinstance(node, (ast.Import, ast.ImportFrom)) \
            or _is_toplevel_import(node, toplevel_sigs) \
            or id(node) in exempt_ids:
        return []
    if isinstance(node, ast.ImportFrom):
        offenders = import_from_offenders(node, pkg_candidates)
        module = node.module or "?"
    else:
        offenders = import_member_offenders(node.names, pkg_candidates)
        module = ", ".join(name for name, _asname in offenders)
    if not offenders:
        return []
    return [{
        "type": "function_inner_import",
        "file": fpath, "line": node.lineno, "module": module,
    }]
def _scan_bare_except(node: ast.AST, fpath: str) -> list:
    issues: list[dict] = []
    if isinstance(node, ast.ExceptHandler) and _is_bare_except_pass(node):
        issues.append({
            "type": "bare_except_pass",
            "file": fpath, "line": node.lineno,
        })
    return issues
def _scan_dynamic_import(
        node: ast.AST, fpath: str,
        patterns: tuple[str, ...] | frozenset[str],
        resolver: ScopeNameResolver | None) -> list:
    offense = _dynamic_import_offense(node, patterns, resolver)
    if offense is None:
        return []
    return [{
        "type": "dynamic_import", "file": fpath,
        "line": node.lineno, "function": offense[0], "module": offense[1],
    }]
def _default_param_bindings(node: ast.AST) -> list[tuple[ast.arg, ast.AST]]:
    args = node.args
    positional = args.posonlyargs + args.args
    paired = list(zip(positional[len(positional) - len(args.defaults):],
                      args.defaults, strict=True))
    paired += [(arg, default) for arg, default in zip(args.kwonlyargs,
                                                      args.kw_defaults,
                                                      strict=True)
               if default is not None]
    return paired
def _scan_mutable_default(node: ast.AST, fpath: str) -> list:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
        return []
    return [
        {
            "type": RULE_MUTABLE_DEFAULT,
            "file": fpath, "line": default.lineno,
            "func": getattr(node, "name", "<lambda>"), "param": arg.arg,
        }
        for arg, default in _default_param_bindings(node)
        if _is_mutable_default(default)
    ]
def _fallback_issue_detail(issue: dict) -> str:
    itype = issue.get("type", "")
    if itype == "function_inner_import":
        return f"函数内导入 {issue.get('module') or '?'}"
    if itype == "bare_except_pass":
        return "裸 except + pass：吞掉异常且无处理"
    if itype == "dynamic_import":
        return (f"动态导入调用 {issue.get('function') or '__import__'}"
                f"（模块 {issue.get('module') or '?'}）")
    if itype == RULE_MUTABLE_DEFAULT:
        func = issue.get('func') or '?'
        param = issue.get('param')
        if param:
            return f"函数 {func} 的参数 {param} 使用可变默认参数"
        return f"函数 {func} 使用可变默认参数"
    return str(itype)
_NODE_SCANNERS = [_scan_bare_except, _scan_mutable_default]
def _scan_file_fallback(tree: ast.Module, fpath: str) -> list[dict]:
    toplevel = _toplevel_import_sigs(tree)
    pkgs = skill_pkg_candidates(fpath)
    exempt_ids = _collect_exempt_import_ids(tree)
    dynamic_resolver = _source_name_resolver(tree, fpath)
    type_only_ids = _type_checking_scope_ids(tree)
    issues: list[dict] = []
    for node in walk_nodes(tree):
        if id(node) in type_only_ids:
            continue
        issues.extend(_scan_import_in_function(
            node, fpath, toplevel, pkgs, exempt_ids))
        issues.extend(_scan_dynamic_import(
            node, fpath, DynamicImportConverter.DYNAMIC_PATTERNS,
            dynamic_resolver))
        for scanner in _NODE_SCANNERS:
            issues.extend(scanner(node, fpath))
    issues.sort(key=lambda issue: (
        issue.get("line", 0), issue.get("type", ""),
        issue.get("module", ""), issue.get("func", "")))
    return issues
def fallback_scan_file(fpath: str) -> list[dict] | None:
    path = _coerce_source_path(fpath)
    if path is None:
        return None
    parsed = ASTUtils.parse_file(path)
    if parsed is None:
        return None
    issues = _scan_file_fallback(parsed[0], path)
    for issue in issues:
        issue["severity"] = _FALLBACK_SEVERITY.get(issue.get("type", ""), "low")
        issue.setdefault("detail", _fallback_issue_detail(issue))
    return issues

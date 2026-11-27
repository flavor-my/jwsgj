# ruff: noqa: I001
from __future__ import annotations
import ast
import logging
import math
import operator
import os
import re
import symtable
from bisect import bisect_left
from collections import defaultdict
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, NamedTuple, Self
from jwsgj.build_module_topology import (
    ImportBinding,
    import_binding_name,
    iter_import_bindings,
    unused_import_bindings,
)
from jwsgj.cleanup_file_hygiene import (
    _analyze_import_scope,
    _ImportAnalysisDetails,
)
from jwsgj.diag_shared_ast_nodes import (
    argument_param_names,
    build_node_parent_map,
    class_body_owner,
    collect_annotation_names,
    count_params,
    decision_points,
    decorator_name,
    expr_target_name,
    is_static_method,
    iter_arg_nodes,
    iter_module_level_stmts,
    iter_scope_nodes,
)
from jwsgj.diag_shared_ast_surface import replay_export_surface
from jwsgj.diag_shared_source_core import (
    SOURCE_READ_PARSE_ERRORS,
    code_part,
    count_lines,
    parse_cached,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    split_lines_lf,
    string_comment_spans,
    string_token_row_spans,
)
from jwsgj.diag_types_vocab import (
    FIELD_TOTAL_FUNCTIONS,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    TEST_ARTIFACT_DIRS,
    is_pruned_scan_dir,
    scan_exclude_dirs,
)
from jwsgj.skill_profile import is_scan_py_name
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    'SQALE_REMEDIATION_MINUTES',
    'STALE_TODO_PATTERNS',
    'CodeCleaner',
    'CodeCleanupItem',
    'CodeCleanupReport',
    'CodeSmellDetector',
    'CodeSmellItem',
    'ComplexityAnalyzer',
    'ComplexityMetrics',
    'DebtItem',
    'DebtQuantifyReport',
    'compare_quality_baseline',
    'compute_quality_metrics',
    'estimate_remediation_minutes',
    'quantify_debt',
]
_log = logging.getLogger(__name__)
_NOQA_MARK_RE = re.compile(r"#\s*noqa\b", re.IGNORECASE)
def _function_param_names(
        node: ast.FunctionDef | ast.AsyncFunctionDef, *,
        is_method: bool) -> list[str]:
    names = argument_param_names(node.args)
    positional = [*node.args.posonlyargs, *node.args.args]
    if (is_method and positional and positional[0].arg in ("self", "cls")
            and not is_static_method(node)):
        return names[1:]
    return names
def _nested_function_line_numbers(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> set[int]:
    covered: set[int] = set()
    for child in walk_nodes(node):
        if child is node or not isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        end = child.end_lineno or child.lineno
        covered.update(range(child.lineno, end + 1))
    return covered
def function_effective_loc(
        source_lines: list[str],
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    end = node.end_lineno or node.lineno
    nested_lines = _nested_function_line_numbers(node)
    return sum(1 for i in range(node.lineno, end + 1)
               if i <= len(source_lines)
               and i not in nested_lines
               and source_lines[i - 1].strip()
               and not source_lines[i - 1].strip().startswith("#"))
def _line_has_noqa(source_lines: list[str], line: int) -> bool:
    if not 1 <= line <= len(source_lines):
        return False
    text = source_lines[line - 1]
    return bool(_NOQA_MARK_RE.search(text[len(code_part(text)):]))
def noqa_exempts_line(source_lines: list[str], line: int) -> bool:
    if _line_has_noqa(source_lines, line):
        return True
    prev = line - 1
    if not 1 <= prev <= len(source_lines):
        return False
    return (not code_part(source_lines[prev - 1]).strip()
            and _line_has_noqa(source_lines, prev))
@dataclass
class CodeCleanupItem:
    file_path: str = ""
    line_start: int = 0
    line_end: int = 0
    category: str = ""
    severity: str = "info"
    description: str = ""
    snippet: str = ""
    suggestion: str = ""
    confidence: float = 1.0
    metric_value: float = 0.0
_DYNAMIC_ATTRIBUTE_CALLS = frozenset({
    "getattr", "hasattr", "setattr", "delattr", "__getattribute__",
})
def _string_constant(node: ast.AST) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None
def _dynamic_attribute_accesses(
        node: ast.Call) -> tuple[tuple[ast.expr, ast.expr], ...]:
    func = node.func
    if isinstance(func, ast.Name) and func.id in _DYNAMIC_ATTRIBUTE_CALLS:
        if len(node.args) >= 2:
            return ((node.args[0], node.args[1]),)
        return ()
    if not (isinstance(func, ast.Attribute)
            and func.attr in _DYNAMIC_ATTRIBUTE_CALLS):
        return ()
    accesses: list[tuple[ast.expr, ast.expr]] = []
    if len(node.args) >= 2:
        accesses.append((node.args[0], node.args[1]))
    if node.args:
        accesses.append((func.value, node.args[0]))
    return tuple(accesses)
class DeadCodeFileIndex:
    def __init__(self: Self) -> None:
        self._referrers: dict[str, set[str]] = defaultdict(set)
        self._targeted: dict[str, dict[str, set[str]]] = defaultdict(
            lambda: defaultdict(set))
        self._wildcard_referrers: dict[str, set[str]] = defaultdict(set)
        self._attribute_names: set[str] = set()
    def add_import(self: Self, file_path: str, names: Iterable[str]) -> None:
        for name in names:
            self._referrers[name].add(file_path)
    def add_attribute_names(self: Self, names: Iterable[str]) -> None:
        self._attribute_names.update(names)
    def is_attribute_used(self: Self, name: str) -> bool:
        return name in self._attribute_names
    def add_reference(self: Self, file_path: str, name: str,
                      target_file: str) -> None:
        self._targeted[name][target_file].add(file_path)
    def add_wildcard_reference(self: Self, file_path: str,
                               target_file: str) -> None:
        self._wildcard_referrers[target_file].add(file_path)
    def has_wildcard_reference(self: Self, current_file: str = "") -> bool:
        if current_file:
            return any(
                fp != current_file
                for fp in self._wildcard_referrers.get(current_file, ()))
        return any(self._wildcard_referrers.values())
    def is_referenced(self: Self, name: str, current_file: str = "") -> bool:
        if any(fp != current_file for fp in self._referrers.get(name, ())):
            return True
        for target_file, referrers in self._targeted.get(name, {}).items():
            if current_file and target_file != current_file:
                continue
            if any(fp != current_file for fp in referrers):
                return True
        return False
class DeadCodeBaseVisitor(ast.NodeVisitor):
    def __init__(self: Self, source_lines: list[str],
                 file_path: str = "") -> None:
        super().__init__()
        self.source_lines = source_lines
        self.file_path = file_path
        self.items: list[CodeCleanupItem] = []
        self._used: set[str] = set()
        self._exported: set[str] = set()
        self._exports_declared = False
        self._exports_exact = True
    def _consume_annotation(self: Self, annotation: ast.expr | None) -> None:
        collect_annotation_names(annotation, self._used)
    def _is_possible_export(self: Self, name: str) -> bool:
        return (name in self._exported
                or (self._exports_declared and not self._exports_exact))
    def _snippet(self: Self, node: ast.AST, max_lines: int = 3) -> str:
        start = getattr(node, "lineno", 0)
        if start < 1 or start > len(self.source_lines):
            return ""
        end = min(getattr(node, "end_lineno", start) or start, start + max_lines - 1)
        return "\n".join(s.rstrip() for s in self.source_lines[start - 1:end])
    def _shared_visit_Name(self: Self, node: ast.Name) -> None:
        if isinstance(node.ctx, ast.Load):
            self._used.add(node.id)
        self.generic_visit(node)
    def _shared_visit_Attribute(self: Self, node: ast.Attribute) -> None:
        if isinstance(node.value, ast.Name):
            self._used.add(node.value.id)
        self.generic_visit(node)
    def visit(self: Self, node: ast.AST) -> Any:
        if isinstance(node, ast.Module):
            replay = replay_export_surface(node)
            self._exported.update(replay.names)
            self._exports_declared = replay.declared
            self._exports_exact = replay.exact
        return super().visit(node)
_PROP_NAME_FORMS: frozenset = frozenset({"property", "cached_property"})
_PROP_ATTR_FORMS: frozenset = frozenset(
    {"getter", "setter", "deleter", "property", "cached_property"})
_DECLARATIVE_STUB_FORMS: frozenset = frozenset(
    {"abstractmethod", "abstractproperty", "overload"})
def declarative_stub(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    names = {decorator_name(decorator) for decorator in node.decorator_list}
    return bool(names & _DECLARATIVE_STUB_FORMS)
LAZY_REGISTRY_FILENAMES: tuple[str, ...] = (
    "lazy_imports.py", "lazy_registry.py", "_lazy_registry.py",
)
_LAZY_REGISTRY_ENV = "SAFE_CODE_LAZY_REGISTRIES"
_LAZY_REGISTRY_CACHE: dict[
    str,
    tuple[
        tuple[str, ...],
        tuple[tuple[int, int] | None, ...],
        frozenset[str],
    ],
] | None = None
def _dict_symbol_items(node: ast.Dict) -> set:
    symbols: set = set()
    for value in node.values:
        if not isinstance(value, ast.Tuple):
            continue
        symbols.update(elt.value for elt in value.elts
                       if isinstance(elt, ast.Constant)
                       and isinstance(elt.value, str))
    return symbols
def _parse_lazy_registry_keys(tree: ast.Module) -> set:
    names: set = set()
    for stmt in iter_module_level_stmts(tree):
        if not isinstance(stmt, (ast.Assign, ast.AnnAssign)):
            continue
        if isinstance(stmt.value, ast.Dict):
            names |= _dict_symbol_items(stmt.value)
    return names
def _registry_names_in_file(lazy_path: str) -> set:
    source = read_source(lazy_path)
    if source is None:
        _log.warning("[DeadCode] lazy 登记册不可读，豁免集退化为空: %s",
                     lazy_path)
        return set()
    try:
        return _parse_lazy_registry_keys(
            parse_cached(source, filename=lazy_path))
    except SOURCE_READ_PARSE_ERRORS as e:
        _log.warning(
            "[DeadCode] lazy 登记册解析失败，豁免集退化为空: %s: %s: %s",
            lazy_path, type(e).__name__, e)
        return set()
def _consume_signature_annotations(node: ast.AST, used: set) -> None:
    collect_annotation_names(node.returns, used)
    for arg in iter_arg_nodes(node.args):
        collect_annotation_names(arg.annotation, used)
def _consume_class_annotations(node: ast.ClassDef, used: set) -> None:
    for base in node.bases:
        collect_annotation_names(base, used)
    for kw in node.keywords:
        collect_annotation_names(kw.value, used)
def _lazy_registry_stamp(lazy_path: str) -> tuple[int, int] | None:
    try:
        stat = os.stat(lazy_path)
    except OSError as e:
        if isinstance(e, FileNotFoundError):
            return None
        _log.warning(
            "[DeadCode] lazy 登记册指纹读取失败（豁免集退化为空）: %s: %s",
            lazy_path, e)
        return None
    return stat.st_mtime_ns, stat.st_size
def _lazy_registry_env_names() -> list[str]:
    raw = os.environ.get(_LAZY_REGISTRY_ENV, "")
    if not isinstance(raw, str) or not raw.strip():
        return []
    return [item.strip() for item in raw.split(os.pathsep) if item.strip()]
def _lazy_registry_paths(directory: str) -> list[str]:
    paths: list[str] = []
    seen: set[str] = set()
    for name in (*LAZY_REGISTRY_FILENAMES, *_lazy_registry_env_names()):
        path = name if os.path.isabs(name) else os.path.join(directory, name)
        key = os.path.normcase(os.path.abspath(path))
        if key in seen:
            continue
        seen.add(key)
        paths.append(path)
    return paths
def _load_lazy_registry_names(file_path: str) -> frozenset[str]:
    global _LAZY_REGISTRY_CACHE
    d = os.path.dirname(os.path.abspath(file_path))
    if _LAZY_REGISTRY_CACHE is None:
        _LAZY_REGISTRY_CACHE = {}
    paths = _lazy_registry_paths(d)
    path_keys = tuple(
        os.path.normcase(os.path.abspath(path)) for path in paths)
    stamps = tuple(_lazy_registry_stamp(path) for path in paths)
    cached = _LAZY_REGISTRY_CACHE.get(d)
    if (cached is not None and cached[0] == path_keys
            and cached[1] == stamps):
        return cached[2]
    names: set[str] = set()
    for path, stamp in zip(paths, stamps, strict=True):
        if stamp is not None:
            names |= _registry_names_in_file(path)
    frozen = frozenset(names)
    _LAZY_REGISTRY_CACHE[d] = (path_keys, stamps, frozen)
    return frozen
class _DeadDefinition(NamedTuple):
    line: int
    scope: tuple[str, ...]
    name: str
    is_property: bool
class DeadCodeVisitor(DeadCodeBaseVisitor):
    def __init__(self: Self, source_lines: list[str], file_path: str,
                 cross_index: DeadCodeFileIndex | None = None) -> None:
        super().__init__(source_lines, file_path)
        self.cross_index = cross_index
        self._defined: list[_DeadDefinition] = []
        self._defined_keys: set[tuple[tuple[str, ...], str, int]] = set()
        self._deleted: set[tuple[tuple[str, ...], str]] = set()
        self._scope_kinds: list[str] = []
        self._class_path: list[str] = []
        self._lazy_exported: frozenset[str] = _load_lazy_registry_names(
            file_path)
    def _inside_function_scope(self: Self) -> bool:
        return "function" in self._scope_kinds
    def visit_AnnAssign(self: Self, node: ast.AnnAssign) -> None:
        self.generic_visit(node)
        self._consume_annotation(node.annotation)
    @staticmethod
    def _has_property_decorator(decorator_list: list) -> bool:
        return any(
            (isinstance(decorator, ast.Name) and decorator.id in _PROP_NAME_FORMS)
            or (isinstance(decorator, ast.Attribute)
                and decorator.attr in _PROP_ATTR_FORMS)
            for decorator in decorator_list)
    def _register_defined(self: Self, name: str, lineno: int, *,
                          is_property: bool = False) -> None:
        if name.startswith("__") and name.endswith("__"):
            return
        scope = tuple(self._class_path)
        key = (scope, name, lineno)
        if key in self._defined_keys:
            return
        self._defined_keys.add(key)
        self._defined.append(_DeadDefinition(lineno, scope, name, is_property))
    def visit_FunctionDef(self: Self, node: ast.FunctionDef) -> None:
        if not self._inside_function_scope() and not declarative_stub(node):
            self._register_defined(
                node.name, node.lineno,
                is_property=self._has_property_decorator(node.decorator_list))
        _consume_signature_annotations(node, self._used)
        self._scope_kinds.append("function")
        try:
            self.generic_visit(node)
        finally:
            self._scope_kinds.pop()
    visit_AsyncFunctionDef = visit_FunctionDef
    def visit_ClassDef(self: Self, node: ast.ClassDef) -> None:
        if not self._inside_function_scope():
            self._register_defined(node.name, node.lineno)
        _consume_class_annotations(node, self._used)
        self._scope_kinds.append("class")
        self._class_path.append(node.name)
        try:
            self.generic_visit(node)
        finally:
            self._class_path.pop()
            self._scope_kinds.pop()
    def visit_Name(self: Self, node: ast.Name) -> None:
        if isinstance(node.ctx, ast.Del) and not self._inside_function_scope():
            self._deleted.add((tuple(self._class_path), node.id))
        self._shared_visit_Name(node)
    def visit_Attribute(self: Self, node: ast.Attribute) -> None:
        self._used.add(node.attr)
        self._shared_visit_Attribute(node)
    def visit_Call(self: Self, node: ast.Call) -> None:
        self._track_dynamic_refs(node)
        self._track_super_calls(node)
        self.generic_visit(node)
    def _track_dynamic_refs(self: Self, node: ast.Call) -> None:
        accesses = list(_dynamic_attribute_accesses(node))
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in ("get", "__getitem__", "__getattr__",
                                       "__getattribute__") and node.args):
            accesses.append((node.func.value, node.args[0]))
        for _receiver, name_node in accesses:
            value = _string_constant(name_node)
            if value is not None:
                self._used.add(value)
    def _track_super_calls(self: Self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Call):
            call = node.func.value
            if isinstance(call.func, ast.Name) and call.func.id == "super":
                self._used.add(node.func.attr)
    def _mark_import_bindings(
            self: Self, node: ast.Import | ast.ImportFrom) -> None:
        for alias in node.names:
            name = import_binding_name(node, alias)
            if name is not None:
                self._used.add(name)
        self.generic_visit(node)
    visit_Import = _mark_import_bindings
    visit_ImportFrom = _mark_import_bindings
    def _calc_confidence(self: Self, name: str) -> float:
        if self.cross_index is None:
            return 0.60
        if self.cross_index.is_referenced(name, self.file_path):
            return 0.0
        return 0.80
    def _covered_by_star_import(self: Self,
                                definition: _DeadDefinition) -> bool:
        if definition.scope:
            return False
        if not self._exports_declared:
            return not definition.name.startswith("_")
        if not self._exports_exact:
            return True
        return definition.name in self._exported
    def finalize(self: Self) -> None:
        definitions = sorted(
            self._defined, key=lambda d: (d.line, d.scope, d.name))
        for definition in definitions:
            scope = definition.scope
            name = definition.name
            if ((scope, name) in self._deleted
                    or definition.is_property or name in self._used):
                continue
            if not scope and (self._is_possible_export(name)
                              or name in self._lazy_exported):
                continue
            if (scope and self.cross_index is not None
                    and self.cross_index.is_attribute_used(name)):
                # 方法只能经属性访问；其他文件通过实例变量调用时导入链无法
                # 回溯到定义类，按文件内 visit_Attribute 的同一口径视为已引用。
                continue
            if (self.cross_index is not None
                    and self.cross_index.has_wildcard_reference(self.file_path)
                    and self._covered_by_star_import(definition)):
                continue
            line_no = definition.line
            if line_no > 0 and noqa_exempts_line(self.source_lines, line_no):
                continue
            confidence = self._calc_confidence(name)
            if confidence <= 0.0:
                continue
            self.items.append(CodeCleanupItem(
                file_path=self.file_path,
                line_start=line_no,
                line_end=line_no,
                category="dead_code",
                description=f"名称 '{name}' 已定义但未被使用",
                suggestion="如果确实不需要，请删除此定义；如果是公共 API，请添加到 __all__",
                confidence=confidence,
            ))
class _SymbolTableIndex:
    def __init__(self: Self, tree: ast.Module, source_lines: list[str],
                 file_path: str) -> None:
        self._tree = tree
        self._root = symtable.symtable(
            "\n".join(source_lines), file_path or "<scan>", "exec")
        self._children: dict[int, list[symtable.SymbolTable]] = {}
        self._table_parents: dict[int, symtable.SymbolTable] = {}
        self._tables: list[symtable.SymbolTable] = []
        self._scope_tables: dict[ast.AST, symtable.SymbolTable] = {tree: self._root}
        self._binding_scopes: dict[ast.stmt, ast.AST] = {}
        self._annotation_used: set[tuple[int, str]] = set()
        self._deleted_names: set[tuple[int, str]] = set()
        self._comprehension_loads: set[tuple[int, str]] = set()
        self._register_tables(self._root)
        self._map_scopes(tree, self._root, tree)
        self._captured_names: set[tuple[int, str]] = set()
        for table in self._tables:
            for symbol in table.get_symbols():
                if not (symbol.is_free() and symbol.is_referenced()):
                    continue
                provider = self._free_provider(table, symbol.get_name())
                if provider is not None:
                    self._captured_names.add((id(provider), symbol.get_name()))
        self._module_references = {
            symbol.get_name()
            for table in self._tables
            for symbol in table.get_symbols()
            if symbol.is_global() and symbol.is_referenced()
        }
    @classmethod
    def build(cls: type[Self], tree: ast.Module, source_lines: list[str],
              file_path: str) -> Self | None:
        try:
            return cls(tree, source_lines, file_path)
        except (SyntaxError, ValueError, RecursionError, MemoryError) as exc:
            _log.warning(
                "[CodeCleaner] %s 符号表构建失败，名称使用检测保守跳过: %s: %s",
                file_path, type(exc).__name__, exc)
            return None
    def _register_tables(self: Self, table: symtable.SymbolTable) -> None:
        children = list(table.get_children())
        self._tables.append(table)
        self._children[id(table)] = children
        for child in children:
            self._table_parents[id(child)] = table
            self._register_tables(child)
    def _take_child(self: Self, table: symtable.SymbolTable, name: str,
                    lineno: int, scope_type: str) -> symtable.SymbolTable:
        children = self._children[id(table)]
        index = next((i for i, child in enumerate(children)
                      if child.get_name() == name
                      and child.get_lineno() == lineno
                      and child.get_type() == scope_type), None)
        if index is None:
            raise ValueError(f"AST/符号表作用域不一致: {name}@{lineno}")
        return children.pop(index)
    def _map_scopes(self: Self, node: ast.AST,
                    table: symtable.SymbolTable, scope: ast.AST) -> None:
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Del):
            self._deleted_names.add((id(table), node.id))
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            self._binding_scopes[node] = scope
        if isinstance(node, _INLINED_COMPREHENSIONS):
            self._comprehension_loads.update(
                (id(table), name)
                for name in _comprehension_load_names(node))
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            scope_type = "class" if isinstance(node, ast.ClassDef) else "function"
            owner = table
            if getattr(node, "type_params", ()):
                # PEP 695：泛型函数/类在符号表中先挂一层 "type parameter" 作用域，
                # 函数/类作用域是它的子表，直接从父表取会误判作用域不一致。
                owner = self._take_child(
                    table, node.name, node.lineno, "type parameter")
            child = self._take_child(
                owner, node.name, node.lineno, scope_type)
            self._scope_tables[node] = child
            if isinstance(node, ast.ClassDef):
                header = [*node.decorator_list, *node.bases, *node.keywords]
            else:
                header = [*node.decorator_list, node.args, node.returns]
            for expr in header:
                if expr is not None:
                    self._map_scopes(expr, table, scope)
            for stmt in node.body:
                self._map_scopes(stmt, child, node)
            return
        for child in ast.iter_child_nodes(node):
            self._map_scopes(child, table, scope)
    def binding_scope(self: Self, stmt: ast.stmt | None) -> ast.AST:
        if stmt is None:
            return self._tree
        try:
            return self._binding_scopes[stmt]
        except KeyError as exc:
            raise ValueError(
                f"导入绑定缺少词法作用域映射: line {getattr(stmt, 'lineno', 0)}") from exc
    def _free_provider(self: Self, table: symtable.SymbolTable,
                       name: str) -> symtable.SymbolTable | None:
        current = self._table_parents.get(id(table))
        while current is not None:
            if current.get_type() == "function":
                try:
                    symbol = current.lookup(name)
                except KeyError:
                    symbol = None
                if (symbol is not None and symbol.is_local()
                        and not symbol.is_global() and not symbol.is_free()):
                    return current
            current = self._table_parents.get(id(current))
        return None
    def _resolve_annotation_table(
            self: Self, start: symtable.SymbolTable,
            name: str, allow_class: bool) -> symtable.SymbolTable:
        current = start
        allow_class = allow_class and start.get_type() == "class"
        while current is not None:
            if current.get_type() == "class" and not allow_class:
                current = self._table_parents.get(id(current))
                continue
            try:
                symbol = current.lookup(name)
            except KeyError:
                symbol = None
            if symbol is not None:
                if current is self._root or symbol.is_global():
                    return self._root
                if symbol.is_free():
                    provider = self._free_provider(current, name)
                    if provider is not None:
                        return provider
                return current
            allow_class = False
            current = self._table_parents.get(id(current))
        return self._root
    def mark_annotations(self: Self, scope: ast.AST,
                         names: Iterable[str], *,
                         allow_current_class: bool) -> None:
        table = self._scope_tables.get(scope)
        if table is None:
            return
        for name in names:
            resolved = self._resolve_annotation_table(
                table, name, allow_current_class)
            self._annotation_used.add((id(resolved), name))
    def name_used(self: Self, scope: ast.AST, name: str) -> bool:
        table = self._scope_tables.get(scope)
        if table is None:
            return True
        if ((id(table), name) in self._annotation_used
                or (id(table), name) in self._deleted_names
                or (id(table), name) in self._comprehension_loads):
            return True
        if table is self._root and name in self._module_references:
            return True
        try:
            symbol = table.lookup(name)
        except KeyError:
            return False
        if symbol.is_global():
            return (symbol.is_referenced()
                    or name in self._module_references
                    or (id(self._root), name) in self._annotation_used)
        if symbol.is_free():
            provider = self._free_provider(table, name)
            if provider is not None:
                try:
                    provider_symbol = provider.lookup(name)
                except KeyError:
                    provider_symbol = None
                if provider_symbol is not None and provider_symbol.is_referenced():
                    return True
                if ((id(provider), name) in self._annotation_used
                        or (id(provider), name) in self._captured_names):
                    return True
        return (symbol.is_referenced()
                or (id(table), name) in self._captured_names)
_INLINED_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp)
def _comprehension_load_names(node: ast.expr) -> set[str]:
    """收集内联推导式中解析到外层作用域的 Load 名称。

    CPython ≥3.12 按 PEP 709 内联 list/set/dict 推导式后，元素表达式与条件中的
    引用不再登记到外层 symtable，符号索引须从 AST 补采。推导式自身绑定的名称
    （迭代目标、海象赋值）与 lambda/生成器表达式体内的名称不解析到外层绑定，
    故先收集全部绑定再采集引用，避免元素表达式先于迭代目标被遍历而漏判。
    """
    bound: set[str] = set()
    pending: list[ast.AST] = [node]
    while pending:
        current = pending.pop()
        for child in ast.iter_child_nodes(current):
            if isinstance(child, ast.Name):
                if not isinstance(child.ctx, ast.Load):
                    bound.add(child.id)
                continue
            if isinstance(child, (ast.Lambda, ast.GeneratorExp)):
                continue
            pending.append(child)
    loads: set[str] = set()
    pending = [node]
    while pending:
        current = pending.pop()
        for child in ast.iter_child_nodes(current):
            if isinstance(child, ast.Name):
                if (isinstance(child.ctx, ast.Load)
                        and child.id not in bound):
                    loads.add(child.id)
                continue
            if isinstance(child, ast.Lambda):
                pending.extend([
                    *child.args.defaults,
                    *(d for d in child.args.kw_defaults if d is not None)])
                continue
            if isinstance(child, ast.GeneratorExp):
                pending.append(child.generators[0].iter)
                continue
            pending.append(child)
    return loads

def _is_reexport_binding(binding: ImportBinding) -> bool:
    stmt = binding.stmt
    if not isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return False
    return any(alias.asname is not None
               and alias.asname == alias.name == binding.bound
               for alias in stmt.names)
class DeadImportVisitor(DeadCodeBaseVisitor):
    def __init__(self: Self, source_lines: list[str], file_path: str) -> None:
        super().__init__(source_lines, file_path)
        self._imported: list[ImportBinding] = []
        self._attribute_names: set[str] = set()
    def visit(self: Self, node: ast.AST) -> Any:
        if isinstance(node, ast.Module):
            self._imported.extend(iter_import_bindings(node))
            self._symbol_index = _SymbolTableIndex.build(
                node, self.source_lines, self.file_path)
            self._current_scope = node
        return super().visit(node)
    def _mark_annotation_names(self: Self, names: set[str], *,
                               allow_current_class: bool) -> None:
        index = getattr(self, "_symbol_index", None)
        if index is not None:
            index.mark_annotations(
                self._current_scope, names,
                allow_current_class=allow_current_class)
    def _visit_function(self: Self, node: ast.FunctionDef) -> None:
        names: set[str] = set()
        _consume_signature_annotations(node, names)
        self._mark_annotation_names(names, allow_current_class=True)
        previous = self._current_scope
        self._current_scope = node
        try:
            for stmt in node.body:
                self.visit(stmt)
        finally:
            self._current_scope = previous
    visit_FunctionDef = _visit_function
    visit_AsyncFunctionDef = _visit_function
    def visit_ClassDef(self: Self, node: ast.ClassDef) -> None:
        names: set[str] = set()
        _consume_class_annotations(node, names)
        self._mark_annotation_names(names, allow_current_class=True)
        previous = self._current_scope
        self._current_scope = node
        try:
            for stmt in node.body:
                self.visit(stmt)
        finally:
            self._current_scope = previous
    def visit_AnnAssign(self: Self, node: ast.AnnAssign) -> None:
        names: set[str] = set()
        collect_annotation_names(node.annotation, names)
        self._mark_annotation_names(names, allow_current_class=True)
        self.generic_visit(node)
    def visit_Attribute(self: Self, node: ast.Attribute) -> None:
        self._attribute_names.add(node.attr)
        self.generic_visit(node)
    def _binding_used(self: Self, binding: ImportBinding) -> bool:
        index = getattr(self, "_symbol_index", None)
        if index is None:
            return True
        scope = index.binding_scope(binding.stmt)
        if index.name_used(scope, binding.bound):
            return True
        if isinstance(scope, ast.Module):
            return self._is_possible_export(binding.bound)
        return (isinstance(scope, ast.ClassDef)
                and binding.bound in self._attribute_names)
    def _binding_exempt(self: Self, binding: ImportBinding) -> bool:
        index = getattr(self, "_symbol_index", None)
        module_scope = (index is not None and isinstance(
            index.binding_scope(binding.stmt), ast.Module))
        if _is_reexport_binding(binding) and (index is None or module_scope):
            return True
        if noqa_exempts_line(self.source_lines, binding.lineno):
            return True
        return (binding.alias_lineno != binding.lineno
                and noqa_exempts_line(self.source_lines, binding.alias_lineno))
    def finalize(self: Self) -> None:
        bindings = sorted(self._imported,
                          key=lambda b: (b.lineno, b.alias_lineno))
        for binding in unused_import_bindings(
                bindings, self._binding_used, self._binding_exempt):
            line_no = binding.alias_lineno or binding.lineno
            self.items.append(CodeCleanupItem(
                file_path=self.file_path,
                line_start=line_no,
                line_end=line_no,
                category="dead_import",
                severity="warning",
                description=f"导入 '{binding.bound}' 在本文件中未被使用",
                suggestion=f"移除未使用的导入 '{binding.bound}'（若为 re-export 请加入 __all__）",
                confidence=0.8,
            ))
def _stmt_frag_if(stmt: ast.If) -> str:
    extra = f"if_{len(stmt.body)}"
    if stmt.orelse:
        extra += f"_else_{len(stmt.orelse)}"
    return f"{type(stmt).__name__}|{extra}"
def _stmt_frag_loop(stmt: ast.For | ast.While) -> str:
    return f"{type(stmt).__name__}|{type(stmt).__name__.lower()}_{len(stmt.body)}"
def _stmt_frag_try(stmt: ast.stmt) -> str:
    return f"{type(stmt).__name__}|try_{len(stmt.body)}_{len(stmt.handlers)}"
def _stmt_frag_return(_stmt: ast.stmt) -> str:
    return "Return|ret"
def _stmt_frag_assign(stmt: ast.Assign) -> str:
    return f"{type(stmt).__name__}|assign_{len(stmt.targets)}"
def _stmt_frag_expr(stmt: ast.Expr) -> str:
    if isinstance(stmt.value, ast.Call):
        func_id = stmt.value.func.id if isinstance(stmt.value.func, ast.Name) else "call"
        return f"{type(stmt).__name__}|call_{func_id}"
    return f"{type(stmt).__name__}|expr"
_STMT_HASH_FRAGMENTS: dict = {
    "If": _stmt_frag_if,
    "For": _stmt_frag_loop,
    "While": _stmt_frag_loop,
    "Try": _stmt_frag_try,
    "TryStar": _stmt_frag_try,
    "Return": _stmt_frag_return,
    "Assign": _stmt_frag_assign,
    "Expr": _stmt_frag_expr,
}
class StructuralDupDetector(DeadCodeBaseVisitor):
    def __init__(self: Self, source_lines: list[str], file_path: str) -> None:
        super().__init__(source_lines, file_path)
        self._struct_hashes: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
    def finalize(self: Self) -> None:
        for locations in self._struct_hashes.values():
            if len(locations) < 2:
                continue
            first = locations[0]
            for dup in locations[1:]:
                if noqa_exempts_line(self.source_lines, dup[0]):
                    continue
                self.items.append(CodeCleanupItem(
                    file_path=self.file_path,
                    line_start=dup[0],
                    line_end=dup[1],
                    category="duplicate_code",
                    description=f"函数 '{dup[2]}' 与 '{first[2]}' (line {first[0]}) 结构重复",
                    suggestion="提取为公共函数或使用装饰器消除重复",
                    confidence=0.7,
                ))
    def visit_FunctionDef(self: Self, node: ast.FunctionDef) -> None:
        if len(node.body) >= 3:
            self._struct_hashes[self._hash_body(node.body)].append(
                (node.lineno, node.end_lineno or node.lineno, node.name))
        self.generic_visit(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    @staticmethod
    def _hash_body(body: list[ast.stmt]) -> str:
        return "|".join(StructuralDupDetector._stmt_hash_part(stmt) for stmt in body)
    @staticmethod
    def _stmt_hash_part(stmt: ast.stmt) -> str:
        builder = _STMT_HASH_FRAGMENTS.get(type(stmt).__name__)
        if builder is None:
            return type(stmt).__name__
        return builder(stmt)
def _is_docstring_stmt(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and isinstance(stmt.value.value, str))
def _is_ellipsis_stmt(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and stmt.value.value is Ellipsis)
def _is_noop_stmt(stmt: ast.stmt) -> bool:
    if (isinstance(stmt, ast.Pass) or _is_ellipsis_stmt(stmt)
            or _is_docstring_stmt(stmt)):
        return True
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and stmt.value.value is None)
def _shape_exempt(name: str, exported: set[str]) -> bool:
    return name in exported or name.startswith("test_")
def _signature_locked(name: str) -> bool:
    return name != "__init__" and name.startswith("__") and name.endswith("__")
_DECLARATIVE_CLASS_BASES = frozenset({"Protocol", "ABC", "ABCMeta"})
def _class_base_name(base: ast.expr) -> str:
    while isinstance(base, ast.Subscript):
        base = base.value
    return expr_target_name(base)
def _is_declarative_class(node: ast.ClassDef) -> bool:
    if any(_class_base_name(base) in _DECLARATIVE_CLASS_BASES
           for base in node.bases):
        return True
    return any(kw.arg == "metaclass"
               and _class_base_name(kw.value) in _DECLARATIVE_CLASS_BASES
               for kw in node.keywords)
class RedundantCodeVisitor(DeadCodeBaseVisitor):
    def __init__(self: Self, source_lines: list[str],
                 file_path: str = "") -> None:
        super().__init__(source_lines, file_path)
        self._declarative_depth = 0
    def _append_shape_item(self: Self, node: ast.stmt | ast.ExceptHandler,
                           description: str, suggestion: str) -> None:
        self.items.append(CodeCleanupItem(
            file_path=self.file_path,
            line_start=node.lineno,
            line_end=node.end_lineno or node.lineno,
            category="redundant", severity="warning",
            description=description,
            snippet=self._snippet(node),
            suggestion=suggestion,
        ))
    def visit_FunctionDef(self: Self, node: ast.FunctionDef) -> None:
        if (self._declarative_depth
                or _shape_exempt(node.name, self._exported)
                or _signature_locked(node.name)
                or declarative_stub(node)):
            self.generic_visit(node)
            return
        is_stub, stub_reason = self._classify_stub_body(node.body)
        if is_stub and not noqa_exempts_line(self.source_lines, node.lineno):
            self._append_shape_item(
                node,
                f"空壳/桩函数 '{node.name}': {stub_reason}",
                f"实现函数 '{node.name}' 或移除该桩定义",
            )
        self.generic_visit(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    @staticmethod
    def _classify_stub_body(body: list[ast.stmt]) -> tuple[bool, str]:
        statements = [stmt for stmt in body if not _is_docstring_stmt(stmt)]
        if not statements:
            return True, "仅含文档字符串的空壳函数"
        if len(statements) != 1:
            return False, ""
        stmt = statements[0]
        for checker in (RedundantCodeVisitor._stub_reason_pass,
                        RedundantCodeVisitor._stub_reason_ellipsis,
                        RedundantCodeVisitor._stub_reason_notimpl,
                        RedundantCodeVisitor._stub_reason_return,
                        RedundantCodeVisitor._stub_reason_none_expr):
            is_stub, reason = checker(stmt)
            if is_stub:
                return True, reason
        return False, ""
    @staticmethod
    def _stub_reason_pass(stmt: ast.stmt) -> tuple[bool, str]:
        if isinstance(stmt, ast.Pass):
            return True, "仅含 pass 的空壳函数"
        return False, ""
    @staticmethod
    def _stub_reason_ellipsis(stmt: ast.stmt) -> tuple[bool, str]:
        if _is_ellipsis_stmt(stmt):
            return True, "仅含省略号 '...' 的空壳函数"
        return False, ""
    @staticmethod
    def _stub_reason_notimpl(stmt: ast.stmt) -> tuple[bool, str]:
        if not isinstance(stmt, ast.Raise) or stmt.exc is None:
            return False, ""
        exc = stmt.exc.func if isinstance(stmt.exc, ast.Call) else stmt.exc
        is_not_implemented = (
            isinstance(exc, ast.Name) and exc.id == "NotImplementedError"
        ) or (
            isinstance(exc, ast.Attribute) and exc.attr == "NotImplementedError"
        )
        if is_not_implemented:
            return True, "仅抛出 NotImplementedError 的桩函数"
        return False, ""
    @staticmethod
    def _stub_reason_return(stmt: ast.stmt) -> tuple[bool, str]:
        if isinstance(stmt, ast.Return):
            if stmt.value is None:
                return True, "仅 return None 的空函数"
            if isinstance(stmt.value, ast.Constant):
                return True, f"仅返回常量 '{stmt.value.value}' 的无意义函数"
        return False, ""
    @staticmethod
    def _stub_reason_none_expr(stmt: ast.stmt) -> tuple[bool, str]:
        if (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and stmt.value.value is None):
            return True, "仅含 None 表达式的空函数"
        return False, ""
    def visit_ClassDef(self: Self, node: ast.ClassDef) -> None:
        declarative = (self._declarative_depth > 0
                       or _is_declarative_class(node))
        if declarative:
            self._declarative_depth += 1
        try:
            self._visit_class_body(node, declarative)
        finally:
            if declarative:
                self._declarative_depth -= 1
    def _visit_class_body(self: Self, node: ast.ClassDef,
                          declarative: bool) -> None:
        if declarative or node.name in self._exported:
            self.generic_visit(node)
            return
        body = [n for n in node.body
                if not _is_noop_stmt(n)
                and not _is_docstring_stmt(n)]
        is_bare = not node.bases and not node.keywords
        if not body and is_bare and not noqa_exempts_line(self.source_lines, node.lineno):
            self._append_shape_item(
                node,
                f"空壳类 '{node.name}': 无任何方法或属性",
                f"实现类 '{node.name}' 或移除该空壳定义",
            )
        self.generic_visit(node)
    def visit_Try(self: Self, node: ast.Try) -> None:
        for handler in node.handlers:
            if (handler.body
                    and all(_is_noop_stmt(stmt) for stmt in handler.body)
                    and not noqa_exempts_line(self.source_lines, handler.lineno)):
                exc_name = self._handler_exc_name(handler)
                self._append_shape_item(
                    handler,
                    f"空 except 块（静默吞 {exc_name} 异常）",
                    "添加日志记录或重新抛出异常",
                )
        self.generic_visit(node)
    visit_TryStar = visit_Try
    @staticmethod
    def _handler_exc_name(handler: ast.ExceptHandler) -> str:
        if handler.type is None:
            return "Exception"
        if isinstance(handler.type, ast.Name):
            return handler.type.id
        if isinstance(handler.type, ast.Tuple):
            names = [e.id for e in handler.type.elts if isinstance(e, ast.Name)]
            return ", ".join(names) if names else "Exception"
        return "Exception"
class InvalidFuncVisitor(DeadCodeBaseVisitor):
    def visit(self: Self, node: ast.AST) -> Any:
        if isinstance(node, ast.Module):
            self._parents = build_node_parent_map(node)
            self._symbol_index = _SymbolTableIndex.build(
                node, self.source_lines, self.file_path)
        return super().visit(node)
    def visit_FunctionDef(self: Self, node: ast.FunctionDef) -> None:
        if (_shape_exempt(node.name, self._exported)
                or _signature_locked(node.name) or declarative_stub(node)):
            self.generic_visit(node)
            return
        args = _function_param_names(
            node, is_method=class_body_owner(
                node, getattr(self, '_parents', {})) is not None)
        if args:
            self._report_all_unused_params(node, args)
        self.generic_visit(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    def _parameter_used(self: Self, node: ast.FunctionDef, name: str) -> bool:
        index = getattr(self, "_symbol_index", None)
        if index is None:
            return True
        return index.name_used(node, name)
    def _report_all_unused_params(self: Self, node: ast.FunctionDef,
                                  args: list[str]) -> None:
        if len(args) < 2 or noqa_exempts_line(self.source_lines, node.lineno):
            return
        unused_args = [
            name for name in args if not self._parameter_used(node, name)]
        if unused_args != args:
            return
        self.items.append(CodeCleanupItem(
            file_path=self.file_path,
            line_start=node.lineno,
            line_end=node.end_lineno or node.lineno,
            category="invalid_func", severity="info",
            description=f"全部参数未使用: {', '.join(unused_args)}",
            snippet=self._snippet(node, max_lines=1).strip(),
            suggestion=f"检查函数 '{node.name}' 参数是否必要",
        ))
_StaleLineMatcher = Callable[[str, str, int], re.Match[str] | None]
STALE_TODO_PATTERNS: list[tuple[str, str]] = [
    (r"#\s*TODO.*(?:later|someday|eventually|maybe|never)", "过时 TODO（含推延关键词）"),
    (r"#\s*FIXME.*(?:later|someday|eventually|never)", "过时 FIXME（含推延关键词）"),
    (r"#\s*HACK.*(?:workaround|magic|ugly|hack|temporary)", "临时 HACK 标记"),
    (r"#\s*XXX.*(?:\?\?|\?\?\?)", "未明确的 XXX 标记"),
    (r"#\s*BUG.*(?:later|maybe|someday|never)", "延迟修复的 BUG 标记"),
    (r"#\s*(?:待办|待修复|待优化|待删除|待重构).*$", "中文待办标记"),
]
_EMPTY_COMMENT_PATTERNS: list[str] = [
    r"^\s*#\s*$",
    r"^\s*#\s*[=\-]{3,}\s*$",
    r"^\s*#\s*TODO\s*$",
    r"^\s*#\s*FIXME\s*$",
    r"^\s*#\s*HACK\s*$",
    r"^\s*#\s*XXX\s*$",
    r"^\s*#\s*NOTE\s*$",
]
_REDUNDANT_COMMENT_PATTERNS: list[str] = [
    r"^\s*#\s*import\s+[A-Za-z_]",
    r"^\s*#\s*from\s+[A-Za-z_][\w.]*\s+import\s",
    r"^\s*#\s*print\(",
    r"^\s*#\s*logging\.",
    r"^\s*#\s*(?:if|elif|for|while)\s+(?:not\s+[A-Za-z_(]|(?!not\b)[A-Za-z_(])",
    r"^\s*#\s*try\s*:",
    r"^\s*#\s*except\b[^:\n]*:",
    r"^\s*#\s*(?:def|class)\s+[A-Za-z_]",
    r"^\s*#\s*return(?:\s+[A-Za-z_\d({\['\"+-]|$)",
    r"^\s*#\s*raise\s+[A-Za-z_]",
]
_MIN_CONSECUTIVE_COMMENT_BLOCK = 5
_LEGACY_PATTERNS: list[tuple[str, str]] = [
    (r"except\s+ImportError\s*:\s*\n\s*\w+\s*=\s*(?:None|object|dict|list)", "ImportError 兜底赋值"),
    (r"if\s+sys\.version_info\s*<\s*\(\s*3\s*[,\)]", "Python 2/3 版本检查"),
    (r"if\s+sys\.version_info\s*\[0\]\s*<\s*3", "Python 主版本号检查"),
    (r"if\s+sys\.version_info\s*\[0\]\s*==\s*2", "Python 2 显式版本分支"),
    (r"from\s+typing\s+import\s+[^#\n]*\b(?:List|Dict|Tuple|Set|Optional|Union)\b", "旧版 typing 导入"),
    (r"isinstance\(.*,\s*(?:unicode|basestring|long)\b", "Python 2 内置类型检查"),
]
_LEGACY_COMMENT_PATTERNS: list[tuple[str, str]] = [
    (r"#\s*py2\b", "Python 2 注释"),
    (r"coding\s*[:=]\s*.*(?:latin|gb2312|gbk|big5)", "旧版编码声明"),
]
def _mask_source(content: str, *, include_comments: bool = False
                 ) -> str | None:
    spans = (string_comment_spans(content) if include_comments
             else string_token_row_spans(content))
    if spans is None:
        return None
    lines = content.split("\n")
    for row, row_spans in spans.items():
        if not 0 < row <= len(lines):
            continue
        chars = list(lines[row - 1])
        for start, end in row_spans:
            for index in range(max(0, start), min(len(chars), end)):
                if chars[index] not in "\r\n":
                    chars[index] = " "
        lines[row - 1] = "".join(chars)
    return "\n".join(lines)
_STALE_LINE_RULES: tuple[tuple[_StaleLineMatcher, int,
                              tuple[tuple[str, str], ...], str, str],
                         ...] = (
    (re.search, re.IGNORECASE, tuple(STALE_TODO_PATTERNS), "info",
     "移除该标记并解决对应问题"),
    (re.match, 0, tuple((p, "空注释或分隔线") for p in _EMPTY_COMMENT_PATTERNS),
     "info", "移除此行"),
    (re.match, 0, tuple((p, "注释掉的代码行") for p in _REDUNDANT_COMMENT_PATTERNS),
     "warning", "移除此行，依赖版本控制管理历史代码"),
)
def _line_snippet(lines: list[str], lineno: int) -> str:
    return lines[lineno - 1].strip() if 0 < lineno <= len(lines) else ""
def _match_stale_line(file_path: str, lineno: int, stripped: str,
                      snippet: str | None = None) -> CodeCleanupItem | None:
    for matcher, flags, patterns, severity, suggestion in _STALE_LINE_RULES:
        for pattern, desc in patterns:
            if matcher(pattern, stripped, flags):
                return CodeCleanupItem(
                    file_path=file_path, line_start=lineno, line_end=lineno,
                    category="stale_comment", severity=severity,
                    description=desc,
                    snippet=stripped if snippet is None else snippet,
                    suggestion=suggestion,
                )
    return None
def _comment_block_item(file_path: str, start: int | None, end_line: int,
                       count: int) -> CodeCleanupItem | None:
    if start is None or count < _MIN_CONSECUTIVE_COMMENT_BLOCK:
        return None
    return CodeCleanupItem(
        file_path=file_path,
        line_start=start, line_end=end_line,
        category="stale_comment", severity="info",
        description=f"过长连续注释块（{count} 行）",
        snippet=f"第 {start}-{end_line} 行",
        suggestion="压缩或移除过长的连续注释块",
    )
def detect_stale_comments(file_path: str, lines: list[str]) -> list[CodeCleanupItem]:
    items: list[CodeCleanupItem] = []
    masked = _mask_source("\n".join(lines))
    if masked is None:
        _log.warning(
            "[CodeCleaner] %s 掩码不可用（tokenize 失败），跳过注释类检测",
            file_path)
        return items
    masked_lines = masked.split("\n")
    consecutive_comment_start: int | None = None
    consecutive_count = 0
    for i, (line, masked_line) in enumerate(
            zip(lines + [""], masked_lines + [""], strict=True), 1):
        stripped = masked_line.strip()
        if stripped.startswith("#"):
            if consecutive_comment_start is None:
                consecutive_comment_start = i
            consecutive_count += 1
        else:
            block = _comment_block_item(
                file_path, consecutive_comment_start, i - 1,
                consecutive_count)
            if block is not None:
                items.append(block)
            consecutive_comment_start = None
            consecutive_count = 0
        matched = _match_stale_line(file_path, i, stripped,
                                    snippet=line.strip())
        if matched is not None:
            items.append(matched)
    return items
def detect_legacy_code(file_path: str, content: str) -> list[CodeCleanupItem]:
    items: list[CodeCleanupItem] = []
    lines = content.split("\n")
    newline_offsets = [m.start() for m in re.finditer(r"\n", content)]
    views = (
        (_mask_source(content, include_comments=True), _LEGACY_PATTERNS),
        (_mask_source(content), _LEGACY_COMMENT_PATTERNS),
    )
    if all(view is None for view, _patterns in views):
        _log.warning(
            "[CodeCleaner] %s 掩码不可用（tokenize 失败），跳过遗留代码检测",
            file_path)
        return items
    for view, patterns in views:
        if view is None:
            continue
        for pattern, desc in patterns:
            for match in re.finditer(pattern, view, re.MULTILINE):
                line_no = bisect_left(newline_offsets, match.start()) + 1
                snippet = _line_snippet(lines, line_no)
                items.append(CodeCleanupItem(
                    file_path=file_path, line_start=line_no, line_end=line_no,
                    category="legacy_compat", severity="info",
                    description=desc, snippet=snippet,
                    suggestion=f"移除旧版代码：{desc}",
                ))
    items.sort(key=lambda item: (item.line_start, item.description))
    return items
def _import_source(node: ast.Import | ast.ImportFrom,
                   alias: ast.alias) -> str:
    if isinstance(node, ast.ImportFrom):
        return f"from:{'.' * node.level}{node.module or ''}:{alias.name}"
    return f"import:{alias.name}"
def detect_redundant_imports(file_path: str, tree: ast.AST, lines: list[str]) -> list[CodeCleanupItem]:
    details = _ImportAnalysisDetails()
    _analyze_import_scope(getattr(tree, "body", []), details)
    alias_lines: dict[tuple[int, str, str], list[int]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        for alias in node.names:
            binding = import_binding_name(node, alias)
            if binding is None:
                continue
            key = (node.lineno, _import_source(node, alias), binding)
            alias_lines.setdefault(key, []).append(
                getattr(alias, "lineno", 0) or node.lineno)
    items: list[CodeCleanupItem] = []
    for scope_records in details.scope_records:
        for record in scope_records.values():
            for node, alias, previous_lines in record.occurrences:
                binding = import_binding_name(node, alias)
                if binding is None or not previous_lines:
                    continue
                first_line = min(previous_lines)
                source = _import_source(node, alias)
                first_candidates = alias_lines.get(
                    (first_line, source, binding), [first_line])
                first_report_line = min(first_candidates)
                dup_line = node.lineno
                dup_alias_line = getattr(alias, "lineno", 0) or dup_line
                dup_report_line = dup_alias_line or dup_line
                if (noqa_exempts_line(lines, dup_line)
                        or (dup_alias_line != dup_line
                            and noqa_exempts_line(lines, dup_alias_line))):
                    continue
                items.append(CodeCleanupItem(
                    file_path=file_path,
                    line_start=dup_report_line, line_end=dup_report_line,
                    category="redundant", severity="warning",
                    description=f"重复导入: '{binding}'（首次在第 {first_report_line} 行）",
                    snippet=_line_snippet(lines, dup_report_line),
                    suggestion="移除重复的导入语句",
                ))
    items.sort(key=lambda item: (item.line_start, item.description))
    return items
@dataclass
class CodeSmellItem:
    file_path: str = ""
    line_start: int = 0
    line_end: int = 0
    func_name: str = ""
    smell_type: str = ""
    severity: str = "info"
    description: str = ""
    metric_value: float = 0.0
    threshold: float = 0.0
    suggestion: str = ""
@dataclass
class ComplexityMetrics:
    func_name: str = ""
    file_path: str = ""
    line_start: int = 0
    line_end: int = 0
    lines_of_code: int = 0
    cyclomatic_complexity: int = 0
    halstead_volume: float = 0.0
    maintainability_index: float = 100.0
    param_count: int = 0
    max_nesting_depth: int = 0
    branch_count: int = 0
@dataclass
class CodeCleanupReport:
    skill_dir: str = ""
    total_files_scanned: int = 0
    total_lines_scanned: int = 0
    items: list[CodeCleanupItem] = field(default_factory=list)
    smell_items: list[CodeSmellItem] = field(default_factory=list)
    complexity_top: list[ComplexityMetrics] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    debt: DebtQuantifyReport | None = None
@dataclass
class DebtItem:
    id: str = ""
    rule_id: str = ""
    severity: str = ""
    file: str = ""
    line: int = 0
    message: str = ""
    remediation_minutes: int = 0
    debt_type: str = "code"
    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id, "rule_id": self.rule_id, "severity": self.severity,
            "file": self.file, "line": self.line, "message": self.message,
            "remediation_minutes": self.remediation_minutes,
            "debt_type": self.debt_type,
        }
@dataclass
class DebtQuantifyReport:
    debt_items: list[DebtItem] = field(default_factory=list)
    total_remediation_minutes: int = 0
    estimated_dev_hours: float = 0.0
    debt_ratio_pct: float = 0.0
    overall_score: int = 100
    recommendations: list[str] = field(default_factory=list)
    summary: str = ""
    def to_dict(self) -> dict[str, Any]:
        return {
            "debt_items": [d.to_dict() for d in self.debt_items],
            "total_remediation_minutes": self.total_remediation_minutes,
            "estimated_dev_hours": round(self.estimated_dev_hours, 2),
            "debt_ratio_pct": round(self.debt_ratio_pct, 2),
            "overall_score": self.overall_score,
            "recommendations": list(self.recommendations),
            "summary": self.summary,
        }
class _SmellType:
    LONG_FUNCTION = "long_function"
    LONG_PARAMS = "long_params"
    HIGH_CC = "high_cc"
    DEEP_NESTING = "deep_nesting"
SQALE_REMEDIATION_MINUTES: dict[str, int] = {
    _SmellType.LONG_FUNCTION: 30,
    _SmellType.LONG_PARAMS: 10,
    _SmellType.HIGH_CC: 15,
    _SmellType.DEEP_NESTING: 15,
    "magic_number": 10,
    "dead_code": 5,
}
_SQALE_DEFAULT_MINUTES = 15
_QUALITY_SCORE_NOT_MEASURED = -1
def estimate_remediation_minutes(smell_type: str) -> int:
    if not isinstance(smell_type, str):
        return _SQALE_DEFAULT_MINUTES
    return SQALE_REMEDIATION_MINUTES.get(smell_type, _SQALE_DEFAULT_MINUTES)
_MI_PENALTIES: tuple[tuple[float, int], ...] = ((50, 30), (65, 15), (85, 5))
_DEBT_RATIO_PENALTIES: tuple[tuple[float, int], ...] = ((20, 25), (10, 10))
_CYCLOMATIC_PENALTIES: tuple[tuple[float, int], ...] = ((20, 15), (10, 5))
_MAX_FILE_LOC_HINT = 1000
def _tiered_penalty(
    value: float,
    tiers: tuple[tuple[float, int], ...],
    compare: Callable[[float, float], bool],
) -> int:
    for threshold, penalty in tiers:
        if compare(value, threshold):
            return penalty
    return 0
def _sqale_overall_score(mi: float, debt_ratio: float, cyclomatic: int) -> int:
    score = (100
             - _tiered_penalty(mi, _MI_PENALTIES, operator.lt)
             - _tiered_penalty(debt_ratio, _DEBT_RATIO_PENALTIES, operator.gt)
             - _tiered_penalty(cyclomatic, _CYCLOMATIC_PENALTIES, operator.gt))
    return max(0, min(100, score))
def _sqale_recommendations(
    mi: float, debt_ratio: float, cyclomatic: int, loc: int
) -> list[str]:
    recs: list[str] = []
    if _tiered_penalty(mi, _MI_PENALTIES, operator.lt):
        recs.append("可维护性指数低,建议优先重构高复杂度模块")
    if _tiered_penalty(debt_ratio, _DEBT_RATIO_PENALTIES, operator.gt):
        recs.append(f"技术债务率 {debt_ratio:.1f}%,建议制定分期偿还计划")
    if _tiered_penalty(cyclomatic, _CYCLOMATIC_PENALTIES, operator.gt):
        recs.append("整体圈复杂度较高,建议简化条件逻辑")
    if loc > _MAX_FILE_LOC_HINT:
        recs.append("文件过大,建议简化逻辑、消除重复并迁移不相关职责")
    return recs
def _safe_number(value: Any, default: float) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return default
    try:
        number = float(value)
    except OverflowError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_safe_number:OverflowError')
        return default
    if not math.isfinite(number):
        return default
    return number
def _smell_field(item: Any, key: str, default: Any = None) -> Any:
    if isinstance(item, dict):
        return item.get(key, default)
    return getattr(item, key, default)
def _debt_item(idx: int, item: Any) -> DebtItem:
    smell_type = str(
        _smell_field(item, "smell_type")
        or _smell_field(item, "category") or "")
    return DebtItem(
        id=f"DEBT-{idx + 1:03d}",
        rule_id=smell_type,
        severity=str(_smell_field(item, "severity") or "info"),
        file=str(_smell_field(item, "file_path") or ""),
        line=int(_safe_number(_smell_field(item, "line_start"), 0.0)),
        message=str(_smell_field(item, "description") or ""),
        remediation_minutes=estimate_remediation_minutes(smell_type),
        debt_type="code",
    )
def _as_smell_items(value: Any) -> list[Any]:
    if isinstance(value, (str, bytes, dict)) or not isinstance(value, Iterable):
        return []
    return list(value)
def _debt_smell_items(value: Any) -> list[Any]:
    return [item for item in _as_smell_items(value)
            if (_smell_field(item, "smell_type")
                or _smell_field(item, "category"))]
def quantify_debt(
    smell_items: list[Any],
    loc: int | None = None,
    cyclomatic: int | None = None,
    mi: float | None = None,
    max_file_loc: int | None = None,
) -> DebtQuantifyReport:
    debt_items = [_debt_item(idx, item)
                  for idx, item in enumerate(_debt_smell_items(smell_items))]
    total_minutes = sum(d.remediation_minutes for d in debt_items)
    mi_val = min(100.0, max(0.0, _safe_number(mi, 100.0)))
    cc = max(0, int(_safe_number(cyclomatic, 0.0)))
    loc_val = max(0.0, _safe_number(loc, 0.0))
    file_loc_val = (max(0.0, _safe_number(max_file_loc, 0.0))
                    if max_file_loc is not None else 0.0)
    dev_hours = (loc_val / 20) if loc_val else 0.0
    ratio = (total_minutes / 60 / dev_hours) * 100 if dev_hours > 0 else 0.0
    return DebtQuantifyReport(
        debt_items=debt_items,
        total_remediation_minutes=total_minutes,
        estimated_dev_hours=dev_hours,
        debt_ratio_pct=ratio,
        overall_score=_sqale_overall_score(mi_val, ratio, cc),
        recommendations=_sqale_recommendations(mi_val, ratio, cc, file_loc_val),
        summary=f"Debt={total_minutes}min, Ratio={ratio:.1f}%, CC={cc}, LOC={int(loc_val)}",
    )
def _is_elif_continuation(stmt: ast.stmt, parent: ast.If) -> bool:
    return isinstance(stmt, ast.If) and stmt.col_offset == parent.col_offset
_SMELL_THRESHOLDS = {
    _SmellType.LONG_FUNCTION: 50,
    _SmellType.LONG_PARAMS: 5,
    _SmellType.HIGH_CC: 10,
    _SmellType.DEEP_NESTING: 4,
}
class _IfChainWalker:
    _current_nesting: int
    def _visit_if(self, node: ast.If, deepens_nesting: bool) -> None:
        self._before_if(node, deepens_nesting)
        old_nesting = (self._enter_block() if deepens_nesting
                       else self._current_nesting)
        self._after_enter_if(node, deepens_nesting)
        for stmt in node.body:
            self.visit(stmt)
        for stmt in node.orelse:
            if _is_elif_continuation(stmt, node):
                self._visit_if(stmt, deepens_nesting=False)
            else:
                self.visit(stmt)
        self._current_nesting = old_nesting
    def _before_if(self, node: ast.If, deepens_nesting: bool) -> None:  # jwsgj:suppress IA-03 SK-01 C8_dead_code empty_function — 模板钩子：基类空实现，子类 _MetricSmellWalker 覆写为统计逻辑
        pass  # jwsgj:suppress empty_function — 模板钩子基类空实现，子类覆写
    def _after_enter_if(self, node: ast.If, deepens_nesting: bool) -> None:  # jwsgj:suppress IA-03 SK-01 C8_dead_code empty_function — 模板钩子：基类空实现，子类覆写为嵌套深度统计
        pass
class _FunctionFrame(NamedTuple):
    metrics: ComplexityMetrics | None
    nesting: int
    max_nesting: int
    operators_total: int
    operands_total: int
    operators_unique: set[str]
    operands_unique: set[str]
class ComplexityAnalyzer(_IfChainWalker, ast.NodeVisitor):
    def __init__(self: Self, source_lines: list[str]) -> None:
        super().__init__()
        self.source_lines = source_lines
        self.metrics: list[ComplexityMetrics] = []
        self._current_func: ComplexityMetrics | None = None
        self._func_stack: list[ComplexityMetrics | None] = []
        self._current_nesting = 0
        self._max_nesting = 0
        self._operators_total = 0
        self._operands_total = 0
        self._operators_unique: set[str] = set()
        self._operands_unique: set[str] = set()
        self._parents: dict[ast.AST, ast.AST] = {}
    def visit(self: Self, node: ast.AST) -> Any:
        if isinstance(node, ast.Module):
            self._parents = build_node_parent_map(node)
        return super().visit(node)
    def visit_FunctionDef(self: Self, node: ast.FunctionDef) -> None:
        for decorator in node.decorator_list:
            self.visit(decorator)
        self.visit(node.args)
        if node.returns is not None:
            self.visit(node.returns)
        frame = self._begin_function(node)
        for type_param in getattr(node, "type_params", ()):
            self.visit(type_param)
        for stmt in node.body:
            self.visit(stmt)
        self._finish_function(frame)
    def _begin_function(self: Self, node: ast.FunctionDef) -> _FunctionFrame:
        metrics: ComplexityMetrics | None = None
        if not noqa_exempts_line(self.source_lines, node.lineno):
            metrics = ComplexityMetrics(
                func_name=node.name,
                line_start=node.lineno,
                line_end=node.end_lineno or node.lineno,
                lines_of_code=function_effective_loc(
                    self.source_lines, node),
                cyclomatic_complexity=1,
                param_count=count_params(
                    node, is_method=class_body_owner(
                        node, self._parents) is not None),
            )
        frame = _FunctionFrame(
            metrics=metrics,
            nesting=self._current_nesting,
            max_nesting=self._max_nesting,
            operators_total=self._operators_total,
            operands_total=self._operands_total,
            operators_unique=self._operators_unique.copy(),
            operands_unique=self._operands_unique.copy(),
        )
        self._func_stack.append(self._current_func)
        self._current_func = metrics
        self._current_nesting = 0
        self._max_nesting = 0
        self._operators_total = 0
        self._operands_total = 0
        self._operators_unique.clear()
        self._operands_unique.clear()
        return frame
    def _finish_function(self: Self, frame: _FunctionFrame) -> None:
        metrics = frame.metrics
        if metrics is not None:
            n_total = self._operators_total + self._operands_total
            n_unique = len(self._operators_unique) + len(self._operands_unique)
            hv = (n_total * math.log2(n_unique)
                  if n_unique > 0 and n_total > 0 else 0.0)
            metrics.halstead_volume = hv
            cc = metrics.cyclomatic_complexity
            loc_val = max(metrics.lines_of_code, 1)
            mi_raw = (171.0 - 5.2 * math.log(max(hv, 1))
                      - 0.23 * cc - 16.2 * math.log(loc_val))
            metrics.maintainability_index = max(0.0, mi_raw * 100.0 / 171.0)
            metrics.max_nesting_depth = self._max_nesting
            self.metrics.append(metrics)
        self._operators_total = frame.operators_total
        self._operands_total = frame.operands_total
        self._operators_unique = frame.operators_unique
        self._operands_unique = frame.operands_unique
        self._current_nesting = frame.nesting
        self._max_nesting = frame.max_nesting
        self._current_func = self._func_stack.pop()
    visit_AsyncFunctionDef = visit_FunctionDef
    def _enter_block(self: Self) -> int:
        self._current_nesting += 1
        self._max_nesting = max(self._max_nesting, self._current_nesting)
        return self._current_nesting - 1
    def visit_If(self: Any, node: ast.If) -> None:
        self._visit_if(node, deepens_nesting=True)
    def _before_if(self: Any, node: ast.If,
                   deepens_nesting: bool) -> None:
        if self._current_func:
            self._current_func.cyclomatic_complexity += 1
            self._current_func.branch_count += 1
        self.visit(node.test)
    def _visit_cc_block(self: Any, node: Any) -> None:
        if self._current_func:
            self._current_func.cyclomatic_complexity += 1
        old_nesting = self._enter_block()
        self.generic_visit(node)
        self._current_nesting = old_nesting
    visit_While = _visit_cc_block
    visit_For = _visit_cc_block
    visit_AsyncFor = _visit_cc_block
    def _visit_nesting_block(self: Any, node: Any) -> None:
        old_nesting = self._enter_block()
        self.generic_visit(node)
        self._current_nesting = old_nesting
    visit_With = _visit_nesting_block
    visit_AsyncWith = _visit_nesting_block
    def _visit_cc_leaf(self: Any, node: ast.AST) -> None:
        if self._current_func:
            self._current_func.cyclomatic_complexity += 1
        self.generic_visit(node)
    visit_ExceptHandler = _visit_cc_block
    visit_Try = _visit_nesting_block
    visit_TryStar = visit_Try
    visit_IfExp = _visit_cc_leaf
    def visit_Match(self: Any, node: ast.Match) -> None:
        if self._current_func:
            self._current_func.cyclomatic_complexity += len(node.cases)
            self._current_func.branch_count += len(node.cases)
        old_nesting = self._enter_block()
        self.generic_visit(node)
        self._current_nesting = old_nesting
    visit_Assert = _visit_cc_leaf
    def visit_BoolOp(self: Any, node: ast.BoolOp) -> None:
        if self._current_func and isinstance(node.op, (ast.And, ast.Or)):
            self._current_func.cyclomatic_complexity += len(node.values) - 1
        self._operators_total += len(node.values) - 1
        self._operators_unique.add(type(node.op).__name__)
        self.generic_visit(node)
    def _visit_comp(self: Any, node: Any) -> None:
        if self._current_func:
            self._current_func.cyclomatic_complexity += (
                len(node.generators)
                + sum(len(g.ifs) for g in node.generators))
        self.generic_visit(node)
    visit_ListComp = _visit_comp
    visit_SetComp = _visit_comp
    visit_DictComp = _visit_comp
    visit_GeneratorExp = _visit_comp
    def _visit_operator_leaf(self: Any, node: Any) -> None:
        self._operators_total += 1
        self._operators_unique.add(type(node.op).__name__)
        self.generic_visit(node)
    visit_BinOp = _visit_operator_leaf
    visit_UnaryOp = _visit_operator_leaf
    def visit_Compare(self: Any, node: ast.Compare) -> None:
        self._operators_total += len(node.ops)
        for op in node.ops:
            self._operators_unique.add(type(op).__name__)
        self.generic_visit(node)
    def visit_Constant(self: Any, node: ast.Constant) -> None:
        self._operands_total += 1
        self._operands_unique.add(repr(node.value)[:20])
        self.generic_visit(node)
    def visit_Name(self: Any, node: ast.Name) -> None:
        if isinstance(node.ctx, ast.Load):
            self._operands_total += 1
            self._operands_unique.add(node.id)
        self.generic_visit(node)
class CodeSmellDetector(_IfChainWalker, DeadCodeBaseVisitor):
    def __init__(self: Self, source_lines: list[str], file_path: str,
                 complexity_metrics: list[ComplexityMetrics]) -> None:
        super().__init__(source_lines, file_path)
        self.complexity_metrics = complexity_metrics
        self.items: list[CodeSmellItem] = []
        self._current_nesting = 0
        self._current_funcs: list[tuple[str, int]] = []
        self._func_nesting: dict[tuple[str, int], int] = {}
        self._parents: dict[ast.AST, ast.AST] = {}
    def visit(self: Self, node: ast.AST) -> Any:
        if isinstance(node, ast.Module):
            self._parents = build_node_parent_map(node)
        return super().visit(node)
    def visit_FunctionDef(self: Any, node: ast.FunctionDef) -> None:
        exempt = (self._is_exempt_name(node.name)
                  or noqa_exempts_line(self.source_lines, node.lineno))
        if not exempt:
            self._report_function_smells(node)
        old_nesting = self._current_nesting
        self._current_funcs.append(("", 0) if exempt else (node.name, node.lineno))
        self._current_nesting = 0
        self.generic_visit(node)
        self._current_nesting = old_nesting
        self._current_funcs.pop()
    visit_AsyncFunctionDef = visit_FunctionDef
    def _is_exempt_name(self: Self, name: str) -> bool:
        return name.startswith("test_")
    def _report_function_smells(self: Self, node: ast.FunctionDef) -> None:
        end = node.end_lineno or node.lineno
        loc = function_effective_loc(self.source_lines, node)
        if loc > _SMELL_THRESHOLDS[_SmellType.LONG_FUNCTION]:
            self.items.append(CodeSmellItem(
                file_path=self.file_path, line_start=node.lineno, line_end=end,
                func_name=node.name, smell_type=_SmellType.LONG_FUNCTION,
                severity="warning",
                description=f"长函数 '{node.name}' ({loc} 行, 阈值 {_SMELL_THRESHOLDS[_SmellType.LONG_FUNCTION]})",
                metric_value=loc,
                threshold=_SMELL_THRESHOLDS[_SmellType.LONG_FUNCTION],
                suggestion=f"提取 '{node.name}' 内的独立职责段为同模块私有函数，降低函数长度",
            ))
        params = count_params(
            node, is_method=class_body_owner(node, self._parents) is not None)
        if params > _SMELL_THRESHOLDS[_SmellType.LONG_PARAMS]:
            self.items.append(CodeSmellItem(
                file_path=self.file_path, line_start=node.lineno, line_end=node.lineno,
                func_name=node.name, smell_type=_SmellType.LONG_PARAMS,
                severity="warning",
                description=f"过多参数 '{node.name}' ({params} 个, 阈值 {_SMELL_THRESHOLDS[_SmellType.LONG_PARAMS]})",
                metric_value=params,
                threshold=_SMELL_THRESHOLDS[_SmellType.LONG_PARAMS],
                suggestion="将参数封装为数据类或配置对象",
            ))
    def _enter_block(self: Self) -> int:
        self._current_nesting += 1
        if self._current_funcs:
            fn = self._current_funcs[-1]
            if fn[0]:
                self._func_nesting[fn] = max(self._func_nesting.get(fn, 0),
                                             self._current_nesting)
        return self._current_nesting - 1
    def _report_module_level_deep_nesting(self: Self, node: ast.AST) -> None:
        if (self._current_nesting == _SMELL_THRESHOLDS[_SmellType.DEEP_NESTING] + 1
                and not self._current_funcs):
            self.items.append(CodeSmellItem(
                smell_type=_SmellType.DEEP_NESTING, file_path=self.file_path,
                line_start=node.lineno,
                line_end=node.end_lineno or node.lineno,
                description=f"模块级嵌套深度 {self._current_nesting}",
                metric_value=self._current_nesting,
                threshold=_SMELL_THRESHOLDS[_SmellType.DEEP_NESTING],
                severity="warning",
                suggestion="将深层模块级控制流提取为模块级函数",
            ))
    def visit_If(self: Any, node: ast.If) -> None:
        self._visit_if(node, deepens_nesting=True)
    def _after_enter_if(self: Any, node: ast.If, deepens_nesting: bool) -> None:
        if deepens_nesting:
            self._report_module_level_deep_nesting(node)
    def _visit_nested_block(self: Any, node: Any) -> None:
        old_nesting = self._enter_block()
        self._report_module_level_deep_nesting(node)
        self.generic_visit(node)
        self._current_nesting = old_nesting
    visit_For = _visit_nested_block
    visit_While = _visit_nested_block
    visit_With = _visit_nested_block
    visit_AsyncWith = _visit_nested_block
    visit_AsyncFor = _visit_nested_block
    visit_Match = _visit_nested_block
    visit_Try = _visit_nested_block
    visit_TryStar = _visit_nested_block
    visit_ExceptHandler = _visit_nested_block
    def _metric_smell(self: Self, m: ComplexityMetrics, smell_type: str,
                      value: float, description: str,
                      suggestion: str) -> CodeSmellItem:
        return CodeSmellItem(
            file_path=self.file_path, line_start=m.line_start,
            line_end=m.line_end, func_name=m.func_name,
            smell_type=smell_type, severity="warning",
            description=description, metric_value=value,
            threshold=_SMELL_THRESHOLDS[smell_type],
            suggestion=suggestion,
        )
    def finalize_with_metrics(self: Self) -> None:
        for m in self.complexity_metrics:
            if m.line_start <= 0:
                continue
            if self._is_exempt_name(m.func_name):
                continue
            if m.cyclomatic_complexity > _SMELL_THRESHOLDS[_SmellType.HIGH_CC]:
                self.items.append(self._metric_smell(
                    m, _SmellType.HIGH_CC, m.cyclomatic_complexity,
                    f"圈复杂度 {m.cyclomatic_complexity}",
                    f"简化 '{m.func_name}' 的条件分支或提取同模块私有函数"))
            func_max_nesting = self._func_nesting.get(
                (m.func_name, m.line_start), 0)
            if func_max_nesting > _SMELL_THRESHOLDS[_SmellType.DEEP_NESTING]:
                self.items.append(self._metric_smell(
                    m, _SmellType.DEEP_NESTING, func_max_nesting,
                    f"最大嵌套深度 {func_max_nesting}",
                    f"提取 '{m.func_name}' 的深嵌套块为独立函数或用卫语句提前返回"))
def _read_text_file(file_path: str) -> tuple[str | None, str]:
    content = read_source(file_path)
    if content is not None:
        return content, ""
    try:
        with open(file_path, "rb"):
            pass
    except OSError as e:
        return None, str(e)
    return None, "源码不可读（共享读取通道返回空）"
def _relative_module_name(path: str, root: str) -> tuple[str, bool]:
    rel = os.path.relpath(path, root)
    rel_dir, fname = os.path.split(rel)
    stem = os.path.splitext(fname)[0]
    parts = [p for p in rel_dir.split(os.sep) if p not in ("", ".")]
    is_package = stem == "__init__"
    if is_package:
        return ".".join(parts), True
    return ".".join([*parts, stem]), False
def _module_names_of(path: str, root: str,
                     root_is_package: bool) -> tuple[list[str], str]:
    dotted, is_package = _relative_module_name(path, root)
    root_name = os.path.basename(os.path.abspath(root))
    if root_is_package and root_name:
        primary = f"{root_name}.{dotted}" if dotted else root_name
    else:
        primary = dotted
    if is_package:
        package = primary
    elif "." in primary:
        package = primary.rsplit(".", 1)[0]
    else:
        package = ""
    aliases = [primary] if primary else []
    if dotted and dotted != primary:
        aliases.append(dotted)
    return aliases, package
def _source_root_alias(path: str, root: str) -> str | None:
    rel = os.path.relpath(path, root).replace("\\", "/")
    parts = [part for part in rel.split("/") if part not in ("", ".")]
    if len(parts) < 2:
        return None
    filename = parts[-1]
    stem = filename[:-3] if filename.lower().endswith(".py") else filename
    for cut in range(1, len(parts)):
        container = os.path.join(root, *parts[:cut])
        if os.path.isfile(os.path.join(container, "__init__.py")):
            return None
        module_parts = (parts[cut:-1] if stem == "__init__"
                        else [*parts[cut:-1], stem])
        candidate = ".".join(module_parts)
        if not candidate:
            continue
        rel_candidate = candidate.replace(".", os.sep)
        expected = (os.path.join(container, rel_candidate, "__init__.py")
                    if stem == "__init__"
                    else os.path.join(container, rel_candidate + ".py"))
        if os.path.normcase(os.path.abspath(expected)) == (
                os.path.normcase(os.path.abspath(path))):
            return candidate
    return None
def _build_module_index(paths: Iterable[str],
                        root: str | os.PathLike[str]
                        ) -> tuple[dict[str, str], dict[str, str]]:
    root_path = os.fspath(root)
    root_is_package = os.path.isfile(os.path.join(root_path, "__init__.py"))
    candidates: dict[str, set[str]] = defaultdict(set)
    packages: dict[str, str] = {}
    for path in paths:
        aliases, package = _module_names_of(path, root_path, root_is_package)
        candidate = _source_root_alias(path, root_path)
        if candidate is not None and candidate not in aliases:
            aliases.append(candidate)
        for name in aliases:
            candidates[name].add(path)
        if package:
            packages[path] = package
    module_index = {
        name: next(iter(files))
        for name, files in candidates.items() if len(files) == 1
    }
    return module_index, packages
_EXTRA_SCAN_IGNORED_DIRS = frozenset({"_versions"})
_QUALITY_SCAN_EXCLUDED_FILES = frozenset({"conftest.py"})
def _excluded_dir_names(root: str | os.PathLike[str]) -> frozenset[str]:
    return frozenset(scan_exclude_dirs(root) | _EXTRA_SCAN_IGNORED_DIRS)
def _index_excluded_dir_names(root: str | os.PathLike[str]) -> frozenset[str]:
    return frozenset(_excluded_dir_names(root) - TEST_ARTIFACT_DIRS)
def _quality_scan_file_allowed(fname: str) -> bool:
    return (is_scan_py_name(fname)
            and fname.lower() not in _QUALITY_SCAN_EXCLUDED_FILES)
class CodeCleaner:
    def __init__(self: Self, skill_dir: str) -> None:
        if not skill_dir or not isinstance(skill_dir, (str, os.PathLike)):
            raise ValueError(f"无效的项目目录: {skill_dir!r}")
        self._skill_dir = Path(skill_dir)
        if not self._skill_dir.is_dir():
            raise ValueError(f"无效的项目目录: {skill_dir}")
        self._excluded_dirs = _excluded_dir_names(self._skill_dir)
        self._index_excluded_dirs = _index_excluded_dir_names(self._skill_dir)
    def analyze(self: Self) -> CodeCleanupReport:
        report = CodeCleanupReport(skill_dir=str(self._skill_dir))
        py_files = self._collect_py_files(report)
        file_contents = self._pre_read_contents(py_files, report)
        cross_index = self._build_cross_index(
            file_contents, self._collect_index_only_files(py_files, report),
            errors=report.errors)
        all_complexity = self._analyze_all_files(file_contents, cross_index, report)
        self._summarize_debt(file_contents, all_complexity, report)
        return report
    def _pre_read_contents(self: Self, py_files: list[str],
                           report: CodeCleanupReport) -> dict[str, str]:
        file_contents: dict[str, str] = {}
        for fp in py_files:
            content, error = _read_text_file(fp)
            if content is None:
                _log.warning("[CodeCleaner] 文件读取失败（跳过）: %s", error)
                report.errors.append(f"{fp}: {error}")
                continue
            file_contents[fp] = content
        return file_contents
    def _build_cross_index(
            self: Self, file_contents: dict[str, str],
            index_only_paths: Sequence[str] = (),
            errors: list[str] | None = None) -> DeadCodeFileIndex:
        cross_index = DeadCodeFileIndex()
        all_paths = [*file_contents, *index_only_paths]
        module_index, packages = _build_module_index(all_paths, self._skill_dir)
        for file_path, content in file_contents.items():
            self._index_file(file_path, cross_index, content=content,
                             module_index=module_index, packages=packages)
        for file_path in index_only_paths:
            self._index_file(file_path, cross_index,
                             module_index=module_index, packages=packages,
                             errors=errors)
        return cross_index
    def _analyze_all_files(self: Self, file_contents: dict[str, str],
                           cross_index: DeadCodeFileIndex,
                           report: CodeCleanupReport) -> list[ComplexityMetrics]:
        all_complexity: list[ComplexityMetrics] = []
        for file_path, content in file_contents.items():
            file_items, complexity, smell_items = self._analyze_file(
                file_path, cross_index, content=content,
                errors=report.errors)
            report.items.extend(file_items)
            report.smell_items.extend(smell_items)
            all_complexity.extend(complexity)
            report.total_files_scanned += 1
        return all_complexity
    def _summarize_debt(self: Self, file_contents: dict[str, str],
                        all_complexity: list[ComplexityMetrics],
                        report: CodeCleanupReport) -> None:
        all_complexity.sort(key=lambda m: m.cyclomatic_complexity, reverse=True)
        report.complexity_top = all_complexity[:20]
        report.total_lines_scanned = sum(
            count_lines(c) for c in file_contents.values())
        if all_complexity:
            mi_avg = sum(m.maintainability_index for m in all_complexity) / len(all_complexity)
        else:
            mi_avg = 100.0
        report.debt = quantify_debt(
            [*report.smell_items, *report.items],
            loc=report.total_lines_scanned,
            cyclomatic=max((m.cyclomatic_complexity for m in all_complexity),
                           default=0),
            mi=mi_avg,
            max_file_loc=max(
                (count_lines(c) for c in file_contents.values()),
                default=0),
        )
        if not file_contents or report.errors:
            report.debt.overall_score = _QUALITY_SCORE_NOT_MEASURED
            reason = ("未扫描到可读取的 Python 源码，质量评分未度量"
                      if not file_contents else
                      "扫描或分析存在错误，质量评分未完整度量")
            report.debt.recommendations.insert(0, reason)
            report.debt.summary += ", Status=UNMEASURED"
    def _report_walk_error(self: Self, exc: OSError,
                           report: CodeCleanupReport | None) -> None:
        target = getattr(exc, "filename", "") or str(self._skill_dir)
        _log.warning("[CodeCleaner] 目录遍历失败（结果不完整）: %s: %s",
                     target, exc)
        if report is not None:
            report.errors.append(f"{target}: {exc}")
    def _collect_py_files(
            self: Self, report: CodeCleanupReport | None = None) -> list[str]:
        py_files: list[str] = []
        for root, dirs, files in os.walk(
                self._skill_dir,
                onerror=lambda exc: self._report_walk_error(exc, report)):
            dirs[:] = [d for d in dirs
                       if not is_pruned_scan_dir(d, self._excluded_dirs)]
            py_files.extend(os.path.join(root, fname)
                            for fname in files if _quality_scan_file_allowed(fname))
        return sorted(py_files)
    def _collect_index_only_files(
            self: Self, scanned: list[str],
            report: CodeCleanupReport | None = None) -> list[str]:
        scanned_set = set(scanned)
        extra: list[str] = []
        for root, dirs, files in os.walk(
                self._skill_dir,
                onerror=lambda exc: self._report_walk_error(exc, report)):
            dirs[:] = [d for d in dirs
                       if not is_pruned_scan_dir(d, self._index_excluded_dirs)]
            for fname in files:
                if not is_scan_py_name(fname):
                    continue
                fp = os.path.join(root, fname)
                if fp not in scanned_set:
                    extra.append(fp)
        return sorted(extra)
    def _read_source_or_none(self: Self, file_path: str,
                             errors: list[str] | None = None) -> str | None:
        content, error = _read_text_file(file_path)
        if content is None:
            _log.warning("[CodeCleaner] %s 不可读，跳过: %s", file_path, error)
            if errors is not None:
                errors.append(f"{file_path}: {error}")
        return content
    @staticmethod
    def _parse_tree_or_none(file_path: str, content: str,
                            errors: list[str] | None = None
                            ) -> ast.Module | None:
        try:
            return parse_cached(content, filename=file_path)
        except PARSE_DEGRADE_EXC as e:
            _log.warning(
                "[CodeCleaner] %s 解析失败（语法/递归/内存超限），跳过 AST: %s",
                file_path, e)
            if errors is not None:
                errors.append(
                    f"{file_path}: 解析失败: {type(e).__name__}: {e}")
            return None
    def _index_file(self: Self, file_path: str, cross_index: DeadCodeFileIndex,
                    content: str | None = None,
                    module_index: dict[str, str] | None = None,
                    packages: dict[str, str] | None = None,
                    errors: list[str] | None = None) -> None:
        if content is None:
            content = self._read_source_or_none(file_path, errors)
            if content is None:
                return
        tree = self._parse_tree_or_none(file_path, content, errors)
        if tree is None:
            return
        self._register_imports(tree, file_path, cross_index)
        self._register_attribute_names(tree, cross_index)
        if module_index:
            self._register_wildcard_imports(
                tree, file_path, cross_index, module_index, packages or {})
            self._register_attribute_refs(
                tree, file_path, cross_index, module_index, packages or {})
    @staticmethod
    def _import_bindings(node: ast.AST) -> list[str]:
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            return []
        bindings: list[str] = []
        for alias in node.names:
            name = import_binding_name(node, alias)
            if name is not None:
                bindings.append(name)
            if (isinstance(node, ast.ImportFrom) and alias.asname
                    and alias.name != "*"):
                bindings.append(alias.name)
        return bindings
    @classmethod
    def _register_imports(cls, tree: ast.Module, file_path: str,
                          cross_index: DeadCodeFileIndex) -> None:
        for node in walk_nodes(tree):
            bindings = cls._import_bindings(node)
            if bindings:
                cross_index.add_import(file_path, bindings)
    @staticmethod
    def _register_attribute_names(tree: ast.Module,
                                  cross_index: DeadCodeFileIndex) -> None:
        cross_index.add_attribute_names(
            node.attr for node in walk_nodes(tree)
            if isinstance(node, ast.Attribute))
    @classmethod
    def _register_wildcard_imports(
            cls, tree: ast.Module, file_path: str,
            cross_index: DeadCodeFileIndex,
            module_index: dict[str, str],
            packages: dict[str, str]) -> None:
        targets: set[str] = set()
        package = packages.get(file_path, "")
        for node in walk_nodes(tree):
            if (not isinstance(node, ast.ImportFrom)
                    or not any(alias.name == "*" for alias in node.names)):
                continue
            base = cls._import_from_base(node, package)
            if base is None:
                continue
            target_file = module_index.get(base)
            if target_file is not None:
                targets.add(target_file)
        if not targets:
            return
        attribute_names = {
            node.attr for node in walk_nodes(tree)
            if isinstance(node, ast.Attribute)
        }
        for target_file in targets:
            cross_index.add_wildcard_reference(file_path, target_file)
            for name in attribute_names:
                cross_index.add_reference(file_path, name, target_file)
            cls._register_reexport_attribute_refs(
                tree, file_path, cross_index, module_index, packages,
                target_file)
    @classmethod
    def _register_reexport_attribute_refs(
            cls, tree: ast.Module, file_path: str,
            cross_index: DeadCodeFileIndex,
            module_index: dict[str, str], packages: dict[str, str],
            target_file: str) -> None:
        content = read_source(target_file)
        if content is None:
            return
        try:
            target_tree = parse_cached(content, filename=target_file)
        except PARSE_DEGRADE_EXC:
            return
        module_names: set[str] = set()
        bindings = cls._imported_module_bindings(
            target_tree, packages.get(target_file, ""), module_index,
            module_names_out=module_names)
        if bindings:
            cls._register_attribute_bindings(
                tree, file_path, cross_index, module_index, bindings,
                module_names=module_names)
    @classmethod
    def _register_attribute_refs(cls, tree: ast.Module, file_path: str,
                                 cross_index: DeadCodeFileIndex,
                                 module_index: dict[str, str],
                                 packages: dict[str, str]) -> None:
        module_names: set[str] = set()
        bindings = cls._imported_module_bindings(
            tree, packages.get(file_path, ""), module_index,
            module_names_out=module_names)
        if bindings:
            cls._register_attribute_bindings(
                tree, file_path, cross_index, module_index, bindings,
                module_names=module_names)
    @classmethod
    def _register_attribute_bindings(
            cls, tree: ast.Module, file_path: str,
            cross_index: DeadCodeFileIndex,
            module_index: dict[str, str], bindings: dict[str, set[str]],
            module_names: set[str] | None = None) -> None:
        known_module_names = (set(bindings) if module_names is None
                              else module_names)
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Attribute):
                continue
            parts = cls._attribute_chain(node)
            if len(parts) < 2 or parts[0] not in bindings:
                continue
            for imported_module in bindings[parts[0]]:
                module = imported_module
                target_file = module_index.get(module)
                if target_file is None:
                    continue
                if parts[0] not in known_module_names:
                    cross_index.add_reference(file_path, parts[1], target_file)
                    continue
                consumed = 1
                while consumed < len(parts):
                    submodule = f"{module}.{parts[consumed]}"
                    submodule_file = module_index.get(submodule)
                    if submodule_file is None:
                        break
                    module, target_file = submodule, submodule_file
                    consumed += 1
                if consumed >= len(parts):
                    continue
                cross_index.add_reference(file_path, parts[-1], target_file)
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Call):
                continue
            for receiver, name_node in _dynamic_attribute_accesses(node):
                name = _string_constant(name_node)
                if name is None:
                    continue
                for module in cls._expression_modules(
                        receiver, bindings, module_index):
                    target_file = module_index.get(module)
                    if target_file is not None:
                        cross_index.add_reference(
                            file_path, name, target_file)
    @classmethod
    def _expression_modules(
            cls, node: ast.expr, bindings: dict[str, set[str]],
            module_index: dict[str, str]) -> set[str]:
        while isinstance(node, ast.Call):
            node = node.func
        if isinstance(node, ast.Name):
            return set(bindings.get(node.id, ()))
        if not isinstance(node, ast.Attribute):
            return set()
        parts = cls._attribute_chain(node)
        if len(parts) < 2 or parts[0] not in bindings:
            return set()
        modules: set[str] = set()
        for imported_module in bindings[parts[0]]:
            module = imported_module
            for attr in parts[1:]:
                submodule = f"{module}.{attr}"
                if submodule not in module_index:
                    break
                module = submodule
            if module in module_index:
                modules.add(module)
        return modules
    @classmethod
    def _imported_module_bindings(
            cls, tree: ast.Module, package: str,
            module_index: dict[str, str], *,
            module_names_out: set[str] | None = None
            ) -> dict[str, set[str]]:
        bindings: dict[str, set[str]] = {}
        module_names: set[str] = set()
        constructor_names: set[str] = set()
        for node in walk_nodes(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.asname:
                        bound, module = alias.asname, alias.name
                    else:
                        bound = module = alias.name.split(".")[0]
                    bindings.setdefault(bound, set()).add(module)
                    module_names.add(bound)
            elif isinstance(node, ast.ImportFrom):
                base = cls._import_from_base(node, package)
                if base is None:
                    continue
                for alias in node.names:
                    if alias.name == "*":
                        continue
                    bound = alias.asname or alias.name
                    module = f"{base}.{alias.name}" if base else alias.name
                    if module in module_index:
                        bindings.setdefault(bound, set()).add(module)
                        module_names.add(bound)
                    elif base in module_index:
                        bindings.setdefault(bound, set()).add(base)
                        constructor_names.add(bound)
        cls._propagate_module_bindings(
            tree, bindings, module_index, module_names, constructor_names)
        if module_names_out is not None:
            module_names_out.update(module_names)
        return bindings
    @classmethod
    def _propagate_module_bindings(
            cls, tree: ast.Module, bindings: dict[str, set[str]],
            module_index: dict[str, str], module_names: set[str],
            constructor_names: set[str]) -> None:
        for node in walk_nodes(tree):
            if isinstance(node, ast.ClassDef):
                sources: set[str] = set()
                for base in node.bases:
                    sources.update(cls._expression_modules(
                        base, bindings, module_index))
                if sources:
                    bindings.setdefault(node.name, set()).update(sources)
                    constructor_names.add(node.name)
                continue
            if isinstance(node, ast.Assign):
                targets = [target.id for target in node.targets
                           if isinstance(target, ast.Name)]
                value = node.value
            elif (isinstance(node, ast.AnnAssign)
                  and node.value is not None
                  and isinstance(node.target, ast.Name)):
                targets = [node.target.id]
                value = node.value
            else:
                continue
            if not targets:
                continue
            constructor_alias = False
            module_alias = False
            if isinstance(value, ast.Name):
                sources = cls._expression_modules(
                    value, bindings, module_index)
                constructor_alias = value.id in constructor_names
                module_alias = value.id in module_names
            elif isinstance(value, ast.Call):
                func = value.func
                if isinstance(func, ast.Name):
                    if func.id not in constructor_names:
                        continue
                elif isinstance(func, ast.Attribute):
                    parts = cls._attribute_chain(func)
                    if (not parts or parts[0] not in module_names
                            or any(isinstance(child, ast.Call)
                                   for child in walk_nodes(func))):
                        continue
                else:
                    continue
                sources = cls._expression_modules(
                    func, bindings, module_index)
            elif isinstance(value, ast.Attribute):
                parts = cls._attribute_chain(value)
                if not parts or parts[0] not in module_names:
                    continue
                module_alias = any(
                    f"{module}.{'.'.join(parts[1:])}" in module_index
                    for module in bindings.get(parts[0], ())
                )
                sources = cls._expression_modules(
                    value, bindings, module_index)
                constructor_alias = not module_alias
            else:
                continue
            if not sources:
                continue
            for name in targets:
                bindings.setdefault(name, set()).update(sources)
                if constructor_alias:
                    constructor_names.add(name)
                if module_alias:
                    module_names.add(name)
    @staticmethod
    def _import_from_base(node: ast.ImportFrom, package: str) -> str | None:
        if node.level == 0:
            return node.module or ""
        if not package:
            return None
        parts = package.split(".")
        drop = node.level - 1
        if drop >= len(parts):
            return None
        base = parts[:len(parts) - drop]
        if node.module:
            base.extend(node.module.split("."))
        return ".".join(base)
    @staticmethod
    def _attribute_chain(node: ast.Attribute) -> list[str]:
        parts: list[str] = []
        cur: ast.AST = node
        while isinstance(cur, (ast.Attribute, ast.Call)):
            if isinstance(cur, ast.Call):
                cur = cur.func
                continue
            parts.append(cur.attr)
            cur = cur.value
        if not isinstance(cur, ast.Name):
            return []
        parts.append(cur.id)
        return list(reversed(parts))
    def _analyze_file(self: Self, file_path: str, cross_index: DeadCodeFileIndex,
                      content: str | None = None,
                      errors: list[str] | None = None,
                      ) -> tuple[list[CodeCleanupItem], list[ComplexityMetrics], list[CodeSmellItem]]:
        items: list[CodeCleanupItem] = []
        complexity: list[ComplexityMetrics] = []
        smell_items: list[CodeSmellItem] = []
        if content is None:
            content = self._read_source_or_none(file_path, errors)
            if content is None:
                return items, complexity, smell_items
        lines = content.split("\n")
        tree = self._parse_tree_or_none(file_path, content, errors)
        try:
            if tree is not None:
                ast_items, complexity, smell_items = self._run_ast_detectors(
                    tree, lines, file_path, cross_index)
                items.extend(ast_items)
        except Exception as _analysis_exc:  # noqa: BLE001 -- AST 通道降级：文本通道仍须执行
            _log.warning(
                "文件 AST 分析异常: %s，降级为文本检测", file_path,
                exc_info=True)
            if errors is not None:
                errors.append(
                    f"{file_path}: AST 分析异常: "
                    f"{type(_analysis_exc).__name__}: {_analysis_exc}")
        items.extend(detect_stale_comments(file_path, lines))
        items.extend(detect_legacy_code(file_path, content))
        return items, complexity, smell_items
    def _run_ast_detectors(
        self: Self, tree: ast.Module, lines: list[str],
        file_path: str, cross_index: DeadCodeFileIndex,
    ) -> tuple[list[CodeCleanupItem], list[ComplexityMetrics], list[CodeSmellItem]]:
        items: list[CodeCleanupItem] = []
        ca = ComplexityAnalyzer(lines)
        ca.visit(tree)
        complexity = ca.metrics
        for m in complexity:
            m.file_path = file_path
        visitors = (
            (DeadCodeVisitor(lines, file_path, cross_index), True),
            (RedundantCodeVisitor(lines, file_path), False),
            (StructuralDupDetector(lines, file_path), True),
            (DeadImportVisitor(lines, file_path), True),
            (InvalidFuncVisitor(lines, file_path), False),
        )
        for visitor, needs_finalize in visitors:
            visitor.visit(tree)
            if needs_finalize:
                visitor.finalize()
            items.extend(visitor.items)
        items.extend(detect_redundant_imports(file_path, tree, lines))
        smell_detector = CodeSmellDetector(lines, file_path, complexity)
        smell_detector.visit(tree)
        smell_detector.finalize_with_metrics()
        return items, complexity, smell_detector.items
_BLOCK_SIZE = 6
def _accumulate_file_metrics(path: str, metrics: dict,
                             seen_blocks: dict[str, int]) -> int:
    src = read_source(path)
    if src is None:
        _log.warning("compute_quality_metrics: 文件读取失败跳过: %s", path)
        metrics["scan_errors"] += 1
        return 0
    lines = split_lines_lf(src)
    metrics["total_lines"] += count_lines(src)
    try:
        tree = parse_cached(src, filename=path)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(
            __name__, _e,
            context=f'_accumulate_file_metrics:{type(_e).__name__}')
        metrics["syntax_errors"] += 1
        return 0
    file_complexity = _count_structure_metrics(tree, metrics)
    _fingerprint_blocks(lines, seen_blocks)
    return file_complexity
def _count_structure_metrics(tree: ast.Module, metrics: dict) -> int:
    file_complexity = 0
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            metrics[FIELD_TOTAL_FUNCTIONS] += 1
            if not ast.get_docstring(node):
                metrics["missing_docstrings"] += 1
            file_complexity += 1 + decision_points(node, iter_scope_nodes)
        elif isinstance(node, ast.ClassDef):
            metrics["total_classes"] += 1
            if not ast.get_docstring(node):
                metrics["missing_docstrings"] += 1
    return file_complexity
def _fingerprint_blocks(lines: list[str], seen_blocks: dict[str, int]) -> None:
    norm = [ln.strip() for ln in lines
            if ln.strip() and not ln.strip().startswith("#")]
    for i in range(len(norm) - _BLOCK_SIZE + 1):
        fp = "\n".join(norm[i:i + _BLOCK_SIZE])
        seen_blocks[fp] = seen_blocks.get(fp, 0) + 1
def _walk_and_accumulate(skill_dir: str, metrics: dict,
                         seen_blocks: dict[str, int]) -> int:
    total_complexity = 0
    excluded = _excluded_dir_names(skill_dir)
    def _onerror(exc: OSError) -> None:
        metrics["scan_errors"] += 1
        _log.warning("compute_quality_metrics: 目录遍历失败（结果不完整）: %s: %s",
                     getattr(exc, "filename", "") or skill_dir, exc)
    for root, dirs, files in os.walk(skill_dir, onerror=_onerror):
        dirs[:] = [d for d in dirs
                   if not is_pruned_scan_dir(d, excluded)]
        for fname in files:
            if not _quality_scan_file_allowed(fname):
                continue
            path = os.path.join(root, fname)
            metrics["files_added"] += 1
            total_complexity += _accumulate_file_metrics(path, metrics, seen_blocks)
    return total_complexity
def compute_quality_metrics(skill_dir: str) -> dict:
    metrics = {
        "total_lines": 0,
        FIELD_TOTAL_FUNCTIONS: 0,
        "total_classes": 0,
        "avg_complexity": 0.0,
        "syntax_errors": 0,
        "scan_errors": 0,
        "duplicated_blocks": 0,
        "missing_docstrings": 0,
        "files_added": 0,
    }
    if (not skill_dir or not isinstance(skill_dir, (str, os.PathLike))
            or not os.path.isdir(skill_dir)):
        return metrics
    seen_blocks: dict[str, int] = {}
    total_complexity = _walk_and_accumulate(
        os.fspath(skill_dir), metrics, seen_blocks)
    metrics["duplicated_blocks"] = sum(1 for c in seen_blocks.values() if c > 1)
    total_funcs = metrics[FIELD_TOTAL_FUNCTIONS]
    metrics["avg_complexity"] = round(
        total_complexity / total_funcs, 2) if total_funcs else 0.0
    return metrics
_DEGRADATION_SENSITIVE_KEYS = frozenset({
    "syntax_errors", "scan_errors", "duplicated_blocks",
    "missing_docstrings", "avg_complexity",
    "total_lines",
})
def _is_comparable_metric(value: Any) -> bool:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return False
    if isinstance(value, float) and not math.isfinite(value):
        return False
    return value >= 0
def _classify_metric_delta(key: str, before: Any, after: Any) -> str | None:
    if not (_is_comparable_metric(before) and _is_comparable_metric(after)):
        return None
    if after == before:
        return "unchanged"
    if key not in _DEGRADATION_SENSITIVE_KEYS:
        return "changed"
    return "degraded" if after > before else "improved"
def _finalize_comparison(
    comparison: dict, after_files: int | None, after_scan_errors: int | None,
    after_syntax_errors: int | None, incomparable_count: int,
) -> None:
    comparable = (len(comparison["degraded"]) + len(comparison["improved"])
                  + len(comparison["changed"]) + len(comparison["unchanged"]))
    comparison["comparable_count"] = comparable
    comparison["summary"] = (
        f"{comparable} 项指标中: "
        f"改进 {len(comparison['improved'])} 项, "
        f"退化 {len(comparison['degraded'])} 项, "
        f"变化(不计入判定) {len(comparison['changed'])} 项, "
        f"不变 {len(comparison['unchanged'])} 项"
    )
    if comparable == 0:
        comparison["summary"] += "（无可比指标，不得判定质量通过）"
    if incomparable_count:
        comparison["summary"] += (
            f"；{incomparable_count} 项指标不可比，不得判定质量通过")
    new_files = comparison.get("new_files")
    removed_files = comparison.get("removed_files")
    if new_files is None or removed_files is None:
        comparison["summary"] += "；文件计数不可比，需人工复核"
    else:
        if new_files:
            comparison["summary"] += f"；新增文件 {new_files} 个，需人工复核"
        if removed_files:
            comparison["summary"] += f"；删除文件 {removed_files} 个，需人工复核"
    if after_files == 0:
        comparison["summary"] += "；未扫描到可度量源码，不得判定质量通过"
    if after_scan_errors is None:
        comparison["summary"] += "；当前读取/遍历错误计数不可比，不得判定质量通过"
    elif after_scan_errors:
        comparison["summary"] += (
            f"；当前扫描有 {after_scan_errors} 项读取/遍历错误，不得判定质量通过")
    if after_syntax_errors is None:
        comparison["summary"] += "；当前语法错误计数不可比，不得判定质量通过"
    comparison["quality_pass"] = (comparable > 0
                                  and incomparable_count == 0
                                  and after_files is not None
                                  and after_files > 0
                                  and after_scan_errors == 0
                                  and after_syntax_errors == 0
                                  and not comparison["degraded"]
                                  and new_files == 0
                                  and removed_files == 0)
def _as_file_count(value: Any) -> int | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    if isinstance(value, float):
        if not math.isfinite(value) or not value.is_integer():
            return None
        value = int(value)
    return value if value >= 0 else None
def _file_count_delta(before_metrics: dict, after_metrics: dict) -> int | None:
    before_files = _as_file_count(before_metrics.get("files_added"))
    after_files = _as_file_count(after_metrics.get("files_added"))
    if before_files is None or after_files is None:
        return None
    return after_files - before_files
def compare_quality_baseline(skill_dir: str, before_metrics: dict,
                             after_metrics: dict) -> dict:
    before_metrics = before_metrics if isinstance(before_metrics, dict) else {}
    after_metrics = after_metrics if isinstance(after_metrics, dict) else {}
    file_delta = _file_count_delta(before_metrics, after_metrics)
    after_files = _as_file_count(after_metrics.get("files_added"))
    after_scan_errors = _as_file_count(after_metrics.get("scan_errors"))
    after_syntax_errors = _as_file_count(after_metrics.get("syntax_errors"))
    comparison = {
        "skill_dir": skill_dir,
        "degraded": [],
        "improved": [],
        "changed": [],
        "unchanged": [],
        "new_files": max(0, file_delta) if file_delta is not None else None,
        "removed_files": max(0, -file_delta) if file_delta is not None else None,
    }
    metric_keys = ["total_lines", FIELD_TOTAL_FUNCTIONS, "total_classes",
                   "avg_complexity", "syntax_errors", "scan_errors",
                   "duplicated_blocks", "missing_docstrings"]
    incomparable_count = 0
    for key in metric_keys:
        before = before_metrics.get(key)
        after = after_metrics.get(key)
        cls = _classify_metric_delta(key, before, after)
        if cls is None:
            incomparable_count += 1
            continue
        entry = {"metric": key, "before": before, "after": after,
                 "delta": after - before}
        comparison[cls].append(entry)
    _finalize_comparison(
        comparison, after_files, after_scan_errors, after_syntax_errors,
        incomparable_count)
    return comparison

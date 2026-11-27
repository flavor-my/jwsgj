from __future__ import annotations

import ast
import logging
import symtable
import threading
from collections import OrderedDict
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, ClassVar

from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    TYPE_ALIAS_NODES,
    build_node_parent_map,
    build_parent_map,
    coerce_str,
    collect_param_names,
    expr_target_name,
    is_docstring_stmt,
    is_main_check,
    is_placeholder_stmt,
    is_type_checking_guard,
    iter_def_site_nodes,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    pattern_capture_name,
    scope_chain,
    str_constant_value,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
def _import_alias_paths(node: ast.Import | ast.ImportFrom) -> dict[str, str]:
    paths: dict[str, str] = {}
    if isinstance(node, ast.Import):
        for alias in node.names:
            top = alias.name.split(".")[0]
            paths[alias.asname or top] = alias.name if alias.asname else top
        return paths
    source = ("." * node.level + (node.module or "")
              if node.level else node.module or "")
    separator = "" if source.endswith(".") else "."
    for alias in node.names:
        if alias.name != "*":
            paths[alias.asname or alias.name] = (
                f"{source}{separator}{alias.name}")
    return paths
_COMPREHENSION_SCOPE_NAMES = {
    ast.ListComp: "listcomp",
    ast.SetComp: "setcomp",
    ast.DictComp: "dictcomp",
    ast.GeneratorExp: "genexpr",
}
_BINDING_EVALUATION_ATTRS = {
    ast.Assign: "value",
    ast.AugAssign: "value",
    ast.AnnAssign: "value",
    ast.NamedExpr: "value",
    ast.For: "iter",
    ast.AsyncFor: "iter",
    ast.comprehension: "iter",
    ast.FunctionDef: "",
    ast.AsyncFunctionDef: "",
    ast.ClassDef: "",
    ast.ExceptHandler: "type",
}
_EAGER_COMPREHENSION_TABLES = frozenset({"listcomp", "setcomp", "dictcomp"})
class ScopeNameResolver:
    def __init__(self, source_code: str, file_path: str, tree: ast.AST,
                 fallback_names: set[str]) -> None:
        self._source_code = source_code
        self._file_path = file_path or "<scan>"
        self._tree = tree
        self._fallback_names = fallback_names
        self._resolved: dict[int, bool] = {}
        self._name_import_paths: dict[int, str | None] = {}
        self._name_tables: dict[int, symtable.SymbolTable] = {}
        self._name_inlined_names: dict[int, frozenset[str]] = {}
        self._children: dict[int, list[symtable.SymbolTable]] = {}
        self._table_parents: dict[int, symtable.SymbolTable] = {}
        self._import_events: dict[
            int, dict[str, list[tuple[tuple[int, int], str]]]] = {}
        self._nonimport_writes: dict[
            int, dict[str, list[tuple[int, int]]]] = {}
        self._binding_activations: dict[
            tuple[int, str, tuple[int, int]], tuple[int, int]] = {}
        self._unbinding_writes: set[
            tuple[int, str, tuple[int, int]]] = set()
        self._parents: dict[int, ast.AST] = {}
        self._root: symtable.SymbolTable | None = None
        self._ready = False
        self._complete = False
    @staticmethod
    def _symbol_bound(symbol: symtable.Symbol) -> bool:
        return (symbol.is_assigned() or symbol.is_parameter()
                or symbol.is_imported() or symbol.is_namespace())
    def _register(self, table: symtable.SymbolTable,
                  parent: symtable.SymbolTable | None = None) -> None:
        children = list(table.get_children())
        self._children[id(table)] = children
        if parent is not None:
            self._table_parents[id(table)] = parent
        for child in children:
            self._register(child, table)
    def _declared_binding_table(self, table: symtable.SymbolTable,
                                name: str) -> symtable.SymbolTable:
        if table is self._root:
            return table
        try:
            symbol = table.lookup(name)
        except KeyError:
            return table
        if symbol.is_global():
            return self._root or table
        if not symbol.is_nonlocal():
            return table
        current = self._table_parents.get(id(table))
        while current is not None:
            if current.get_type() != "class":
                try:
                    candidate = current.lookup(name)
                except KeyError:
                    candidate = None
                if (candidate is not None and self._symbol_bound(candidate)
                        and not candidate.is_global()
                        and not candidate.is_nonlocal()):
                    return current
            if current is self._root:
                break
            current = self._table_parents.get(id(current))
        return table
    def _take_child(self, table: symtable.SymbolTable, name: str,
                    lineno: int, table_type: str | None = None
                    ) -> symtable.SymbolTable | None:
        children = self._children[id(table)]
        index = next((i for i, child in enumerate(children)
                      if child.get_name() == name
                      and child.get_lineno() == lineno
                      and (table_type is None
                           or child.get_type() == table_type)), None)
        if index is None:
            return None
        return children.pop(index)
    def _is_self_rebinding(self, node: ast.Name) -> bool:
        parent = self._parents.get(id(node))
        if isinstance(parent, ast.Assign):
            return (any(target is node for target in parent.targets)
                    and isinstance(parent.value, ast.Name)
                    and parent.value.id == node.id)
        if isinstance(parent, (ast.AnnAssign, ast.NamedExpr)):
            return (parent.target is node
                    and isinstance(parent.value, ast.Name)
                    and parent.value.id == node.id)
        return False
    def _record_write(self, table: symtable.SymbolTable, name: str,
                      node: ast.AST,
                      position: tuple[int, int] | None = None, *,
                      unbind: bool = False) -> None:
        if isinstance(node, ast.Name) and self._is_self_rebinding(node):
            return
        table = self._declared_binding_table(table, name)
        if position is None:
            position = (getattr(node, "lineno", -1),
                        getattr(node, "col_offset", -1))
        writes = self._nonimport_writes.setdefault(id(table), {})
        writes.setdefault(name, []).append(position)
        event_key = (id(table), name, position)
        if unbind or (isinstance(node, ast.Name)
                      and isinstance(node.ctx, ast.Del)):
            self._unbinding_writes.add(event_key)
        self._binding_activations[event_key] = self._binding_activation(node)
    def _record_imports(self, table: symtable.SymbolTable,
                        node: ast.Import | ast.ImportFrom) -> None:
        position = (getattr(node, "lineno", -1),
                    getattr(node, "col_offset", -1))
        for name, path in _import_alias_paths(node).items():
            target = self._declared_binding_table(table, name)
            events = self._import_events.setdefault(id(target), {})
            events.setdefault(name, []).append((position, path))
    def _binding_activation(self, node: ast.AST) -> tuple[int, int]:
        pos = (getattr(node, "lineno", -1), getattr(node, "col_offset", -1))
        root = None
        parent = node
        while parent is not None:
            attr = _BINDING_EVALUATION_ATTRS.get(type(parent))
            if attr is not None:
                root = getattr(parent, attr, parent)
                break
            if isinstance(parent, ast.stmt):
                break
            parent = self._parents.get(id(parent))
        return (getattr(root, "end_lineno", pos[0]),
                getattr(root, "end_col_offset", pos[1]))
    def _in_type_param_expression(self, node: ast.AST) -> bool:
        current = node
        while current is not None:
            if isinstance(current, _PEP695_TYPE_PARAM_NODES):
                return True
            if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef)):
                return False
            current = self._parents.get(id(current))
        return False
    def _is_delayed_use(
        self, node: ast.AST,
        boundary: symtable.SymbolTable | None = None,
    ) -> bool:
        table = self._name_tables.get(id(node))
        in_type_param = self._in_type_param_expression(node)
        while table is not None and table is not boundary:
            table_type = table.get_type()
            if (table_type == "function"
                    and table.get_name() not in _EAGER_COMPREHENSION_TABLES):
                return True
            if table_type == "type alias" or (
                    table_type == "type parameter" and in_type_param):
                return True
            table = self._table_parents.get(id(table))
        return False
    def _last_write_before(self, table: symtable.SymbolTable, name: str,
                           use_node: ast.AST) -> tuple[int, int] | None:
        writes = self._nonimport_writes.get(id(table), {}).get(name, ())
        use_position = (getattr(use_node, "lineno", -1),
                        getattr(use_node, "col_offset", -1))
        use_table = self._name_tables.get(id(use_node))
        outer_delayed = (table is not use_table
                         and self._is_delayed_use(use_node, table))
        prior = [
            position for position in writes
            if (outer_delayed or position <= use_position) and (
                self._binding_activations.get(
                    (id(table), name, position), position) <= use_position
                or outer_delayed)
        ]
        return max(prior, default=None)
    def _nonimport_binding_active(self, node: ast.Name, *,
                                  global_scope: bool = False) -> bool | None:
        self._ensure_ready()
        if not self._complete:
            return None
        table = (self._root if global_scope
                 else self._name_tables.get(id(node)))
        if table is None:
            return None
        write = self._last_write_before(table, node.id, node)
        if write is None:
            return False
        return (id(table), node.id, write) not in self._unbinding_writes
    def _import_binding_at(
        self, table: symtable.SymbolTable, name: str, use_node: ast.AST,
    ) -> tuple[tuple[int, int], str] | None:
        events = self._import_events.get(id(table), {}).get(name, ())
        if not events:
            return None
        use_table = self._name_tables.get(id(use_node))
        if (table is not use_table
                and self._is_delayed_use(use_node, table)):
            return max(events)
        use_position = (getattr(use_node, "lineno", -1),
                        getattr(use_node, "col_offset", -1))
        prior = [event for event in events if event[0] <= use_position]
        return max(prior) if prior else None
    def _visible_import_path(
        self, table: symtable.SymbolTable, name: str,
        inlined_names: frozenset[str], use_node: ast.AST,
    ) -> str | None:
        if name in inlined_names:
            return None
        current = table
        first = True
        while current is not None:
            if first or current.get_type() != "class":
                try:
                    symbol = current.lookup(name)
                except KeyError:
                    symbol = None
                if symbol is not None:
                    declared = self._declared_binding_table(current, name)
                    if declared is not current:
                        current = declared
                        first = False
                        continue
                    if not symbol.is_imported():
                        binding = self._import_binding_at(
                            current, name, use_node)
                        if binding is not None:
                            write = self._last_write_before(
                                current, name, use_node)
                            if write is None or write <= binding[0]:
                                return binding[1]
                    if symbol.is_imported():
                        binding = self._import_binding_at(
                            current, name, use_node)
                        if binding is None:
                            if current.get_type() != "class":
                                return None
                        else:
                            write = self._last_write_before(
                                current, name, use_node)
                            if write is not None and write > binding[0]:
                                return None
                            return binding[1]
                    if (symbol.is_assigned() or symbol.is_parameter()
                            or symbol.is_namespace()):
                        if current.get_type() != "class":
                            return None
                        if self._last_write_before(
                                current, name, use_node) is not None:
                            return None
            if current is self._root:
                break
            current = self._table_parents.get(id(current))
            first = False
        return None
    def _name_bound(self, table: symtable.SymbolTable, name: str,
                    inlined_names: frozenset[str]) -> bool:
        if name in inlined_names:
            return True
        try:
            symbol = table.lookup(name)
        except KeyError:
            symbol = None
        if symbol is not None and (self._symbol_bound(symbol)
                                   or symbol.is_free()):
            return True
        if table is self._root:
            return False
        try:
            module_symbol = self._root.lookup(name)
        except KeyError:
            return False
        return self._symbol_bound(module_symbol)
    def _visit_arg_defaults(self, args: ast.arguments,
                            table: symtable.SymbolTable,
                            inlined_names: frozenset[str]) -> None:
        for default in [*args.defaults,
                        *[value for value in args.kw_defaults
                          if value is not None]]:
            self._visit(default, table, inlined_names)
    def _visit_arg_annotations(self, args: ast.arguments,
                               table: symtable.SymbolTable,
                               inlined_names: frozenset[str]) -> None:
        args_list = [*args.posonlyargs, *args.args, *args.kwonlyargs]
        if args.vararg is not None:
            args_list.append(args.vararg)
        if args.kwarg is not None:
            args_list.append(args.kwarg)
        for arg in args_list:
            if arg.annotation is not None:
                self._visit(arg.annotation, table, inlined_names)
    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef,
                        table: symtable.SymbolTable,
                        inlined_names: frozenset[str]) -> None:
        self._record_write(table, node.name, node)
        for decorator in node.decorator_list:
            self._visit(decorator, table, inlined_names)
        type_params = getattr(node, "type_params", ())
        scope = table
        if type_params:
            self._visit_arg_defaults(node.args, table, inlined_names)
            scope = self._take_child(
                table, node.name, node.lineno, "type parameter")
            if scope is None:
                raise ValueError(f"AST/符号表类型参数作用域不一致: {node.name}")
            for type_param in type_params:
                self._visit(type_param, scope, inlined_names)
            self._visit_arg_annotations(node.args, scope, inlined_names)
            if node.returns is not None:
                self._visit(node.returns, scope, inlined_names)
        else:
            self._visit(node.args, table, inlined_names)
            if node.returns is not None:
                self._visit(node.returns, table, inlined_names)
        child = self._take_child(
            scope, node.name, node.lineno, "function")
        if child is None:
            raise ValueError(f"AST/符号表函数作用域不一致: {node.name}")
        for stmt in node.body:
            self._visit(stmt, child, inlined_names)
    def _visit_lambda(self, node: ast.Lambda,
                      table: symtable.SymbolTable,
                      inlined_names: frozenset[str]) -> None:
        self._visit(node.args, table, inlined_names)
        child = self._take_child(table, "lambda", node.lineno, "function")
        if child is None:
            raise ValueError("AST/符号表 lambda 作用域不一致")
        self._visit(node.body, child, inlined_names)
    def _visit_class(self, node: ast.ClassDef,
                     table: symtable.SymbolTable,
                     inlined_names: frozenset[str]) -> None:
        self._record_write(table, node.name, node)
        for decorator in node.decorator_list:
            self._visit(decorator, table, inlined_names)
        type_params = getattr(node, "type_params", ())
        scope = table
        if type_params:
            scope = self._take_child(
                table, node.name, node.lineno, "type parameter")
            if scope is None:
                raise ValueError(f"AST/符号表类型参数作用域不一致: {node.name}")
            for type_param in type_params:
                self._visit(type_param, scope, inlined_names)
        for part in [*node.bases, *[kw.value for kw in node.keywords]]:
            self._visit(part, scope, inlined_names)
        child = self._take_child(scope, node.name, node.lineno, "class")
        if child is None:
            raise ValueError(f"AST/符号表类作用域不一致: {node.name}")
        for stmt in node.body:
            self._visit(stmt, child, inlined_names)
    def _visit_type_alias(self, node: ast.AST,
                          table: symtable.SymbolTable,
                          inlined_names: frozenset[str]) -> None:
        name = node.name.id
        self._record_write(table, name, node.name)
        type_params = getattr(node, "type_params", ())
        scope = table
        if type_params:
            scope = self._take_child(
                table, name, node.lineno, "type parameter")
            if scope is None:
                raise ValueError(f"AST/符号表类型参数作用域不一致: {name}")
            for type_param in type_params:
                self._visit(type_param, scope, inlined_names)
        child = self._take_child(scope, name, node.lineno, "type alias")
        if child is None:
            raise ValueError(f"AST/符号表类型别名作用域不一致: {name}")
        self._visit(node.value, child, inlined_names)
    def _visit_comprehension(
        self, node: ast.AST, table: symtable.SymbolTable,
        inlined_names: frozenset[str],
    ) -> None:
        child = self._take_child(
            table, _COMPREHENSION_SCOPE_NAMES[type(node)], node.lineno)
        scope = child or table
        generators = node.generators
        self._visit(generators[0].iter, table, inlined_names)
        targets = frozenset(
            name for generator in generators
            for name in iter_unpack_target_names(generator.target))
        inner_names = inlined_names | targets
        for index, generator in enumerate(generators):
            if index:
                self._visit(generator.iter, scope, inner_names)
            self._visit(generator.target, scope, inner_names)
            for condition in generator.ifs:
                self._visit(condition, scope, inner_names)
        if isinstance(node, ast.DictComp):
            self._visit(node.key, scope, inner_names)
            self._visit(node.value, scope, inner_names)
        else:
            self._visit(node.elt, scope, inner_names)
    def _visit(
        self, node: ast.AST, table: symtable.SymbolTable,
        inlined_names: frozenset[str] = frozenset(),
    ) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self._visit_function(node, table, inlined_names)
            return
        if isinstance(node, ast.Lambda):
            self._visit_lambda(node, table, inlined_names)
            return
        if isinstance(node, ast.ClassDef):
            self._visit_class(node, table, inlined_names)
            return
        if (_PEP695_TYPE_ALIAS_NODE is not None
                and isinstance(node, _PEP695_TYPE_ALIAS_NODE)):
            self._visit_type_alias(node, table, inlined_names)
            return
        if type(node) in _COMPREHENSION_SCOPE_NAMES:
            self._visit_comprehension(node, table, inlined_names)
            return
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            self._record_imports(table, node)
            return
        if isinstance(node, ast.ExceptHandler) and node.name:
            self._record_write(table, node.name, node)
        capture = pattern_capture_name(node)
        if capture is not None:
            self._record_write(table, capture, node)
        if isinstance(node, ast.Name):
            if isinstance(node.ctx, ast.Load):
                self._name_tables[id(node)] = table
                self._name_inlined_names[id(node)] = inlined_names
                self._resolved[id(node)] = self._name_bound(
                    table, node.id, inlined_names)
            elif (isinstance(node.ctx, (ast.Store, ast.Del))
                  and node.id not in inlined_names):
                parent = self._parents.get(id(node))
                bare_annotation = (
                    isinstance(parent, ast.AnnAssign)
                    and parent.target is node and parent.value is None)
                if not bare_annotation:
                    self._record_write(table, node.id, node)
        for child in ast.iter_child_nodes(node):
            self._visit(child, table, inlined_names)
        if isinstance(node, ast.ExceptHandler) and node.name:
            self._record_write(
                table, node.name, node,
                position=(getattr(node, "end_lineno", -1),
                          getattr(node, "end_col_offset", -1)), unbind=True)
    def _ensure_ready(self) -> None:
        if self._ready:
            return
        self._ready = True
        try:
            self._root = symtable.symtable(
                self._source_code, self._file_path, "exec")
            self._register(self._root)
            self._parents = build_parent_map(self._tree)
            self._binding_activations.clear()
            self._visit(self._tree, self._root)
            self._complete = True
        except (SyntaxError, ValueError, RecursionError, MemoryError) as exc:
            logger.warning("词法作用域解析失败，回退到汇总绑定集合: %s", exc)
    def is_bound(self, node: ast.Name) -> bool:
        self._ensure_ready()
        if self._complete:
            return self._resolved.get(id(node), False)
        return node.id in self._fallback_names
    def import_path(self, node: ast.Name) -> str | None:
        # 必须在整棵树访问完成后再解析：函数体/lambda/生成器内的使用是延迟
        # 求值，其后出现的模块级重绑定在定义时已生效；访问过程中间缓存的
        # 结果看不到这些后续写入，会把已被覆盖的导入名误判为导入。
        self._ensure_ready()
        if not self._complete:
            return None
        key = id(node)
        if key not in self._name_import_paths:
            table = self._name_tables.get(key)
            self._name_import_paths[key] = (
                None if table is None else self._visible_import_path(
                    table, node.id,
                    self._name_inlined_names.get(key, frozenset()), node))
        return self._name_import_paths[key]
def binding_names_of(target: ast.AST) -> set[str]:
    return set(iter_unpack_target_names(target))
def module_binding_names(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.Assign):
        names: set[str] = set()
        for target in node.targets:
            names |= binding_names_of(target)
        return names
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return binding_names_of(node.target)
    return set()
def _bind_target(target: ast.AST, bag: set) -> None:
    bag.update(iter_unpack_target_names(target))
_STRING_SEQUENCE_TYPES = (ast.List, ast.Tuple)
def _string_elts(node: ast.AST | None) -> list[str] | None:
    if not isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return None
    return [e.value for e in node.elts
            if isinstance(e, ast.Constant) and isinstance(e.value, str)]
_TRY_STMT_TYPES = (ast.Try,) + ((ast.TryStar,)
                                if hasattr(ast, "TryStar") else ())
_MATCH_STMT_TYPES = (ast.Match,) if hasattr(ast, "Match") else ()
def import_bound_names(stmts) -> set[str]:
    binds: set[str] = set()
    for stmt in stmts:
        binds |= _module_stmt_import_binds(stmt)
    return binds
def _module_stmt_import_binds(stmt: ast.stmt) -> set[str]:
    handler = _STMT_IMPORT_BIND_HANDLERS.get(type(stmt))
    return handler(stmt) if handler is not None else set()
def _try_stmt_import_binds(stmt: ast.stmt) -> set[str]:
    binds = (import_bound_names(stmt.body)
             | import_bound_names(stmt.orelse)
             | import_bound_names(stmt.finalbody))
    for handler in stmt.handlers:
        binds |= import_bound_names(handler.body)
    return binds
def _if_stmt_import_binds(stmt: ast.If) -> set[str]:
    binds = import_bound_names(stmt.orelse)
    if not is_type_checking_guard(stmt.test):
        binds |= import_bound_names(stmt.body)
    return binds
def _match_stmt_import_binds(stmt: ast.stmt) -> set[str]:
    binds: set[str] = set()
    for case in stmt.cases:
        binds |= import_bound_names(case.body)
    return binds
def _loop_stmt_import_binds(stmt: ast.stmt) -> set[str]:
    return (import_bound_names(stmt.body)
            | import_bound_names(stmt.orelse))
def _with_stmt_import_binds(stmt: ast.stmt) -> set[str]:
    return import_bound_names(stmt.body)
def import_stmt_binds(stmt) -> set[str]:
    if isinstance(stmt, ast.Import):
        return {a.asname or a.name.split(".")[0] for a in stmt.names}
    if isinstance(stmt, ast.ImportFrom):
        return {a.asname or a.name for a in stmt.names if a.name != "*"}
    return set()
_STMT_IMPORT_BIND_HANDLERS: dict[type, Callable[[ast.stmt], set[str]]] = {
    ast.Import: import_stmt_binds,
    ast.ImportFrom: import_stmt_binds,
    ast.If: _if_stmt_import_binds,
    **dict.fromkeys(_TRY_STMT_TYPES, _try_stmt_import_binds),
    **dict.fromkeys((ast.For, ast.AsyncFor, ast.While), _loop_stmt_import_binds),
    **dict.fromkeys((ast.With, ast.AsyncWith), _with_stmt_import_binds),
    **dict.fromkeys(_MATCH_STMT_TYPES, _match_stmt_import_binds),
}
def _string_constant_elts(value: ast.AST) -> set[str]:
    return set(_string_elts(value) or ())
_TEST_FRAMEWORK_ROOTS = frozenset({"pytest", "unittest"})
def _is_assertion_call(node: ast.Call) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        name = func.id
    elif isinstance(func, ast.Attribute):
        name = func.attr
    else:
        return False
    return name.startswith("assert") and len(name) > len("assert")
_MODULE_SCOPE = object()
_BUILTIN_EXEC_NAMES = frozenset({"exec", "eval"})
_BUILTIN_EXEC_PATHS = frozenset({"builtins.exec", "builtins.eval"})
_PEP695_TYPE_PARAM_NODES: tuple[type, ...] = tuple(
    _node_type for _node_type in (
        getattr(ast, "TypeVar", None),
        getattr(ast, "ParamSpec", None),
        getattr(ast, "TypeVarTuple", None),
    ) if _node_type is not None)
_PEP695_TYPE_ALIAS_NODE: type | None = getattr(ast, "TypeAlias", None)
_PEP695_BINDING_NODES: tuple[type, ...] = _PEP695_TYPE_PARAM_NODES + (
    (_PEP695_TYPE_ALIAS_NODE,) if _PEP695_TYPE_ALIAS_NODE is not None else ())
def scope_key(owner: ast.AST | None) -> int:
    return id(owner) if owner is not None else id(_MODULE_SCOPE)
_DUNDER_ALL_METHODS = frozenset({'extend', 'append', 'insert'})
def _list_mutation_facts(
    node: ast.AST,
) -> tuple[str, str, ast.AST] | None:
    if not isinstance(node, ast.Call) or not node.args:
        return None
    func = node.func
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)):
        return None
    method = func.attr
    if method not in _DUNDER_ALL_METHODS:
        return None
    arg_index = 1 if method == "insert" else 0
    if len(node.args) <= arg_index:
        return None
    return func.value.id, method, node.args[arg_index]
class ScanContext:
    __slots__ = (
        "_exec_binding_cache",
        "_exec_scope_nodes",
        "_list_value_aliases",
        "_list_value_binds",
        "_parents_built",
        "_pending_all_refs",
        "_pending_bare_parse_calls",
        "_scope_names",
        "alias_paths",
        "all_calls",
        "all_declarations",
        "all_funcs",
        "ast_parse_bare_names",
        "attribute_nodes",
        "bare_ast_parse_calls",
        "builtins_",
        "compile_error",
        "compile_ok",
        "defined",
        "docstrings",
        "except_handlers",
        "exec_scope_keys",
        "file_path",
        "has_assert",
        "has_main_guard",
        "imported",
        "name_nodes",
        "parents",
        "pass_only_funcs",
        "star_import_modules",
        "tree",
    )
    def __init__(self, source_code: str, file_path: str = "", _tree: ast.AST | None = None):
        source_code = coerce_str(source_code)
        file_path = coerce_str(file_path)
        self.file_path = file_path
        self.tree = None
        self.compile_ok = True
        self.compile_error = None
        self._scope_names: ScopeNameResolver | None = None
        source_code = source_code.removeprefix("\ufeff")
        self._resolve_tree(source_code, _tree)
        self._init_containers()
        if self.tree is None:
            return
        self._scope_names = ScopeNameResolver(
            source_code, self.file_path, self.tree, self.defined)
        self._collect_from_tree()
    def _resolve_tree(self, source_code: str, _tree: ast.AST | None) -> None:
        if isinstance(_tree, ast.AST):
            self.tree = _tree
            return
        try:
            compile(source_code, self.file_path or "<scan>", "exec")
            self.tree = ast.parse(source_code)
        except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
            log_swallowed(__name__, e,
                          context=f'ScanContext:compile:{type(e).__name__}')
            self.compile_ok = False
            self.compile_error = e
            self.tree = None
    def _init_containers(self) -> None:
        self.defined: set[str] = set()
        self.imported: set[str] = set()
        self.alias_paths: dict[str, str] = {}
        self._list_value_binds: dict[str, set[str]] = {}
        self._list_value_aliases: dict[str, str] = {}
        self._exec_binding_cache: dict[
            ast.AST, tuple[frozenset[str], frozenset[str]]] = {}
        self._pending_all_refs: list[str] = []
        self.builtins_: set[str] = set(BUILTIN_NAMES)
        self.all_calls: list[ast.Call] = []
        self.all_funcs: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
        self._exec_scope_nodes: list[ast.AST] = []
        self.except_handlers: list[ast.ExceptHandler] = []
        self.name_nodes: list[ast.Name] = []
        self.attribute_nodes: list[ast.Attribute] = []
        self.has_main_guard = False
        self.has_assert = False
        self.bare_ast_parse_calls: list[tuple[int, str]] = []
        self.ast_parse_bare_names: set[str] = set()
        self._pending_bare_parse_calls: list[ast.Call] = []
        self.exec_scope_keys: set[int] = set()
        self.star_import_modules: list[str] = []
        self.all_declarations: set[str] = set()
        self.pass_only_funcs: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
        self.docstrings: list[tuple[str, int]] = []
        self.parents: dict[ast.AST, ast.AST] = {}
        self._parents_built = False
    def _collect_from_tree(self) -> None:
        for node in walk_nodes(self.tree):
            handler = self._NODE_DISPATCH.get(type(node))
            if handler is not None:
                handler(self, node)
        self._resolve_pending_all_refs()
        self._replay_simple_module_exports()
        self._resolve_pending_bare_parses()
        self._build_exec_scope_keys()
    def _resolve_pending_bare_parses(self) -> None:
        for _call in self._pending_bare_parse_calls:
            if (_call.func.id in self.ast_parse_bare_names
                    and self._import_path_at(_call.func) == "ast.parse"
                    and self._is_condition_eval_use(_call)):
                self.bare_ast_parse_calls.append(
                    (getattr(_call, "lineno", 0), _call.func.id))
        self._pending_bare_parse_calls.clear()
    def innermost_func_owner(self, line: int) -> ast.AST | None:
        best = None
        best_span = -1
        for func_node in self._exec_scope_nodes:
            start = getattr(func_node, "lineno", 0) or 0
            end = getattr(func_node, "end_lineno", None) or start
            if not (start <= line <= end):
                continue
            span = end - start
            if best is None or span < best_span:
                best = func_node
                best_span = span
        return best
    def _build_exec_scope_keys(self) -> None:
        for call in self.all_calls:
            if self._is_builtin_exec_call(call):
                self.exec_scope_keys.add(
                    scope_key(self.enclosing_exec_scope(call)))
    def enclosing_exec_scope(self, node: ast.AST) -> ast.AST | None:
        self._ensure_parent_map()
        cur: ast.AST = node
        parent = self.parents.get(cur)
        while parent is not None:
            if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.Lambda, ast.ClassDef))
                    and not _is_def_site_child(parent, cur)):
                return parent
            cur = parent
            parent = self.parents.get(cur)
        return None
    def referenced_outside_own_scope(self, func_node: ast.AST) -> bool:
        name = getattr(func_node, "name", "")
        return any(
            node.id == name
            and isinstance(node.ctx, ast.Load)
            and self.enclosing_exec_scope(node) is not func_node
            and self._name_resolves_to_module(node, name)
            for node in self.name_nodes
        )
    def _name_resolves_to_module(self, node: ast.AST, name: str) -> bool:
        self._ensure_parent_map()
        cur = node
        crossed_function = False
        while True:
            parent = self.parents.get(cur)
            if parent is None:
                return True
            is_scope, next_crossed = _exec_scope_parent(
                self, cur, crossed_function)
            if is_scope:
                if not (isinstance(parent, ast.ClassDef) and crossed_function):
                    local, global_names = self._exec_scope_binding(parent)
                    if name in global_names:
                        return True
                    if name in local:
                        return isinstance(parent, ast.Module)
                crossed_function = next_crossed
            cur = parent
    def _exec_scope_binding(self, scope: ast.AST) -> tuple[frozenset, frozenset]:
        cached = self._exec_binding_cache.get(scope)
        if cached is None:
            cached = exec_scope_declarations(scope)
            self._exec_binding_cache[scope] = cached
        return cached
    def _import_path_at(self, node: ast.Name) -> str | None:
        path = self._scope_names.import_path(node)
        if path is not None or self._scope_names._complete:
            return path
        if node.id in self.imported and self._scope_names.is_bound(node):
            return self.alias_paths.get(node.id)
        return path
    def _is_builtin_exec_call(self, call: ast.Call) -> bool:
        func = call.func
        if isinstance(func, ast.Name):
            path = self._import_path_at(func)
            if path is not None:
                return path in _BUILTIN_EXEC_PATHS
            return (func.id in _BUILTIN_EXEC_NAMES
                    and not _bare_exec_name_is_shadowed(self, call, func.id))
        if (isinstance(func, ast.Attribute)
                and func.attr in _BUILTIN_EXEC_NAMES
                and isinstance(func.value, ast.Name)):
            return self._import_path_at(func.value) == "builtins"
        return False
    def _ensure_parent_map(self) -> None:
        if self._parents_built:
            return
        self.parents = build_node_parent_map(self.tree)
        self._parents_built = True
    def _is_condition_eval_use(self, node: ast.Call) -> bool:
        self._ensure_parent_map()
        cur = node
        while True:
            parent = self.parents.get(cur)
            if parent is None:
                return False
            if isinstance(parent, (ast.Expr, ast.Assert)):
                return True
            if isinstance(parent, (ast.If, ast.While)):
                return any(n is node for n in walk_nodes(parent.test))
            if isinstance(parent, (ast.UnaryOp, ast.BoolOp, ast.Compare,
                                    ast.IfExp)):
                cur = parent
                continue
            return False
        return False
    def _collect_docstring(self, node: ast.AST) -> None:
        if not getattr(node, "body", None):
            return
        first = node.body[0]
        if is_docstring_stmt(first):
            self.docstrings.append(
                (first.value.value, getattr(first, "lineno", 0) or 0))
    _PROTOCOL_STUB_DECORATORS = frozenset({"abstractmethod", "overload"})
    @classmethod
    def _is_protocol_stub(cls, node: ast.AST) -> bool:
        for deco in getattr(node, "decorator_list", ()):
            target = deco.func if isinstance(deco, ast.Call) else deco
            if expr_target_name(target) in cls._PROTOCOL_STUB_DECORATORS:
                return True
        return False
    def _handle_func_def(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        self.defined.add(node.name)
        self.all_funcs.append(node)
        self._exec_scope_nodes.append(node)
        self._collect_docstring(node)
        body = node.body
        real_body = [s for s in body if not is_docstring_stmt(s)]
        if (len(real_body) == 1 and is_placeholder_stmt(real_body[0])
                and not self._is_protocol_stub(node)):
            self.pass_only_funcs.append(node)
    def _handle_lambda(self, node: ast.Lambda) -> None:
        self._exec_scope_nodes.append(node)

    def _handle_import(self, node: ast.Import) -> None:
        for alias in node.names:
            top = alias.name.split(".")[0]
            name = alias.asname or top
            self.imported.add(name)
            self.alias_paths[name] = alias.name if alias.asname else top
            self._mark_test_framework(top)
    def _handle_import_from(self, node: ast.ImportFrom) -> None:
        star_src = self._relative_import_source(node)
        for alias in node.names:
            self._handle_import_from_alias(node, alias, star_src)
        if not node.level and node.module:
            self._mark_test_framework(node.module.split(".")[0])
    def _relative_import_source(self, node: ast.ImportFrom) -> str:
        if node.level:
            return "." * node.level + (node.module or "")
        return node.module or ""
    def _handle_import_from_alias(self, node: ast.ImportFrom,
                                  alias: ast.alias, star_src: str) -> None:
        if alias.name == "*":
            self.star_import_modules.append(star_src)
            return
        if (not node.level and node.module == "ast"
                and alias.name == "parse"):
            self.ast_parse_bare_names.add(alias.asname or alias.name)
        name = alias.asname or alias.name
        self.imported.add(name)
        _sep = "" if star_src.endswith(".") else "."
        self.alias_paths[name] = f"{star_src}{_sep}{alias.name}"
    def _mark_test_framework(self, module_root: str) -> None:
        if module_root in _TEST_FRAMEWORK_ROOTS:
            self.has_assert = True
    def _handle_call(self, node: ast.Call) -> None:
        self.all_calls.append(node)
        if _is_assertion_call(node):
            self.has_assert = True
        self._collect_all_method_call(node)
        self._collect_ast_parse_call(node)
    def _collect_all_method_call(self, node: ast.Call) -> None:
        facts = _list_mutation_facts(node)
        if facts is None or self.enclosing_exec_scope(node) is not None:
            return
        target, _method, arg = facts
        if target == "__all__":
            self._record_all_name_arg(arg)
            return
        current = self._resolve_list_value(target)
        if current is None:
            return
        name = str_constant_value(arg)
        added = ({name} if name is not None
                 else self._static_list_value(arg))
        if added is None:
            return
        self._list_value_aliases.pop(target, None)
        self._list_value_binds[target] = set(current) | added
    def _record_all_name_arg(self, arg: ast.AST) -> None:
        name = str_constant_value(arg)
        if name is not None:
            self.all_declarations.add(name)
            return
        self._collect_all_names(arg)
    def _collect_ast_parse_call(self, node: ast.Call) -> None:
        if (isinstance(node.func, ast.Attribute) and node.func.attr == "parse"
                and isinstance(node.func.value, ast.Name)
                and self._import_path_at(node.func.value) == "ast"
                and self._is_condition_eval_use(node)):
            self.bare_ast_parse_calls.append((getattr(node, "lineno", 0), "ast.parse"))
        elif (isinstance(node.func, ast.Name)
                and node.func.id in self.ast_parse_bare_names):
            self._pending_bare_parse_calls.append(node)
    def _handle_except(self, node: ast.ExceptHandler) -> None:
        self.except_handlers.append(node)
        if node.name:
            self.defined.add(node.name)
    def _handle_class_def(self, node: ast.ClassDef) -> None:
        self.defined.add(node.name)
        self._collect_docstring(node)
    def _handle_ann_assign(self, node: ast.AnnAssign) -> None:
        if not isinstance(node.target, ast.Name):
            return
        self._bind_name(
            node.target.id, node.value,
            module_scope=self.enclosing_exec_scope(node) is None)
    def _static_list_value(self, value: ast.AST) -> set[str] | None:
        if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            return _string_constant_elts(value)
        if isinstance(value, ast.Name):
            resolved = self._resolve_list_value(value.id)
            return set(resolved) if resolved is not None else None
        if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
            left = self._static_list_value(value.left)
            right = self._static_list_value(value.right)
            if left is not None and right is not None:
                return left | right
        return None
    def _record_binding(self, name: str, value: ast.AST | None, *,
                        module_scope: bool) -> None:
        if not module_scope:
            return
        if name == "__all__":
            if value is not None:
                self._collect_all_names(value)
            return
        if value is None:
            return
        static_value = self._static_list_value(value)
        self._list_value_binds.pop(name, None)
        self._list_value_aliases.pop(name, None)
        if static_value is not None:
            self._list_value_binds[name] = static_value
        elif isinstance(value, ast.Name):
            self._list_value_aliases[name] = value.id
    def _resolve_list_value(self, name: str) -> set[str] | None:
        seen: set[str] = set()
        current = name
        while current not in seen:
            seen.add(current)
            bound = self._list_value_binds.get(current)
            if bound is not None:
                return bound
            alias = self._list_value_aliases.get(current)
            if alias is None:
                break
            current = alias
        return None
    def _bind_name(self, name: str, value: ast.AST | None, *,
                   module_scope: bool) -> None:
        self.defined.add(name)
        self._record_binding(name, value, module_scope=module_scope)
    def _handle_aug_assign(self, node: ast.AugAssign) -> None:
        if (not isinstance(node.target, ast.Name)
                or self.enclosing_exec_scope(node) is not None):
            return
        name = node.target.id
        if name == "__all__":
            self._collect_all_names(node.value)
            return
        if not isinstance(node.op, ast.Add):
            return
        current = self._resolve_list_value(name)
        added = self._static_list_value(node.value)
        if current is None or added is None:
            return
        self._list_value_aliases.pop(name, None)
        self._list_value_binds[name] = set(current) | added
    def _handle_target_owner(self, node: ast.AST) -> None:
        self._collect_target_names(node.target)
    def _handle_arg(self, node: ast.arg) -> None:
        self.defined.add(node.arg)
    def _handle_with(self, node: ast.With | ast.AsyncWith) -> None:
        for item in node.items:
            if item.optional_vars is not None:
                self._collect_target_names(item.optional_vars)
    def _handle_named_expr(self, node: ast.NamedExpr) -> None:
        if isinstance(node.target, ast.Name):
            self.defined.add(node.target.id)
    def _handle_match_capture(self, node: ast.AST) -> None:
        capture = pattern_capture_name(node)
        if capture is not None:
            self.defined.add(capture)
    def _handle_pep695_binding(self, node: ast.AST) -> None:
        name = getattr(node, "name", None)
        if isinstance(name, ast.Name):
            self.defined.add(name.id)
        elif isinstance(name, str) and name:
            self.defined.add(name)
    def _handle_name(self, node: ast.Name) -> None:
        self.name_nodes.append(node)
    def _handle_assert(self, _node: ast.Assert) -> None:
        self.has_assert = True
    def _handle_attribute(self, node: ast.Attribute) -> None:
        self.attribute_nodes.append(node)
    def _handle_assign(self, node: ast.Assign) -> None:
        module_scope = self.enclosing_exec_scope(node) is None
        for target in node.targets:
            if isinstance(target, ast.Name):
                self._bind_name(
                    target.id, node.value, module_scope=module_scope)
            elif isinstance(target, (ast.Tuple, ast.List)):
                self._collect_target_names(target)
    def _collect_all_names(self, value: ast.AST) -> None:
        if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            self.all_declarations.update(_string_constant_elts(value))
        elif isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
            self._collect_all_names(value.left)
            self._collect_all_names(value.right)
        elif isinstance(value, ast.Name):
            self._pending_all_refs.append(value.id)
            bound = self._resolve_list_value(value.id)
            if bound is not None:
                self.all_declarations.update(bound)
    def _resolve_pending_all_refs(self, *, preserve: bool = False) -> None:
        if not self._pending_all_refs:
            return
        for ref in dict.fromkeys(self._pending_all_refs):
            bound = self._resolve_list_value(ref)
            if bound is not None:
                self.all_declarations.update(bound)
        if not preserve:
            self._pending_all_refs.clear()
    def _simple_module_export_events(self) -> list[ast.AST] | None:
        if not isinstance(self.tree, ast.Module):
            return None
        events: list[ast.AST] = []
        definition_nodes = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
        for stmt in self.tree.body:
            if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                events.append(stmt)
                continue
            if isinstance(stmt, ast.Expr):
                if (isinstance(stmt.value, ast.Call)
                        and _list_mutation_facts(stmt.value) is not None):
                    events.append(stmt.value)
                continue
            if isinstance(stmt, definition_nodes):
                if any(_list_mutation_facts(node) is not None
                       for site in iter_def_site_nodes(stmt)
                       for node in walk_nodes(site)):
                    return None
                continue
            if isinstance(stmt, (ast.Import, ast.ImportFrom, ast.Pass)):
                continue
            return None
        return events
    @staticmethod
    def _direct_assignment_targets(node: ast.AST) -> list[ast.Name]:
        targets = (node.targets if isinstance(node, ast.Assign)
                   else [getattr(node, "target", None)])
        return [target for target in targets
                if isinstance(target, ast.Name)]
    def _replay_simple_module_exports(self) -> None:
        events = self._simple_module_export_events()
        if events is None:
            return
        self._list_value_binds.clear()
        self._list_value_aliases.clear()
        self.all_declarations.clear()
        self._pending_all_refs.clear()
        for node in events:
            if isinstance(node, ast.Call):
                self._collect_all_method_call(node)
                self._resolve_pending_all_refs(preserve=True)
                continue
            if isinstance(node, ast.AnnAssign) and node.value is None:
                continue
            targets = self._direct_assignment_targets(node)
            target_names = {target.id for target in targets}
            self._resolve_pending_all_refs(preserve=True)
            if isinstance(node, ast.AugAssign):
                self._handle_aug_assign(node)
                self._resolve_pending_all_refs(preserve=True)
                continue
            replaces_all = "__all__" in target_names
            if replaces_all:
                self.all_declarations.clear()
                self._pending_all_refs.clear()
            else:
                self._pending_all_refs = [
                    ref for ref in self._pending_all_refs
                    if ref not in target_names]
            if isinstance(node, ast.Assign):
                self._handle_assign(node)
            else:
                self._handle_ann_assign(node)
            if replaces_all:
                for name in target_names - {"__all__"}:
                    if name not in self._pending_all_refs:
                        self._pending_all_refs.append(name)
            self._resolve_pending_all_refs(preserve=True)
        self._pending_all_refs.clear()
    def _main_guard_in_exec_scope(self, node: ast.If) -> bool:
        self._ensure_parent_map()
        cur = self.parents.get(node)
        while cur is not None:
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
                return False
            if isinstance(cur, ast.Module):
                return True
            cur = self.parents.get(cur)
        return False
    def _handle_if(self, node: ast.If) -> None:
        if (is_main_check(node.test)
                and self._main_guard_in_exec_scope(node)):
            self.has_main_guard = True
    def _collect_target_names(self, target: ast.AST) -> None:
        _bind_target(target, self.defined)
    _NODE_DISPATCH: ClassVar[dict[type, Any]] = {
        ast.FunctionDef: _handle_func_def,
        ast.AsyncFunctionDef: _handle_func_def,
        ast.ClassDef: _handle_class_def,
        ast.Lambda: _handle_lambda,
        ast.Import: _handle_import,
        ast.ImportFrom: _handle_import_from,
        ast.Call: _handle_call,
        ast.ExceptHandler: _handle_except,
        ast.Assign: _handle_assign,
        ast.AnnAssign: _handle_ann_assign,
        ast.AugAssign: _handle_aug_assign,
        ast.For: _handle_target_owner,
        ast.AsyncFor: _handle_target_owner,
        ast.arg: _handle_arg,
        ast.With: _handle_with,
        ast.AsyncWith: _handle_with,
        ast.NamedExpr: _handle_named_expr,
        ast.comprehension: _handle_target_owner,
        ast.MatchAs: _handle_match_capture,
        ast.MatchStar: _handle_match_capture,
        ast.MatchMapping: _handle_match_capture,
        ast.Name: _handle_name,
        ast.If: _handle_if,
        ast.Assert: _handle_assert,
        ast.Attribute: _handle_attribute,
        ast.Module: _collect_docstring,
    }
    _NODE_DISPATCH.update(dict.fromkeys(_PEP695_BINDING_NODES,
                                        _handle_pep695_binding))
def _enclosing_scope_exprs(def_node: ast.AST) -> list[ast.expr]:
    exprs = list(iter_def_site_nodes(def_node))
    for type_param in getattr(def_node, "type_params", None) or ():
        for attr in ("bound", "default"):
            expression = getattr(type_param, attr, None)
            if expression is not None:
                exprs.append(expression)
    return exprs
def expr_load_roots(expr: ast.expr | None) -> set[str]:
    if expr is None:
        return set()
    return {sub.id for sub in walk_nodes(expr)
            if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)}
def enclosing_scope_load_names(node: ast.AST) -> set[str]:
    names: set[str] = set()
    for expr in _enclosing_scope_exprs(node):
        names |= expr_load_roots(expr)
    return names
def enclosing_scope_binds(node: ast.AST) -> set[str]:
    binds: set[str] = set()
    for expr in _enclosing_scope_exprs(node):
        _expr_module_binds(expr, binds)
    return binds
def expr_binds(expr: ast.expr | None) -> set[str]:
    binds: set[str] = set()
    _expr_module_binds(expr, binds)
    return binds
def _collect_global_refs(scope, refs: set[str]) -> None:
    for symbol in scope.get_symbols():
        if symbol.is_global():
            refs.add(symbol.get_name())
    for child in scope.get_children():
        _collect_global_refs(child, refs)
def symtable_global_refs(sym_table, name: str) -> set[str] | None:
    try:
        sym = sym_table.lookup(name)
        if not sym.is_namespace():
            return None
        namespaces = sym.get_namespaces()
    except (KeyError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'symtable_global_refs:{type(_e).__name__}')
        return None
    refs: set[str] = set()
    for ns in namespaces:
        _collect_global_refs(ns, refs)
    return refs
def _pattern_binds(pattern: ast.AST | None, binds: set[str]) -> None:
    if pattern is not None:
        binds.update(iter_pattern_capture_names(pattern))
def _expr_module_binds_no_scope(expr, binds: set[str]) -> None:
    if expr is None:
        return
    if isinstance(expr, ast.NamedExpr):
        binds.add(expr.target.id)
        _expr_module_binds_no_scope(expr.value, binds)
        return
    if isinstance(expr, (ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)):
        _comp_module_binds(expr, binds)
        return
    if isinstance(expr, ast.Lambda):
        return
    for child in ast.iter_child_nodes(expr):
        if isinstance(child, ast.expr):
            _expr_module_binds_no_scope(child, binds)
        elif isinstance(child, ast.keyword):
            _expr_module_binds_no_scope(child.value, binds)
def _comp_module_binds(expr, binds: set[str]) -> None:
    generators = expr.generators
    if not generators:
        return
    _expr_module_binds(generators[0].iter, binds)
    for gen in generators[1:]:
        _expr_module_binds_no_scope(gen.iter, binds)
    for gen in generators:
        for cond in gen.ifs:
            _expr_module_binds_no_scope(cond, binds)
    if isinstance(expr, ast.DictComp):
        _expr_module_binds_no_scope(expr.key, binds)
        _expr_module_binds_no_scope(expr.value, binds)
    else:
        _expr_module_binds_no_scope(expr.elt, binds)
def _expr_children(expr, binds: set[str]) -> None:
    for child in ast.iter_child_nodes(expr):
        if isinstance(child, ast.expr):
            _expr_module_binds(child, binds)
        elif isinstance(child, ast.keyword):
            _expr_module_binds(child.value, binds)
def _expr_module_binds(expr: ast.expr | None, binds: set[str]) -> None:
    if expr is None:
        return
    if isinstance(expr, ast.NamedExpr):
        binds.add(expr.target.id)
        _expr_module_binds(expr.value, binds)
        return
    if isinstance(expr, (ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)):
        _comp_module_binds(expr, binds)
        return
    if isinstance(expr, ast.Lambda):
        for default in expr.args.defaults:
            _expr_module_binds(default, binds)
        for default in expr.args.kw_defaults:
            _expr_module_binds(default, binds)
        return
    _expr_children(expr, binds)
def _stmt_module_binds(stmt: ast.stmt, binds: set[str]) -> None:
    handler = _STMT_BIND_HANDLERS.get(type(stmt))
    if handler is not None:
        handler(stmt, binds)
def _bind_definition(stmt: ast.stmt, binds: set[str]) -> None:
    binds.add(stmt.name)
    binds |= enclosing_scope_binds(stmt)
def _bind_type_alias(stmt: ast.stmt, binds: set[str]) -> None:
    binds.add(stmt.name.id)
    for tp in getattr(stmt, "type_params", None) or ():
        for attr in ("bound", "default"):
            sub = getattr(tp, attr, None)
            if sub is not None:
                _expr_module_binds(sub, binds)
    _expr_module_binds(stmt.value, binds)
def _bind_assign(stmt: ast.stmt, binds: set[str]) -> None:
    for t in stmt.targets:
        _bind_target(t, binds)
    _expr_module_binds(stmt.value, binds)
def _bind_annassign(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.annotation, binds)
    if stmt.value is not None:
        _bind_target(stmt.target, binds)
        _expr_module_binds(stmt.value, binds)
def _bind_augassign(stmt: ast.stmt, binds: set[str]) -> None:
    _bind_target(stmt.target, binds)
    _expr_module_binds(stmt.value, binds)
def _bind_import_stmt(stmt: ast.stmt, binds: set[str]) -> None:
    binds |= import_stmt_binds(stmt)
def _bind_for(stmt: ast.stmt, binds: set[str]) -> None:
    _bind_target(stmt.target, binds)
    _expr_module_binds(stmt.iter, binds)
    for sub in stmt.body + stmt.orelse:
        _stmt_module_binds(sub, binds)
def _bind_while(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.test, binds)
    for sub in stmt.body + stmt.orelse:
        _stmt_module_binds(sub, binds)
def _bind_if(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.test, binds)
    if not is_type_checking_guard(stmt.test):
        for sub in stmt.body:
            _stmt_module_binds(sub, binds)
    for sub in stmt.orelse:
        _stmt_module_binds(sub, binds)
def _bind_try(stmt: ast.stmt, binds: set[str]) -> None:
    for sub in stmt.body:
        _stmt_module_binds(sub, binds)
    for handler in stmt.handlers:
        _expr_module_binds(handler.type, binds)
        if handler.name:
            binds.add(handler.name)
        for sub in handler.body:
            _stmt_module_binds(sub, binds)
    for sub in stmt.orelse + stmt.finalbody:
        _stmt_module_binds(sub, binds)
def _bind_with(stmt: ast.stmt, binds: set[str]) -> None:
    for item in stmt.items:
        _expr_module_binds(item.context_expr, binds)
        if item.optional_vars is not None:
            _bind_target(item.optional_vars, binds)
    for sub in stmt.body:
        _stmt_module_binds(sub, binds)
def _bind_match(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.subject, binds)
    for case in stmt.cases:
        _pattern_binds(case.pattern, binds)
        _expr_module_binds(case.guard, binds)
        for sub in case.body:
            _stmt_module_binds(sub, binds)
def _bind_expr(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.value, binds)
def _bind_assert(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.test, binds)
    _expr_module_binds(stmt.msg, binds)
def _bind_raise(stmt: ast.stmt, binds: set[str]) -> None:
    _expr_module_binds(stmt.exc, binds)
    _expr_module_binds(stmt.cause, binds)
_STMT_BIND_HANDLERS = {
    ast.FunctionDef: _bind_definition,
    ast.AsyncFunctionDef: _bind_definition,
    ast.ClassDef: _bind_definition,
    ast.Assign: _bind_assign,
    ast.AnnAssign: _bind_annassign,
    ast.AugAssign: _bind_augassign,
    ast.Import: _bind_import_stmt,
    ast.ImportFrom: _bind_import_stmt,
    ast.For: _bind_for,
    ast.AsyncFor: _bind_for,
    ast.While: _bind_while,
    ast.If: _bind_if,
    ast.Try: _bind_try,
    ast.With: _bind_with,
    ast.AsyncWith: _bind_with,
    ast.Expr: _bind_expr,
    ast.Assert: _bind_assert,
    ast.Raise: _bind_raise,
}
_STMT_BIND_HANDLERS.update(dict.fromkeys(_TRY_STMT_TYPES, _bind_try))
_STMT_BIND_HANDLERS.update(dict.fromkeys(_MATCH_STMT_TYPES, _bind_match))
if hasattr(ast, "TypeAlias"):
    _STMT_BIND_HANDLERS[ast.TypeAlias] = _bind_type_alias
def _flat_definition_name(node) -> str | None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return node.name
    return None
def _flat_type_alias_name(node) -> str | None:
    if hasattr(ast, "TypeAlias") and isinstance(node, ast.TypeAlias):
        return node.name.id
    return None
def _flat_node_binds(node) -> set[str]:
    name = _flat_definition_name(node)
    if name is not None:
        return {name}
    name = _flat_type_alias_name(node)
    if name is not None:
        return {name}
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return import_stmt_binds(node)
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
        return {node.id}
    capture = pattern_capture_name(node)
    return {capture} if capture is not None else set()
def _flat_fallback_binds(stmts) -> set[str]:
    flat: set[str] = set()
    stack = list(reversed(stmts))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            flat |= _flat_node_binds(node)
            stack.extend(reversed(_enclosing_scope_exprs(node)))
            continue
        if isinstance(node, ast.Lambda):
            stack.extend(reversed(_enclosing_scope_exprs(node)))
            continue
        if isinstance(node, TYPE_ALIAS_NODES):
            flat |= _flat_node_binds(node)
            stack.append(node.value)
            for type_param in getattr(node, "type_params", None) or ():
                for attr in ("bound", "default"):
                    expression = getattr(type_param, attr, None)
                    if expression is not None:
                        stack.append(expression)
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            stack.append(node.annotation)
            continue
        if isinstance(node, ast.If) and is_type_checking_guard(node.test):
            stack.append(node.test)
            stack.extend(reversed(node.orelse))
            continue
        if isinstance(node, ast.comprehension):
            stack.append(node.iter)
            stack.extend(reversed(node.ifs))
            continue
        flat |= _flat_node_binds(node)
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
    return flat
def module_scope_binds(stmts) -> set[str]:
    binds: set[str] = set()
    try:
        for stmt in stmts:
            _stmt_module_binds(stmt, binds)
        return binds
    except RecursionError as _e:
        log_swallowed(
            __name__, _e,
            context='module_scope_binds:RecursionError')
        return _flat_fallback_binds(stmts)
_SCOPE_INDEX_NODES = (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.Call,
                      ast.For, ast.AsyncFor, ast.NamedExpr, ast.With,
                      ast.AsyncWith)
_BINDING_STMT_NODES = (ast.Assign, ast.AugAssign, ast.AnnAssign,
                       ast.NamedExpr, ast.For, ast.AsyncFor, ast.With,
                       ast.AsyncWith, ast.Delete)
#: ``build_scope_index`` 的 memo。
#:
#: 容量控制用**真 LRU**（命中移队尾、满则逐出最久未用项），不能用「满即
#: ``clear()``」：扫描 307 个文件时该 memo 必然撞上限，一次清空会把所有兄弟
#: 模块的作用域索引全部作废并逐个重建，形成周期性重建雪崩（与
#: ``_SINK_RESOLVER_MEMO`` 同一教训）。
_SCOPE_INDEX_MEMO: OrderedDict[int, tuple[ast.AST, dict[int, str]]] = OrderedDict()
_SCOPE_INDEX_MEMO_LOCK = threading.Lock()
_SCOPE_INDEX_MEMO_CAP = 512
#: ``_definition_scope_keys`` 的**单条最近树**缓存。
#:
#: 该函数是树的纯函数（只读遍历），实测单文件被调用 441 次，每次都要全量遍历
#: 一遍 AST。调用方（``build_scope_index`` / ``collect_shadow_bindings``）总是
#: 对同一棵树连续调用，因此只需记住「上一棵树」就能消掉绝大多数重复遍历。
#:
#: 刻意**不**做成多条目 LRU：``_definition_scope_keys`` 的结果是「整棵树节点
#: id→作用域」的大字典，多条目缓存会强引用大量 AST（实测把安全扫描从 8.1s
#: 推高到 12.7s）；单条缓存的驻留成本是常数，收益却有上界。
#: 结构：``[tree, keys]``，用 ``is`` 做身份校验以抵御 id 复用。
_DEF_SCOPE_KEYS_LAST: list = [None, None]
_DEF_SCOPE_KEYS_LOCK = threading.Lock()

def _is_def_site_child(node: ast.AST, child: ast.AST) -> bool:
    if any(child is _d for _d in (getattr(node, 'decorator_list', None) or [])):
        return True
    if any(child is _p for _p in (getattr(node, 'type_params', None) or [])):
        return True
    if isinstance(node, ast.ClassDef):
        return any(
            child is _x
            for _seq in (getattr(node, 'bases', None) or [],
                         getattr(node, 'keywords', None) or [])
            for _x in _seq)
    if child is getattr(node, 'returns', None):
        return True
    _args = getattr(node, 'args', None)
    return _args is not None and child is _args
def _iter_exec_child_nodes(node: ast.AST):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        yield from node.body
    else:
        yield from ast.iter_child_nodes(node)
def _index_def_site_nodes(child: ast.AST, scope: str,
                          idx: dict[int, str]) -> None:
    for _site in iter_def_site_nodes(child):
        for _sub in walk_nodes(_site):
            if isinstance(_sub, _SCOPE_INDEX_NODES):
                idx[id(_sub)] = scope
class ScopeEventIndex:
    def __init__(self, tree: ast.AST) -> None:
        self._parents = build_parent_map(tree)
        self._events: dict[int, dict[str, list[tuple[tuple[int, int], Any]]]] = {}
    def _chain(self, node: ast.AST) -> list[ast.AST]:
        return scope_chain(node, self._parents)
    @staticmethod
    def _prior_value(events: list[tuple[tuple[int, int], Any]],
                     node: ast.AST) -> tuple[bool, Any]:
        pos = (node.lineno, node.col_offset)
        prior = [event for event in events if event[0] <= pos]
        if not prior:
            return False, None
        return True, prior[-1][1]
    @staticmethod
    def _add_event(events: dict[str, list[tuple[tuple[int, int], Any]]],
                   name: str, node: ast.AST, value: Any) -> None:
        pos = (getattr(node, "lineno", -1), getattr(node, "col_offset", -1))
        events.setdefault(name, []).append((pos, value))
def build_scope_index(tree: ast.AST) -> dict[int, str]:
    _key = id(tree)
    with _SCOPE_INDEX_MEMO_LOCK:
        _hit = _SCOPE_INDEX_MEMO.get(_key)
        if _hit is not None and _hit[0] is tree:
            # 命中移回队尾，避免热条目被先逐出。
            _SCOPE_INDEX_MEMO.move_to_end(_key)
            return _hit[1]
    idx: dict[int, str] = {}
    scope_keys = _definition_scope_keys(tree)
    _stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while _stack:
        node, scope = _stack.pop()
        for child in _iter_exec_child_nodes(node):
            _index_scope_child(child, scope, idx, _stack, scope_keys)
    with _SCOPE_INDEX_MEMO_LOCK:
        _SCOPE_INDEX_MEMO[_key] = (tree, idx)
        _SCOPE_INDEX_MEMO.move_to_end(_key)
        while len(_SCOPE_INDEX_MEMO) > _SCOPE_INDEX_MEMO_CAP:
            _SCOPE_INDEX_MEMO.popitem(last=False)
    return idx
def _child_scope_key(scope: str, name: str) -> str:
    return f"{scope}.{name}" if scope else name
def _definition_scope_keys(tree: ast.AST) -> dict[int, str]:
    """返回 ``{id(定义节点): 作用域键}``——树的纯函数，按「最近一棵树」memo 化。

    调用方 ``build_scope_index`` / ``collect_shadow_bindings`` 只读返回值，
    故可直接共享缓存实例。
    """
    with _DEF_SCOPE_KEYS_LOCK:
        _last_tree, _last_keys = _DEF_SCOPE_KEYS_LAST[0], _DEF_SCOPE_KEYS_LAST[1]
    if _last_tree is tree and _last_keys is not None:
        return _last_keys
    keys: dict[int, str] = {}
    used_names: dict[str, set[str]] = {}
    stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while stack:
        node, scope = stack.pop()
        for child in _iter_exec_child_nodes(node):
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.ClassDef)):
                stack.append((child, scope))
                continue
            used = used_names.setdefault(scope, set())
            key = _child_scope_key(scope, child.name)
            if child.name in used:
                key = (f"{key}@{getattr(child, 'lineno', -1)}:"
                       f"{getattr(child, 'col_offset', -1)}")
            used.add(child.name)
            keys[id(child)] = key
            stack.append((child, key))
    with _DEF_SCOPE_KEYS_LOCK:
        _DEF_SCOPE_KEYS_LAST[0] = tree
        _DEF_SCOPE_KEYS_LAST[1] = keys
    return keys
def _index_scope_child(child: ast.AST, scope: str, idx: dict[int, str],
                       stack: list[tuple[ast.AST, str]],
                       scope_keys: dict[int, str]) -> None:
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
        idx[id(child)] = scope
        _index_def_site_nodes(child, scope, idx)
        stack.append((child, scope_keys[id(child)]))
        return
    if isinstance(child, _SCOPE_INDEX_NODES):
        idx[id(child)] = scope
    stack.append((child, scope))
def release_binding_caches() -> dict[str, int]:
    """清空本模块全部「按 AST 对象身份作键」的派生缓存。"""
    out: dict[str, int] = {}
    with _SCOPE_INDEX_MEMO_LOCK:
        out["scope_index"] = len(_SCOPE_INDEX_MEMO)
        _SCOPE_INDEX_MEMO.clear()
    with _DEF_SCOPE_KEYS_LOCK:
        out["def_scope_keys"] = 1 if _DEF_SCOPE_KEYS_LAST[0] is not None else 0
        _DEF_SCOPE_KEYS_LAST[0] = None
        _DEF_SCOPE_KEYS_LAST[1] = None
    return out


def clear_scope_index_memo() -> int:
    """清空本模块全部树级派生缓存，返回清掉的条目数。"""
    with _SCOPE_INDEX_MEMO_LOCK:
        n = len(_SCOPE_INDEX_MEMO)
        _SCOPE_INDEX_MEMO.clear()
    with _DEF_SCOPE_KEYS_LOCK:
        if _DEF_SCOPE_KEYS_LAST[0] is not None:
            n += 1
        _DEF_SCOPE_KEYS_LAST[0] = None
        _DEF_SCOPE_KEYS_LAST[1] = None
    return n
@dataclass
class _ScopeCtx:
    local: dict
    global_names: dict
    nonlocal_decls: dict
    class_scopes: set
    def bags(self, scope: str) -> tuple[set, set, set]:
        return (self.local.setdefault(scope, set()),
                self.global_names.setdefault(scope, set()),
                self.nonlocal_decls.setdefault(scope, set()))
def collect_shadow_bindings(tree: ast.AST) -> tuple[dict, dict, frozenset]:
    ctx = _ScopeCtx(local={}, global_names={}, nonlocal_decls={},
                    class_scopes=set())
    _visit_scope(tree, "", ctx, _definition_scope_keys(tree))
    ctx.global_names[''] = set()
    return (
        {k: frozenset(v) for k, v in ctx.local.items()},
        {k: frozenset(v) for k, v in ctx.global_names.items()},
        frozenset(ctx.class_scopes),
    )
def _collect_walrus_targets(expr: ast.AST | None, bag: set) -> None:
    if expr is None:
        return
    stack = [expr]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Lambda):
            stack.extend(iter_def_site_nodes(cur))
            continue
        if isinstance(cur, ast.NamedExpr):
            _bind_target(cur.target, bag)
        stack.extend(ast.iter_child_nodes(cur))
def _visit_scope(node: ast.AST, scope: str, ctx: _ScopeCtx,
                 scope_keys: dict[int, str]) -> None:
    bag, _gbag, nbag = ctx.bags(scope)
    annotations_bind = isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    if annotations_bind:
        bag |= collect_param_names(node)
    stack = [node]
    while stack:
        cur = stack.pop()
        for child in _iter_exec_child_nodes(cur):
            if _dispatch_scope_child(
                    child, scope, ctx, annotations_bind, scope_keys):
                continue
            stack.append(child)
    bag -= nbag
def collect_binding_names(node: ast.AST, names: set, *,
                          include_imports: bool = True) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        _collect_nested_scope_names(node, names)
        return True
    if isinstance(node, _BINDING_STMT_NODES):
        _collect_target_binding(node, names)
    elif isinstance(node, (ast.Import, ast.ImportFrom)):
        if include_imports:
            names.update(import_stmt_binds(node))
    elif isinstance(node, TYPE_ALIAS_NODES):
        _collect_type_alias_names(node, names)
    else:
        _collect_name_only_binding(node, names)
    return False
def _collect_nested_scope_names(node: ast.AST, names: set) -> None:
    if not isinstance(node, ast.Lambda):
        names.add(node.name)
    for _site in iter_def_site_nodes(node):
        _collect_walrus_targets(_site, names)
def exec_scope_declarations(
        scope: ast.AST) -> tuple[frozenset[str], frozenset[str]]:
    local = (set(collect_param_names(scope))
             if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.Lambda)) else set())
    global_names: set[str] = set()
    nonlocal_names: set[str] = set()
    annotations_bind = isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
    stack = [scope.body] if isinstance(scope, ast.Lambda) else [scope]
    while stack:
        cur = stack.pop()
        for child in _iter_exec_child_nodes(cur):
            if isinstance(child, ast.Global):
                global_names.update(child.names)
                continue
            if isinstance(child, ast.Nonlocal):
                nonlocal_names.update(child.names)
                continue
            if (annotations_bind and isinstance(child, ast.AnnAssign)
                    and child.value is None):
                _bind_target(child.target, local)
            if not collect_binding_names(child, local):
                stack.append(child)
    local.difference_update(nonlocal_names)
    return frozenset(local), frozenset(global_names)
def _module_exec_name_bound(ctx: ScanContext, name: str) -> bool:
    if not isinstance(ctx.tree, ast.Module):
        return False
    local, _globals = ctx._exec_scope_binding(ctx.tree)
    return name in local
def _exec_scope_parent(ctx: ScanContext, cur: ast.AST,
                       crossed_function: bool) -> tuple[bool, bool]:
    parent = ctx.parents.get(cur)
    if parent is None or not isinstance(
            parent, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.ClassDef, ast.Module)):
        return False, crossed_function
    if not isinstance(parent, ast.Module) and _is_def_site_child(parent, cur):
        return False, crossed_function
    return True, (crossed_function or isinstance(
        parent, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)))
def _bare_exec_name_is_shadowed(ctx: ScanContext, call: ast.Call,
                                name: str) -> bool:
    ctx._ensure_parent_map()
    cur: ast.AST = call
    crossed_function = False
    while True:
        parent = ctx.parents.get(cur)
        if parent is None:
            return False
        is_scope, next_crossed = _exec_scope_parent(ctx, cur, crossed_function)
        if is_scope:
            if not (isinstance(parent, ast.ClassDef) and crossed_function):
                local, global_names = ctx._exec_scope_binding(parent)
                immediate = None
                if (not crossed_function
                        and isinstance(parent, (ast.Module, ast.ClassDef))):
                    immediate = ctx._scope_names._nonimport_binding_active(
                        call.func,
                        global_scope=(isinstance(parent, ast.Module)
                                      or name in global_names))
                if immediate is not None:
                    if immediate:
                        return True
                elif name in global_names:
                    return _module_exec_name_bound(ctx, name)
                elif name in local:
                    return True
            crossed_function = next_crossed
        cur = parent
def _dispatch_scope_child(child, scope: str, ctx: _ScopeCtx,
                          annotations_bind: bool,
                          scope_keys: dict[int, str]) -> bool:
    bag, gbag, nbag = ctx.bags(scope)
    if (annotations_bind and isinstance(child, ast.AnnAssign)
            and child.value is None):
        _bind_target(child.target, bag)
    if isinstance(child, ast.Nonlocal):
        nbag.update(child.names)
        return True
    if isinstance(child, ast.Global):
        gbag.update(child.names)
        return True
    if collect_binding_names(child, bag):
        if not isinstance(child, ast.Lambda):
            _child_scope = scope_keys[id(child)]
            if isinstance(child, ast.ClassDef):
                ctx.class_scopes.add(_child_scope)
            _visit_scope(child, _child_scope, ctx, scope_keys)
        return True
    return False
def _collect_name_only_binding(child, bag: set) -> None:
    capture = pattern_capture_name(child)
    if capture is not None:
        bag.add(capture)
def _collect_target_binding(child, bag: set) -> None:
    if isinstance(child, ast.Assign):
        for t in child.targets:
            _bind_target(t, bag)
    elif isinstance(child, (ast.With, ast.AsyncWith)):
        for item in child.items:
            if item.optional_vars is not None:
                _bind_target(item.optional_vars, bag)
    elif isinstance(child, ast.Delete):
        for t in child.targets:
            _bind_target(t, bag)
    elif isinstance(child, ast.AnnAssign):
        if child.value is not None:
            _bind_target(child.target, bag)
    else:
        _bind_target(child.target, bag)
def _scope_level_owner(sc: str, name: str, local_bindings: dict,
                       global_names: dict) -> str | None:
    if name in global_names.get(sc, frozenset()):
        return ""
    if name in local_bindings.get(sc, frozenset()):
        return sc
    return None
def _skip_class_scope(sc: str, scope: str,
                      class_scopes: frozenset | None) -> bool:
    return bool(class_scopes) and sc in class_scopes and sc != scope
def owner_scope(scope: str, name: str, local_bindings: dict,
                global_names: dict,
                class_scopes: frozenset | None = None) -> str:
    if not scope:
        return ""
    parts = scope.split('.')
    for i in range(len(parts), 0, -1):
        sc = '.'.join(parts[:i])
        if _skip_class_scope(sc, scope, class_scopes):
            continue
        _owner = _scope_level_owner(sc, name, local_bindings, global_names)
        if _owner is not None:
            return _owner
    return ""
def module_fallback_shadowed(scope: str, name: str,
                             local_bindings: dict,
                             global_names: dict,
                             class_scopes: frozenset | None = None) -> bool:
    return owner_scope(scope, name, local_bindings, global_names,
                       class_scopes) != ""
def _version_gated_types(*names: str) -> tuple:
    return tuple(
        _t for _t in (getattr(ast, _name, None) for _name in names)
        if _t is not None
    )
_TYPE_ALIAS_TYPES = _version_gated_types("TypeAlias")
_COMPOUND_STMT_TYPES = ((ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
                         ast.If, ast.While)
                        + _TRY_STMT_TYPES + _MATCH_STMT_TYPES)
_SIMPLE_EXPR_STMT_TYPES = (ast.Expr, ast.Assert, ast.AugAssign, ast.Raise)
def build_module_symbol_table(tree: ast.Module) -> set:
    symbols: set = set()
    for node in getattr(tree, "body", []):
        _collect_stmt_symbols(node, symbols)
    return symbols
def _collect_stmt_symbols(node, symbols: set) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        symbols.add(node.name)
        symbols.update(enclosing_scope_binds(node))
        return
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        _collect_assign_names(node, symbols)
        return
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        _collect_import_names(node, symbols)
        return
    if isinstance(node, _SIMPLE_EXPR_STMT_TYPES):
        for expr in _stmt_expr_slots(node):
            _collect_walrus_targets(expr, symbols)
        return
    if isinstance(node, ast.Delete):
        for target in node.targets:
            symbols.difference_update(iter_unpack_target_names(target))
        return
    if isinstance(node, _TYPE_ALIAS_TYPES):
        _collect_type_alias_names(node, symbols)
        return
    if isinstance(node, _COMPOUND_STMT_TYPES):
        _collect_compound_names(node, symbols)
def _stmt_expr_slots(node):
    if isinstance(node, ast.Assert):
        return node.test, node.msg
    if isinstance(node, ast.Raise):
        return node.exc, node.cause
    return node.value,
def _collect_assign_names(node, symbols: set) -> None:
    if isinstance(node, ast.Assign):
        for t in node.targets:
            _bind_target(t, symbols)
        _collect_walrus_targets(node.value, symbols)
    elif isinstance(node, ast.AnnAssign):
        _collect_walrus_targets(node.annotation, symbols)
        if node.value is not None:
            _bind_target(node.target, symbols)
            _collect_walrus_targets(node.value, symbols)
def _collect_import_names(node, symbols: set) -> None:
    symbols.update(import_stmt_binds(node))
def _collect_type_alias_names(node, symbols: set) -> None:
    alias_name = getattr(node.name, "id", None)
    if isinstance(alias_name, str) and alias_name:
        symbols.add(alias_name)
def _collect_compound_names(node, symbols: set) -> None:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        _collect_for_names(node, symbols)
        return
    if isinstance(node, (ast.With, ast.AsyncWith)):
        _collect_with_names(node, symbols)
        return
    if isinstance(node, (ast.If, ast.While)):
        _collect_conditional_names(node, symbols)
        return
    if isinstance(node, _MATCH_STMT_TYPES):
        _collect_match_names(node, symbols)
        return
    if isinstance(node, _TRY_STMT_TYPES):
        _collect_try_block_symbols(node, symbols)
def _symbol_path(base: set[str], statements) -> set[str]:
    path = set(base)
    _collect_block_stmts(statements, path)
    return path

def _merge_symbol_paths(symbols: set[str], paths: list[set[str]]) -> None:
    merged = set().union(*paths)
    symbols.clear()
    symbols.update(merged)

def _collect_for_names(node, symbols: set) -> None:
    base = set(symbols)
    _collect_walrus_targets(node.iter, base)
    iterated = set(base)
    _bind_target(node.target, iterated)
    _collect_block_stmts(node.body, iterated)
    _collect_block_stmts(node.orelse, iterated)
    skipped = _symbol_path(base, node.orelse)
    _merge_symbol_paths(symbols, [iterated, skipped])
def _collect_with_names(node, symbols: set) -> None:
    for item in node.items:
        _collect_walrus_targets(item.context_expr, symbols)
        if item.optional_vars is not None:
            _bind_target(item.optional_vars, symbols)
    _collect_block_stmts(node.body, symbols)
def _collect_conditional_names(node, symbols: set) -> None:
    _collect_walrus_targets(node.test, symbols)
    if isinstance(node, ast.If) and is_type_checking_guard(node.test):
        _collect_block_stmts(node.orelse, symbols)
        return
    base = set(symbols)
    body = _symbol_path(base, node.body)
    if isinstance(node, ast.If):
        alternate = _symbol_path(base, node.orelse)
    else:
        _collect_block_stmts(node.orelse, body)
        alternate = _symbol_path(base, node.orelse)
    _merge_symbol_paths(symbols, [body, alternate])
def _collect_match_names(node, symbols: set) -> None:
    _collect_walrus_targets(node.subject, symbols)
    base = set(symbols)
    paths: list[set[str]] = []
    exhaustive = False
    for case in node.cases:
        path = set(base)
        _collect_match_capture_names(case.pattern, path)
        _collect_walrus_targets(getattr(case, "guard", None), path)
        _collect_block_stmts(case.body, path)
        paths.append(path)
        if (case.guard is None and isinstance(case.pattern, ast.MatchAs)
                and case.pattern.pattern is None):
            exhaustive = True
    if not exhaustive:
        paths.append(base)
    _merge_symbol_paths(symbols, paths)
def _collect_block_stmts(stmts, symbols: set) -> None:
    for sub in stmts:
        _collect_stmt_symbols(sub, symbols)
def _collect_try_block_symbols(node, symbols: set) -> None:
    base = set(symbols)
    normal = _symbol_path(base, node.body)
    _collect_block_stmts(node.orelse, normal)
    paths = [normal]
    for handler in node.handlers:
        path = set(base)
        _collect_walrus_targets(handler.type, path)
        _collect_block_stmts(handler.body, path)
        if handler.name:
            path.discard(handler.name)
        paths.append(path)
    for path in paths:
        _collect_block_stmts(node.finalbody, path)
    _merge_symbol_paths(symbols, paths)
def _collect_match_capture_names(pattern, symbols: set) -> None:
    if pattern is not None:
        symbols.update(iter_pattern_capture_names(pattern))
__all__ = [
    "ScanContext",
    "ScopeEventIndex",
    "ScopeNameResolver",
    "binding_names_of",
    "build_module_symbol_table",
    "build_scope_index",
    "clear_scope_index_memo",
    "collect_binding_names",
    "collect_shadow_bindings",
    "enclosing_scope_binds",
    "enclosing_scope_load_names",
    "exec_scope_declarations",
    "expr_binds",
    "expr_load_roots",
    "import_bound_names",
    "import_stmt_binds",
    "module_binding_names",
    "module_fallback_shadowed",
    "module_scope_binds",
    "owner_scope",
    "scope_key",
    "symtable_global_refs",
]
logger.info(
    "diag_shared_ast_bindings L0 名字绑定·词法作用域·扫描上下文与符号名集合已加载: %d 项导出",
    len(__all__))

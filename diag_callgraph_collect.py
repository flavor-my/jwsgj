from __future__ import annotations

import ast
import copy
import os
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass
from typing import NamedTuple

from jwsgj.diag_callgraph_facts import (
    CallEdge,
    ScopedNameResolver,
    _qualify_module_member,
    assignment_name_index,
    build_assignment_scope_index,
    symbol_hit,
)
from jwsgj.diag_callgraph_resolve import (
    _MODULE_SCOPE_NAME,
    _MODULE_SCOPE_SUFFIX,
    SELF_CLS_NAMES,
    CalleeFileContext,
    CalleeResolver,
    _add_call_edge,
    _add_constructor_init_edge,
    _constant_str_arg,
    _destructured_elements,
    _dispatch_key,
    _DispatchKeyT,
    _file_alias_map,
    _graph_pkg_root,
    _graph_type_store,
    _iter_definition_annotations,
    _RefEdgeBuilder,
    dotted_name_of,
    extract_type_name,
    is_cls_bound_factory,
    is_project_class,
    is_self_attr_target,
    prescan_module_globals,
    resolve_inherited_method,
    walk_visitors_once,
)
from jwsgj.diag_callgraph_verdicts import (
    CallGraphBuilderProtocol,
    append_synthetic_edge,
)
from jwsgj.diag_module_surface import relative_import_base
from jwsgj.diag_shared_ast_nodes import (
    FastDispatchNodeVisitor,
    iter_arg_nodes,
    iter_module_scope_nodes,
    module_postpones_annotations,
    path_to_dotted_module,
    pkg_root_name,
    resolve_import_binding,
    split_identifier,
    strip_pkg_root,
    torn_list,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    parent_map,
    scope_import_tables,
    scope_shadows_import,
)

__all__ = [
    'AssignmentDataflowTracker',
    'CallCollectorV2',
    'DispatchListVisitor',
    'DispatchTables',
    'DynamicImportVisitor',
    'DynamicRegistrationVisitor',
    'ImportAliasCollector',
    'ReturnTypeProducer',
    'TypeFlowState',
    'collect_dynamic_patterns',
    'relative_import_module',
    'track_assignment_chains',
]
_SELF_ATTR_PREFIXES = ("self.", "cls.")
def _lexical_binding_scope(table, scope, name: str):
    direct = scope
    while scope is not None:
        if (not (isinstance(scope, ast.ClassDef) and scope is not direct)
                and name in table.bound.get(scope, ())):
            return scope
        scope = table.parent.get(scope)
    return table.tree
@dataclass(frozen=True)
class _DispatchScope:
    module_level: bool
    global_names: frozenset[str] | set[str]
    class_name: str | None = None
    binding_frames: Callable[[str], list[int]] | None = None
    def enclosing_frames(self, var_name: str) -> list[int]:
        if self.binding_frames is None:
            return []
        return self.binding_frames(var_name)
    def resolves_to_module(self, var_name: str) -> bool:
        return self.module_level or var_name in self.global_names
    def is_self_attr(self, var_name: str) -> bool:
        return var_name.startswith(_SELF_ATTR_PREFIXES)
    def binding_key(self, var_name: str) -> str:
        return _dispatch_binding_key(var_name, self.class_name)
def _dispatch_binding_key(var_name: str,
                          class_name: str | None) -> str:
    if not var_name.startswith(_SELF_ATTR_PREFIXES):
        return var_name
    return f"{class_name}.{var_name}" if class_name else var_name
def _binding_target_key(target) -> str | None:
    if isinstance(target, ast.Name):
        return target.id
    if (isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id in SELF_CLS_NAMES):
        return f"{target.value.id}.{target.attr}"
    return None
def _copy_bucket(
        bucket: dict[str, dict[_DispatchKeyT, str]],
) -> dict[str, dict[_DispatchKeyT, str]]:
    return {name: dict(entries) for name, entries in bucket.items()}
class DispatchTables:
    def __init__(
            self, *,
            uses_module_binding: Callable[[str], bool] | None = None,
            binding_frames: Callable[[str], list[int]] | None = None,
    ) -> None:
        self._module_literals: dict[str, dict[_DispatchKeyT, str]] = {}
        self._local_literals: dict[str, dict[_DispatchKeyT, str]] = {}
        self._registry_entries: dict[str, dict[_DispatchKeyT, str]] = {}
        self._local_opaque: set[str] = set()
        self._module_opaque: set[str] = set()
        self._uses_module_binding = uses_module_binding
        self._binding_frames = binding_frames
        self._local_literals_stack: list[dict[str, dict[_DispatchKeyT, str]]] = []
        self._registry_stack: list[dict[str, dict[_DispatchKeyT, str]]] = []
        self._local_opaque_stack: list[set[str]] = []
    def push_scope(self) -> None:
        self._local_literals_stack.append(_copy_bucket(self._local_literals))
        self._registry_stack.append(_copy_bucket(self._registry_entries))
        self._local_opaque_stack.append(set(self._local_opaque))
    def pop_scope(self) -> None:
        self._local_literals = self._local_literals_stack.pop()
        self._registry_entries = self._registry_stack.pop()
        self._local_opaque = self._local_opaque_stack.pop()
    def track_dict_literal(self, node, *, scope: _DispatchScope) -> bool:
        bindings = self._literal_bindings(node)
        if not bindings:
            return False
        tracked = False
        for var_name, value in bindings:
            if not isinstance(value, ast.Dict):
                self._drop_binding(var_name, scope=scope)
                continue
            key_map = self._dict_literal_key_map(value)
            if not key_map and value.keys:
                self._record_binding(var_name, {}, scope=scope)
                continue
            self._record_binding(var_name, key_map, scope=scope)
            tracked = True
        return tracked
    @staticmethod
    def _literal_bindings(node) -> list[tuple[str, ast.expr]]:
        targets = ([node.target] if isinstance(node, ast.AnnAssign)
                   else list(node.targets))
        return [
            (var_name, node.value)
            for target in targets
            if (var_name := _binding_target_key(target)) is not None
        ]
    @staticmethod
    def _dict_literal_key_map(dict_node) -> dict[_DispatchKeyT, str]:
        key_map: dict[_DispatchKeyT, str] = {}
        for k, v in zip(dict_node.keys, dict_node.values, strict=True):
            key_str = _dispatch_key(k)
            if key_str is None:
                continue
            if isinstance(v, ast.Name):
                key_map[key_str] = v.id
            elif isinstance(v, ast.Attribute):
                key_map[key_str] = ast.unparse(v)
        return key_map
    def track_registry_assignment(self, node: ast.Assign, *,
                                  scope: _DispatchScope) -> None:
        func_name = dotted_name_of(node.value)
        for target in node.targets:
            if not isinstance(target, ast.Subscript):
                continue
            var_name = _binding_target_key(target.value)
            if var_name is None or not self._is_registry_container(
                    var_name, scope):
                continue
            key_str = _dispatch_key(target.slice)
            if key_str is None:
                continue
            if func_name is None:
                self._discard_registry_entry(var_name, key_str, scope=scope)
            else:
                self._record_registry_entry(
                    var_name, key_str, func_name, scope=scope)
    def _is_registry_container(self, var_name: str,
                               scope: _DispatchScope) -> bool:
        key = scope.binding_key(var_name)
        if key in self._local_opaque:
            return False
        if any(key in bucket for bucket in (
                self._local_literals, self._registry_entries)):
            return True
        if key in self._module_opaque:
            return False
        if key in self._module_literals:
            return True
        simple = var_name.rsplit(".", 1)[-1]
        lowered = simple.lower()
        return (simple.isupper() or "registry" in lowered
                or "register" in lowered)
    def _drop_binding(self, var_name: str, *,
                      scope: _DispatchScope) -> None:
        key = scope.binding_key(var_name)
        self._registry_entries.pop(key, None)
        if scope.is_self_attr(var_name) or scope.resolves_to_module(var_name):
            self._module_literals.pop(key, None)
            self._local_literals.pop(key, None)
            self._local_opaque.discard(key)
            self._module_opaque.add(key)
            return
        self._local_literals.pop(key, None)
        self._local_opaque.add(key)
        for index in scope.enclosing_frames(var_name):
            self._local_literals_stack[index].pop(key, None)
            self._registry_stack[index].pop(key, None)
            self._local_opaque_stack[index].add(key)
    def _record_binding(
            self, var_name: str, key_map: dict[_DispatchKeyT, str], *,
                        scope: _DispatchScope) -> None:
        key = scope.binding_key(var_name)
        self._registry_entries.pop(key, None)
        self._local_opaque.discard(key)
        if scope.is_self_attr(var_name) or scope.resolves_to_module(var_name):
            self._module_opaque.discard(key)
            self._module_literals[key] = dict(key_map)
        else:
            self._local_literals[key] = dict(key_map)
            for index in scope.enclosing_frames(var_name):
                self._registry_stack[index].pop(key, None)
                self._local_opaque_stack[index].discard(key)
                self._local_literals_stack[index][key] = dict(key_map)
    def _record_registry_entry(
            self, var_name: str, key_str: _DispatchKeyT,
                               func_name: str, *, scope: _DispatchScope) -> None:
        key = scope.binding_key(var_name)
        if (scope.is_self_attr(var_name)
                or self._registry_hits_module_bucket(var_name, key, scope)):
            self._module_literals.setdefault(
                key, {})[key_str] = func_name
        else:
            self._registry_entries.setdefault(
                key, {})[key_str] = func_name
            for index in scope.enclosing_frames(var_name):
                self._registry_stack[index].setdefault(
                    key, {})[key_str] = func_name
    def _discard_registry_entry(
            self, var_name: str, key_str: _DispatchKeyT, *,
                                scope: _DispatchScope) -> None:
        key = scope.binding_key(var_name)
        module_bucket = (scope.is_self_attr(var_name)
                         or self._registry_hits_module_bucket(
                             var_name, key, scope))
        if module_bucket:
            buckets = (self._module_literals,)
        else:
            buckets = (self._local_literals, self._registry_entries)
        for bucket in buckets:
            entries = bucket.get(key)
            if entries is not None:
                entries.pop(key_str, None)
        if not module_bucket:
            for index in scope.enclosing_frames(var_name):
                for stack in (self._local_literals_stack,
                              self._registry_stack):
                    entries = stack[index].get(key)
                    if entries is not None:
                        entries.pop(key_str, None)
    def _registry_hits_module_bucket(
        self, var_name: str, key: str, scope: _DispatchScope
    ) -> bool:
        if scope.resolves_to_module(var_name):
            return True
        return key in self._module_literals and key not in self._local_literals
    def merged_map(self, var_name: str,
                   class_name: str | None = None
                   ) -> dict[_DispatchKeyT, str] | None:
        key = _dispatch_binding_key(var_name, class_name)
        is_self_attr = var_name.startswith(_SELF_ATTR_PREFIXES)
        lexical_local = not is_self_attr and self._uses_module_binding is not None
        if lexical_local and self._uses_module_binding(var_name):
            if key in self._module_opaque:
                return None
            entries = self._module_literals.get(key)
            return dict(entries) if entries is not None else None
        local_literals = self._local_literals
        registry_entries = self._registry_entries
        local_opaque = self._local_opaque
        if lexical_local and self._binding_frames is not None:
            frames = self._binding_frames(var_name)
            if frames:
                frame = frames[-1]
                local_literals = self._local_literals_stack[frame]
                registry_entries = self._registry_stack[frame]
                local_opaque = self._local_opaque_stack[frame]
        if key in local_opaque:
            return None
        base = None if lexical_local else self._module_literals.get(key)
        local_lit = local_literals.get(key)
        local_reg = registry_entries.get(key)
        if (key in self._module_opaque
                and local_lit is None and local_reg is None):
            return None
        if base is None and local_lit is None and local_reg is None:
            return None
        merged: dict[_DispatchKeyT, str] = {}
        buckets = ((local_lit, local_reg) if local_lit is not None
                   else (base, local_reg))
        for bucket in buckets:
            if bucket:
                merged.update(bucket)
        return merged
class TypeFlowState:
    def __init__(self, shared_instance_attrs: dict[str, str | None],
                 module_name: str = "") -> None:
        self._module_name = module_name
        self._shared_instance_attrs = shared_instance_attrs
        self._local_types: dict[str, str | None] = {}
        self._type_stack: list[dict[str, str | None]] = []
        self._module_globals: dict[str, str | None] = {}
        self._global_names: set[str] = set()
        self._global_stack: list[set[str]] = []
        self._local_callables: set[str] = set()
        self._callable_stack: list[set[str]] = []
        self._callable_aliases: dict[str, str | None] = {}
        self._callable_alias_stack: list[dict[str, str | None]] = []
        self._cls_bound_to_class: bool = False
        self._cls_stack: list[bool] = []
        self._instance_attrs: dict[str, str | None] = {}
        self._class_closure_stack: list[tuple[
            dict[str, str | None], set[str], dict[str, str | None]]] = []
        self._nonlocal_names: set[str] = set()
        self._nonlocal_stack: list[set[str]] = []
        self._module_callables: set[str] = set()
        self._module_callable_aliases: dict[str, str | None] = {}
        self._lexical_scopes = None
        self._scope_node: ast.AST | None = None
        self._scope_node_stack: list[ast.AST | None] = []
    def push_class_scope(self, *, nested_in_class: bool = False,
                         node: ast.ClassDef | None = None) -> None:
        if nested_in_class and self._class_closure_stack:
            closure = self._class_closure_stack[-1]
        else:
            closure = (
                dict(self._local_types), set(self._local_callables),
                dict(self._callable_aliases),
            )
        self._class_closure_stack.append(closure)
        self._push_scope_frames(node)
        self._global_names = set()
    def pop_class_scope(self) -> None:
        self._pop_scope_frames()
        self._class_closure_stack.pop()
    def _push_scope_frames(self, node: ast.AST | None) -> None:
        self._type_stack.append(dict(self._local_types))
        self._callable_stack.append(set(self._local_callables))
        self._callable_alias_stack.append(dict(self._callable_aliases))
        self._global_stack.append(set(self._global_names))
        self._nonlocal_stack.append(set(self._nonlocal_names))
        self._scope_node_stack.append(self._scope_node)
        self._scope_node = node
        self._nonlocal_names = set()
    def _pop_scope_frames(self) -> None:
        self._local_types = self._type_stack.pop()
        self._local_callables = self._callable_stack.pop()
        self._callable_aliases = self._callable_alias_stack.pop()
        self._global_names = self._global_stack.pop()
        self._nonlocal_names = self._nonlocal_stack.pop()
        self._scope_node = self._scope_node_stack.pop()
    def push_function_scope(
            self, node: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
            *, direct_method: bool = False) -> None:
        self._push_scope_frames(node)
        if direct_method and self._class_closure_stack:
            types, callables, aliases = self._class_closure_stack[-1]
            self._local_types = dict(types)
            self._local_callables = set(callables)
            self._callable_aliases = dict(aliases)
        self._cls_stack.append(self._cls_bound_to_class)
        self._global_names = set()
        self._reset_cls_binding(node, direct_method)
        self._bind_param_annotations(node)
    def _reset_cls_binding(
            self, node: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
            direct_method: bool) -> None:
        has_cls = any(arg.arg == 'cls' for arg in iter_arg_nodes(node.args))
        if not has_cls:
            self._cls_bound_to_class = (
                self._cls_bound_to_class and not direct_method)
            return
        self._cls_bound_to_class = any(
            isinstance(_dec, ast.Name) and _dec.id == 'classmethod'
            for _dec in getattr(node, 'decorator_list', ()))
    def _bind_param_annotations(
            self, node: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda,
    ) -> None:
        for arg in iter_arg_nodes(node.args):
            self._local_callables.add(arg.arg)
            self._callable_aliases[arg.arg] = None
            type_name = (extract_type_name(arg.annotation)
                         if arg.annotation is not None else None)
            self._local_types[arg.arg] = type_name
    def register_local_callable(self, name: str,
                                at_module_scope: bool = False) -> None:
        self._local_callables.add(name)
        self._callable_aliases[name] = None
        if at_module_scope or name in self._global_names:
            self._module_callables.add(name)
            self._module_callable_aliases[name] = None
        else:
            self._write_nonlocal_alias(name, None)
        self._invalidate_name_type(name, at_module_scope=at_module_scope)
    def pop_function_scope(self) -> None:
        self._pop_scope_frames()
        self._cls_bound_to_class = self._cls_stack.pop()
    def seed_module_globals(self, node: ast.Module) -> None:
        self._lexical_scopes = collect_lexical_scope_table(node)
        self._scope_node = node
        prescan_module_globals(node, self._module_globals)
    def _resolve_name_scope(self, name: str, scope=None):
        table = self._lexical_scopes
        if table is None:
            return None
        scope = self._scope_node if scope is None else scope
        return _lexical_binding_scope(table, scope, name)
    def _uses_module_binding(self, name: str) -> bool:
        # ``global`` 声明会跳过所有外层函数作用域；词法表虽已把名字搬回模块，
        # 但外层函数同名局部仍会先被 ``_resolve_name_scope`` 命中，导致
        # ``global X`` 被误判为闭包引用（接收者类型/可调用别名取到外层旧值）。
        if name in self._global_names:
            return True
        table = self._lexical_scopes
        return table is not None and self._resolve_name_scope(name) is table.tree
    def enclosing_binding_frames(self, name: str) -> list[int]:
        if self._lexical_scopes is None:
            return []
        target = self._resolve_name_scope(name)
        return [
            index for index, scope in enumerate(self._scope_node_stack)
            if self._resolve_name_scope(name, scope) is target
        ]
    def _nonlocal_frames(self, name: str) -> list[int]:
        if name not in self._nonlocal_names:
            return []
        return self.enclosing_binding_frames(name)
    def _write_nonlocal_alias(self, name: str, target: str | None,
                              *, bound: bool = True) -> None:
        for index in self._nonlocal_frames(name):
            self._callable_alias_stack[index][name] = target
            if bound:
                self._callable_stack[index].add(name)
            else:
                self._callable_stack[index].discard(name)
    def _write_nonlocal_type(self, name: str, type_name: str) -> None:
        for index in self._nonlocal_frames(name):
            self._type_stack[index][name] = type_name
            self._callable_alias_stack[index][name] = None
            self._callable_stack[index].discard(name)
    def var_type(self, name: str) -> str | None:
        # 与 is_tracked_callable/has_callable_binding 同口径：显式 module 绑定
        # （模块作用域或 ``global``）不得回退到外层函数的同名局部类型。
        if self._uses_module_binding(name):
            return self._module_globals.get(name)
        if name in self._local_types:
            return self._local_types[name]
        if name in self._module_globals:
            return self._module_globals[name]
        return None
    def _attr_key(self, class_name: str, attr: str) -> str:
        # 嵌套类路径（``Outer.Inner``）必须与顶层类一样带模块前缀：共享实例
        # 属性表是全工程级的，旧逻辑见「名字含点」即视为已限定，导致跨模块
        # 同名嵌套类互相覆盖；别名赋值 ``self.y = self.x`` 会读到别的模块的
        # 类型，连出指向不存在函数的幻影调用边。仅本模块全限定名保留原样。
        module = self._module_name
        if module and not class_name.startswith(f"{module}."):
            class_name = _qualify_module_member(module, class_name)
        return f"{class_name}.{attr}"
    def instance_attr_type(self, class_name: str, attr: str) -> str | None:
        return self._instance_attrs.get(self._attr_key(class_name, attr))
    def shared_instance_attr_type(self, class_name: str, attr: str) -> str | None:
        attr_key = self._attr_key(class_name, attr)
        if attr_key in self._shared_instance_attrs:
            return self._shared_instance_attrs[attr_key]
        return self._instance_attrs.get(attr_key)
    def is_tracked_callable(self, name: str) -> bool:
        if self._uses_module_binding(name):
            return (self._module_globals.get(name) is not None
                    or name in self._module_callables)
        if name in self._local_types:
            return (self._local_types[name] is not None
                    or name in self._local_callables)
        return (self._module_globals.get(name) is not None
                or name in self._local_callables)
    def is_bound_callable(self, name: str) -> bool:
        if self._uses_module_binding(name):
            return name in self._module_callables
        return name in self._local_callables
    @property
    def global_names(self) -> set[str]:
        return set(self._global_names)
    @property
    def cls_bound_to_class(self) -> bool:
        return self._cls_bound_to_class
    def declare_globals(self, names: list[str]) -> None:
        self._global_names.update(names)
    def declare_nonlocals(self, names: list[str]) -> None:
        self._nonlocal_names.update(names)
    def has_callable_binding(self, name: str) -> bool:
        if self._uses_module_binding(name):
            return name in self._module_callable_aliases
        return name in self._callable_aliases
    def callable_alias(self, name: str) -> str | None:
        if self._uses_module_binding(name):
            return self._module_callable_aliases.get(name)
        return self._callable_aliases.get(name)
    def clear_module_callable_binding(self, name: str) -> None:
        self._local_callables.discard(name)
        self._callable_aliases.pop(name, None)
        self._module_callables.discard(name)
        self._module_callable_aliases.pop(name, None)
        self._invalidate_name_type(name, at_module_scope=True)
    def bind_callable_alias(self, name: str, target: str | None,
                            at_module_scope: bool = False) -> None:
        self._local_callables.add(name)
        self._callable_aliases[name] = target
        if at_module_scope or name in self._global_names:
            self._module_callables.add(name)
            self._module_callable_aliases[name] = target
        else:
            self._write_nonlocal_alias(name, target)
        self._invalidate_name_type(name, at_module_scope)
    def bind_name(self, name: str, type_name: str, at_module_scope: bool) -> None:
        self._local_callables.discard(name)
        if at_module_scope:
            self._callable_aliases.pop(name, None)
            self._module_callables.discard(name)
            self._module_callable_aliases.pop(name, None)
            self._module_globals[name] = type_name
        else:
            self._callable_aliases[name] = None
            self._local_types[name] = type_name
            if name in self._global_names:
                self._module_callables.discard(name)
                self._module_callable_aliases.pop(name, None)
                self._module_globals[name] = type_name
            else:
                self._write_nonlocal_type(name, type_name)
    def _invalidate_name_type(self, name: str, at_module_scope: bool) -> None:
        if at_module_scope:
            if name in self._module_globals:
                self._module_globals[name] = None
            return
        if name in self._local_types or name in self._module_globals:
            self._local_types[name] = None
        if name in self._global_names and name in self._module_globals:
            self._module_globals[name] = None
        for index in self._nonlocal_frames(name):
            self._type_stack[index][name] = None
    def unbind_name(self, name: str, at_module_scope: bool) -> None:
        self._local_callables.discard(name)
        if at_module_scope:
            self._callable_aliases.pop(name, None)
            self._module_callables.discard(name)
            self._module_callable_aliases.pop(name, None)
        else:
            self._callable_aliases[name] = None
            if name in self._global_names:
                self._module_callables.discard(name)
                self._module_callable_aliases.pop(name, None)
            else:
                self._write_nonlocal_alias(name, None, bound=False)
        self._invalidate_name_type(name, at_module_scope)
    def is_name_type_invalidated(self, name: str) -> bool:
        if name in self._local_types:
            return self._local_types[name] is None
        return name in self._module_globals and self._module_globals[name] is None
    def bind_self_attr(self, class_name: str, attr: str, type_name: str) -> None:
        attr_key = self._attr_key(class_name, attr)
        self._instance_attrs[attr_key] = type_name
        self._shared_instance_attrs[attr_key] = type_name
    def unbind_self_attr(self, class_name: str, attr: str) -> None:
        attr_key = self._attr_key(class_name, attr)
        if attr_key in self._instance_attrs or attr_key in self._shared_instance_attrs:
            self._instance_attrs[attr_key] = None
            self._shared_instance_attrs[attr_key] = None
    def is_self_attr_type_invalidated(self, class_name: str, attr: str) -> bool:
        attr_key = self._attr_key(class_name, attr)
        return (attr_key in self._instance_attrs
                and self._instance_attrs[attr_key] is None)
def _infer_value_type(value, current_class, types_state, resolver):
    if isinstance(value, ast.Name):
        return types_state.var_type(value.id)
    if (isinstance(value, ast.Attribute)
            and isinstance(value.value, ast.Name)
            and value.value.id == 'self'
            and current_class):
        return types_state.shared_instance_attr_type(
            current_class, value.attr)
    if isinstance(value, ast.Call):
        return resolver._resolve_call_receiver_type(value, current_class)
    return None
class ReturnTypeProducer:
    def __init__(self, types_state, resolver, return_types):
        self._types = types_state
        self._resolver = resolver
        self._return_types = return_types
    def track(self, node, current_class, current_func, is_direct_method):
        if node.value is None:
            return
        ret_type = _infer_value_type(
            node.value, current_class, self._types, self._resolver)
        if not (ret_type and current_func):
            return
        self._store_return_type(current_func, ret_type)
        self._store_class_key(
            ret_type, current_class, current_func, is_direct_method)
    def _store_return_type(self, key, ret_type) -> None:
        if key not in self._return_types:
            self._return_types[key] = ret_type
        elif self._return_types[key] != ret_type:
            self._return_types[key] = None
    def _store_class_key(self, ret_type, current_class, current_func,
                         is_direct_method) -> None:
        if not (current_class and is_direct_method):
            return
        func_simple = (current_func.split('.')[-1]
                       if '.' in current_func else current_func)
        self._store_return_type(f"{current_class}.{func_simple}", ret_type)
class AssignmentDataflowTracker:
    def __init__(self, types_state, resolver) -> None:
        self._types = types_state
        self._resolver = resolver
    def track(self, node, current_class, at_module_scope):
        self._track_value(node.value, node.targets, current_class,
                          at_module_scope)
    def track_named_expr(self, node, current_class, at_module_scope):
        self._track_value(node.value, [node.target], current_class,
                          at_module_scope)
    def _track_value(self, value, targets, current_class, at_module_scope):
        if isinstance(value, ast.Lambda):
            self._unbind_targets(targets, current_class, at_module_scope)
            self._bind_local_callables(targets, at_module_scope)
            return
        type_name = _infer_value_type(
            value, current_class, self._types, self._resolver)
        if type_name is not None:
            self._bind_targets(targets, type_name, current_class,
                               at_module_scope)
            return
        if isinstance(value, ast.Name):
            self._track_name_alias(value, targets, current_class,
                                   at_module_scope)
            return
        self._unbind_targets(targets, current_class, at_module_scope)
        if (isinstance(value, ast.Call)
                and isinstance(value.func, ast.Name)
                and value.func.id == "getattr"):
            self._bind_local_callables(targets, at_module_scope)
    def _track_name_alias(self, value, targets, current_class,
                          at_module_scope: bool) -> None:
        source_name = value.id
        target_name = (self._types.callable_alias(source_name)
                       if self._types.has_callable_binding(source_name)
                       else source_name)
        for target in targets:
            if isinstance(target, ast.Name):
                resolved = None if target_name == target.id else target_name
                self._types.bind_callable_alias(
                    target.id, resolved, at_module_scope=at_module_scope)
            else:
                self._unbind_targets([target], current_class, at_module_scope)
    def _unbind_targets(self, targets, current_class, at_module_scope):
        for target in targets:
            if isinstance(target, ast.Name):
                self._types.unbind_name(target.id, at_module_scope)
            elif is_self_attr_target(target, current_class):
                self._types.unbind_self_attr(current_class, target.attr)
            elif isinstance(target, (ast.Tuple, ast.List, ast.Starred)):
                self._unbind_targets(_destructured_elements(target),
                                     current_class, at_module_scope)
    def _bind_targets(self, targets, type_name, current_class,
                      at_module_scope):
        for target in targets:
            if isinstance(target, ast.Name):
                self._types.bind_name(target.id, type_name, at_module_scope)
            elif is_self_attr_target(target, current_class):
                self._types.bind_self_attr(
                    current_class, target.attr, type_name)
            elif isinstance(target, (ast.Tuple, ast.List, ast.Starred)):
                self._unbind_targets(_destructured_elements(target),
                                     current_class, at_module_scope)
    def _bind_local_callables(self, targets, at_module_scope):
        for target in targets:
            if isinstance(target, ast.Name):
                self._types.register_local_callable(
                    target.id, at_module_scope=at_module_scope)
class CallCollectorV2(FastDispatchNodeVisitor):
    _REGISTER_METHODS = frozenset({
        "register", "add", "append", "subscribe", "add_listener",
        "add_handler", "on", "include"})
    def __init__(self, filepath, graph, file_symbols, import_aliases,
                 symbol_owner=None, symbol_index=None) -> None:
        self.filepath = filepath
        self.graph = graph
        self.import_aliases = import_aliases
        self._module_name = path_to_dotted_module(filepath)
        self._future_annotations = False
        self._init_scope_state()
        self._wire_collaborators(filepath, graph, file_symbols,
                                 import_aliases, symbol_owner,
                                 symbol_index)
    def _init_scope_state(self) -> None:
        self._lambda_depth = 0
        self._current_func: str | None = None
        self._current_class: str | None = None
        self._class_path: str = ""
        self._in_class_body: bool = False
        self._current_func_is_direct_method: bool = False
        self._current_caller: str = _qualify_module_member(
            self._module_name, _MODULE_SCOPE_NAME)
        self._call_func_nodes: set[int] = set()
    def _wire_collaborators(self, filepath, graph, file_symbols,
                            import_aliases, symbol_owner,
                            symbol_index) -> None:
        _return_types = _graph_type_store(graph, "_return_type_store")
        self._types = TypeFlowState(
            _graph_type_store(graph, "_instance_attr_store"),
            module_name=self._module_name)
        self._refs = _RefEdgeBuilder(
            graph, filepath, self._module_name,
            _file_alias_map(import_aliases, filepath))
        self._dispatch = DispatchTables(
            uses_module_binding=self._types._uses_module_binding,
            binding_frames=self._types.enclosing_binding_frames)
        self._resolver = CalleeResolver(
            graph,
            CalleeFileContext(filepath, import_aliases, file_symbols,
                              symbol_index=symbol_index),
            symbol_owner, _return_types,
            self._types, self._dispatch)
        self._return_producer = ReturnTypeProducer(
            self._types, self._resolver, _return_types)
        self._dataflow = AssignmentDataflowTracker(
            self._types, self._resolver)
    def visit_Module(self, node: ast.Module) -> None:
        self._future_annotations = module_postpones_annotations(node)
        self._types.seed_module_globals(node)
        self.generic_visit(node)
    def _caller_key(self) -> str:
        return self._current_caller
    def _at_module_scope(self) -> bool:
        if self._lambda_depth:
            return False
        _f = self._current_func
        _in_func = (_f is not None and _f != _MODULE_SCOPE_NAME
                    and not _f.endswith(_MODULE_SCOPE_SUFFIX))
        return (not _in_func) and self._current_class is None
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._visit_class_definition_time_exprs(node)
        if self._at_module_scope():
            self._types.clear_module_callable_binding(node.name)
            self._resolver.shadow_name(node.name)
        elif self._current_func is not None:
            self._types.register_local_callable(node.name)
        old = self._current_class
        old_path = self._class_path
        old_in_body = self._in_class_body
        self._dispatch.push_scope()
        self._class_path = (f"{old_path}.{node.name}"
                            if old_path else node.name)
        self._current_class = self._class_path
        self._in_class_body = True
        self._types.push_class_scope(node=node, nested_in_class=old_in_body)
        for _stmt in node.body:
            self.visit(_stmt)
        self._current_class = old
        self._class_path = old_path
        self._in_class_body = old_in_body
        self._types.pop_class_scope()
        self._dispatch.pop_scope()
    def _visit_class_definition_time_exprs(self, node: ast.ClassDef) -> None:
        for dec in node.decorator_list:
            self.visit(dec)
        for base in node.bases:
            self.visit(base)
        for keyword in node.keywords:
            self.visit(keyword.value)
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        at_module = self._at_module_scope()
        self._visit_definition_time_exprs(node)
        if at_module:
            self._types.clear_module_callable_binding(node.name)
            self._resolver.shadow_name(node.name)
        elif self._current_func is not None:
            self._types.register_local_callable(node.name)
        old_func = self._current_func
        old_class = self._current_class
        old_in_body = self._in_class_body
        old_is_direct = self._current_func_is_direct_method
        old_caller = self._current_caller
        self._dispatch.push_scope()
        self._current_func_is_direct_method = (
            self._in_class_body and self._current_class is not None)
        self._types.push_function_scope(
            node, direct_method=self._current_func_is_direct_method)
        if self._in_class_body and self._current_class:
            self._current_func = _qualify_module_member(
                self._module_name, f"{self._current_class}.{node.name}")
        else:
            self._current_func = _qualify_module_member(
                self._module_name, node.name)
        if at_module or self._current_func_is_direct_method:
            self._current_caller = self._current_func
        self._in_class_body = False
        for _stmt in node.body:
            self.visit(_stmt)
        self._current_func = old_func
        self._current_class = old_class
        self._in_class_body = old_in_body
        self._current_func_is_direct_method = old_is_direct
        self._current_caller = old_caller
        self._types.pop_function_scope()
        self._dispatch.pop_scope()
    visit_AsyncFunctionDef = visit_FunctionDef
    def visit_Lambda(self, node: ast.Lambda) -> None:
        for default in node.args.defaults:
            self.visit(default)
        for default in node.args.kw_defaults:
            if default is not None:
                self.visit(default)
        self._dispatch.push_scope()
        self._types.push_function_scope(node)
        self._lambda_depth += 1
        self.visit(node.body)
        self._lambda_depth -= 1
        self._types.pop_function_scope()
        self._dispatch.pop_scope()
    def _visit_definition_time_exprs(self, node) -> None:
        for dec in node.decorator_list:
            self.visit(dec)
        for default in node.args.defaults:
            self.visit(default)
        for default in node.args.kw_defaults:
            if default is not None:
                self.visit(default)
        if not self._future_annotations:
            for annotation in _iter_definition_annotations(node):
                self.visit(annotation)
    def visit_Global(self, node: ast.Global) -> None:
        self._types.declare_globals(node.names)
    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        self._types.declare_nonlocals(node.names)
    def visit_Return(self, node: ast.Return) -> None:
        if self._current_func == self._current_caller:
            self._return_producer.track(
                node, self._current_class, self._current_func,
                self._current_func_is_direct_method)
        self.generic_visit(node)
    def visit_Call(self, node: ast.Call) -> None:
        caller = self._caller_key()
        if isinstance(node.func, ast.Attribute):
            self._call_func_nodes.add(id(node.func))
        self._record_function_ref_args(node, caller)
        if self._try_link_super_call(node, caller):
            return
        callee_name, is_self = self._resolver._resolve_callee(
            node.func, self._current_class, caller)
        callee_name = self._rewrite_cls_construction(node, callee_name)
        self._handle_string_ref_call(node, caller, callee_name)
        if callee_name is None:
            self.generic_visit(node)
            return
        if self._is_unresolved_register_call(node):
            self.generic_visit(node)
            return
        self._emit_resolved_call(node, caller, callee_name, is_self)
    def _try_link_super_call(self, node: ast.Call, caller: str) -> bool:
        if (self._current_class
                and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Call)
                and isinstance(node.func.value.func, ast.Name)
                and node.func.value.func.id == "super"):
            self._refs.link_super_call(node, caller, self._current_class)
            self.generic_visit(node)
            return True
        return False
    def _rewrite_cls_construction(self, node: ast.Call, callee_name):
        if (isinstance(node.func, ast.Name)
                and is_cls_bound_factory(
                    self._types, node.func.id, self._current_class)):
            return self._current_class
        return callee_name
    def _handle_string_ref_call(self, node: ast.Call, caller: str,
                                callee_name) -> None:
        if callee_name not in ("getattr", "setattr", "hasattr"):
            return
        if not self._resolver._is_builtin_name_call(node.func, callee_name):
            return
        _receiver_type = (self._resolver._resolve_receiver_type(
                              node.args[0], self._current_class)
                          if node.args else None)
        self._refs.handle_string_ref(node, caller, callee_name,
                                     _receiver_type)
    def _is_unresolved_register_call(self, node: ast.Call) -> bool:
        return (isinstance(node.func, ast.Attribute)
                and node.func.attr in self._REGISTER_METHODS
                and not self._resolver._receiver_has_project_method(
                    node.func, self._current_class))
    def _emit_resolved_call(self, node: ast.Call, caller: str,
                            callee_name, is_self: bool) -> None:
        if not is_self and "." in callee_name:
            callee_name = self._resolver._resolve_dataflow_callee(
                callee_name, self._current_class,
                receiver_node=(node.func.value
                               if isinstance(node.func, ast.Attribute)
                               else None))
        callee_name, callee_file, is_external = self._resolver._resolve_call_target(
            callee_name, is_self, self._current_class)
        if callee_name is None:
            self.generic_visit(node)
            return
        type_resolution_blocked = self._receiver_type_resolution_blocked(node)
        if self._is_external_dep(callee_name, is_external):
            self.graph.external_deps.add(callee_name)
        self._emit_call_edges(node, caller, callee_name, callee_file,
                              is_external, is_self, type_resolution_blocked)
    def _record_function_ref_args(self, node: ast.Call, caller: str) -> None:
        for arg in node.args:
            self._record_function_ref(arg, caller)
        for keyword in node.keywords:
            self._record_function_ref(keyword.value, caller)
    def _record_function_ref(self, arg, caller: str) -> None:
        if not isinstance(arg, ast.Name):
            return
        callee_name, _is_self = self._resolver._resolve_callee(
            arg, self._current_class, caller)
        if not callee_name or self._resolver._is_tracked_local_callable(callee_name):
            return
        target, _file, is_external = self._resolver._resolve_call_target(
            callee_name, False, self._current_class)
        if is_external or target not in self.graph.functions:
            return
        self.graph.function_references.append(CallEdge(
            caller_file=self.filepath,
            caller_func=caller,
            callee_func=target,
            callee_file=_file or self.graph.functions[target].filepath,
            line=arg.lineno,
            is_external=False,
        ))
        self.graph.callers[target].add(caller)
    def _is_external_dep(self, callee_name: str, is_external: bool) -> bool:
        return (bool(is_external)
                and not is_project_class(
                    self.graph, self._module_name, callee_name)
                and not self._resolver._is_tracked_local_callable(callee_name))
    def _receiver_type_resolution_blocked(self, node: ast.Call) -> bool:
        if not isinstance(node.func, ast.Attribute):
            return False
        receiver = node.func.value
        if isinstance(receiver, ast.Name) and receiver.id not in SELF_CLS_NAMES:
            return (self._types.is_name_type_invalidated(receiver.id)
                    or self._bare_receiver_has_tracked_attr(receiver.id))
        if (self._current_class and isinstance(receiver, ast.Attribute)
                and isinstance(receiver.value, ast.Name)
                and receiver.value.id in SELF_CLS_NAMES):
            return self._types.is_self_attr_type_invalidated(
                self._current_class, receiver.attr)
        return False
    def _bare_receiver_has_tracked_attr(self, name: str) -> bool:
        return (bool(self._current_class)
                and self._types.var_type(name) is None
                and self._types.instance_attr_type(
                    self._current_class, name) is not None)
    def _constructor_binding_blocked(self, node: ast.Call) -> bool:
        if not isinstance(node.func, ast.Name):
            return False
        name = node.func.id
        return (self._types.var_type(name) is None
                and self._types.has_callable_binding(name)
                and self._types.callable_alias(name) is None)
    def _emit_call_edges(self, node: ast.Call, caller: str, callee_name: str,
                         callee_file, is_external: bool, is_self: bool,
                         type_resolution_blocked: bool) -> None:
        if isinstance(node.func, ast.Call):
            self._refs.mark_dyn_resolved(callee_name, node.lineno)
        _add_call_edge(self.graph, self.filepath, node, caller, callee_name,
                       callee_file, is_external, is_self, type_resolution_blocked)
        if not self._constructor_binding_blocked(node):
            _add_constructor_init_edge(
                self.graph, self.filepath, self._module_name,
                callee_name, caller, node)
        self.generic_visit(node)
    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None:
            self.visit(node.value)
            annotation_type = extract_type_name(node.annotation)
            if (annotation_type
                    and annotation_type.rsplit(".", 1)[-1] == "Callable"):
                self._dataflow._track_value(
                    node.value, [node.target], self._current_class,
                    self._at_module_scope())
            else:
                self._bind_annotated_target(node.target, node.annotation)
            self._dispatch.track_dict_literal(
                node, scope=_DispatchScope(
                    self._at_module_scope(), self._types.global_names,
                    self._current_class,
                    self._types.enclosing_binding_frames))
            self._resolver._track_dict_value_calls(
                node.value, self._caller_key(), self._current_class)
        self.visit(node.target)
        if (not self._future_annotations
                and (self._in_class_body or self._current_func is None)):
            self.visit(node.annotation)
    def _bind_annotated_target(self, target, annotation) -> None:
        type_name = extract_type_name(annotation)
        if not type_name:
            return
        if isinstance(target, ast.Name):
            self._types.bind_name(
                target.id, type_name, self._at_module_scope())
        elif is_self_attr_target(target, self._current_class):
            self._types.bind_self_attr(
                self._current_class, target.attr, type_name)
    def visit_Assign(self, node: ast.Assign) -> None:
        self.visit(node.value)
        self._dataflow.track(node, self._current_class,
                             self._at_module_scope())
        scope = _DispatchScope(
            self._at_module_scope(), self._types.global_names,
            self._current_class, self._types.enclosing_binding_frames)
        self._dispatch.track_registry_assignment(node, scope=scope)
        self._dispatch.track_dict_literal(node, scope=scope)
        self._resolver._track_dict_value_calls(
            node.value, self._caller_key(), self._current_class)
        for target in node.targets:
            self.visit(target)
    def visit_NamedExpr(self, node: ast.NamedExpr) -> None:
        self.visit(node.value)
        self._dataflow.track_named_expr(
            node, self._current_class, self._at_module_scope())
        self.visit(node.target)
    def visit_For(self, node: ast.For) -> None:
        self.visit(node.iter)
        self._dataflow._unbind_targets(
            [node.target], self._current_class, self._at_module_scope())
        self.visit(node.target)
        for stmt in (*node.body, *node.orelse):
            self.visit(stmt)
    visit_AsyncFor = visit_For
    def visit_With(self, node: ast.With) -> None:
        for item in node.items:
            self.visit(item.context_expr)
            if item.optional_vars is not None:
                self._dataflow._unbind_targets(
                    [item.optional_vars], self._current_class,
                    self._at_module_scope())
                self.visit(item.optional_vars)
        for stmt in node.body:
            self.visit(stmt)
    visit_AsyncWith = visit_With
    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        if node.type is not None:
            self.visit(node.type)
        if isinstance(node.name, str):
            self._types.unbind_name(node.name, self._at_module_scope())
        for stmt in node.body:
            self.visit(stmt)
    def visit_Import(self, node: ast.Import) -> None:
        at_module_scope = self._at_module_scope()
        for alias in node.names:
            name = alias.asname or alias.name.split(".", 1)[0]
            target = alias.name if alias.asname else name
            self._types.bind_callable_alias(
                name, target, at_module_scope=at_module_scope)
    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        at_module_scope = self._at_module_scope()
        module = relative_import_module(
            node, self._module_name, self.filepath)
        for alias in node.names:
            if alias.name != "*":
                name = alias.asname or alias.name
                target = f"{module}.{alias.name}" if module else alias.name
                self._types.bind_callable_alias(
                    name, target, at_module_scope=at_module_scope)
    def visit_Delete(self, node: ast.Delete) -> None:
        self._dataflow._unbind_targets(
            node.targets, self._current_class, self._at_module_scope())
        self.generic_visit(node)
    def visit_Attribute(self, node: ast.Attribute) -> None:
        if isinstance(node.ctx, ast.Load) and id(node) not in self._call_func_nodes:
            self._emit_attribute_read(node)
        self.generic_visit(node)
    def _emit_attribute_read(self, node: ast.Attribute) -> None:
        caller = self._caller_key()
        class_name, is_self = self._attribute_read_context(node)
        self._refs.handle_attribute_read(node, caller, class_name, is_self)
    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        if isinstance(node.target, ast.Attribute):
            self._emit_attribute_read(node.target)
        self.generic_visit(node)
    def _attribute_read_context(self, node: ast.Attribute):
        if isinstance(node.value, ast.Name):
            name = node.value.id
            if name in SELF_CLS_NAMES and self._current_class:
                return self._current_class, True
            return self._types.var_type(name), False
        return self._self_attr_receiver_type(node.value), False
    def _self_attr_receiver_type(self, value):
        if not is_self_attr_target(value, self._current_class):
            return None
        return self._types.instance_attr_type(self._current_class, value.attr)
class _ClassSpanIndex:
    def __init__(self) -> None:
        self._spans: list[tuple[int, int, str]] = []
    def record(self, node) -> None:
        self._spans.append(
            (node.lineno, node.end_lineno or node.lineno, node.name))
    def owner_at(self, lineno: int) -> str | None:
        chain = sorted(
            (span for span in self._spans
             if span[0] <= lineno <= span[1]),
            key=lambda span: (span[0], -(span[1] - span[0]), span[1]),
        )
        return ".".join(name for _start, _end, name in chain) or None
_REGISTRATION_ARG_INDEX = {
    "atexit.register": 0,
    "signal.signal": 1,
    "sys.settrace": 0,
    "sys.setprofile": 0,
}
_REGISTRATION_ARG_KEYWORD = {
    "signal.signal": "handler",
}
_REGISTRATION_MODULES = frozenset(
    name.split(".", 1)[0] for name in _REGISTRATION_ARG_INDEX)
def _registration_arg_node(node, entry: str, arg_index: int):
    if len(node.args) > arg_index:
        return node.args[arg_index]
    keyword = _REGISTRATION_ARG_KEYWORD.get(entry)
    if keyword is None:
        return None
    return next(
        (kw.value for kw in node.keywords if kw.arg == keyword), None)
class _RuntimeImportVisitor(ast.NodeVisitor):
    def visit_Module(self, node: ast.Module) -> None:
        self._parents = parent_map(node)
        self._imports = scope_import_tables(node)
        self._lexical = collect_lexical_scope_table(node)
        self.generic_visit(node)
    def _scope_for(self, node: ast.AST):
        scope = node
        while scope is not None and scope not in self._lexical.bound:
            scope = self._parents.get(scope)
        return scope
    def _is_shadowed(self, node: ast.AST, name: str) -> bool:
        scope = self._scope_for(node)
        return bool(scope is not None and scope_shadows_import(
            self._lexical, scope, name))
    def _binding_scope(self, node: ast.AST, name: str):
        return _lexical_binding_scope(
            self._lexical, self._scope_for(node), name)
    def _visible_reference_name(
            self, node: ast.AST, allow_module: bool = False) -> str | None:
        if isinstance(node, ast.Attribute):
            base = self._visible_reference_name(
                node.value, allow_module=True)
            return f"{base}.{node.attr}" if base else None
        if not isinstance(node, ast.Name):
            return None
        name = node.id
        scope = self._scope_for(node)
        direct = scope
        while scope is not None:
            if not (isinstance(scope, ast.ClassDef) and scope is not direct):
                if name in self._lexical.shadow_bound.get(scope, ()):
                    if isinstance(scope, (ast.Module, ast.ClassDef)):
                        return name
                    return None
                record = self._imports.get(scope, {}).get(name)
                if record is not None:
                    if record[0] == "import":
                        return record[1] if allow_module else None
                    if record[0] != "from" or not record[1]:
                        return None
                    return f"{record[1]}.{record[2]}"
            scope = self._lexical.parent.get(scope)
        return name
    def _import_record(self, node: ast.AST, name: str):
        if self._is_shadowed(node, name):
            return None
        return resolve_import_binding(self._imports, self._parents, node, name)
class DynamicRegistrationVisitor(_RuntimeImportVisitor):
    def __init__(self, filepath, module_name, call_graph, file_symbols) -> None:
        self.filepath = filepath
        self.module_name = module_name
        self.call_graph = call_graph
        self.file_symbols = file_symbols
        self._class_spans = _ClassSpanIndex()
    def visit_ClassDef(self, node) -> None:
        self._class_spans.record(node)
        self.generic_visit(node)
    def _canonical_registration_name(self, node):
        if (isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name)):
            record = self._import_record(node, node.value.id)
            if (record is not None and record[0] == "import"
                    and record[1] in _REGISTRATION_MODULES):
                return f"{record[1]}.{node.attr}"
        if isinstance(node, ast.Name):
            record = self._import_record(node, node.id)
            if record is not None and record[0] == "from":
                canonical = (f"{record[1]}.{record[2]}"
                             if record[1] else record[2])
                if canonical in _REGISTRATION_ARG_INDEX:
                    return canonical
        return None
    def _resolve_from_file_symbols(self, callee_name):
        functions = self.call_graph.functions
        hits: set[str] = set()
        simple = callee_name.rsplit(".", 1)[-1]
        for fp, file_syms in self.file_symbols.items():
            if not isinstance(file_syms, dict):
                continue
            module = path_to_dotted_module(fp)
            hit = symbol_hit(callee_name, simple, file_syms, module)
            if hit is None:
                continue
            qualified = _qualify_module_member(module, hit)
            if qualified not in functions:
                continue
            hits.add(qualified)
        return hits.pop() if len(hits) == 1 else None
    def _add_synthetic_edge(self, callee_name, line):
        callee_fqn = self._resolve_callee_fqn(callee_name)
        if callee_fqn is None:
            return
        append_synthetic_edge(
            self.call_graph, caller_func="<dynamic_registration>",
            caller_file=self.filepath, callee_fqn=callee_fqn, line=line,
            caller_record=f"<dynamic_registration>:{self.filepath}")
    def _resolve_callee_fqn(self, callee_name: str):
        for candidate in (callee_name,
                          _qualify_module_member(
                              self.module_name, callee_name)):
            if candidate in self.call_graph.functions:
                return candidate
        return self._resolve_from_file_symbols(callee_name)
    def _add_edge_for_name(self, name: str, lineno: int,
                           query_node: ast.AST | None = None) -> None:
        if not name.startswith(_SELF_ATTR_PREFIXES):
            if query_node is not None:
                name = self._visible_reference_name(query_node)
                if name is None:
                    return
            self._add_synthetic_edge(name, lineno)
            return
        sym_fqn = self._resolve_self_method_fqn(
            name.split(".", 1)[1], self._class_spans.owner_at(lineno))
        if sym_fqn is not None:
            self._add_synthetic_edge(sym_fqn, lineno)
    def _resolve_self_method_fqn(self, method_name: str,
                                 owner_cls: str | None = None):
        own_syms = self.file_symbols.get(self.filepath)
        if owner_cls:
            if isinstance(own_syms, dict):
                own_key = f"{owner_cls}.{method_name}"
                if own_key in own_syms:
                    return own_key
            return resolve_inherited_method(
                self.call_graph, self.module_name, method_name, owner_cls)
        suffix = f".{method_name}"
        own_hits = self._suffix_hits(own_syms, suffix)
        if len(own_hits) == 1:
            return own_hits.pop()
        if len(own_hits) > 1:
            return None
        other_hits: set[str] = set()
        for fp, file_syms in self.file_symbols.items():
            if fp == self.filepath:
                continue
            other_hits |= self._suffix_hits(file_syms, suffix)
        if len(other_hits) != 1:
            return None
        return other_hits.pop()
    @staticmethod
    def _suffix_hits(file_syms, suffix: str) -> set[str]:
        if not isinstance(file_syms, dict):
            return set()
        return {
            sym_fqn for sym_fqn in file_syms
            if isinstance(sym_fqn, str) and sym_fqn.endswith(suffix)
        }
    def visit_Call(self, node) -> None:
        full = self._canonical_registration_name(node.func)
        if full is not None:
            self._handle_registration_target(full, node)
        self.generic_visit(node)
    def _handle_registration_target(self, full: str, node) -> None:
        arg_index = _REGISTRATION_ARG_INDEX.get(full)
        if arg_index is None:
            return
        arg_node = _registration_arg_node(node, full, arg_index)
        if arg_node is None:
            return
        name = dotted_name_of(arg_node)
        if name:
            self._add_edge_for_name(name, node.lineno, arg_node)
    def visit_Assign(self, node) -> None:
        for target in node.targets:
            self._handle_excepthook_target(target, node.value, node.lineno)
        self.generic_visit(node)
    def visit_AnnAssign(self, node) -> None:
        if node.value is not None:
            self._handle_excepthook_target(
                node.target, node.value, node.lineno)
        self.generic_visit(node)
    def _handle_excepthook_target(self, target, value, lineno: int) -> None:
        if self._canonical_registration_name(target) == "sys.excepthook":
            name = dotted_name_of(value)
            if name:
                self._add_edge_for_name(name, lineno, value)
_VALUE_ITER_METHODS = frozenset({"values", "items"})
def _trace_dispatch_iter_name(iter_node):
    if isinstance(iter_node, ast.Name):
        return iter_node.id, False
    if not isinstance(iter_node, ast.Call):
        return None
    if (isinstance(iter_node.func, ast.Attribute)
            and isinstance(iter_node.func.value, ast.Name)
            and iter_node.func.attr in _VALUE_ITER_METHODS):
        value = iter_node.func.value
        if value.id in SELF_CLS_NAMES:
            return None
        return value.id, True
    return None
class _DispatchRef(NamedTuple):
    func_name: str
    is_self_ref: bool
    owner_cls: str | None
    node: ast.AST | None = None
    key: _DispatchKeyT | None = None
class _DispatchContainer(NamedTuple):
    kind: str
    refs: list[_DispatchRef]
class DispatchListVisitor(_RuntimeImportVisitor):
    def __init__(self, filepath, module_name, call_graph,
                 import_aliases=None) -> None:
        self.filepath = filepath
        self.module_name = module_name
        self.call_graph = call_graph
        self.import_aliases = import_aliases or {}
        self._emitted_dispatch: set[tuple[str, str]] = set()
        self._pkg_root = _graph_pkg_root(call_graph)
        self.dispatch_lists: dict[str, _DispatchContainer] = {}
        self._scope_lists: dict[
            tuple[int, int], dict[str, _DispatchContainer]] = {}
        self._scope_spans: list[tuple[int, int, str]] = []
        self._scope_keys: dict[ast.AST, tuple[int, int]] = {}
        self._class_spans = _ClassSpanIndex()
    def visit_ClassDef(self, node) -> None:
        self._class_spans.record(node)
        self._record_scope(node, "class")
        self.generic_visit(node)
    def visit_FunctionDef(self, node) -> None:
        self._record_scope(node, "function")
        self.generic_visit(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    def _record_scope(self, node, kind: str) -> None:
        start, end = node.lineno, node.end_lineno or node.lineno
        self._scope_spans.append((start, end, kind))
        self._scope_keys[node] = (start, end)
    def _scope_chain(self, lineno: int) -> list[tuple[int, int, str]]:
        hits = [span for span in self._scope_spans
                if span[0] <= lineno <= span[1]]
        return sorted(hits)
    def _bucket_for_scope(self, scope) -> dict[str, _DispatchContainer]:
        if scope is self._lexical.tree:
            return self.dispatch_lists
        key = self._scope_keys.get(scope)
        if key is None:
            return self.dispatch_lists
        return self._scope_lists.setdefault(key, {})
    def _dispatch_container(self, name: str,
                            lineno: int) -> _DispatchContainer | None:
        chain = self._scope_chain(lineno)
        inside_class_body = bool(chain) and chain[-1][2] == "class"
        for start, end, kind in reversed(chain):
            if kind == "class" and not inside_class_body:
                continue
            bucket = self._scope_lists.get((start, end))
            if bucket is not None and name in bucket:
                return bucket[name]
            inside_class_body = False
        return self.dispatch_lists.get(name)
    def visit_Assign(self, node) -> None:
        for target in node.targets:
            self._register_container_target(target, node.value, node.lineno)
        self.generic_visit(node)
    def visit_AnnAssign(self, node) -> None:
        if node.value is not None:
            self._register_container_target(
                node.target, node.value, node.lineno)
        self.generic_visit(node)
    def _register_container_target(self, target, value, lineno: int) -> None:
        if isinstance(target, ast.Subscript):
            self._update_dict_target(target, value, lineno)
            return
        if not isinstance(target, ast.Name):
            return
        bucket = self._bucket_for_scope(
            self._binding_scope(target, target.id))
        if not isinstance(value, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            if self._dispatch_container(target.id, lineno) is not None:
                bucket[target.id] = _DispatchContainer("opaque", [])
            return
        owner_cls = self._class_spans.owner_at(lineno)
        bucket[target.id] = _DispatchContainer(
            kind="dict" if isinstance(value, ast.Dict) else "sequence",
            refs=self._container_refs(value, owner_cls),
        )
    def _update_dict_target(self, target, value, lineno: int) -> None:
        if not isinstance(target.value, ast.Name):
            return
        key = _dispatch_key(target.slice)
        if key is None:
            return
        name = target.value.id
        container = self._dispatch_container(name, lineno)
        if container is None or container.kind != "dict":
            return
        bucket = self._bucket_for_scope(
            self._binding_scope(target.value, name))
        if bucket.get(name) is not container:
            return
        refs = [ref for ref in container.refs if ref.key != key]
        owner_cls = self._class_spans.owner_at(lineno)
        refs.extend(self._container_refs(value, owner_cls, key=key))
        bucket[name] = _DispatchContainer("dict", refs)
    def _container_refs(self, value, owner_cls, key=None) -> list[_DispatchRef]:
        return [
            _DispatchRef(
                func_name, is_self_ref,
                owner_cls if is_self_ref else None, ref_node, ref_key)
            for func_name, is_self_ref, ref_node, ref_key
            in self._value_refs(value, key=key)
        ]
    def _value_refs(self, node, key=None) -> list:
        if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            return self._refs_from_elements(node.elts, key=key)
        if isinstance(node, ast.Dict):
            return [
                ref for key_node, val in zip(
                    node.keys, node.values, strict=True)
                for ref in self._value_refs(
                    val, key=_dispatch_key(key_node))
            ]
        ref = self._resolve_self_method(node)
        return [(*ref, key)] if ref else []
    def _refs_from_elements(self, elements, key=None) -> list:
        return [
            ref for elt in elements
            for ref in self._value_refs(elt, key=key)
        ]
    def _resolve_self_method(self, node):
        if (isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name)
                and node.value.id in SELF_CLS_NAMES):
            return node.attr, True, node
        if isinstance(node, ast.Name):
            return node.id, False, node
        if isinstance(node, ast.Attribute):
            func_name = dotted_name_of(node)
            if func_name:
                return func_name, False, node
        return None
    def _resolve_fqn(self, func_name: str, owner_cls: str | None = None) -> str | None:
        if owner_cls:
            candidate = _qualify_module_member(
                self.module_name, f"{owner_cls}.{func_name}")
            if candidate in self.call_graph.functions:
                return candidate
            return resolve_inherited_method(
                self.call_graph, self.module_name, func_name, owner_cls)
        candidate = strip_pkg_root(func_name, self._pkg_root)
        if candidate in self.call_graph.functions:
            return candidate
        candidate = _qualify_module_member(self.module_name, func_name)
        if candidate in self.call_graph.functions:
            return candidate
        imported = strip_pkg_root(
            self.import_aliases.get(func_name, ''), self._pkg_root)
        if imported in self.call_graph.functions:
            return imported
        return None
    def visit_For(self, node):
        iter_spec = _trace_dispatch_iter_name(node.iter)
        if iter_spec:
            name, produces_values = iter_spec
            container = self._dispatch_container(name, node.lineno)
            if (container is not None
                    and (produces_values or container.kind != "dict")):
                for ref in container.refs:
                    self._add_dispatch_edge(
                        "<dispatch_list>", ref, node.lineno)
        self.generic_visit(node)
    visit_AsyncFor = visit_For
    def visit_Subscript(self, node):
        if (isinstance(node.ctx, ast.Load)
                and isinstance(node.value, ast.Name)):
            container = self._dispatch_container(
                node.value.id, node.lineno)
            if container is not None:
                refs = container.refs
                key = (_dispatch_key(node.slice)
                       if container.kind == "dict"
                       and isinstance(node.slice, ast.Constant) else None)
                if key is not None:
                    refs = [ref for ref in refs if ref.key == key]
                for ref in refs:
                    self._add_dispatch_edge(
                        "<dispatch_subscript>", ref, node.lineno)
        self.generic_visit(node)
    def _add_dispatch_edge(self, caller_key: str, ref: _DispatchRef,
                           line: int):
        func_name = ref.func_name
        if not ref.is_self_ref and ref.node is not None:
            func_name = self._visible_reference_name(ref.node)
            if func_name is None:
                return
        owner_cls = ref.owner_cls
        if (owner_cls is None and isinstance(ref.node, ast.Name)
                and isinstance(self._scope_for(ref.node), ast.ClassDef)):
            class_owner = self._class_spans.owner_at(ref.node.lineno)
            if (class_owner and func_name in torn_list(
                    self.call_graph.class_methods.get(class_owner))):
                owner_cls = class_owner
        fqn = self._resolve_fqn(func_name, owner_cls)
        if not fqn:
            return
        edge_key = (fqn, caller_key)
        if edge_key in self._emitted_dispatch:
            return
        self._emitted_dispatch.add(edge_key)
        append_synthetic_edge(
            self.call_graph, caller_func=caller_key,
            caller_file=self.filepath, callee_fqn=fqn, line=line,
            is_self_call=ref.is_self_ref,
            caller_record=f"{caller_key}:{self.filepath}")
class DynamicImportVisitor(_RuntimeImportVisitor):
    def __init__(self, project_root, rel_path, graph):
        self.project_root = project_root
        self.rel_path = rel_path
        self.graph = graph
        self._pkg_prefix = pkg_root_name(project_root)
    def visit_Call(self, node: ast.Call) -> None:
        self._collect_dynamic_import(node)
        self.generic_visit(node)
    def _collect_dynamic_import(self, node: ast.Call) -> None:
        kind = self._dynamic_import_kind(node.func)
        if kind is None:
            return
        module_name = _constant_str_arg(node)
        if module_name is None:
            return
        if kind == "__import__":
            level = self._dunder_import_level(node)
            if level is None or module_name.startswith("."):
                return
            if level:
                self._register_relative_import(module_name, level)
                return
        elif module_name.startswith("."):
            if not self._relative_anchor_uses_current_package(node):
                return
            level = len(module_name) - len(module_name.lstrip("."))
            self._register_relative_import(module_name[level:], level)
            return
        self._register_dynamic_imports(
            self._dynamic_import_candidates(module_name))
    def _dynamic_import_kind(self, func: ast.expr) -> str | None:
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)):
            record = self._import_record(func, func.value.id)
            if func.attr == "import_module":
                return ("importlib"
                        if record == ("import", "importlib") else None)
            if (func.attr == "__import__"
                    and record == ("import", "builtins")):
                return "__import__"
        if not isinstance(func, ast.Name):
            return None
        record = self._import_record(func, func.id)
        if record == ("from", "builtins", "__import__"):
            return "__import__"
        if func.id == "__import__":
            if self._is_shadowed(func, func.id) or record is not None:
                return None
            return "__import__"
        if record == ("from", "importlib", "import_module"):
            return "importlib"
        return None
    @staticmethod
    def _dunder_import_level(node: ast.Call) -> int | None:
        level_node = node.args[4] if len(node.args) > 4 else next(
            (kw.value for kw in node.keywords if kw.arg == "level"), None)
        if level_node is None:
            return 0
        if (not isinstance(level_node, ast.Constant)
                or type(level_node.value) is not int
                or level_node.value < 0):
            return None
        return level_node.value
    def _relative_anchor_uses_current_package(self, node: ast.Call) -> bool:
        anchor = node.args[1] if len(node.args) > 1 else next(
            (kw.value for kw in node.keywords if kw.arg == "package"), None)
        if not isinstance(anchor, ast.Name) or self._is_shadowed(
                anchor, anchor.id):
            return False
        return (anchor.id == "__package__"
                or (anchor.id == "__name__"
                    and os.path.basename(self.rel_path).lower()
                    == "__init__.py"))
    def _dynamic_import_candidates(self, module_name: str) -> list:
        parts = module_name.split(".")
        if not all(part.isidentifier() for part in parts):
            return []
        candidates = [module_name]
        head = parts[0]
        if len(parts) > 1:
            candidates.append(head)
            if head == self._pkg_prefix:
                candidates.append(module_name.split(".", 1)[1])
        return candidates
    def _register_dynamic_imports(self, candidates: list) -> None:
        for mod in candidates:
            mod_rel = mod.replace(".", "/")
            for suffix in (".py", "/__init__.py"):
                self._register_dynamic_import_path(os.path.join(
                    self.project_root, mod_rel + suffix))
    def _register_relative_import(self, module_name: str, level: int) -> None:
        parts = module_name.split(".") if module_name else []
        if not all(part.isidentifier() for part in parts):
            return
        source_path = os.path.join(self.project_root, self.rel_path)
        base = relative_import_base(source_path, level, self.project_root)
        if base is None:
            return
        target_base = os.path.join(str(base), *parts)
        for target in (target_base + ".py",
                       os.path.join(target_base, "__init__.py")):
            self._register_dynamic_import_path(target)
    def _register_dynamic_import_path(self, path: str) -> None:
        if not os.path.isfile(path):
            return
        target = os.path.relpath(path, self.project_root).replace("\\", "/")
        self.graph.dynamic_imports[target].add(self.rel_path)
_REGISTRATION_VERBS = frozenset({
    "register", "subscribe", "add", "append", "install",
    "hook", "connect", "bind",
})
def _is_registration_call(func_node) -> bool:
    if isinstance(func_node, ast.Name):
        func_name = func_node.id
    elif isinstance(func_node, ast.Attribute):
        func_name = func_node.attr
    else:
        return False
    return any(seg in _REGISTRATION_VERBS
               for seg in split_identifier(func_name))
def _is_defined_name(node, defined_names) -> bool:
    return isinstance(node, ast.Name) and node.id in defined_names
class _AssignmentChainVisitor(_RuntimeImportVisitor):
    def __init__(self, call_graph, defined_names, rel_path, edge_keys):
        self.call_graph = call_graph
        self.defined_names = defined_names
        self.rel_path = rel_path
        self.edge_keys = edge_keys
    def visit_Assign(self, node: ast.Assign) -> None:
        self._track_assigned_value(node.value, node.lineno)
        self.generic_visit(node)
    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None:
            self._track_assigned_value(node.value, node.lineno)
        self.generic_visit(node)
    def _track_assigned_value(self, value, lineno: int) -> None:
        if isinstance(value, ast.Name):
            self._edge_for_defined(value, lineno, 'assignment')
        elif isinstance(value, ast.Dict):
            for val in value.values:
                self._edge_for_defined(val, lineno, 'dict_value')
    def visit_Call(self, node: ast.Call) -> None:
        if _is_registration_call(node.func):
            for arg in node.args:
                self._edge_for_defined(arg, node.lineno, 'callback_registration')
            for kw in node.keywords:
                self._edge_for_defined(kw.value, node.lineno, 'kwarg_registration')
        self.generic_visit(node)
    def _edge_for_defined(self, node, line: int, edge_type: str) -> None:
        if not isinstance(node, ast.Name):
            return
        visible = self._visible_reference_name(node)
        if visible is None:
            return
        if visible == node.id:
            if not _is_defined_name(node, self.defined_names):
                return
            fqn = self.defined_names.get(node.id)
        else:
            fqn = visible if visible in self.call_graph.functions else None
        self._add_synthetic_edge(fqn, line, edge_type)
    def _collect_container_elements(self, node, edge_type: str) -> None:
        for elt in node.elts:
            self._edge_for_defined(elt, node.lineno, edge_type)
        self.generic_visit(node)
    def visit_List(self, node: ast.List) -> None:
        self._collect_container_elements(node, 'list_element')
    def visit_Tuple(self, node: ast.Tuple) -> None:
        self._collect_container_elements(node, 'tuple_element')
    def visit_Set(self, node: ast.Set) -> None:
        self._collect_container_elements(node, 'set_element')
    def _add_synthetic_edge(self, fqn, line, edge_type):
        if not fqn:
            return
        caller_key = f"<assignment_chain:{edge_type}>"
        if (fqn, caller_key) in self.edge_keys:
            return
        self.edge_keys.add((fqn, caller_key))
        append_synthetic_edge(
            self.call_graph, caller_func=caller_key,
            caller_file=self.rel_path, callee_fqn=fqn, line=line,
            caller_record=f"{caller_key}:{self.rel_path}")
def track_assignment_chains(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    defined_name_index = assignment_name_index(graph, include_methods=False)
    if not defined_name_index:
        return
    _synthetic_edge_keys = {
        (e.callee_func, e.caller_func)
        for e in graph.calls
        if isinstance(e.caller_func, str)
        and e.caller_func.startswith('<assignment_chain:')
    }
    own_map, prefix_map, unique_names = build_assignment_scope_index(
        defined_name_index)
    for filepath in builder.collect_build_scope_files():
        _source, tree = builder.get_source_and_ast(filepath)
        if tree is None:
            continue
        rel_path = os.path.relpath(filepath, builder.project_root).replace("\\", "/")
        module_name = path_to_dotted_module(rel_path)
        defined_short_names = ScopedNameResolver(
            own_map.get(module_name), prefix_map.get(module_name),
            unique_names)
        visitor = _AssignmentChainVisitor(
            graph, defined_short_names, rel_path, _synthetic_edge_keys)
        walk_visitors_once(tree, [visitor])
class ImportAliasCollector(ast.NodeVisitor):
    def __init__(self, filepath: str, aliases: dict[str, dict[str, str]],
                 plain_modules: dict[str, dict[str, set[str]]]
                 | None = None) -> None:
        self.filepath = filepath
        self.aliases = aliases
        self.plain_modules = plain_modules
    def visit_Module(self, node: ast.Module) -> None:
        for stmt in iter_module_scope_nodes(node, descend_classes=False):
            if isinstance(stmt, ast.Import):
                self._register_import(stmt)
            elif isinstance(stmt, ast.ImportFrom):
                self._register_import_from(stmt)
    def _register_import(self, node: ast.Import) -> None:
        for alias in node.names:
            if alias.asname:
                self.aliases.setdefault(self.filepath, {})[
                    alias.asname] = alias.name
                continue
            head = alias.name.split(".", 1)[0]
            self.aliases.setdefault(self.filepath, {})[head] = head
            if self.plain_modules is not None:
                self.plain_modules.setdefault(self.filepath, {}).setdefault(
                    head, set()).add(alias.name)
    def _register_import_from(self, node: ast.ImportFrom) -> None:
        module = relative_import_module(
            node, path_to_dotted_module(self.filepath), self.filepath)
        for alias in node.names:
            if alias.name == "*":
                continue
            name = alias.asname or alias.name
            self.aliases.setdefault(self.filepath, {})[name] = (
                module + "." + alias.name if module else alias.name)
def package_name_of(module_name: str, filepath: str) -> str:
    if os.path.basename(filepath).lower() == "__init__.py":
        return "" if module_name == "__init__" else module_name
    return module_name.rsplit(".", 1)[0] if "." in module_name else ""
def relative_import_module(node: ast.ImportFrom, module_name: str,
                           filepath: str) -> str:
    module = node.module or ""
    if node.level <= 0:
        return module
    pkg = package_name_of(module_name, filepath)
    ascend = node.level - 1
    if not ascend:
        base = pkg
    elif pkg.count(".") + 1 <= ascend:
        return ""
    else:
        base = pkg.rsplit(".", ascend)[0]
    if module and base:
        return f"{base}.{module}"
    return module or base
def _return_type_preview_graph(graph):
    preview = copy.copy(graph)
    preview.calls = []
    preview.callers = defaultdict(set)
    preview.external_deps = set()
    preview.function_references = []
    return preview
def _prescan_return_types(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    if getattr(graph, "_return_type_prescan_complete", False):
        return
    return_types = _graph_type_store(graph, "_return_type_store")
    instance_attrs = _graph_type_store(graph, "_instance_attr_store")
    scanned = []
    for filepath in builder.collect_build_scope_files():
        _source, tree = builder.get_source_and_ast(filepath)
        if tree is None:
            continue
        rel_path = os.path.relpath(
            filepath, builder.project_root).replace("\\", "/")
        ImportAliasCollector(
            rel_path, builder._import_aliases, builder._plain_imports
        ).visit(tree)
        scanned.append((rel_path, tree))
    max_passes = max(1, len(graph.functions) + 1)
    for _ in range(max_passes):
        before = (dict(return_types), dict(instance_attrs))
        preview = _return_type_preview_graph(graph)
        for rel_path, tree in scanned:
            CallCollectorV2(
                filepath=rel_path, graph=preview,
                file_symbols=builder._file_symbols,
                import_aliases=builder._import_aliases,
                symbol_owner=builder._symbol_owner_index,
                symbol_index=builder.symbol_lookup_index(),
            ).visit(tree)
        after = (dict(return_types), dict(instance_attrs))
        if after == before:
            break
    graph._return_type_prescan_complete = True
def _dynamic_scan_target(builder: CallGraphBuilderProtocol,
                         filepath: str) -> tuple:
    _source, tree = builder.get_source_and_ast(filepath)
    if tree is None:
        return None, "", ""
    rel_path = os.path.relpath(
        filepath, builder.project_root).replace("\\", "/")
    return tree, rel_path, path_to_dotted_module(rel_path)
def collect_dynamic_patterns(builder: CallGraphBuilderProtocol,
                             filepath: str) -> None:
    _prescan_return_types(builder)
    tree, rel_path, module_name = _dynamic_scan_target(builder, filepath)
    if tree is None:
        return
    imp_collector = ImportAliasCollector(
        rel_path, builder._import_aliases, builder._plain_imports)
    walk_visitors_once(tree, [
        DynamicRegistrationVisitor(
            filepath=rel_path, module_name=module_name,
            call_graph=builder.graph, file_symbols=builder._file_symbols,
        ),
        DispatchListVisitor(
            filepath=rel_path, module_name=module_name,
            call_graph=builder.graph,
            import_aliases=builder._import_aliases.get(rel_path, {}),
        ),
        DynamicImportVisitor(builder.project_root, rel_path, builder.graph),
        imp_collector,
    ])
    visitor = CallCollectorV2(
        filepath=rel_path, graph=builder.graph,
        file_symbols=builder._file_symbols,
        import_aliases=builder._import_aliases,
        symbol_owner=builder._symbol_owner_index,
        symbol_index=builder.symbol_lookup_index(),
    )
    visitor.visit(tree)

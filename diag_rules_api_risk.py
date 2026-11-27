from __future__ import annotations

import ast
import logging
import threading
import weakref
from collections.abc import Callable
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_bindings import (
    _definition_scope_keys,
    build_scope_index,
    collect_shadow_bindings,
)
from jwsgj.diag_shared_ast_nodes import (
    build_parent_map,
    collect_param_names,
    dotted_name,
    iter_class_scope_methods,
    iter_def_site_nodes,
    iter_own_nodes,
    node_position,
)
from jwsgj.diag_types_defs import finding_scan_exempt
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "check_DP01",
    "check_DP02",
    "check_DP03",
    "check_DP04",
    "check_DP05",
    "check_DP06",
    "check_DP07",
    "check_DP08",
    "check_DP09",
    "check_DP10",
    "check_DP11",
    "check_DP12",
    "check_DP13",
    "check_DP24",
    "check_DP32",
    "check_DP33",
    "check_DP34",
    "check_DP36",
    "check_DP37",
    "check_DP38",
    "check_DP39",
    "check_DP40",
    "check_DP41",
    "check_DP42",
    "check_DP43",
    "check_DP44",
    "check_DP45",
    "check_DP46",
    "check_DP47",
    "check_DP48",
    "check_DP49",
    "check_DP50",
    "check_DP51",
    "check_DP52",
    "check_DP53",
    "dp_issue",
]
_log = logging.getLogger(__name__)
_log.info("diag_rules_api_risk API 风险规则域已加载: %d 项导出", len(__all__))
def dp_issue(rule_id: str, severity: str, line: int, title: str,
             description: str, suggestion: str) -> dict[str, Any]:
    return {
        "rule_id": rule_id,
        "severity": severity,
        "line": line,
        "title": title,
        "description": description,
        "suggestion": suggestion,
        "category": "deprecated-api",
    }
def _api_rule(
    impl: Callable[[ast.AST], list[dict[str, Any]]],
) -> Callable[..., list[dict[str, Any]]]:
    def detector(tree: ast.AST | None = None, source_lines: Any = None,
                 filepath: str = "") -> list[dict[str, Any]]:
        _ = source_lines
        if tree is None or finding_scan_exempt(filepath):
            return []
        return impl(tree)
    detector.__name__ = impl.__name__
    detector.__qualname__ = impl.__name__
    detector.__doc__ = impl.__doc__
    detector.__module__ = impl.__module__
    return detector
def _module_root_imported(tree: ast.AST, module: str) -> bool:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            if any(_module_chain_matches(alias.name, module)
                   for alias in node.names):
                return True
        elif (isinstance(node, ast.ImportFrom) and not node.level
              and _module_chain_matches(node.module or "", module)):
            return True
    return False
def _module_chain_matches(candidate: str, module: str) -> bool:
    return candidate == module or candidate.startswith(module + ".")
def _nested_scope_name(scope: str, name: str) -> str:
    return f"{scope}.{name}" if scope else name
def _anonymous_scope_name(scope: str, kind: str, node: ast.AST) -> str:
    name = (f"<{kind}@{getattr(node, 'lineno', -1)}:"
            f"{getattr(node, 'col_offset', -1)}>")
    return _nested_scope_name(scope, name)
_COMPREHENSION_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                        ast.GeneratorExp)
_BINDING_EVALUATION_ATTRS = {
    ast.Assign: "value",
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
def _build_scope_names(tree: ast.AST) -> tuple[dict[int, str], set[str]]:
    names: dict[int, str] = {}
    delayed: set[str] = set()
    scope_keys = _definition_scope_keys(tree)
    stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while stack:
        node, scope = stack.pop()
        names[id(node)] = scope
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            inner = scope_keys[id(node)]
            delayed.add(inner)
            body_ids = {id(stmt) for stmt in node.body}
            for child in ast.iter_child_nodes(node):
                stack.append((child, inner if id(child) in body_ids else scope))
            continue
        if isinstance(node, ast.Lambda):
            inner = _anonymous_scope_name(scope, "lambda", node)
            delayed.add(inner)
            for child in ast.iter_child_nodes(node):
                stack.append((child, inner if child is node.body else scope))
            continue
        if isinstance(node, _COMPREHENSION_NODES):
            inner = _anonymous_scope_name(scope, "comprehension", node)
            if isinstance(node, ast.GeneratorExp):
                delayed.add(inner)
            generators = node.generators
            if generators:
                stack.append((generators[0].iter, scope))
            for index, generator in enumerate(generators):
                names[id(generator)] = inner
                if index:
                    stack.append((generator.iter, inner))
                stack.append((generator.target, inner))
                for condition in generator.ifs:
                    stack.append((condition, inner))
            values = ((node.key, node.value)
                      if isinstance(node, ast.DictComp) else (node.elt,))
            for value in values:
                stack.append((value, inner))
            continue
        for child in ast.iter_child_nodes(node):
            stack.append((child, scope))
    return names, delayed
class _ApiBindingIndex:
    def __init__(self, tree: ast.AST) -> None:
        self._parents = build_parent_map(tree)
        self._scope_names, self._delayed_scopes = _build_scope_names(tree)
        local, self._globals, self._classes = collect_shadow_bindings(tree)
        self._delayed_scopes.difference_update(self._classes | {""})
        self._comprehension_scopes = {
            self._scope_for(node.generators[0].target)
            for node in walk_nodes(tree)
            if isinstance(node, _COMPREHENSION_NODES) and node.generators
        }
        extra_local: dict[str, set[str]] = {}
        for node in walk_nodes(tree):
            if isinstance(node, ast.Lambda):
                scope = self._scope_for(node.body)
                extra_local.setdefault(scope, set()).update(
                    collect_param_names(node))
            elif isinstance(node, _COMPREHENSION_NODES):
                scope = self._scope_for(node.generators[0].target)
                targets = extra_local.setdefault(scope, set())
                for generator in node.generators:
                    targets.update(
                        child.id for child in walk_nodes(generator.target)
                        if isinstance(child, ast.Name))
            elif isinstance(node, ast.NamedExpr):
                scope = self._event_scope_for(node.target)
                extra_local.setdefault(scope, set()).add(node.target.id)
        self._local = {
            scope: frozenset(names | extra_local.get(scope, set()))
            for scope, names in local.items()
        }
        for scope, names in extra_local.items():
            self._local.setdefault(scope, frozenset(names))
        self._events: dict[str, dict[str, list[tuple[tuple[int, int], str | None]]]] = {}
        self._value_events: dict[
            str, dict[str, list[tuple[tuple[int, int], ast.AST | None]]]] = {}
        self._binding_activations: dict[
            tuple[str, str, tuple[int, int]], tuple[int, int]] = {}
        for node in walk_nodes(tree):
            scope = self._scope_for(node)
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                self._record_imports(scope, node)
            elif (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef))
                  or (isinstance(node, ast.ExceptHandler) and node.name)):
                self._add(scope, node.name, node, None)
            elif (isinstance(node, ast.Name)
                  and isinstance(node.ctx, (ast.Store, ast.Del))):
                parent = self._parents.get(id(node))
                if (isinstance(parent, ast.AnnAssign)
                        and parent.target is node and parent.value is None):
                    continue
                scope = self._event_scope_for(node)
                self._add(scope, node.id, node, None)
                self._add_assigned_value(scope, node)
        for names in self._events.values():
            for events in names.values():
                events.sort(key=lambda event: event[0])
        for names in self._value_events.values():
            for events in names.values():
                events.sort(key=lambda event: event[0])
    def _scope_for(self, node: ast.AST) -> str:
        return self._scope_names.get(id(node), "")
    def _event_scope_for(self, node: ast.Name) -> str:
        scope = self._scope_for(node)
        parent = self._parents.get(id(node))
        if not (isinstance(parent, ast.NamedExpr) and parent.target is node):
            return scope
        while scope in self._comprehension_scopes:
            scope = scope.rpartition(".")[0]
        return scope
    def _add(self, scope: str, name: str, node: ast.AST,
             origin: str | None) -> None:
        pos = (getattr(node, "lineno", -1), getattr(node, "col_offset", -1))
        self._events.setdefault(scope, {}).setdefault(name, []).append((pos, origin))
        self._binding_activations[(scope, name, pos)] = (
            self._binding_activation(node))
    def _record_imports(self, scope: str,
                        node: ast.Import | ast.ImportFrom) -> None:
        for alias in node.names:
            if alias.name == "*":
                continue
            if isinstance(node, ast.Import):
                bound = alias.asname or alias.name.split(".")[0]
                origin = alias.name if alias.asname else alias.name.split(".")[0]
            else:
                bound = alias.asname or alias.name
                origin = (None if node.level
                          else f"{node.module or ''}.{alias.name}")
            self._add(scope, bound, node, origin)
    def _add_assigned_value(self, scope: str, node: ast.Name) -> None:
        pos = (getattr(node, "lineno", -1), getattr(node, "col_offset", -1))
        self._value_events.setdefault(scope, {}).setdefault(
            node.id, []).append((pos, self._assignment_rhs(node)))
    def _assignment_rhs(self, node: ast.Name) -> ast.AST | None:
        assign = self._parents.get(id(node))
        while assign is not None and not isinstance(
                assign, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            assign = self._parents.get(id(assign))
        if isinstance(assign, ast.Assign):
            for target in assign.targets:
                if _contains_node(target, node):
                    return _target_value_for(target, assign.value, node)
            return None
        if isinstance(assign, (ast.AnnAssign, ast.NamedExpr)):
            return (assign.value
                    if _contains_node(assign.target, node) else None)
        return None
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
    def _is_delayed_use(self, node: ast.AST,
                        boundary: str | None = None) -> bool:
        scope = self._scope_for(node)
        while scope and scope != boundary:
            if scope in self._delayed_scopes:
                return True
            scope = scope.rpartition(".")[0]
        return False
    def _prior_events(self, events: list, node: ast.AST,
                      scope: str, name: str) -> list:
        pos = (getattr(node, "lineno", -1), getattr(node, "col_offset", -1))
        outer_delayed = (scope != self._scope_for(node)
                         and self._is_delayed_use(node, scope))
        return [
            event for event in events
            if (outer_delayed or event[0] <= pos) and (
                self._binding_activations.get(
                    (scope, name, event[0]), event[0]) <= pos or outer_delayed)
        ]
    def _prior(self, events: list[tuple[tuple[int, int], str | None]],
               node: ast.AST, scope: str, name: str) -> tuple[bool, str | None]:
        prior = self._prior_events(events, node, scope, name)
        return (True, prior[-1][1]) if prior else (False, None)
    def origin_at(self, node: ast.AST, name: str) -> tuple[bool, str | None]:
        scope = self._scope_for(node)
        first = True
        while True:
            if scope and name in self._globals.get(scope, frozenset()):
                scope, first = "", False
                continue
            class_scope = scope in self._classes
            if not (class_scope and not first) and name in self._local.get(
                    scope, frozenset()):
                found, origin = self._prior(
                    self._events.get(scope, {}).get(name, []), node, scope, name)
                if scope and not class_scope:
                    return True, origin if found else None
                if found:
                    return True, origin
            if not scope:
                return False, None
            scope = scope.rpartition(".")[0]
            first = False
    def assigned_value_at(self, node: ast.AST, name: str) -> ast.AST | None:
        scope = self._scope_for(node)
        first = True
        while True:
            if scope and name in self._globals.get(scope, frozenset()):
                scope, first = "", False
                continue
            class_scope = scope in self._classes
            if not (class_scope and not first) and name in self._local.get(
                    scope, frozenset()):
                events = self._value_events.get(scope, {}).get(name, [])
                prior = self._prior_events(events, node, scope, name)
                if prior:
                    return prior[-1][1]
                if scope and not class_scope:
                    return None
            if not scope:
                return None
            scope = scope.rpartition(".")[0]
            first = False
    def refine_constructor_assignments(self, tree: ast.AST, func_name: str,
                                       module_name: str, marker: str) -> None:
        for node in walk_nodes(tree):
            if isinstance(node, ast.Assign):
                targets, value = node.targets, node.value
            elif isinstance(node, ast.AnnAssign) and node.value is not None:
                targets, value = [node.target], node.value
            else:
                continue
            if not isinstance(value, ast.Call):
                continue
            origin = (marker if _dp_call_matches_at(
                value, func_name, module_name, self) else None)
            for target in targets:
                for name_node in walk_nodes(target):
                    if not isinstance(name_node, ast.Name):
                        continue
                    scope = self._scope_for(name_node)
                    events = self._events.get(scope, {}).get(name_node.id, [])
                    pos = (name_node.lineno, name_node.col_offset)
                    for index, (event_pos, _old) in enumerate(events):
                        if event_pos == pos:
                            events[index] = (event_pos, origin)
def _contains_node(root: ast.AST, node: ast.AST) -> bool:
    return any(sub is node for sub in walk_nodes(root))
def _target_value_for(target: ast.AST, value: ast.AST,
                      node: ast.Name) -> ast.AST | None:
    if target is node:
        return value
    if isinstance(target, ast.Starred):
        return None
    if isinstance(target, (ast.Tuple, ast.List)):
        if not isinstance(value, (ast.Tuple, ast.List)):
            return None
        starred_index = next(
            (index for index, elt in enumerate(target.elts)
             if isinstance(elt, ast.Starred)), None)
        if starred_index is None:
            aligned = list(zip(target.elts, value.elts, strict=False))
        elif (any(isinstance(elt, ast.Starred) for elt in value.elts)
              or len(value.elts) < len(target.elts) - 1):
            return None
        else:
            aligned = []
            for index, target_elt in enumerate(target.elts):
                if index == starred_index:
                    continue
                value_index = (
                    index if index < starred_index
                    else len(value.elts) - len(target.elts) + index
                )
                aligned.append((target_elt, value.elts[value_index]))
        for target_elt, value_elt in aligned:
            found = _target_value_for(target_elt, value_elt, node)
            if found is not None:
                return found
    return None
_API_BINDING_INDEX_CACHE: weakref.WeakKeyDictionary = (
    weakref.WeakKeyDictionary())
_API_BINDING_INDEX_LOCK = threading.Lock()
def _binding_index(tree: ast.AST) -> _ApiBindingIndex:
    """按 AST 对象身份缓存绑定索引。

    `_ApiBindingIndex.__init__` 要对整棵树做 8 次遍历（父图、作用域名、
    影子绑定、推导式作用域、Lambda/海象局部名、事件收集）。索引构造完成后
    全部字段只读，而 API 风险族有 26 个 `check_DPxx` 入口各自构造一次索引，
    同一文件的同一棵树被重复建索引 26 次。按对象身份记忆化后，每棵树只建
    一次，语义与逐次构造等价（索引本身不可变）。

    用 `WeakKeyDictionary` 而非 `dict`：树对象在文件处理结束后应可回收，
    不能让缓存成为内存泄漏源。
    """
    with _API_BINDING_INDEX_LOCK:
        cached = _API_BINDING_INDEX_CACHE.get(tree)
    if cached is not None:
        return cached
    index = _ApiBindingIndex(tree)
    with _API_BINDING_INDEX_LOCK:
        _API_BINDING_INDEX_CACHE[tree] = index
    return index
def _visible_origin(expr: ast.AST, node: ast.AST, bindings: _ApiBindingIndex,
                    *, allow_literal: bool = True) -> str | None:
    return _visible_origin_recursive(
        expr, node, bindings, allow_literal=allow_literal, seen=set())
def _visible_origin_recursive(expr: ast.AST, node: ast.AST,
                              bindings: _ApiBindingIndex, *,
                              allow_literal: bool,
                              seen: set[int]) -> str | None:
    dotted = dotted_name(expr)
    if not dotted or id(expr) in seen:
        return None
    seen.add(id(expr))
    root, *members = dotted.split(".")
    found, origin = bindings.origin_at(node, root)
    if found and origin is None:
        assigned = bindings.assigned_value_at(node, root)
        if assigned is not None:
            resolved = _visible_origin_recursive(
                assigned, assigned, bindings, allow_literal=False, seen=seen)
            if resolved is None:
                return None
            return ".".join((resolved, *members))
    if not found:
        if not allow_literal:
            return None
        origin = root
    if origin is None:
        return None
    return ".".join((origin, *members))
def _visible_definition_key(
        scope: str, name: str, reference: ast.AST,
        definitions: dict[str, ast.AST],
        bindings: _ApiBindingIndex) -> str | None:
    base = _nested_scope_name(scope, name)
    candidates = {
        key: node for key, node in definitions.items()
        if key == base or key.startswith(base + "@")
    }
    if not candidates:
        return None
    events = bindings._events.get(scope, {}).get(name, [])
    prior = bindings._prior_events(events, reference, scope, name)
    if not prior:
        return None
    visible_position = prior[-1][0]
    return next(
        (key for key, node in candidates.items()
         if node_position(node) == visible_position), None)
def _module_attr_hit_at(node: ast.AST, module: str,
                        bindings: _ApiBindingIndex, *,
                        allow_literal: bool = True) -> str | None:
    if not (isinstance(node, ast.Attribute)
            and isinstance(node.ctx, ast.Load)):
        return None
    origin = _visible_origin(node.value, node, bindings,
                             allow_literal=allow_literal)
    return node.attr if origin == module else None
def _dp_call_matches_at(node: ast.Call, func_name: str, module_name: str,
                        bindings: _ApiBindingIndex) -> bool:
    func = node.func
    if isinstance(func, ast.Attribute):
        return (func.attr == func_name
                and _visible_origin(func.value, node, bindings) == module_name)
    if not isinstance(func, ast.Name):
        return False
    return (_visible_origin(func, node, bindings, allow_literal=False)
            == f"{module_name}.{func_name}")
def _iter_calls(
    tree: ast.AST, func_name: str, module_name: str,
    bindings: _ApiBindingIndex,
) -> list[ast.Call]:
    return [
        node for node in walk_nodes(tree)
        if (isinstance(node, ast.Call)
            and _dp_call_matches_at(node, func_name, module_name, bindings))
    ]
def _iter_attrs(tree: ast.AST, attr_name: str) -> list[ast.Attribute]:
    return [
        node for node in walk_nodes(tree)
        if (isinstance(node, ast.Attribute) and node.attr == attr_name
            and isinstance(node.ctx, ast.Load))
    ]
class _SimpleCallRule(NamedTuple):
    rule_id: str
    func_name: str
    module_name: str
    title: str
    description: str
    suggestion: str
    import_removed: bool = True
def _simple_call_rule_issues(
        tree: ast.AST, rule: _SimpleCallRule,
        bindings: _ApiBindingIndex | None = None) -> list[dict[str, Any]]:
    if bindings is None:
        bindings = _binding_index(tree)
    issues: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if _from_module_member_hits(node, rule.module_name, {rule.func_name}):
            issues.append(_simple_import_rule_issue(node, rule))
        elif (isinstance(node, ast.Call)
              and _dp_call_matches_at(
                  node, rule.func_name, rule.module_name, bindings)):
            issues.append(dp_issue(rule.rule_id, "P2", node.lineno,
                                   rule.title, rule.description,
                                   rule.suggestion))
    return issues
def _simple_import_rule_issue(node: ast.AST,
                              rule: _SimpleCallRule) -> dict[str, Any]:
    status = "已移除的" if rule.import_removed else "已弃用的"
    import_effect = ("；导入语句本身即触发 ImportError"
                     if rule.import_removed else "")
    return dp_issue(rule.rule_id, "P2", node.lineno,
                    f"从{rule.module_name}导入{status}{rule.func_name}()",
                    f"{rule.description}{import_effect}", rule.suggestion)
class _GatedAttrRule(NamedTuple):
    rule_id: str
    module_name: str
    attr_name: str
    severity: str
    title: str
    description: str
    suggestion: str
    receiver_names: frozenset[str] = frozenset()
def _attr_receiver_matches(node: ast.Attribute,
                          names: frozenset[str]) -> bool:
    if not names:
        return True
    receiver = node.value
    if isinstance(receiver, ast.Name):
        return receiver.id in names
    if isinstance(receiver, ast.Attribute):
        return receiver.attr in names
    return False
def _enclosing_class(node: ast.AST,
                     bindings: _ApiBindingIndex) -> ast.ClassDef | None:
    parent = bindings._parents.get(id(node))
    while parent is not None:
        if isinstance(parent, ast.ClassDef):
            return parent
        parent = bindings._parents.get(id(parent))
    return None
def _local_definition_key(
        name: str, reference: ast.AST, scope: str,
        definitions: dict[str, ast.AST],
        bindings: _ApiBindingIndex) -> str | None:
    seen: set[int] = set()
    while id(reference) not in seen:
        seen.add(id(reference))
        found, origin = bindings.origin_at(reference, name)
        if not found or origin is not None:
            return None
        binding_scope = scope
        first = True
        key = None
        while True:
            if binding_scope and name in bindings._globals.get(
                    binding_scope, frozenset()):
                binding_scope, first = "", False
                continue
            class_scope = binding_scope in bindings._classes
            if not (class_scope and not first) and name in bindings._local.get(
                    binding_scope, frozenset()):
                key = _visible_definition_key(
                    binding_scope, name, reference, definitions, bindings)
                break
            if not binding_scope:
                break
            binding_scope = binding_scope.rpartition(".")[0]
            first = False
        if key is not None:
            return key
        value = bindings.assigned_value_at(reference, name)
        if not isinstance(value, ast.Name):
            return None
        scope = bindings._scope_for(value)
        reference, name = value, value.id
    return None
def _local_base_class(base: ast.AST, bindings: _ApiBindingIndex,
                      classes: dict[str, ast.ClassDef]) -> ast.ClassDef | None:
    if not isinstance(base, ast.Name):
        return None
    key = _local_definition_key(
        base.id, base, bindings._scope_for(base), classes, bindings)
    return classes.get(key) if key is not None else None
_UNITTEST_TESTCASE_TOKEN = object()
def _unittest_c3_merge(sequences: list[list]) -> list | None:
    sequences = [list(sequence) for sequence in sequences]
    merged: list = []
    while True:
        sequences = [sequence for sequence in sequences if sequence]
        if not sequences:
            return merged
        candidate = next(
            (sequence[0] for sequence in sequences
             if not any(sequence[0] in other[1:] for other in sequences)),
            None,
        )
        if candidate is None:
            return None
        merged.append(candidate)
        for sequence in sequences:
            if sequence[0] is candidate:
                sequence.pop(0)
def _unittest_mro(
        node: ast.ClassDef, bindings: _ApiBindingIndex,
        classes: dict[str, ast.ClassDef], active: set[int]) -> list | None:
    if id(node) in active:
        return None
    active.add(id(node))
    try:
        base_nodes: list = []
        base_mros: list[list] = []
        for base in node.bases:
            if (_visible_origin(base, base, bindings, allow_literal=False)
                    == "unittest.TestCase"):
                base_node = _UNITTEST_TESTCASE_TOKEN
            else:
                base_node = _local_base_class(base, bindings, classes)
            if base_node is None:
                return None
            base_nodes.append(base_node)
            if base_node is _UNITTEST_TESTCASE_TOKEN:
                base_mros.append([_UNITTEST_TESTCASE_TOKEN])
                continue
            base_mro = _unittest_mro(
                base_node, bindings, classes, active)
            if base_mro is None:
                return None
            base_mros.append(base_mro)
        merged = _unittest_c3_merge([*base_mros, base_nodes])
        return None if merged is None else [node, *merged]
    finally:
        active.remove(id(node))
def _unittest_attr_override(
        node: ast.ClassDef, attr_name: str, bindings: _ApiBindingIndex,
        classes: dict[str, ast.ClassDef], seen: set[int]) -> bool | None:
    mro = _unittest_mro(node, bindings, classes, seen)
    if mro is None:
        return None
    for owner in mro:
        if owner is _UNITTEST_TESTCASE_TOKEN:
            return False
        if any(method.name == attr_name
               for method in iter_class_scope_methods(owner)):
            return True
    return None
def _gated_attr_owner_matches(node: ast.Attribute, rule: _GatedAttrRule,
                              bindings: _ApiBindingIndex,
                              classes: dict[str, ast.ClassDef]) -> bool:
    if rule.module_name != "unittest":
        return True
    owner = _enclosing_class(node, bindings)
    if owner is None:
        return False
    return _unittest_attr_override(
        owner, rule.attr_name, bindings, classes, set()) is False
def _gated_attr_rule_issues(tree: ast.AST,
                            rule: _GatedAttrRule) -> list[dict[str, Any]]:
    if not _module_root_imported(tree, rule.module_name):
        return []
    bindings = _binding_index(tree)
    scope_keys = _definition_scope_keys(tree)
    classes = {
        scope_keys[id(node)]: node
        for node in walk_nodes(tree) if isinstance(node, ast.ClassDef)
    }
    return [
        dp_issue(rule.rule_id, rule.severity, node.lineno,
                 rule.title, rule.description, rule.suggestion)
        for node in _iter_attrs(tree, rule.attr_name)
        if (_attr_receiver_matches(node, rule.receiver_names)
            and _gated_attr_owner_matches(node, rule, bindings, classes))
    ]
class _SSLLegacyCtorRule(NamedTuple):
    ctor_name: str
    module_name: str
    rule_id: str
    suggestion: str
    positional_params: tuple[tuple[int, str], ...] = ()
_SSL_LEGACY_KWARGS = ("keyfile", "certfile")
def _check_ssl_legacy_params(tree: ast.AST,
                             rule: _SSLLegacyCtorRule) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in _iter_calls(tree, rule.ctor_name, rule.module_name, bindings):
        positional_hits = [
            name for index, name in rule.positional_params
            if (len(node.args) > index
                and not any(isinstance(arg, ast.Starred)
                            for arg in node.args[:index + 1]))
        ]
        keyword_hits = [
            kw.arg for kw in node.keywords if kw.arg in _SSL_LEGACY_KWARGS
        ]
        for param_name in dict.fromkeys([*positional_hits, *keyword_hits]):
            issues.append(dp_issue(
                rule.rule_id, "P3", node.lineno,
                f"{rule.module_name}.{rule.ctor_name}() 使用了已移除的 {param_name} 参数",
                f"{param_name} 参数已弃用(3.6)并于3.12移除",
                rule.suggestion,
            ))
    return issues
def _asyncio_coroutine_decorator_hit(decorator: Any,
                                     bindings: _ApiBindingIndex) -> bool:
    return _visible_origin(
        decorator, decorator, bindings, allow_literal=False,
    ) == "asyncio.coroutine"
def _from_module_member_hits(node: Any, module: str, members) -> list[str]:
    if not (isinstance(node, ast.ImportFrom) and not node.level
            and node.module == module):
        return []
    return [alias.name for alias in node.names if alias.name in members]
class _TypingSubscriptRule(NamedTuple):
    symbol: str
    rule_id: str
    title: str
    description: str
    suggestion: str
def _check_typing_subscript(tree: ast.AST, rule: _TypingSubscriptRule) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    symbol = rule.symbol
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Subscript):
            continue
        if not _typing_subscript_is_target_at(node.value, symbol, bindings):
            continue
        issues.append(dp_issue(
            rule.rule_id, "P2", node.lineno,
            rule.title, rule.description, rule.suggestion,
        ))
    return issues
def _typing_subscript_is_target_at(value: ast.AST, symbol: str,
                                   bindings: _ApiBindingIndex) -> bool:
    if isinstance(value, ast.Name):
        found, origin = bindings.origin_at(value, value.id)
        return found and origin == f"typing.{symbol}"
    return (isinstance(value, ast.Attribute) and value.attr == symbol
            and _visible_origin(value.value, value, bindings,
                                allow_literal=False) == "typing")
class _ModuleMemberRule(NamedTuple):
    rule_id: str
    module_name: str
    member: str
    severity: str
    from_title: str
    attr_title: str
    description: str
    suggestion: str
def _module_member_rule_issues(tree: ast.AST,
                               rule: _ModuleMemberRule) -> list[dict[str, Any]]:
    bindings = _binding_index(tree)
    issues: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if _from_module_member_hits(node, rule.module_name, {rule.member}):
            issues.append(dp_issue(
                rule.rule_id, rule.severity, node.lineno,
                rule.from_title.format(member=rule.member),
                rule.description, rule.suggestion,
            ))
        if _module_attr_hit_at(node, rule.module_name, bindings) != rule.member:
            continue
        issues.append(dp_issue(
            rule.rule_id, rule.severity, node.lineno,
            rule.attr_title.format(member=rule.member),
            rule.description, rule.suggestion,
        ))
    return issues
_DP01_REMOVED_MODULES = frozenset({"distutils", "asynchat", "asyncore", "smtpd", "imp"})
_DP01_REMOVED_FUNCTIONS: dict[str, dict[str, str]] = {
    "unittest": {"makeSuite": "3.13", "findTestCases": "3.13"},
    "sqlite3": {"enable_shared_cache": "3.12"},
}
def _dp01_from_import_issues(node: ast.ImportFrom) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if node.level or not node.module:
        return issues
    top = node.module.split(".")[0]
    if top in _DP01_REMOVED_MODULES:
        issues.append(dp_issue(
            "DP-01", "P1", node.lineno,
            f"从已移除模块导入: {node.module}",
            f"Python 3.12移除了 {node.module} 模块",
            "请替换为现代替代方案",
        ))
    if node.module == top and top in _DP01_REMOVED_FUNCTIONS:
        for alias in node.names:
            if alias.name in _DP01_REMOVED_FUNCTIONS[top]:
                issues.append(dp_issue(
                    "DP-01", "P1", node.lineno,
                    f"使用了已移除的函数: {top}.{alias.name}",
                    f"Python {_DP01_REMOVED_FUNCTIONS[top][alias.name]}移除了 {top}.{alias.name}",
                    "请使用替代API",
                ))
    return issues
def _dp01_import_issues(node: ast.Import) -> list[dict[str, Any]]:
    return [
        dp_issue(
            "DP-01", "P1", node.lineno,
            f"使用了Python 3.12已移除的模块: {alias.name}",
            f"Python 3.12移除了 {alias.name} 模块",
            "请替换为现代替代方案(distutils→setuptools, imp→importlib)",
        )
        for alias in node.names
        if alias.name.split(".")[0] in _DP01_REMOVED_MODULES
    ]
def _dp01_call_issues(node: ast.Call,
                      bindings: _ApiBindingIndex) -> list[dict[str, Any]]:
    func = node.func
    if not isinstance(func, ast.Attribute):
        return []
    mod = _visible_origin(func.value, node, bindings)
    if mod not in _DP01_REMOVED_FUNCTIONS or func.attr not in _DP01_REMOVED_FUNCTIONS[mod]:
        return []
    return [dp_issue(
        "DP-01", "P1", node.lineno,
        f"使用了已移除的函数: {mod}.{func.attr}",
        f"Python {_DP01_REMOVED_FUNCTIONS[mod][func.attr]}移除了 {mod}.{func.attr}",
        "请使用替代API",
    )]
@_api_rule
def check_DP01(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            issues.extend(_dp01_import_issues(node))
        elif isinstance(node, ast.ImportFrom):
            issues.extend(_dp01_from_import_issues(node))
        elif isinstance(node, ast.Call):
            issues.extend(_dp01_call_issues(node, bindings))
    return issues
_DP02_REMOVED_AST = frozenset({"Num", "Str", "Bytes", "NameConstant", "Ellipsis"})
_DP02_REMOVED: dict[str, tuple[frozenset[str], str]] = {
    "ast": (_DP02_REMOVED_AST, "使用 ast.Constant 替代"),
    "pkgutil": (frozenset({"find_loader", "get_loader"}),
                "使用 importlib.util.find_spec() 替代"),
}
def _dp03_call_contexts(
        tree: ast.AST, parents: dict[int, ast.AST],
) -> dict[tuple[int, int], frozenset[tuple[int, str]]]:
    contexts: dict[tuple[int, int], frozenset[tuple[int, str]]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        decisions: list[tuple[int, str]] = []
        current = node
        parent = parents.get(id(current))
        while parent is not None:
            if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef, ast.Lambda)):
                break
            if isinstance(parent, ast.If):
                if any(current is stmt for stmt in parent.body):
                    decisions.append((id(parent), "body"))
                elif any(current is stmt for stmt in parent.orelse):
                    decisions.append((id(parent), "orelse"))
            current = parent
            parent = parents.get(id(current))
        contexts[node_position(node)] = frozenset(decisions)
    return contexts
def _dp03_position_precedes(
        setter: tuple[int, int], process: tuple[int, int],
        contexts: dict[tuple[int, int], frozenset[tuple[int, str]]]) -> bool:
    if setter >= process:
        return False
    return contexts.get(setter, frozenset()).issubset(
        contexts.get(process, frozenset()))
def _dp03_path_precedes(
        setter_path: tuple[tuple[int, int], ...],
        process_path: tuple[tuple[int, int], ...],
        contexts: dict[tuple[int, int], frozenset[tuple[int, str]]]) -> bool:
    setter_context = frozenset().union(
        *(contexts.get(position, frozenset()) for position in setter_path))
    process_context = frozenset().union(
        *(contexts.get(position, frozenset()) for position in process_path))
    if not setter_context.issubset(process_context):
        return False
    for setter, process in zip(setter_path, process_path, strict=False):
        if setter != process:
            return _dp03_position_precedes(setter, process, contexts)
    return len(setter_path) < len(process_path)
def _dp03_early_exit(stmts: list[ast.stmt]) -> bool:
    return bool(stmts) and isinstance(
        stmts[-1], (ast.Return, ast.Raise, ast.Break, ast.Continue))
def _dp03_block_guarantees_setter(
        stmts: list[ast.stmt], setter_ids: set[int]) -> bool:
    for stmt in stmts:
        if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
                and id(stmt.value) in setter_ids):
            return True
        if not isinstance(stmt, ast.If):
            continue
        body_safe = (_dp03_early_exit(stmt.body)
                     or _dp03_block_guarantees_setter(stmt.body, setter_ids))
        else_safe = (_dp03_early_exit(stmt.orelse)
                     or _dp03_block_guarantees_setter(stmt.orelse, setter_ids))
        if body_safe and else_safe:
            return True
    return False
def _dp03_prefix_guarantees_setter(
        node: ast.Call, parents: dict[int, ast.AST],
        setters: list[ast.Call]) -> bool:
    setter_ids = {id(call) for call in setters}
    child = node
    parent = parents.get(id(child))
    while parent is not None:
        for field_name in parent._fields:
            group = getattr(parent, field_name, None)
            if not isinstance(group, list):
                continue
            for index, stmt in enumerate(group):
                if stmt is child and _dp03_block_guarantees_setter(
                        group[:index], setter_ids):
                    return True
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef, ast.Lambda)):
            break
        child, parent = parent, parents.get(id(parent))
    return False
def _dp03_start_method_declared_first(
        tree: Any, first_process: Any, bindings: _ApiBindingIndex,
        scopes: dict[int, str], setters: list[ast.Call],
        contexts: dict[tuple[int, int], frozenset[tuple[int, str]]]) -> bool:
    boundary = node_position(first_process)
    process_scope = scopes.get(id(first_process), "")
    for call in setters:
        call_scope = scopes.get(id(call), "")
        if (call_scope == process_scope and _dp03_position_precedes(
                node_position(call), boundary, contexts)):
            return True
    if _dp03_prefix_guarantees_setter(
            first_process, bindings._parents, setters):
        return True
    if _dp03_module_setter_precedes_definition(
            setters, scopes, first_process, bindings._parents):
        return True
    calls = _dp03_local_call_graph(tree, scopes, bindings)
    setter_paths = [
        path for call in setters
        for path in _dp03_event_paths(calls, scopes, call)
    ]
    if not setter_paths:
        return False
    process_paths = _dp03_event_paths(calls, scopes, first_process)
    return bool(process_paths) and all(
        any(_dp03_path_precedes(setter_path, process_path, contexts)
            for setter_path in setter_paths)
        for process_path in process_paths)
_DP03_DEFINITION_BOUNDARIES = (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda, ast.ClassDef)
def _dp03_module_setter_precedes_definition(
        setters: list[ast.Call], scopes: dict[int, str],
        process: ast.Call, parents: dict[int, ast.AST]) -> bool:
    """模块级 ``set_start_method`` 先于封装定义语句时必然先于 ``Process`` 执行。

    函数/方法/Lambda 体与类体只能在封装它们的 ``def``/``class``/``lambda``
    语句执行之后运行；模块级 setter 若位于该定义语句之前，则无论该作用域
    是否在模块内被调用（框架回调、动态分派），setter 都已先执行。此前的
    调用路径分析只跟踪模块内按名调用，未在模块内调用的方法会被误判为
    "未先声明 start_method"。仅接受模块体直接子语句：位于 if/try/with
    等分支内的 setter 不是无条件执行，仍交回分支路径分析。
    """
    module_setter_positions = [
        node_position(call) for call in setters
        if scopes.get(id(call), "") == ""
        and _dp03_is_direct_module_statement(call, parents)]
    if not module_setter_positions:
        return False
    outermost = None
    node: ast.AST | None = process
    while node is not None:
        if isinstance(node, _DP03_DEFINITION_BOUNDARIES):
            outermost = node
        node = parents.get(id(node))
    if outermost is None:
        return False
    definition_position = node_position(outermost)
    return any(position < definition_position
               for position in module_setter_positions)
def _dp03_is_direct_module_statement(node: ast.AST,
                                     parents: dict[int, ast.AST]) -> bool:
    current: ast.AST | None = node
    while current is not None and not isinstance(current, ast.stmt):
        current = parents.get(id(current))
    if current is None:
        return False
    parent = parents.get(id(current))
    return parent is None or isinstance(parent, ast.Module)
def _dp03_local_function_scope(call: ast.Call, caller_scope: str,
                               functions: dict[str, ast.AST],
                               bindings: _ApiBindingIndex) -> str | None:
    if not isinstance(call.func, ast.Name):
        return None
    return _local_definition_key(
        call.func.id, call, caller_scope, functions, bindings)
def _dp03_local_call_graph(
        tree: ast.AST, scopes: dict[int, str],
        bindings: _ApiBindingIndex,
) -> dict[str, list[tuple[tuple[int, int], str]]]:
    functions: dict[str, ast.AST] = {}
    scope_keys = _definition_scope_keys(tree)
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions[scope_keys[id(node)]] = node
    calls: dict[str, list[tuple[tuple[int, int], str]]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        caller = scopes.get(id(node), "")
        callee = _dp03_local_function_scope(node, caller, functions, bindings)
        if callee is not None:
            calls.setdefault(caller, []).append((node_position(node), callee))
    return calls
def _dp03_event_paths(
        calls: dict[str, list[tuple[tuple[int, int], str]]],
        scopes: dict[int, str], node: ast.Call,
) -> list[tuple[tuple[int, int], ...]]:
    target_scope = scopes.get(id(node), "")
    event_position = node_position(node)
    if not target_scope:
        return [(event_position,)]
    paths: list[tuple[tuple[int, int], ...]] = []
    def visit(caller: str, prefix: tuple[tuple[int, int], ...],
              active: frozenset[str]) -> None:
        for call_position, callee in calls.get(caller, []):
            if callee in active:
                continue
            next_prefix = (*prefix, call_position)
            if callee == target_scope:
                paths.append((*next_prefix, event_position))
                continue
            visit(callee, next_prefix, active | {callee})
    visit("", (), frozenset())
    return paths
def _dp02_from_import_issues(node: ast.ImportFrom) -> list[dict[str, Any]]:
    if node.level or not node.module:
        return []
    removed = _DP02_REMOVED.get(node.module)
    if removed is None:
        return []
    names, replacement = removed
    return [
        dp_issue(
            "DP-02", "P1", node.lineno,
            f"使用了Python 3.14移除的{node.module}.{alias.name}",
            f"{node.module}.{alias.name} 在Python 3.14中已移除",
            replacement,
        )
        for alias in node.names if alias.name in names
    ]
def _dp02_attribute_issues(node: ast.Attribute,
                           bindings: _ApiBindingIndex) -> list[dict[str, Any]]:
    if not isinstance(node.ctx, ast.Load):
        return []
    module = _visible_origin(node.value, node, bindings)
    if module not in _DP02_REMOVED or node.attr not in _DP02_REMOVED[module][0]:
        return []
    return [dp_issue(
        "DP-02", "P1", node.lineno,
        f"使用了Python 3.14移除的{module}.{node.attr}",
        f"{module}.{node.attr} 在Python 3.14中已移除",
        _DP02_REMOVED[module][1],
    )]
@_api_rule
def check_DP02(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.ImportFrom):
            issues.extend(_dp02_from_import_issues(node))
        elif isinstance(node, ast.Attribute):
            issues.extend(_dp02_attribute_issues(node, bindings))
    return issues
@_api_rule
def check_DP03(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not _module_root_imported(tree, "multiprocessing"):
        return issues
    bindings = _binding_index(tree)
    process_calls = _iter_calls(tree, "Process", "multiprocessing", bindings)
    if not process_calls:
        return issues
    scopes = build_scope_index(tree)
    contexts = _dp03_call_contexts(tree, bindings._parents)
    setters = _iter_calls(tree, "set_start_method", "multiprocessing",
                          bindings)
    first = next(
        (call for call in sorted(process_calls, key=node_position)
         if not _dp03_start_method_declared_first(
             tree, call, bindings, scopes, setters, contexts)),
        None,
    )
    if first is None:
        return issues
    issues.append(dp_issue(
        "DP-03", "P2", first.lineno,
        "multiprocessing未显式指定start_method",
        "使用multiprocessing.Process但未调用set_start_method()，跨平台默认行为不一致",
        "在创建Process前调用 multiprocessing.set_start_method('spawn')",
    ))
    return issues
_DP04_REPLACEMENTS = {
    "List": "list", "Dict": "dict", "Tuple": "tuple", "Set": "set",
    "FrozenSet": "frozenset", "Type": "type",
    "DefaultDict": "collections.defaultdict",
    "OrderedDict": "collections.OrderedDict",
    "Counter": "collections.Counter",
    "Deque": "collections.deque",
    "ChainMap": "collections.ChainMap",
}
_DP04_DEPRECATED = frozenset(_DP04_REPLACEMENTS)
@_api_rule
def check_DP04(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        hit_names = _from_module_member_hits(node, "typing", _DP04_DEPRECATED)
        if not hit_names:
            attr = _module_attr_hit_at(
                node, "typing", bindings, allow_literal=False)
            hit_names = [attr] if attr in _DP04_DEPRECATED else []
        for name in hit_names:
            issues.append(dp_issue(
                "DP-04", "P3", node.lineno,
                f"使用已弃用的typing.{name}",
                f"typing.{name} 自Python 3.9起弃用(PEP 585)",
                f"改用 {_DP04_REPLACEMENTS[name]}",
            ))
    return issues
@_api_rule
def check_DP05(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if not (isinstance(func, ast.Attribute)
                and func.attr in ("utcnow", "utcfromtimestamp")):
            continue
        form = _dp05_receiver_form_at(func.value, node, bindings)
        if form is None:
            continue
        note = "" if form[0] else "（需 from datetime import timezone）"
        issues.append(dp_issue(
            "DP-05", "P2", node.lineno,
            f"使用了废弃的datetime.{func.attr}()",
            f"datetime.{func.attr}() 在Python 3.12中弃用，返回naive datetime",
            f"改用 {_dp05_replacement(func.attr, form, node)}{note}",
        ))
    return issues
def _dp05_receiver_form_at(value: ast.AST, node: ast.Call,
                           bindings: _ApiBindingIndex) -> tuple[bool, str, str] | None:
    if isinstance(value, ast.Name):
        origin = _visible_origin(value, node, bindings)
        if origin == "datetime":
            return True, f"{value.id}.datetime", f"{value.id}.timezone"
        if origin == "datetime.datetime":
            return False, value.id, "timezone"
        return None
    if not (isinstance(value, ast.Attribute) and value.attr == "datetime"
            and isinstance(value.value, ast.Name)):
        return None
    if _visible_origin(value, node, bindings) != "datetime.datetime":
        return None
    root = value.value.id
    return True, f"{root}.datetime", f"{root}.timezone"
def _dp05_replacement(attr: str, form: tuple[bool, str, str],
                      node: ast.Call) -> str:
    _class_expr, _tz_expr = form[1], form[2]
    if attr == "utcnow":
        return f"{_class_expr}.now({_tz_expr}.utc)"
    timestamp = (ast.unparse(node.args[0])
                 if len(node.args) == 1
                 and not isinstance(node.args[0], ast.Starred) else "ts")
    return f"{_class_expr}.fromtimestamp({timestamp}, tz={_tz_expr}.utc)"
_DP06_RULE = _TypingSubscriptRule(
    symbol="Optional", rule_id="DP-06",
    title="使用typing.Optional[X]而非X|None",
    description="Python 3.10+支持 X | None 语法",
    suggestion="将 Optional[X] 替换为 X | None",
)
@_api_rule
def check_DP06(tree: ast.AST) -> list[dict[str, Any]]:
    return _check_typing_subscript(tree, _DP06_RULE)
_DP07_RULE = _TypingSubscriptRule(
    symbol="Union", rule_id="DP-07",
    title="使用typing.Union[X,Y]而非X|Y",
    description="Python 3.10+支持 X | Y 语法",
    suggestion="将 Union[X, Y] 替换为 X | Y",
)
@_api_rule
def check_DP07(tree: ast.AST) -> list[dict[str, Any]]:
    return _check_typing_subscript(tree, _DP07_RULE)
_DP08_ABC_TYPES = frozenset({
    "Mapping", "MutableMapping", "Sequence", "MutableSequence", "Set", "MutableSet",
    "Iterable", "Iterator", "Generator", "Callable", "Awaitable", "Coroutine",
    "AsyncIterable", "AsyncIterator", "AsyncGenerator", "Reversible", "Container",
    "Collection", "Hashable", "Sized", "ByteString", "ItemsView", "KeysView",
    "MappingView", "ValuesView",
})
@_api_rule
def check_DP08(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        for name in _from_module_member_hits(node, "collections",
                                            _DP08_ABC_TYPES):
            issues.append(dp_issue(
                "DP-08", "P3", node.lineno,
                f"从collections导入{name}(应从collections.abc导入)",
                f"Python 3.9+ 应从 collections.abc 导入 {name}，collections 下别名已弃用",
                f"改为 from collections.abc import {name}",
            ))
        attr = _module_attr_hit_at(node, "collections", bindings)
        if attr not in _DP08_ABC_TYPES:
            continue
        issues.append(dp_issue(
            "DP-08", "P3", node.lineno,
            f"使用了collections.{attr}(应从collections.abc导入)",
            f"Python 3.9+ 应从 collections.abc 导入 {attr}，collections 下别名已弃用",
            f"改为 from collections.abc import {attr}",
        ))
    return issues
_DP09_THREADING_CAMEL = {
    "currentThread": "current_thread",
    "activeCount": "active_count",
    "notifyAll": "notify_all",
}
_DP09_METHOD_DOMAIN = frozenset({"notifyAll"})
def _dp09_suggestion(old_name: str, from_import: bool) -> str:
    modern = _DP09_THREADING_CAMEL[old_name]
    if old_name in _DP09_METHOD_DOMAIN:
        return (f"threading 模块无 {modern} 函数；{modern} 为 "
                f"threading.Condition 方法，请在 Condition 实例上调用")
    return (f"改为 from threading import {modern}" if from_import
            else f"使用 threading.{modern}")
@_api_rule
def check_DP09(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    bindings.refine_constructor_assignments(
        tree, "Condition", "threading", "threading.Condition.instance")
    for node in walk_nodes(tree):
        for name in _from_module_member_hits(node, "threading",
                                             _DP09_THREADING_CAMEL):
            issues.append(dp_issue(
                "DP-09", "P3", node.lineno,
                f"使用了旧式驼峰命名: from threading import {name}",
                "Python 3.10+统一使用蛇形命名",
                _dp09_suggestion(name, from_import=True),
            ))
        if _dp09_condition_method_hit_at(node, bindings):
            issues.append(dp_issue(
                "DP-09", "P3", node.lineno,
                "使用了旧式驼峰命名: threading.Condition.notifyAll()",
                "Python 3.10+统一使用蛇形命名",
                _dp09_suggestion("notifyAll", from_import=False),
            ))
            continue
        attr = _module_attr_hit_at(node, "threading", bindings)
        if attr not in _DP09_THREADING_CAMEL:
            continue
        issues.append(dp_issue(
            "DP-09", "P3", node.lineno,
            f"使用了旧式驼峰命名: threading.{attr}",
            "Python 3.10+统一使用蛇形命名",
            _dp09_suggestion(attr, from_import=False),
        ))
    return issues
def _dp09_condition_method_hit_at(
        node: Any, bindings: _ApiBindingIndex) -> bool:
    if not (isinstance(node, ast.Attribute) and node.attr == "notifyAll"
            and isinstance(node.ctx, ast.Load)):
        return False
    receiver = node.value
    if _visible_origin(receiver, node, bindings, allow_literal=False) in {
            "threading.Condition", "threading.Condition.instance"}:
        return True
    if isinstance(receiver, ast.Call):
        return _dp_call_matches_at(
            receiver, "Condition", "threading", bindings)
    if not isinstance(receiver, ast.Name):
        return False
    found, origin = bindings.origin_at(node, receiver.id)
    if not found or origin is not None:
        return False
    value = bindings.assigned_value_at(node, receiver.id)
    return (isinstance(value, ast.Call) and _dp_call_matches_at(
        value, "Condition", "threading", bindings))
_DP10_RULE = _SimpleCallRule(
    "DP-10", "getargspec", "inspect",
    "使用了已移除的inspect.getargspec()",
    "Python 3.11移除了 inspect.getargspec()",
    "改用 inspect.getfullargspec() 或 inspect.signature()",
)
@_api_rule
def check_DP10(tree: ast.AST) -> list[dict[str, Any]]:
    return _simple_call_rule_issues(tree, _DP10_RULE)
_DP11_DANGEROUS = frozenset({"eval", "exec", "compile", "__import__"})
def _dp11_iter_execution_nodes(scope: ast.AST):
    stack = list(scope.body)
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            stack.extend(reversed(list(iter_def_site_nodes(node))))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
@_api_rule
def check_DP11(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        for item in iter_class_scope_methods(node):
            if item.name != "__getattr__":
                continue
            if not any(_dp11_is_builtin_call(child, name, bindings)
                       for child in _dp11_iter_execution_nodes(item)
                       for name in _DP11_DANGEROUS):
                continue
            issues.append(dp_issue(
                "DP-11", "P3", item.lineno,
                f"类{node.name}的__getattr__中包含危险操作",
                "__getattr__中调用eval/exec等危险函数可能导致代码注入",
                "避免在__getattr__中执行动态代码",
            ))
    return issues
_DP11_BUILTIN_NAMESPACES = frozenset({"builtins", "__builtins__"})
def _dp11_builtin_expr_matches(node: ast.AST, name: str,
                               bindings: _ApiBindingIndex,
                               seen: set[int]) -> bool:
    if id(node) in seen:
        return False
    seen.add(id(node))
    if isinstance(node, ast.Name):
        found, origin = bindings.origin_at(node, node.id)
        if not found:
            return node.id == name
        if origin is not None:
            return origin == f"builtins.{name}"
        value = bindings.assigned_value_at(node, node.id)
        return (value is not None and _dp11_builtin_expr_matches(
            value, name, bindings, seen))
    if isinstance(node, ast.Attribute):
        return (node.attr == name
                and isinstance(node.ctx, ast.Load)
                and _visible_origin(node.value, node, bindings)
                in _DP11_BUILTIN_NAMESPACES)
    return False
def _dp11_is_builtin_call(node: Any, name: str,
                          bindings: _ApiBindingIndex) -> bool:
    return (isinstance(node, ast.Call)
            and _dp11_builtin_expr_matches(node.func, name, bindings, set()))
def _dp12_is_nested_call(node: Any, bindings: _ApiBindingIndex) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    return (isinstance(func, ast.Attribute) and func.attr == "nested"
            and _visible_origin(func.value, node, bindings) == "contextlib")
@_api_rule
def check_DP12(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not (_dp12_is_nested_call(node, bindings)
                or _from_module_member_hits(node, "contextlib", {"nested"})):
            continue
        issues.append(dp_issue(
            "DP-12", "P2", node.lineno,
            "使用了已移除的contextlib.nested()",
            "Python 3.2移除了 contextlib.nested() (3.1起弃用)",
            "使用嵌套 with 语句或 ExitStack",
        ))
    return issues
_DP13_RULE = _SimpleCallRule(
    "DP-13", "formatargspec", "inspect",
    "使用了已移除的inspect.formatargspec()",
    "Python 3.11移除了 inspect.formatargspec()",
    "改用 inspect.signature() 获取函数签名信息",
)
@_api_rule
def check_DP13(tree: ast.AST) -> list[dict[str, Any]]:
    return _simple_call_rule_issues(tree, _DP13_RULE)
_DP24_RULE = _SimpleCallRule(
    "DP-24", "popen", "platform",
    "使用了platform.popen()(弃用)",
    "platform.popen() 已弃用",
    "改用 subprocess 模块",
    import_removed=False,
)
@_api_rule
def check_DP24(tree: ast.AST) -> list[dict[str, Any]]:
    return _simple_call_rule_issues(tree, _DP24_RULE)
_DP32_LOGGING_ALIASES = frozenset({"_log", "_logger", "logger", "log", "logging"})
@_api_rule
def check_DP32(tree: ast.AST) -> list[dict[str, Any]]:
    bindings = _binding_index(tree)
    bindings.refine_constructor_assignments(
        tree, "getLogger", "logging", "logging.Logger")
    issues: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            issues.extend(_dp32_call_issues_at(node, bindings))
    return issues
def _dp32_call_issues_at(node: ast.Call,
                         bindings: _ApiBindingIndex) -> list[dict[str, Any]]:
    func = node.func
    if isinstance(func, ast.Name):
        if _visible_origin(
                func, node, bindings, allow_literal=False) != "logging.warn":
            return []
        return [dp_issue(
            "DP-32", "P3", node.lineno,
            f"使用了{func.id}()(logging.warn 弃用别名)",
            "from logging import warn 引入的是已弃用的 logging.warn",
            f"改用 from logging import warning，调用点 {func.id}() 同步改为 warning()",
        )]
    if not (isinstance(func, ast.Attribute) and func.attr == "warn"):
        return []
    alias_name = _dp32_receiver_alias_at(node, bindings)
    if not alias_name:
        return []
    return [dp_issue(
        "DP-32", "P3", node.lineno,
        f"使用了{alias_name}.warn()(弃用)",
        "logging.warn() 已弃用",
        f"将 {alias_name}.warn() 替换为 {alias_name}.warning()",
    )]
def _is_logger_factory_call(node: ast.AST | None,
                           bindings: _ApiBindingIndex) -> bool:
    return (isinstance(node, ast.Call)
            and _dp_call_matches_at(node, "getLogger", "logging", bindings))
def _dp32_receiver_alias_at(node: ast.Call,
                            bindings: _ApiBindingIndex) -> str | None:
    receiver = node.func.value
    if isinstance(receiver, ast.Name):
        if _visible_origin(receiver, node, bindings, allow_literal=False) in {
                "logging", "logging.Logger"}:
            return receiver.id
        found, origin = bindings.origin_at(node, receiver.id)
        if not found and receiver.id == "logging":
            return receiver.id
        if found:
            if origin is not None:
                return None
            value = bindings.assigned_value_at(node, receiver.id)
            if _is_logger_factory_call(value, bindings):
                return receiver.id
            if value is not None:
                return None
        return receiver.id if receiver.id in _DP32_LOGGING_ALIASES else None
    if isinstance(receiver, ast.Call):
        return (ast.unparse(receiver)
                if _is_logger_factory_call(receiver, bindings) else None)
    if (isinstance(receiver, ast.Attribute)
            and receiver.attr in _DP32_LOGGING_ALIASES):
        return receiver.attr
    return None
@_api_rule
def check_DP33(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in _iter_calls(tree, "warn_explicit", "warnings", bindings):
        if (len(node.args) >= 7
                and not any(isinstance(arg, ast.Starred) for arg in node.args)):
            issues.append(dp_issue(
                "DP-33", "P3", node.lineno,
                "warnings.warn_explicit() 位置参数超过 6 个",
                "warn_explicit() 可选参数（module/registry/module_globals/"
                "source）应使用关键字传入，按位置传满 7 个易随签名扩展错位",
                "module/registry/module_globals/source 改用关键字传入",
            ))
    return issues
@_api_rule
def check_DP34(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not _dp11_is_builtin_call(node, "__import__", bindings):
            continue
        issues.append(dp_issue(
            "DP-34", "P3", node.lineno,
            "使用了__import__()动态导入",
            "__import__() 语义晦涩且绕过静态导入检查",
            "改用 importlib.import_module()",
        ))
    return issues
_DP36_RULE = _GatedAttrRule(
    "DP-36", "unittest", "assertDictContainsSubset", "P2",
    "使用了已移除的assertDictContainsSubset()",
    "unittest.TestCase.assertDictContainsSubset() 3.2起弃用并于3.12移除",
    "使用 self.assertTrue(d.items() >= subset.items()) 替代",
    frozenset({"self", "cls"}),
)
@_api_rule
def check_DP36(tree: ast.AST) -> list[dict[str, Any]]:
    return _gated_attr_rule_issues(tree, _DP36_RULE)
_DP37_RULE = _GatedAttrRule(
    "DP-37", "unittest", "assert_", "P3",
    "使用了已弃用的assert_()方法",
    "unittest.TestCase.assert_() 已弃用",
    "使用 self.assertTrue() 替代",
    frozenset({"self", "cls"}),
)
@_api_rule
def check_DP37(tree: ast.AST) -> list[dict[str, Any]]:
    return _gated_attr_rule_issues(tree, _DP37_RULE)
_DP38_RULE = _GatedAttrRule(
    "DP-38", "xml", "getchildren", "P2",
    "使用了已移除的getchildren()",
    "xml.etree.ElementTree.getchildren() 3.2起弃用并于3.9移除",
    "使用 list(element) 替代",
)
_DP38_ELEMENT_ORIGIN = "xml.etree.ElementTree.Element"
_DP38_ELEMENT_FACTORIES = frozenset({
    _DP38_ELEMENT_ORIGIN,
    "xml.etree.ElementTree.fromstring",
    "xml.etree.ElementTree.fromstringlist",
    "xml.etree.ElementTree.XML",
})
def _dp38_element_expr_at(expr: ast.AST, reference: ast.AST,
                          bindings: _ApiBindingIndex,
                          seen: set[int]) -> bool:
    if id(expr) in seen:
        return False
    seen.add(id(expr))
    if (_visible_origin(expr, reference, bindings, allow_literal=False)
            == _DP38_ELEMENT_ORIGIN):
        return True
    if isinstance(expr, ast.Call):
        return (_visible_origin(expr.func, expr, bindings, allow_literal=False)
                in _DP38_ELEMENT_FACTORIES)
    if not isinstance(expr, ast.Name):
        return False
    found, origin = bindings.origin_at(reference, expr.id)
    if not found or origin is not None:
        return False
    value = bindings.assigned_value_at(reference, expr.id)
    return (value is not None
            and _dp38_element_expr_at(value, value, bindings, seen))
@_api_rule
def check_DP38(tree: ast.AST) -> list[dict[str, Any]]:
    if not _module_root_imported(tree, "xml"):
        return []
    bindings = _binding_index(tree)
    return [
        dp_issue(_DP38_RULE.rule_id, _DP38_RULE.severity, node.lineno,
                 _DP38_RULE.title, _DP38_RULE.description,
                 _DP38_RULE.suggestion)
        for node in _iter_attrs(tree, _DP38_RULE.attr_name)
        if _dp38_element_expr_at(node.value, node, bindings, set())
    ]
@_api_rule
def check_DP39(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not _module_root_imported(tree, "csv"):
        return issues
    bindings = _binding_index(tree)
    bindings.refine_constructor_assignments(
        tree, "Sniffer", "csv", "csv.Sniffer.instance")
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "sniff"):
            continue
        self_offset = _dp39_self_offset_at(node.func, node, bindings)
        if self_offset is None:
            continue
        positional_limit = 2 + self_offset
        if (len(node.args) <= positional_limit
                or any(isinstance(arg, ast.Starred)
                       for arg in node.args[:positional_limit + 1])):
            continue
        issues.append(dp_issue(
            "DP-39", "P3", node.lineno,
            "csv.Sniffer.sniff() 位置参数超限",
            "sniff(sample, delimiters=None) 只接受两个位置参数，"
            "多传第三个位置参数即 TypeError（不是弃用）",
            "delimiters 改用关键字传入",
        ))
    return issues
def _dp39_self_offset_at(func: ast.Attribute, node: ast.Call,
                         bindings: _ApiBindingIndex) -> int | None:
    receiver = func.value
    if (isinstance(receiver, ast.Call)
            and _dp_call_matches_at(receiver, "Sniffer", "csv", bindings)):
        return 0
    if isinstance(receiver, ast.Name):
        visible_origin = _visible_origin(
            receiver, node, bindings, allow_literal=False)
        if visible_origin == "csv.Sniffer":
            return 1
        if visible_origin == "csv.Sniffer.instance":
            return 0
        found, origin = bindings.origin_at(node, receiver.id)
        if found and origin is None:
            value = bindings.assigned_value_at(node, receiver.id)
            if isinstance(value, ast.Call) and _dp_call_matches_at(
                    value, "Sniffer", "csv", bindings):
                return 0
            if (value is None
                    and (receiver.id == "sniffer"
                         or receiver.id.endswith("_sniffer"))):
                return 0
        return None
    if isinstance(receiver, ast.Attribute):
        if _visible_origin(receiver, node, bindings) == "csv.Sniffer":
            return 1
        if receiver.attr == "sniffer" or receiver.attr.endswith("_sniffer"):
            return 0
    return None
_DP40_REPLACEMENTS = {"encodestring": "encodebytes", "decodestring": "decodebytes"}
_DP40_RULES = tuple(
    _SimpleCallRule(
        "DP-40", func_name, "base64",
        f"使用了base64.{func_name}()",
        f"base64.{func_name}() 3.1起弃用并于3.9移除",
        f"改用 base64.{replacement}()",
    )
    for func_name, replacement in _DP40_REPLACEMENTS.items()
)
@_api_rule
def check_DP40(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for rule in _DP40_RULES:
        issues.extend(_simple_call_rule_issues(tree, rule, bindings))
    return issues
_DP41_SSL_RULE = _SSLLegacyCtorRule(
    ctor_name="IMAP4_SSL", module_name="imaplib", rule_id="DP-41",
    suggestion="使用 ssl_context 参数替代",
    positional_params=((2, "keyfile"), (3, "certfile")),
)
@_api_rule
def check_DP41(tree: ast.AST) -> list[dict[str, Any]]:
    return _check_ssl_legacy_params(tree, _DP41_SSL_RULE)
_DP42_SSL_RULE = _SSLLegacyCtorRule(
    ctor_name="SMTP_SSL", module_name="smtplib", rule_id="DP-42",
    suggestion="使用 context 参数替代",
    positional_params=((3, "keyfile"), (4, "certfile")),
)
@_api_rule
def check_DP42(tree: ast.AST) -> list[dict[str, Any]]:
    return _check_ssl_legacy_params(tree, _DP42_SSL_RULE)
_DP43_RULE = _SimpleCallRule(
    "DP-43", "wrap_socket", "ssl",
    "使用了ssl.wrap_socket()(弃用)",
    "ssl.wrap_socket() 已弃用",
    "改用 SSLContext.wrap_socket()",
)
@_api_rule
def check_DP43(tree: ast.AST) -> list[dict[str, Any]]:
    return _simple_call_rule_issues(tree, _DP43_RULE)
_DP44_RULE = _SimpleCallRule(
    "DP-44", "match_hostname", "ssl",
    "使用了ssl.match_hostname()(已移除)",
    "ssl.match_hostname() 3.7起弃用并于3.12移除",
    "使用 ssl.SSLContext.check_hostname 替代",
)
@_api_rule
def check_DP44(tree: ast.AST) -> list[dict[str, Any]]:
    return _simple_call_rule_issues(tree, _DP44_RULE)
@_api_rule
def check_DP45(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    dp46_owned: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        dp46_owned.update(
            id(decorator)
            for decorator in _legacy_coroutine_decorators(node, bindings)
            if isinstance(decorator, ast.Attribute))
    for node in walk_nodes(tree):
        if not (_dp45_is_coroutine_attr(node, bindings, dp46_owned)
                or _from_module_member_hits(node, "asyncio", {"coroutine"})):
            continue
        issues.append(dp_issue(
            "DP-45", "P2", node.lineno,
            "使用了asyncio.coroutine装饰器",
            "asyncio.coroutine 已弃用(3.8)并移除(3.11)",
            "使用 async def 替代",
        ))
    return issues
def _dp45_is_coroutine_attr(node: Any, bindings: _ApiBindingIndex,
                            dp46_owned: set[int]) -> bool:
    return (isinstance(node, ast.Attribute)
            and isinstance(node.ctx, ast.Load)
            and node.attr == "coroutine"
            and _visible_origin(node.value, node, bindings) == "asyncio"
            and id(node) not in dp46_owned)
def _legacy_coroutine_decorators(fn_node: Any,
                                 bindings: _ApiBindingIndex) -> list:
    decorators = [
        decorator for decorator in fn_node.decorator_list
        if _asyncio_coroutine_decorator_hit(decorator, bindings)
    ]
    if not decorators or not any(
            isinstance(child, ast.YieldFrom)
            for child in iter_own_nodes(fn_node)):
        return []
    return decorators
@_api_rule
def check_DP46(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not _legacy_coroutine_decorators(node, bindings):
            continue
        issues.append(dp_issue(
            "DP-46", "P2", node.lineno,
            "使用了旧式协程写法",
            "@asyncio.coroutine + yield from 已弃用",
            "使用 async def + await 替代",
        ))
    return issues
@_api_rule
def check_DP47(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if not _dp47_is_asyncio_call_at(node, bindings):
            continue
        if any(kw.arg == "loop" for kw in node.keywords):
            issues.append(dp_issue(
                "DP-47", "P3", node.lineno,
                "使用了已移除的loop参数(3.8弃用/3.10移除)",
                "asyncio函数的loop参数已弃用",
                "移除loop参数,使用 asyncio.run() 或当前事件循环",
            ))
    return issues
_DP47_RETAINED_LOOP_APIS = frozenset({
    "Future", "Handle", "Server", "StreamReader", "StreamReaderProtocol",
    "StreamWriter", "Task", "TimerHandle", "all_tasks", "current_task",
    "eager_task_factory", "ensure_future", "run_coroutine_threadsafe",
    "set_event_loop", "wrap_future",
})
def _dp47_is_asyncio_call_at(node: ast.Call,
                             bindings: _ApiBindingIndex) -> bool:
    func = node.func
    if isinstance(func, ast.Attribute):
        if _visible_origin(func.value, node, bindings) != "asyncio":
            return False
        api_name = func.attr
    elif isinstance(func, ast.Name):
        origin = _visible_origin(func, node, bindings, allow_literal=False)
        if origin is None or not origin.startswith("asyncio."):
            return False
        api_name = origin.rpartition(".")[2]
    else:
        return False
    return api_name not in _DP47_RETAINED_LOOP_APIS
@_api_rule
def check_DP48(tree: ast.AST) -> list[dict[str, Any]]:
    lines = _dp48_lines(tree)
    return [
        dp_issue("DP-48", "P2", line,
                 "使用了typing.re旧式泛型",
                 "typing.re 模块已弃用",
                 "使用 re.Pattern / re.Match 替代")
        for line in lines
    ]
def _dp48_lines(tree: ast.AST) -> list[int]:
    import_lines = [node.lineno for node in walk_nodes(tree)
                    if _dp48_is_re_from_import(node)
                    or _dp48_imports_re_namespace(node)]
    if import_lines:
        return import_lines
    bindings = _binding_index(tree)
    return [
        node.lineno
        for node in walk_nodes(tree)
        if (isinstance(node, ast.Attribute) and node.attr == "re"
            and isinstance(node.ctx, ast.Load)
            and _visible_origin(node.value, node, bindings,
                                allow_literal=False) == "typing")
    ]
def _dp48_is_re_from_import(node: Any) -> bool:
    if not (isinstance(node, ast.ImportFrom) and not node.level):
        return False
    module = node.module or ""
    return (_module_chain_matches(module, "typing.re")
            or (module == "typing"
                and any(alias.name == "re" for alias in node.names)))
def _dp48_imports_re_namespace(node: Any) -> bool:
    return (isinstance(node, ast.Import)
            and any(a.name == "typing.re" or a.name.startswith("typing.re.")
                    for a in node.names))
_DP49_LEGACY_MODULES = frozenset({"StringIO", "cStringIO"})
def _dp49_import_issues(node: ast.Import) -> list[dict[str, Any]]:
    return [
        dp_issue(
            "DP-49", "P3", node.lineno,
            f"使用了旧路径导入{alias.name}",
            "应从 io 模块导入 StringIO",
            "from io import StringIO",
        )
        for alias in node.names
        if alias.name in _DP49_LEGACY_MODULES
    ]
def _dp49_from_import_issues(node: ast.ImportFrom) -> list[dict[str, Any]]:
    if node.level or node.module not in _DP49_LEGACY_MODULES:
        return []
    return [dp_issue(
        "DP-49", "P3", node.lineno,
        f"从旧模块{node.module}导入",
        "应从 io 模块导入",
        "from io import StringIO",
    )]
@_api_rule
def check_DP49(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            issues.extend(_dp49_import_issues(node))
        elif isinstance(node, ast.ImportFrom):
            issues.extend(_dp49_from_import_issues(node))
    return issues
_DP50_URLLIB_OLD = frozenset({"urlencode", "quote", "unquote", "urlparse"})
@_api_rule
def check_DP50(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in walk_nodes(tree):
        for name in _from_module_member_hits(node, "urllib", _DP50_URLLIB_OLD):
            issues.append(dp_issue(
                "DP-50", "P1", node.lineno,
                f"从urllib直接导入{name}(旧路径)",
                "应从 urllib.parse 导入",
                f"from urllib.parse import {name}",
            ))
        if not isinstance(node, ast.Call):
            continue
        attr = _module_attr_hit_at(node.func, "urllib", bindings)
        if attr not in _DP50_URLLIB_OLD:
            continue
        issues.append(dp_issue(
            "DP-50", "P1", node.lineno,
            f"调用了urllib.{attr}()旧路径函数",
            "应使用 urllib.parse 模块函数",
            f"from urllib.parse import {attr}",
        ))
    return issues
_DP51_RULE = _ModuleMemberRule(
    "DP-51", "email", "Message", "P2",
    "从email直接导入{member}(旧式)",
    "使用了email.Message(旧式)",
    "应使用 email.message.EmailMessage",
    "from email.message import EmailMessage",
)
@_api_rule
def check_DP51(tree: ast.AST) -> list[dict[str, Any]]:
    return _module_member_rule_issues(tree, _DP51_RULE)
@_api_rule
def check_DP52(tree: ast.AST) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    bindings = _binding_index(tree)
    for node in _iter_calls(tree, "HTTPConnection", "http.client", bindings):
        if any(kw.arg == "strict" for kw in node.keywords):
            issues.append(dp_issue(
                "DP-52", "P3", node.lineno,
                "HTTPConnection使用了已移除的strict参数",
                "strict 参数已于 Python 3.4 移除",
                "移除 strict 参数",
            ))
    return issues
_DP53_RULE = _ModuleMemberRule(
    "DP-53", "configparser", "SafeConfigParser", "P2",
    "使用了configparser.SafeConfigParser",
    "使用了configparser.SafeConfigParser",
    "SafeConfigParser 已在 Python 3.12 移除",
    "改用 configparser.ConfigParser",
)
@_api_rule
def check_DP53(tree: ast.AST) -> list[dict[str, Any]]:
    return _module_member_rule_issues(tree, _DP53_RULE)
def wiring_declarations() -> dict:
    return {"registry": {
        "DP01": check_DP01,
        "DP02": check_DP02,
        "DP03": check_DP03,
        "DP04": check_DP04,
        "DP05": check_DP05,
        "DP06": check_DP06,
        "DP07": check_DP07,
        "DP08": check_DP08,
        "DP09": check_DP09,
        "DP10": check_DP10,
        "DP11": check_DP11,
        "DP12": check_DP12,
        "DP13": check_DP13,
        "DP24": check_DP24,
        "DP32": check_DP32,
        "DP33": check_DP33,
        "DP34": check_DP34,
        "DP36": check_DP36,
        "DP37": check_DP37,
        "DP38": check_DP38,
        "DP39": check_DP39,
        "DP40": check_DP40,
        "DP41": check_DP41,
        "DP42": check_DP42,
        "DP43": check_DP43,
        "DP44": check_DP44,
        "DP45": check_DP45,
        "DP46": check_DP46,
        "DP47": check_DP47,
        "DP48": check_DP48,
        "DP49": check_DP49,
        "DP50": check_DP50,
        "DP51": check_DP51,
        "DP52": check_DP52,
        "DP53": check_DP53,
    }}

from __future__ import annotations

import ast
import logging
import sys
from collections.abc import Iterator
from typing import Any

logger = logging.getLogger(__name__)
_DEFINITION_BOUNDARIES = (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef, ast.Lambda)
def _iter_classes(tree: ast.AST):
    return (n for n in tree_nodes(tree) if isinstance(n, ast.ClassDef))
def _enclosing_lookup_scope(node: ast.AST, parents: dict) -> ast.AST | None:
    cur = parents.get(node)
    while cur is not None:
        if isinstance(cur, (ast.Module, ast.FunctionDef,
                            ast.AsyncFunctionDef, ast.ClassDef)):
            return cur
        cur = parents.get(cur)
    return None
def _outer_lookup_scope(scope: ast.AST, parents: dict) -> ast.AST | None:
    cur = parents.get(scope)
    while cur is not None:
        if isinstance(cur, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef)):
            return cur
        cur = parents.get(cur)
    return None
def _source_position(node: ast.AST) -> tuple[int, int]:
    return getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0)
def _class_scope_index(tree: ast.AST, parents: dict) -> dict[ast.AST, dict[str, list[ast.ClassDef]]]:
    scopes: dict[ast.AST, dict[str, list[ast.ClassDef]]] = {}
    for cls in _iter_classes(tree):
        scope = _enclosing_lookup_scope(cls, parents)
        if scope is None:
            continue
        scopes.setdefault(scope, {}).setdefault(cls.name, []).append(cls)
    for definitions in scopes.values():
        for candidates in definitions.values():
            candidates.sort(key=_source_position)
    return scopes
def _resolve_base(name: str, cls: ast.ClassDef, parents: dict,
                  scopes: dict[ast.AST, dict[str, list[ast.ClassDef]]]) -> ast.ClassDef | None:
    scope = _enclosing_lookup_scope(cls, parents)
    late_bound = False
    while scope is not None:
        candidates = scopes.get(scope, {}).get(name, [])
        if not late_bound:
            candidates = [candidate for candidate in candidates
                          if _source_position(candidate) < _source_position(cls)]
        if candidates:
            candidate = candidates[-1]
            if _class_binding_precedes(
                    cls, name, scope, parents,
                    include_imports=True, after=candidate,
                    before_reference=not late_bound):
                return None
            return candidate
        # 该作用域内没有同名类候选，却存在对 name 的非类绑定（参数、赋值、
        # 导入、嵌套函数名等）：基名在这里已被局部对象遮蔽，不能越过它向外
        # 层解析成同名模块级类。
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if (name in collect_param_names(scope)
                    or _class_binding_precedes(
                        cls, name, scope, parents,
                        include_imports=True, before_reference=False)):
                return None
            late_bound = True
        elif isinstance(scope, ast.ClassDef) and _class_binding_precedes(
                cls, name, scope, parents, include_imports=True):
            return None
        scope = _outer_lookup_scope(scope, parents)
    return None
def _file_class_graph(tree: ast.AST) -> tuple[dict[ast.ClassDef, list[ast.ClassDef]],
                                              dict[ast.ClassDef, list[ast.ClassDef]]]:
    parents = parent_map(tree)
    scopes = _class_scope_index(tree, parents)
    children: dict[ast.ClassDef, list[ast.ClassDef]] = {}
    bases_of: dict[ast.ClassDef, list[ast.ClassDef]] = {}
    for cls in _iter_classes(tree):
        for base in cls.bases:
            base_name = _resolvable_base_name(base)
            if base_name is None:
                continue
            base_cls = _resolve_base(base_name, cls, parents, scopes)
            if base_cls is None or base_cls is cls:
                continue
            bases_of.setdefault(cls, []).append(base_cls)
            children.setdefault(base_cls, []).append(cls)
    return children, bases_of
def _docstring_free_stmts(stmts: list) -> list:
    return [s for s in stmts
            if not (isinstance(s, ast.Expr)
                    and isinstance(s.value, ast.Constant)
                    and isinstance(s.value.value, str))]
def _method_defs(cls: ast.ClassDef) -> list:
    return [m for m in same_scope_bfs_nodes(cls)
            if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))]
def _definition_head_slots(scope: ast.AST) -> list[ast.AST]:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        slots: list[ast.AST] = list(scope.decorator_list)
        slots.extend(scope.args.defaults)
        slots.extend(default for default in scope.args.kw_defaults
                     if default is not None)
        for arg in (*scope.args.posonlyargs, *scope.args.args,
                    *scope.args.kwonlyargs):
            if arg.annotation is not None:
                slots.append(arg.annotation)
        for arg in (scope.args.vararg, scope.args.kwarg):
            if arg is not None and arg.annotation is not None:
                slots.append(arg.annotation)
        if scope.returns is not None:
            slots.append(scope.returns)
        return slots
    if isinstance(scope, ast.Lambda):
        return [*scope.args.defaults,
                *(default for default in scope.args.kw_defaults
                  if default is not None)]
    if isinstance(scope, ast.ClassDef):
        return [*scope.decorator_list, *scope.bases, *scope.keywords]
    return []
def _definition_head_ids(scope: ast.AST) -> set[int]:
    ids: set[int] = set()
    for slot in _definition_head_slots(scope):
        ids.update(id(sub) for sub in walk_nodes(slot))
    return ids
def _slot_walrus_names(slot: ast.AST) -> set[str]:
    if isinstance(slot, _DEFINITION_BOUNDARIES):
        return {name for inner in _definition_head_slots(slot)
                for name in _slot_walrus_names(inner)}
    names = {sub.target.id for sub in same_scope_bfs_nodes(slot)
             if isinstance(sub, ast.NamedExpr)
             and isinstance(sub.target, ast.Name)}
    if isinstance(slot, ast.NamedExpr) and isinstance(slot.target, ast.Name):
        names.add(slot.target.id)
    return names
def _comprehension_target_ids(scope: ast.AST) -> set[int]:
    ids: set[int] = set()
    for sub in subtree_nodes(scope):
        if isinstance(sub, (ast.ListComp, ast.SetComp, ast.DictComp,
                            ast.GeneratorExp)):
            for generator in sub.generators:
                ids.update(id(node) for node in walk_nodes(generator.target))
    return ids
def _add_definition_shadow_binds(sub: ast.AST, binds: set[str]) -> None:
    if not isinstance(sub, ast.Lambda):
        binds.add(sub.name)
    for slot in _definition_head_slots(sub):
        binds |= _slot_walrus_names(slot)
def _apply_match_shadow_binding(sub: ast.AST, binds: set[str]) -> bool:
    if isinstance(sub, (ast.MatchAs, ast.MatchStar)):
        if sub.name:
            binds.add(sub.name)
        return True
    if isinstance(sub, ast.MatchMapping):
        if sub.rest:
            binds.add(sub.rest)
        return True
    return False
def _apply_shadow_binding(sub: ast.AST, binds: set[str], globals_: set[str],
                          nonlocals_: set[str], *, include_imports: bool,
                          head_ids: set[int],
                          comp_target_ids: set[int]) -> None:
    if id(sub) in head_ids:
        return
    if isinstance(sub, ast.Name):
        if (isinstance(sub.ctx, (ast.Store, ast.Del))
                and id(sub) not in comp_target_ids):
            binds.add(sub.id)
        return
    if isinstance(sub, (ast.Import, ast.ImportFrom)):
        if include_imports:
            binds |= import_stmt_binds(sub)
        return
    if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.ClassDef, ast.Lambda)):
        _add_definition_shadow_binds(sub, binds)
        return
    if isinstance(sub, ast.ExceptHandler):
        if sub.name:
            binds.add(sub.name)
        return
    if _apply_match_shadow_binding(sub, binds):
        return
    if isinstance(sub, ast.Global):
        globals_.update(sub.names)
    elif isinstance(sub, ast.Nonlocal):
        nonlocals_.update(sub.names)
def _scope_shadow_names(scope: ast.AST, *,
                        include_imports: bool
                        ) -> tuple[set[str], set[str], set[str]]:
    binds: set[str] = set()
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        binds |= collect_param_names(scope)
    globals_: set[str] = set()
    nonlocals_: set[str] = set()
    head_ids = _definition_head_ids(scope)
    comp_target_ids = _comprehension_target_ids(scope)
    for sub in same_scope_bfs_nodes(scope):
        _apply_shadow_binding(sub, binds, globals_, nonlocals_,
                              include_imports=include_imports,
                              head_ids=head_ids,
                              comp_target_ids=comp_target_ids)
    return binds, globals_, nonlocals_
def _shadow_names_cached(scope: ast.AST, memo: dict, *,
                         include_imports: bool
                         ) -> tuple[set[str], set[str], set[str]]:
    key = (id(scope), include_imports)
    hit = memo.get(key)
    if hit is None:
        hit = _scope_shadow_names(scope, include_imports=include_imports)
        memo[key] = hit
    return hit
def _scope_shadow_state(name: str, scope: ast.AST, memo: dict, *,
                        include_imports: bool = True
                        ) -> tuple[bool, bool]:
    binds, globals_, nonlocals_ = _shadow_names_cached(
        scope, memo, include_imports=include_imports)
    return name in binds and name not in nonlocals_, name in globals_
def _in_comprehension_implicit_scope(node: ast.AST, comp: ast.AST) -> bool:
    first_iter = comp.generators[0].iter if comp.generators else None
    return first_iter is None or not in_subtree(node, first_iter)
def _comp_target_shadows(node: ast.AST, name: str, comp: ast.AST) -> bool:
    return (_in_comprehension_implicit_scope(node, comp)
            and name in comp_target_names(comp))
def _nearest_execution_statement(node: ast.AST, parents: dict) -> ast.AST:
    cur = node
    while cur is not None and not isinstance(cur, (ast.stmt, ast.ExceptHandler)):
        cur = parents.get(cur)
    return cur if cur is not None else node
def _class_binding_precedes(node: ast.AST, name: str, scope: ast.AST,
                            parents: dict, *,
                            include_imports: bool = False,
                            after: ast.AST | None = None,
                            before_reference: bool = True) -> bool:
    reference_pos = _source_position(_nearest_execution_statement(node, parents))
    after_pos = (_source_position(_nearest_execution_statement(after, parents))
                 if after is not None else None)
    head_ids = _definition_head_ids(scope)
    comp_target_ids = _comprehension_target_ids(scope)
    for sub in same_scope_bfs_nodes(scope):
        binds: set[str] = set()
        globals_: set[str] = set()
        nonlocals_: set[str] = set()
        _apply_shadow_binding(
            sub, binds, globals_, nonlocals_,
            include_imports=include_imports,
            head_ids=head_ids, comp_target_ids=comp_target_ids)
        if name not in binds:
            continue
        binding_pos = _source_position(_nearest_execution_statement(sub, parents))
        if ((not before_reference or binding_pos < reference_pos)
                and (after_pos is None or after_pos < binding_pos)):
            return True
    return False
def _import_rebinds_before_reference(node: ast.AST, name: str,
                                     scope: ast.AST, parents: dict) -> bool:
    reference_pos = _source_position(_nearest_execution_statement(node, parents))
    head_ids = _definition_head_ids(scope)
    comp_target_ids = _comprehension_target_ids(scope)
    latest_import: tuple[int, int] | None = None
    latest_other: tuple[int, int] | None = None
    for sub in same_scope_bfs_nodes(scope):
        is_import = (isinstance(sub, (ast.Import, ast.ImportFrom))
                     and name in import_stmt_binds(sub))
        binds: set[str] = set()
        globals_: set[str] = set()
        nonlocals_: set[str] = set()
        _apply_shadow_binding(
            sub, binds, globals_, nonlocals_, include_imports=False,
            head_ids=head_ids, comp_target_ids=comp_target_ids)
        if not is_import and name not in binds:
            continue
        binding_pos = _source_position(_nearest_execution_statement(sub, parents))
        if binding_pos >= reference_pos:
            continue
        if is_import:
            if latest_import is None or binding_pos > latest_import:
                latest_import = binding_pos
        elif latest_other is None or binding_pos > latest_other:
            latest_other = binding_pos
    return (latest_import is not None
            and (latest_other is None or latest_import > latest_other))
def _import_name_shadowed(node: ast.AST, name: str, parents: dict,
                          memo: dict) -> bool:
    cur = parents.get(node)
    passed_function = False
    while cur is not None:
        hit = False
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            rebound, is_global = _scope_shadow_state(
                name, cur, memo, include_imports=False)
            if is_global:
                return False
            hit = rebound and not _import_rebinds_before_reference(
                node, name, cur, parents)
            passed_function = True
        elif isinstance(cur, ast.ClassDef) and not passed_function:
            hit, _is_global = _scope_shadow_state(
                name, cur, memo, include_imports=False)
            if hit:
                hit = (_class_binding_precedes(node, name, cur, parents)
                       and not _import_rebinds_before_reference(
                           node, name, cur, parents))
        elif isinstance(cur, (ast.ListComp, ast.SetComp, ast.DictComp,
                              ast.GeneratorExp)):
            hit = _comp_target_shadows(node, name, cur)
            if _in_comprehension_implicit_scope(node, cur):
                passed_function = True
        if hit:
            return True
        cur = parents.get(cur)
    return False
def _collect_scope_import_aliases(scope: ast.AST) -> dict:
    aliases: dict = {}
    for node in iter_own_nodes(scope):
        if isinstance(node, ast.Import):
            aliases.update({
                a.asname or a.name.split('.')[0]:
                    a.name if a.asname else a.name.split('.')[0]
                for a in node.names
            })
        elif isinstance(node, ast.ImportFrom) and node.module:
            aliases.update({a.asname or a.name: (node.module, a.name)
                            for a in node.names})
    return aliases
def _iter_import_scopes(tree: ast.Module) -> Iterator[ast.AST]:
    yield tree
    for node in tree_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            yield node
def _enclosing_import_aliases(scope: ast.AST, parents: dict,
                              module_aliases: dict) -> dict:
    chain: list[ast.AST] = []
    cur = scope
    while cur is not None and not isinstance(cur, ast.Module):
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            chain.append(cur)
        cur = parents.get(cur)
    aliases = dict(module_aliases)
    for node in reversed(chain):
        if isinstance(node, ast.ClassDef) and node is not scope:
            continue
        aliases.update(_collect_scope_import_aliases(node))
    return aliases
def _alias_refs(aliases: dict, module: str, attr: str | None = None) -> set[str]:
    target = (module, attr) if attr else module
    return {a for a, m in aliases.items() if m == target}
def _ref_sets_from_aliases(aliases: dict, module: str,
                           attr: str) -> tuple[set[str], set[str]]:
    return _alias_refs(aliases, module), _alias_refs(aliases, module, attr)
def _base_name(expr: ast.expr) -> str | None:
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Attribute):
        return expr.attr
    if isinstance(expr, ast.Subscript):
        return _base_name(expr.value)
    return None
def _resolvable_base_name(expr: ast.expr) -> str | None:
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Subscript):
        return _resolvable_base_name(expr.value)
    return None
def _is_receiver_ref(node: ast.AST, receiver: str) -> bool:
    return bool(receiver) and isinstance(node, ast.Name) and node.id == receiver
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ''
def _issue(check_id: str, severity: DiagnoseSeverity, message: str,
           line: int, suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(check_id=check_id, severity=severity, message=message,
                         line=line, suggestion=suggestion, auto_fixable=False)
def _log_hits(check_id: str, label: str, issues: list, filepath: str) -> None:
    if issues:
        logger.debug("[%s] %s 命中 %d 处: %s", check_id, label,
                     len(issues), filepath or "<inline>")
def _finish(check_id: str, label: str, issues: list, filepath: str) -> list:
    _log_hits(check_id, label, issues, filepath)
    return issues
def _iter_class_methods(tree: ast.Module):
    for cls in tree_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        for fn in _method_defs(cls):
            yield cls, fn
def _class_owned_inits(cls: ast.ClassDef):
    for item in _method_defs(cls):
        if item.name == '__init__':
            yield item
_STDLIB_ABSTRACT_BASES = frozenset({'ABC', 'ABCMeta', 'Protocol'})
_STDLIB_ENUM_BASES = frozenset({'Enum', 'IntEnum', 'StrEnum', 'Flag', 'IntFlag'})
_AUTO_FIELD_BASE_NAMES = frozenset({
    'NamedTuple', 'TypedDict',
}) | _STDLIB_ABSTRACT_BASES | _STDLIB_ENUM_BASES
_STDLIB_CONTAINER_ABC_BASES = frozenset({
    'Container', 'Hashable', 'Iterable', 'Iterator', 'Reversible',
    'Generator', 'Awaitable', 'Coroutine', 'AsyncIterable', 'AsyncIterator',
    'Sized', 'Callable', 'Collection', 'ByteString',
    'Mapping', 'MutableMapping', 'Sequence', 'MutableSequence',
    'Set', 'MutableSet',
})
_B53_STATELESS_BASE_NAMES = frozenset({
    'object', 'type', 'NodeVisitor', 'NodeTransformer', 'AST', 'Generic',
    'NamedTuple', 'TypedDict', 'Exception', 'BaseException',
    'RuntimeError', 'ValueError', 'TypeError', 'OSError',
    'dict', 'list', 'set', 'frozenset', 'tuple', 'str',
    'bytes', 'bytearray', 'int', 'float', 'complex',
}) | _STDLIB_ABSTRACT_BASES | _STDLIB_ENUM_BASES | _STDLIB_CONTAINER_ABC_BASES
_EXEMPT_TYPE_SUFFIXES = ('Mixin', 'Visitor', 'Transformer')
def _is_composition_type_name(name: str) -> bool:
    return name.endswith(_EXEMPT_TYPE_SUFFIXES)
_MUTABLE_NODE_KINDS = {
    ast.List: 'list', ast.Dict: 'dict', ast.Set: 'set',
    ast.ListComp: 'list', ast.DictComp: 'dict', ast.SetComp: 'set',
}
_MUTABLE_CTORS = frozenset({'list', 'dict', 'set', 'bytearray'})
_MUTABLE_LITERAL_NODES = tuple(_MUTABLE_NODE_KINDS)
_MAPPING_NODE_TYPES = tuple(
    node_type for node_type, kind in _MUTABLE_NODE_KINDS.items()
    if kind in ('dict', 'set'))
def _is_mutable_ctor(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in _MUTABLE_CTORS)
def _is_list_ctor(node: ast.AST) -> bool:
    return _is_mutable_ctor(node) and node.func.id == 'list'
def _is_tuple_ctor(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'tuple')
def _iterable_projection_has_mutable_elem(source: ast.AST) -> bool:
    if isinstance(source, (ast.List, ast.Tuple)):
        return any(_is_mutable_expr(element) for element in source.elts)
    if isinstance(source, (ast.ListComp, ast.GeneratorExp)):
        return _is_mutable_expr(source.elt)
    if _is_list_ctor(source) or _is_tuple_ctor(source):
        return _sequence_ctor_has_mutable_elem(source)
    return False
def _sequence_ctor_has_mutable_elem(node: ast.Call) -> bool:
    if len(node.args) != 1 or node.keywords:
        return False
    return _iterable_projection_has_mutable_elem(node.args[0])
def _mutable_children(node: ast.AST) -> tuple:
    if isinstance(node, ast.Tuple):
        return tuple(node.elts)
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mult)):
        return (node.left, node.right)
    return ()
def _is_mutable_expr(e: ast.AST) -> bool:
    if isinstance(e, _MUTABLE_LITERAL_NODES):
        return True
    if _is_mutable_ctor(e):
        return True
    if _is_tuple_ctor(e):
        return _sequence_ctor_has_mutable_elem(e)
    if isinstance(e, ast.BinOp) and isinstance(e.op, ast.BitOr):
        return bool(_mutable_carrier_kind(e))
    if isinstance(e, ast.Starred):
        return _iterable_projection_has_mutable_elem(e.value)
    if isinstance(e, ast.BinOp) and isinstance(e.op, ast.Mult):
        left_kind = _replication_carrier_kind(e.left)
        right_kind = _replication_carrier_kind(e.right)
        if not (left_kind and right_kind) and (left_kind or right_kind) == 'tuple':
            count_node = e.right if left_kind else e.left
            repeat_count = _b24_static_repeat_count(count_node)
            if repeat_count is not None and repeat_count <= 0:
                return False
    return any(_is_mutable_expr(child) for child in _mutable_children(e))
def _replication_carrier_kind(node: ast.AST) -> str:
    if (_MUTABLE_NODE_KINDS.get(type(node)) == 'list'
            or _is_list_ctor(node)):
        return 'list'
    if (isinstance(node, ast.Tuple)
            and any(_is_mutable_expr(elem) for elem in node.elts)):
        return 'tuple'
    if _is_tuple_ctor(node) and _sequence_ctor_has_mutable_elem(node):
        return 'tuple'
    return ''
def _replication_kind(node: ast.AST) -> str:
    if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Mult):
        return ''
    left_kind = _replication_carrier_kind(node.left)
    right_kind = _replication_carrier_kind(node.right)
    if left_kind and right_kind:
        return ''
    kind = left_kind or right_kind
    if kind == 'tuple':
        count_node = node.right if left_kind else node.left
        repeat_count = _b24_static_repeat_count(count_node)
        if repeat_count is not None and repeat_count <= 0:
            return ''
    return kind
def _mutable_carrier_kind(node: ast.AST) -> str:
    kind = _MUTABLE_NODE_KINDS.get(type(node))
    if kind is not None:
        return kind
    if _is_mutable_ctor(node):
        return node.func.id
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return (_mutable_carrier_kind(node.left)
                or _mutable_carrier_kind(node.right))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left_kind = _mutable_carrier_kind(node.left)
        right_kind = _mutable_carrier_kind(node.right)
        if left_kind == right_kind and left_kind in {'dict', 'set'}:
            return left_kind
        return ''
    return _replication_carrier_kind(node) or _replication_kind(node)
def _container_assign_parts(stmt: ast.stmt) -> tuple[list[ast.expr], ast.expr] | None:
    if isinstance(stmt, ast.Assign):
        return stmt.targets, stmt.value
    if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        return [stmt.target], stmt.value
    return None
def _unpack_target_value(
    target: ast.expr, value: ast.expr,
) -> list[tuple[ast.expr, ast.expr]]:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and not any(isinstance(elt, ast.Starred) for elt in value.elts)):
        starred = [index for index, elt in enumerate(target.elts)
                   if isinstance(elt, ast.Starred)]
        if not starred and len(target.elts) == len(value.elts):
            pairs: list[tuple[ast.expr, ast.expr]] = []
            for sub_target, sub_value in zip(
                    target.elts, value.elts, strict=True):
                pairs.extend(_unpack_target_value(sub_target, sub_value))
            return pairs
        if len(starred) == 1:
            star_index = starred[0]
            trailing_count = len(target.elts) - star_index - 1
            starred_count = len(value.elts) - star_index - trailing_count
            if starred_count >= 0:
                pairs = []
                for index in range(star_index):
                    pairs.extend(_unpack_target_value(
                        target.elts[index], value.elts[index]))
                packed = ast.copy_location(ast.List(
                    elts=value.elts[star_index:star_index + starred_count],
                    ctx=ast.Load(),
                ), value)
                pairs.extend(_unpack_target_value(
                    target.elts[star_index].value, packed))
                for index in range(star_index + 1, len(target.elts)):
                    value_index = index + starred_count - 1
                    pairs.extend(_unpack_target_value(
                        target.elts[index], value.elts[value_index]))
                return pairs
    return [(target, value)]
def _assign_value_pairs(
    targets: list[ast.expr], value: ast.expr,
) -> list[tuple[ast.expr, ast.expr]]:
    pairs: list[tuple[ast.expr, ast.expr]] = []
    for target in targets:
        pairs.extend(_unpack_target_value(target, value))
    return pairs
def _receiver_attr_name(target: ast.expr, receiver: str) -> str | None:
    if (bool(receiver) and isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id == receiver):
        return target.attr
    return None
def _iter_receiver_attr_targets(target: ast.expr, receiver: str):
    if isinstance(target, (ast.Tuple, ast.List)):
        for elt in target.elts:
            yield from _iter_receiver_attr_targets(elt, receiver)
        return
    if isinstance(target, ast.Starred):
        yield from _iter_receiver_attr_targets(target.value, receiver)
        return
    attr = _receiver_attr_name(target, receiver)
    if attr is not None:
        yield attr
def _default_values(node: ast.AST):
    yield from node.args.defaults
    yield from (d for d in node.args.kw_defaults if d is not None)
def detect_b01_mutable_default(
        code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES,
        filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        _owner = getattr(node, 'name', '<lambda>')
        for default in _default_values(node):
            kind = _mutable_carrier_kind(default)
            if kind:
                issues.append(_issue(
                    'B01', DiagnoseSeverity.ERROR,
                    f"可变默认参数: 函数 '{_owner}' 使用 {kind} 作为默认值，跨调用共享可变状态",
                    default.lineno, '改用 None 作为默认值，函数体内再初始化'))
    return _finish('B01', 'mutable_default', issues, filepath)
def _b12_attr_exempt(name: str) -> bool:
    return is_dunder_name(name) or name.isupper()
def _iter_class_attr_assigns(cls: ast.ClassDef):
    for stmt in same_scope_bfs_nodes(cls):
        parts = _container_assign_parts(stmt)
        if parts is None:
            continue
        if (isinstance(stmt, ast.AnnAssign)
                and _mm01_annotation_is_classvar(stmt.annotation)):
            continue
        targets, value = parts
        for target, bound_value in _assign_value_pairs(targets, value):
            kind = _mutable_carrier_kind(bound_value)
            if not kind:
                continue
            for name, _lineno, _col in iter_target_bindings(target):
                if not _b12_attr_exempt(name):
                    yield name, kind, stmt.lineno
def detect_b12_mutable_class_attr(
        code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES,
        filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for cls in tree_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        for name, kind, lineno in _iter_class_attr_assigns(cls):
            issues.append(_issue(
                'B12', DiagnoseSeverity.WARN,
                f"可变类属性: 类 '{cls.name}' 的 '{name}' 为 {kind}，所有实例共享同一可变对象",
                lineno, f"在 __init__ 中初始化实例属性（self.{name} = ...）"))
    return _finish('B12', 'mutable_class_attr', issues, filepath)
def _b24_has_mutable_elem(operand: ast.expr) -> bool:
    if isinstance(operand, (ast.List, ast.Tuple)):
        return any(_is_mutable_expr(elem) for elem in operand.elts)
    if isinstance(operand, ast.ListComp):
        return _is_mutable_expr(operand.elt)
    if _is_list_ctor(operand) or _is_tuple_ctor(operand):
        return _sequence_ctor_has_mutable_elem(operand)
    return _is_mapping_carrier(operand)
_B24_CONTAINER_TYPES = (*_MUTABLE_LITERAL_NODES, ast.Tuple)
def _is_mapping_carrier(node: ast.AST) -> bool:
    if isinstance(node, _MAPPING_NODE_TYPES):
        return True
    return _is_mutable_ctor(node) and node.func.id in ('dict', 'set')
def _b24_container_operand(node: ast.BinOp) -> tuple[ast.expr, bool] | None:
    left_container = (isinstance(node.left, _B24_CONTAINER_TYPES)
                      or _is_mapping_carrier(node.left)
                      or _is_list_ctor(node.left)
                      or _is_tuple_ctor(node.left))
    right_container = (isinstance(node.right, _B24_CONTAINER_TYPES)
                       or _is_mapping_carrier(node.right)
                       or _is_list_ctor(node.right)
                       or _is_tuple_ctor(node.right))
    if left_container and right_container:
        return node.left, True
    if left_container == right_container:
        return None
    return (node.left if left_container else node.right), False
def _b24_form_message(operand: ast.expr, invalid_operands: bool,
                      invalid_repeat: bool = False) -> tuple[str, str]:
    if invalid_operands:
        return (
            '必然 TypeError: 两个容器不能相乘，重复次数必须是整数',
            '将一个操作数改为整数重复次数；若意在组合容器，改用拼接或推导式')
    if _is_mapping_carrier(operand):
        return (
            '必然 TypeError: dict/set 不支持序列乘法复制，该表达式运行时必抛 TypeError',
            '改用推导式构造，如 {k: [] for k in keys} 或 {i: 0 for i in range(n)}')
    if invalid_repeat:
        return (
            '必然 TypeError: 序列重复次数必须是整数，当前静态操作数不是整数',
            '将重复次数改为 int；若需要复制含可变元素的容器，再用推导式创建独立副本')
    return (
        '可变对象共享: 使用乘法复制含可变元素的容器，所有副本指向同一对象，修改一处影响全部',
        '改用列表推导式创建独立副本，如 [[0 for _ in range(n)] for _ in range(m)]')
def _b24_static_repeat_count(node: ast.AST) -> int | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return int(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = _b24_static_repeat_count(node.operand)
        if value is not None:
            return value if isinstance(node.op, ast.UAdd) else -value
    return None
def _b24_static_invalid_repeat(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return not isinstance(node.value, int)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        return _b24_static_invalid_repeat(node.operand)
    return False
def detect_b24_mutable_replication(
        code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES,
        filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Mult):
            continue
        form = _b24_container_operand(node)
        if form is None:
            continue
        mutable_operand, invalid_operands = form
        invalid_repeat = False
        if not invalid_operands:
            count_node = (node.right if mutable_operand is node.left
                          else node.left)
            mapping_carrier = _is_mapping_carrier(mutable_operand)
            invalid_repeat = (not mapping_carrier
                              and _b24_static_invalid_repeat(count_node))
            if (not invalid_repeat
                    and not _b24_has_mutable_elem(mutable_operand)):
                continue
            repeat_count = _b24_static_repeat_count(count_node)
            if (repeat_count is not None and repeat_count <= 1
                    and not mapping_carrier):
                continue
        message, suggestion = _b24_form_message(
            mutable_operand, invalid_operands, invalid_repeat)
        issues.append(_issue(
            'B24', DiagnoseSeverity.ERROR, message, node.lineno, suggestion))
    return _finish('B24', 'mutable_replication', issues, filepath)
def _b28_leaked_returns(node: ast.AST, mutable_attrs: set[str],
                        receiver: str):
    for ret in iter_own_nodes(node):
        if not isinstance(ret, ast.Return):
            continue
        val = ret.value
        if (isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name)
                and val.value.id == receiver and val.attr in mutable_attrs):
            yield val.attr, ret.lineno
def _collect_init_mutable_attrs(cls: ast.ClassDef) -> set[str]:
    attrs: set[str] = set()
    for node in same_scope_bfs_nodes(cls):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name == '__init__'):
            receiver = _first_positional_name(node)
            if receiver is not None:
                _apply_init_attr_binding(node.body, attrs, receiver)
    return attrs
def _bind_receiver_attrs(targets: list[ast.expr], mutable: bool,
                         attrs: set[str], receiver: str) -> None:
    for target in targets:
        for attr in _iter_receiver_attr_targets(target, receiver):
            if mutable:
                attrs.add(attr)
            else:
                attrs.discard(attr)
_TRY_STATEMENTS = (ast.Try,) + (
    (ast.TryStar,) if sys.version_info >= (3, 11) else ())
def _apply_init_attr_binding(body: list[ast.stmt], attrs: set[str],
                             receiver: str) -> None:
    for stmt in body:
        parts = _container_assign_parts(stmt)
        if parts is not None:
            targets, value = parts
            _bind_assign_pairs(_assign_value_pairs(targets, value), attrs,
                              receiver)
            continue
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            continue
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            _apply_init_attr_binding(stmt.body, attrs, receiver)
            continue
        if isinstance(stmt, ast.If):
            branches = [stmt.body, stmt.orelse]
        elif isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            loop_states = _init_branch_states(
                [stmt.body, []], attrs, receiver)
            else_states = set(loop_states)
            _apply_init_attr_binding(stmt.orelse, else_states, receiver)
            attrs.clear()
            attrs.update(loop_states | else_states)
            continue
        elif isinstance(stmt, _TRY_STATEMENTS):
            body_states = set(attrs)
            _apply_init_attr_binding(stmt.body, body_states, receiver)
            normal_states = set(body_states)
            _apply_init_attr_binding(stmt.orelse, normal_states, receiver)
            states = [normal_states]
            handler_entry = attrs | body_states
            for handler in stmt.handlers:
                handler_states = set(handler_entry)
                _apply_init_attr_binding(
                    handler.body, handler_states, receiver)
                states.append(handler_states)
            attrs.clear()
            attrs.update(set().union(*states))
            _apply_init_attr_binding(stmt.finalbody, attrs, receiver)
            continue
        elif isinstance(stmt, ast.Match):
            branches = [case.body for case in stmt.cases]
            if not any(isinstance(case.pattern, ast.MatchAs)
                       and case.pattern.pattern is None
                       and case.pattern.name is None and case.guard is None
                       for case in stmt.cases):
                branches.append([])
        else:
            continue
        merged = _init_branch_states(branches, attrs, receiver)
        attrs.clear()
        attrs.update(merged)
def _init_branch_states(branches: list[list[ast.stmt]], attrs: set[str],
                        receiver: str) -> set[str]:
    states: list[set[str]] = []
    for branch in branches:
        branch_states = set(attrs)
        _apply_init_attr_binding(branch, branch_states, receiver)
        states.append(branch_states)
    return set().union(*states) if states else set(attrs)
def _bind_assign_pairs(
    pairs: list[tuple[ast.expr, ast.expr]], attrs: set[str], receiver: str,
) -> None:
    for target, bound_value in pairs:
        _bind_receiver_attrs(
            [target], _mutable_carrier_kind(bound_value) != '', attrs, receiver)
def _is_leak_method(node: ast.AST, owned_inits: set) -> bool:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    return node not in owned_inits
def _iter_class_leaks(cls: ast.ClassDef):
    mutable_attrs = _collect_init_mutable_attrs(cls)
    if not mutable_attrs:
        return
    owned_inits = set(_class_owned_inits(cls))
    seen: set[tuple[int, str, int]] = set()
    for method in _method_defs(cls):
        if not _is_leak_method(method, owned_inits):
            continue
        receiver = _implicit_receiver_name(method, is_method=True)
        if receiver is None:
            continue
        for attr, lineno in _b28_leaked_returns(
                method, mutable_attrs, receiver):
            key = (id(method), attr, lineno)
            if key in seen:
                continue
            seen.add(key)
            yield method, attr, lineno
def detect_b28_internal_mutable_return(
        code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES,
        filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for cls in tree_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        for node, attr, lineno in _iter_class_leaks(cls):
            issues.append(_issue(
                'B28', DiagnoseSeverity.WARN,
                f"返回内部可变状态: 方法 '{node.name}' 直接返回 self.{attr}，调用方可绕过封装修改内部 {attr}",
                lineno,
                f"返回副本（如 self.{attr}.copy() 或 list(self.{attr})），或改为只读视图/不可变类型"))
    return _finish('B28', 'internal_mutable_return', issues, filepath)
def _iter_functions(tree: ast.AST):
    return (n for n in tree_nodes(tree)
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))
_BRANCHING_NODES = (ast.If, ast.IfExp, ast.ExceptHandler) + (
    (ast.Match,) if sys.version_info >= (3, 10) else ())
def detect_o01_single_impl_abstraction(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    children, bases_of = _file_class_graph(tree)
    for cls in _iter_classes(tree):
        if not _is_abstract_class(cls):
            continue
        if _o01_concrete_impl_count(cls, children, bases_of) == 1:
            issues.append(_issue('O01', DiagnoseSeverity.WARN, f"抽象类 '{cls.name}' 仅有一个具体子类，抽象层缺少多态变化", cls.lineno, f"若 '{cls.name}' 只有一种实现，可移除抽象层直接使用具体类，避免过度设计"))
    return _finish('O01', '单实现抽象', issues, filepath)
def _o01_class_mro(
        cls: ast.ClassDef, bases_of: dict,
        visiting: frozenset = frozenset()) -> list[ast.ClassDef]:
    if cls in visiting:
        return []
    bases = bases_of.get(cls, [])
    next_visiting = visiting | {cls}
    linearizations: list[list[ast.ClassDef]] = []
    for base in bases:
        linearization = _o01_class_mro(base, bases_of, next_visiting)
        if not linearization:
            return []
        linearizations.append(linearization)
    sequences = [list(mro) for mro in linearizations] + [list(bases)]
    merged: list[ast.ClassDef] = []
    while any(sequences):
        candidate = next((
            sequence[0] for sequence in sequences if sequence
            and not any(sequence[0] in other[1:]
                        for other in sequences if other)
        ), None)
        if candidate is None:
            return []
        merged.append(candidate)
        for sequence in sequences:
            if sequence and sequence[0] is candidate:
                sequence.pop(0)
    return [cls, *merged]
def _o01_value_is_abstract(value: ast.AST) -> bool:
    if not isinstance(value, ast.Call):
        return False
    name = ast_name(value.func)
    if name == 'abstractmethod':
        return True
    if name not in {'staticmethod', 'classmethod', 'property'}:
        return False
    values = [*value.args, *(kw.value for kw in value.keywords)]
    return any(_o01_value_is_abstract(item) for item in values)
def _o01_own_bindings(cls: ast.ClassDef) -> dict[str, bool]:
    events: list[tuple[tuple[int, int], str, bool]] = []
    for node in same_scope_bfs_nodes(cls):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            is_abstract = any(ast_name(dec) == 'abstractmethod'
                              for dec in node.decorator_list)
            events.append((_source_position(node), node.name, is_abstract))
            continue
        if isinstance(node, ast.ClassDef):
            events.append((_source_position(node), node.name, False))
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            events.extend((_source_position(node), name, False)
                          for name in import_stmt_binds(node))
            continue
        parts = _container_assign_parts(node)
        if parts is None:
            continue
        targets, value = parts
        is_abstract = _o01_value_is_abstract(value)
        for target in targets:
            for name, _lineno, _col in iter_target_bindings(target):
                events.append((_source_position(node), name, is_abstract))
    bindings: dict[str, bool] = {}
    for _position, name, is_abstract in sorted(events):
        bindings[name] = is_abstract
    return bindings
def _o01_abstract_method_names(
        cls: ast.ClassDef, bases_of: dict, memo: dict,
        visiting: frozenset = frozenset()) -> set[str]:
    if cls in memo:
        return memo[cls]
    abstract: set[str] = set()
    resolved: set[str] = set()
    for owner in _o01_class_mro(cls, bases_of, visiting):
        for name, is_abstract in _o01_own_bindings(owner).items():
            if name in resolved:
                continue
            resolved.add(name)
            if is_abstract:
                abstract.add(name)
    memo[cls] = abstract
    return abstract
def _o01_concrete_impl_count(
        cls: ast.ClassDef, children: dict[ast.ClassDef, list[ast.ClassDef]],
        bases_of: dict[ast.ClassDef, list[ast.ClassDef]]) -> int:
    impl_count = 0
    seen = {cls}
    queue = [cls]
    memo: dict = {}
    while queue:
        cur = queue.pop()
        for child in children.get(cur, []):
            if child in seen:
                continue
            seen.add(child)
            queue.append(child)
            abstract_names = _o01_abstract_method_names(
                child, bases_of, memo)
            is_protocol = any(
                ast_name(base) == 'Protocol' for base in child.bases)
            if not is_protocol and not abstract_names:
                impl_count += 1
    return impl_count
def _o02_is_factory_name(name: str) -> bool:
    name_lower = name.lower()
    return (name_lower in ('create', 'factory', 'make', 'build')
            or name_lower.startswith(('create_', 'make_', 'build_'))
            or 'factory' in name_lower)
def _o02_single_returned_type(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str | None:
    returns = [n for n in same_scope_bfs_nodes(node)
               if isinstance(n, ast.Return) and n.value is not None]
    if not returns or _has_branching(node):
        return None
    returned = _returned_class_names(returns)
    return next(iter(returned)) if len(returned) == 1 else None
def _returned_class_names(returns: list[ast.Return]) -> set[str]:
    names = {_call_class_name(r.value) for r in returns}
    if '' in names:
        return set()
    return names - {'cls', 'self'}
def detect_o02_branchless_factory(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for node in _iter_functions(tree):
        if not _o02_is_factory_name(node.name):
            continue
        cls_name = _o02_single_returned_type(node)
        if cls_name is None:
            continue
        issues.append(_issue('O02', DiagnoseSeverity.WARN, f"工厂方法 '{node.name}' 仅返回单一类型 '{cls_name}'，无运行时选择逻辑", node.lineno, f"若 '{node.name}' 无多态选择，可直接实例化 '{cls_name}'，移除多余工厂间接层"))
    return _finish('O02', '无分支工厂', issues, filepath)
def _o03_signature_locked(node: ast.AST) -> bool:
    return is_dunder_name(node.name) and node.name != '__init__'
def _o03_interface_stub(node: ast.AST) -> bool:
    body = [stmt for stmt in getattr(node, "body", ()) or ()
            if not is_docstring_stmt(stmt)]
    if not body or all(is_placeholder_stmt(stmt) for stmt in body):
        return True
    return len(body) == 1 and isinstance(body[0], ast.Raise)
def _implicit_receiver_name(node: ast.AST, *, is_method: bool) -> str | None:
    if not is_method or is_static_method(node):
        return None
    return _first_positional_name(node)
def _first_positional_name(node: ast.AST) -> str | None:
    positional = (*node.args.posonlyargs, *node.args.args)
    return positional[0].arg if positional else None
def detect_o03_unused_param(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    method_ids = {id(fn) for _cls, fn in _iter_class_methods(tree)}
    for node in _iter_functions(tree):
        if _o03_signature_locked(node) or _o03_interface_stub(node):
            continue
        loaded = _collect_loaded_names(node)
        receiver_name = _implicit_receiver_name(
            node, is_method=id(node) in method_ids)
        for pname in collect_param_names(node):
            if pname == receiver_name or pname.startswith('_'):
                continue
            if pname in loaded:
                continue
            issues.append(_issue('O03', DiagnoseSeverity.WARN, f"未使用参数: 函数 '{node.name}' 的参数 '{pname}' 从未被使用", node.lineno, '移除未使用参数，或以下划线前缀标记有意保留'))
    return _finish('O03', '未使用参数', issues, filepath)
def detect_o04_trivial_wrapper(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    method_owners = {id(fn): cls.name for cls, fn in _iter_class_methods(tree)}
    for node in _iter_functions(tree):
        if node.name.startswith('_'):
            continue
        if any(ast_name(decorator) not in ('staticmethod', 'classmethod')
               for decorator in node.decorator_list):
            continue
        params = collect_param_names(node)
        returns = [s for s in same_scope_bfs_nodes(node) if isinstance(s, ast.Return)]
        if len(returns) != 1:
            continue
        ret = returns[0]
        returned_value = ret.value
        if isinstance(node, ast.AsyncFunctionDef):
            if not isinstance(returned_value, ast.Await):
                continue
            returned_value = returned_value.value
        if not isinstance(returned_value, ast.Call):
            continue
        if _is_pure_forward(
                node, returned_value, params,
                is_method=id(node) in method_owners,
                owner_name=method_owners.get(id(node))):
            issues.append(_issue('O04', DiagnoseSeverity.WARN, f"纯转发包装: 函数 '{node.name}' 仅原样转发调用，无额外逻辑，是多余间接层", node.lineno, '直接调用底层函数，或为包装层补充真实逻辑（校验/转换/缓存）'))
    return _finish('O04', '平凡包装', issues, filepath)
def _is_pure_static_class(cls: ast.ClassDef) -> bool:
    methods = _method_defs(cls)
    if not methods:
        return False
    if not all(is_static_method(m) or _is_classmethod(m) for m in methods):
        return False
    return not _class_has_instance_state(cls)
def detect_o05_static_method_class(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    children, _bases_of = _file_class_graph(tree)
    for cls in _iter_classes(tree):
        if cls.bases or children.get(cls):
            continue
        if _is_composition_type_name(cls.name):
            continue
        if _is_enum_class(cls):
            continue
        if _is_abstract_class(cls):
            continue
        if _has_class_creation_hooks(cls):
            continue
        if not _is_pure_static_class(cls):
            continue
        issues.append(_issue('O05', DiagnoseSeverity.WARN, f"纯静态方法类: 类 '{cls.name}' 的方法均为 staticmethod/classmethod 且无实例状态，应改为模块级函数", cls.lineno, f"将 '{cls.name}' 的方法提升为模块层普通函数，或用模块/命名空间组织"))
    return _finish('O05', '静态方法类', issues, filepath)
def _single_instance_method(cls: ast.ClassDef):
    if any(is_dunder_name(method.name) and method.name != '__init__'
           for method in _method_defs(cls)):
        return None
    methods = _real_methods(cls)
    if len(methods) != 1:
        return None
    method = methods[0]
    if is_static_method(method) or _is_classmethod(method):
        return None
    if _is_property_like(method):
        return None
    if _class_has_instance_state(cls):
        return None
    return method
def detect_o06_single_method_class(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    children, _bases_of = _file_class_graph(tree)
    for cls in _iter_classes(tree):
        if cls.bases:
            continue
        if children.get(cls):
            continue
        if _is_composition_type_name(cls.name):
            continue
        if _is_abstract_class(cls):
            continue
        if _has_class_creation_hooks(cls):
            continue
        m = _single_instance_method(cls)
        if m is None:
            continue
        issues.append(_issue('O06', DiagnoseSeverity.WARN, f"单一方法类: 类 '{cls.name}' 仅含一个方法 '{m.name}' 且无状态、无继承，应改为函数", cls.lineno, f"若 '{cls.name}' 无需维护状态，改为模块级函数 '{m.name}' 更简洁"))
    return _finish('O06', '单方法类', issues, filepath)
def _inherit_depth(cls: ast.ClassDef,
                   bases_of: dict[ast.ClassDef, list[ast.ClassDef]],
                   visiting: frozenset) -> int:
    if cls in visiting:
        return 0
    bases = bases_of.get(cls, [])
    if not bases:
        return 0
    visiting = visiting | {cls}
    return 1 + max(_inherit_depth(base, bases_of, visiting)
                   for base in bases)
def detect_o07_deep_inheritance(
        code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES,
        filepath: str = _DEFAULT_FILEPATH, max_inheritance_depth: int = 3) -> list[DiagnoseIssue]:
    if (isinstance(max_inheritance_depth, bool)
            or not isinstance(max_inheritance_depth, int)
            or max_inheritance_depth < 0):
        raise ValueError('max_inheritance_depth 须为非负 int')
    issues: list[DiagnoseIssue] = []
    _children, bases_of = _file_class_graph(tree)
    for cls in _iter_classes(tree):
        d = _inherit_depth(cls, bases_of, frozenset())
        if d > max_inheritance_depth:
            issues.append(_issue('O07', DiagnoseSeverity.WARN, f"深层继承: 类 '{cls.name}' 继承链深度 {d}，超过项目预算 {max_inheritance_depth} 层，过度继承增加脆弱性与认知负担", cls.lineno, "改用组合（composition）替代继承，或合并中间继承层级"))
    return _finish('O07', '深层继承', issues, filepath)
def detect_o08_redundant_getter_setter(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for cls in _iter_classes(tree):
        for method in _method_defs(cls):
            issue = _o08_method_issue(cls, method)
            if issue is not None:
                issues.append(issue)
    return _finish('O08', '冗余 getter/setter', issues, filepath)
def _o08_method_issue(cls: ast.ClassDef, method: ast.AST) -> DiagnoseIssue | None:
    if method.name == '__init__':
        return None
    if (_is_property_like(method) or is_static_method(method)
            or _is_classmethod(method)):
        return None
    receiver = _first_positional_name(method)
    if receiver is None:
        return None
    if method.name.startswith('get_'):
        attr = method.name[4:]
        if _is_pure_getter(method, attr, receiver):
            return _issue('O08', DiagnoseSeverity.WARN, f"冗余 getter: 方法 '{cls.name}.{method.name}' 仅 return 属性 self.{attr}（或私有后端 self._{attr}），无校验/转换逻辑，应直接访问属性", method.lineno, f"移除 {method.name}，调用方直接访问 obj.{attr}；如需封装改用 @property")
        return None
    if method.name.startswith('set_'):
        attr = method.name[4:]
        if _is_pure_setter(method, attr, receiver):
            return _issue('O08', DiagnoseSeverity.WARN, f"冗余 setter: 方法 '{cls.name}.{method.name}' 仅赋值属性 self.{attr}（或私有后端 self._{attr}），无校验/转换逻辑，应直接赋值属性", method.lineno, f"移除 {method.name}，调用方直接 obj.{attr} = value；如需校验改用 @property.setter")
    return None
def _is_receiver_attr(node: ast.AST, attr: str, receiver: str) -> bool:
    if not isinstance(node, ast.Attribute):
        return False
    if not isinstance(node.value, ast.Name) or node.value.id != receiver:
        return False
    return node.attr in (attr, f"_{attr}")
def _is_param_ref(node: ast.AST, method: ast.AST, receiver: str) -> bool:
    if not isinstance(node, ast.Name):
        return False
    return node.id in collect_param_names(method) - {receiver}
def _is_pure_getter(method: ast.AST, attr: str, receiver: str) -> bool:
    body = _docstring_free_stmts(method.body)
    if len(body) != 1:
        return False
    stmt = body[0]
    if not isinstance(stmt, ast.Return):
        return False
    return _is_receiver_attr(stmt.value, attr, receiver)
def _is_pure_setter(method: ast.AST, attr: str, receiver: str) -> bool:
    body = _docstring_free_stmts(method.body)
    if len(body) != 1:
        return False
    stmt = body[0]
    if isinstance(stmt, ast.Assign):
        if len(stmt.targets) != 1:
            return False
        target = stmt.targets[0]
    elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        target = stmt.target
    else:
        return False
    if not _is_receiver_attr(target, attr, receiver):
        return False
    return _is_param_ref(stmt.value, method, receiver)
def _is_property_like(m: ast.AST) -> bool:
    return any(ast_name(d) in ('property', 'cached_property',
                               'setter', 'getter', 'deleter')
               for d in m.decorator_list)
def _is_classmethod(m: ast.AST) -> bool:
    return any(ast_name(d) == 'classmethod' for d in m.decorator_list)
def _real_methods(cls: ast.ClassDef) -> list:
    return [m for m in _method_defs(cls) if not is_dunder_name(m.name)]
def _is_dataclass(cls: ast.ClassDef) -> bool:
    return any(ast_name(dec) == 'dataclass' for dec in cls.decorator_list)
def _dataclass_has_instance_field(cls: ast.ClassDef) -> bool:
    if not _is_dataclass(cls):
        return False
    for stmt in same_scope_bfs_nodes(cls):
        if not isinstance(stmt, ast.AnnAssign):
            continue
        if _mm01_annotation_is_classvar(stmt.annotation):
            continue
        return True
    return False
def _assign_targets(node: ast.AST) -> list[ast.expr]:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    return [node.target]
def _is_receiver_attr_write(target: ast.AST, receiver: str) -> bool:
    if any(_iter_receiver_attr_targets(target, receiver)):
        return True
    return any(
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Attribute)
        and node.value.attr == '__dict__'
        and _is_receiver_ref(node.value.value, receiver)
        for node in subtree_nodes(target)
    )
def _class_receiver_accesses_state(cls: ast.ClassDef) -> bool:
    method_names = {method.name for method in _method_defs(cls)}
    for method in same_scope_bfs_nodes(cls):
        if not isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if is_static_method(method) or _is_classmethod(method):
            continue
        receiver = _first_positional_name(method)
        if receiver is None:
            continue
        for node in iter_own_nodes(method):
            if (isinstance(node, ast.Attribute)
                    and isinstance(node.ctx, (ast.Load, ast.Del))
                    and _is_receiver_ref(node.value, receiver)
                    and node.attr not in method_names):
                return True
            if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                continue
            if any(_is_receiver_attr_write(t, receiver)
                   for t in _assign_targets(node)):
                return True
    return False
def _declares_instance_slots(cls: ast.ClassDef) -> bool:
    for stmt in same_scope_bfs_nodes(cls):
        targets: list = []
        value = None
        if isinstance(stmt, ast.Assign):
            targets = list(stmt.targets)
            value = stmt.value
        elif isinstance(stmt, ast.AnnAssign):
            targets = [stmt.target]
            value = stmt.value
        if not any(isinstance(t, ast.Name) and t.id == '__slots__'
                   for t in targets):
            continue
        if value is None:
            return False
        if isinstance(value, (ast.Tuple, ast.List)):
            return bool(value.elts)
        return True
    return False
def _has_indirect_receiver_write(cls: ast.ClassDef) -> bool:
    for method in same_scope_bfs_nodes(cls):
        if not isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if is_static_method(method) or _is_classmethod(method):
            continue
        receiver = _first_positional_name(method)
        if receiver is None:
            continue
        for node in iter_own_nodes(method):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            if (isinstance(func, ast.Attribute)
                    and func.attr in {'clear', 'pop', 'popitem',
                                      'setdefault', 'update'}
                    and isinstance(func.value, ast.Attribute)
                    and func.value.attr == '__dict__'
                    and _is_receiver_ref(func.value.value, receiver)):
                return True
            if not (isinstance(func, ast.Name) and func.id == 'setattr'):
                continue
            if node.args and _is_receiver_ref(node.args[0], receiver):
                return True
    return False
def _class_has_instance_state(cls: ast.ClassDef) -> bool:
    if _dataclass_has_instance_field(cls):
        return True
    if _declares_instance_slots(cls):
        return True
    if _class_receiver_accesses_state(cls):
        return True
    return _has_indirect_receiver_write(cls)
def _load_shadowed(ref: ast.Name, stop_node: ast.AST, pm: dict,
                   head_ids: dict[int, set[int]], memo: dict) -> bool:
    cur = pm.get(ref)
    passed_function = False
    while cur is not None and cur is not stop_node:
        if id(ref) in head_ids.get(id(cur), ()):
            cur = pm.get(cur)
            continue
        hit = False
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            rebound, is_global = _scope_shadow_state(ref.id, cur, memo)
            hit = is_global or rebound
            passed_function = True
        elif isinstance(cur, ast.ClassDef) and not passed_function:
            rebound, is_global = _scope_shadow_state(ref.id, cur, memo)
            hit = is_global or (rebound and _class_binding_precedes(
                ref, ref.id, cur, pm, include_imports=True))
        elif isinstance(cur, ast.ExceptHandler) and cur.name == ref.id:
            hit = True
        elif isinstance(cur, (ast.ListComp, ast.SetComp, ast.DictComp,
                              ast.GeneratorExp)):
            hit = _comp_target_shadows(ref, ref.id, cur)
            if _in_comprehension_implicit_scope(ref, cur):
                passed_function = True
        if hit:
            return True
        cur = pm.get(cur)
    return False
def _collect_loaded_names(node: ast.AST) -> set[str]:
    loaded: set[str] = set()
    pm = parent_map(node)
    head_ids = {id(sub): _definition_head_ids(sub)
                for sub in subtree_nodes(node)
                if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef, ast.Lambda))}
    own_head_ids = head_ids.get(id(node), set())
    memo: dict = {}
    for sub in subtree_nodes(node):
        if isinstance(sub, ast.AugAssign):
            for target in subtree_nodes(sub.target):
                if not (isinstance(target, ast.Name)
                        and isinstance(target.ctx, ast.Store)):
                    continue
                if not _load_shadowed(target, node, pm, head_ids, memo):
                    loaded.add(target.id)
            continue
        if not isinstance(sub, ast.Name):
            continue
        if not isinstance(sub.ctx, (ast.Load, ast.Del)):
            continue
        if id(sub) in own_head_ids:
            continue
        if not _load_shadowed(sub, node, pm, head_ids, memo):
            loaded.add(sub.id)
    return loaded
def _is_forward_arg(arg: ast.AST, params: set[str]) -> bool:
    if isinstance(arg, ast.Starred):
        arg = arg.value
    return isinstance(arg, ast.Name) and arg.id in params
def _forward_positional_args(
        call_args: list[ast.expr], vararg_name: str | None,
        params: set[str]) -> tuple[list[str], list[str]] | None:
    positional_args: list[str] = []
    forwarded: list[str] = []
    for arg in call_args:
        if isinstance(arg, ast.Starred):
            if (vararg_name is None or not isinstance(arg.value, ast.Name)
                    or arg.value.id != vararg_name):
                return None
            name = arg.value.id
        else:
            if (not _is_forward_arg(arg, params)
                    or arg.id == vararg_name):
                return None
            name = arg.id
        positional_args.append(name)
        forwarded.append(name)
    return positional_args, forwarded
def _forward_keywords_ok(call_keywords: list[ast.keyword],
                         vararg_name: str | None, kwarg_name: str | None,
                         params: set[str], forwarded: list[str]) -> bool:
    for kw in call_keywords:
        value = kw.value
        if kw.arg is None:
            if (kwarg_name is None or not isinstance(value, ast.Name)
                    or value.id != kwarg_name):
                return False
        elif (not _is_forward_arg(value, params)
                or not isinstance(value, ast.Name)
                or kw.arg != value.id
                or value.id in (vararg_name, kwarg_name)):
            return False
        forwarded.append(value.id)
    return True
def _forward_covers_params(forwarded: list[str], params: set[str],
                           receiver_name: str | None = None) -> bool:
    required = params - ({receiver_name} if receiver_name is not None else set())
    required_forwarded = [name for name in forwarded if name in required]
    if (len(required_forwarded) != len(required)
            or set(required_forwarded) != required):
        return False
    return all(forwarded.count(name) <= 1 for name in ('self', 'cls'))
def _forward_positional_aligned(positional_args: list[str],
                                channel: list[str],
                                receiver_name: str | None = None) -> bool:
    if (receiver_name is not None and channel
            and channel[0] == receiver_name
            and (not positional_args or positional_args[0] != channel[0])):
        channel = channel[1:]
    return positional_args == channel[:len(positional_args)]
_SELF_CLS_NAMES = frozenset({'self', 'cls'})
def _is_self_recursive_call(node: ast.AST, call: ast.Call,
                            receiver_name: str | None = None,
                            owner_name: str | None = None) -> bool:
    if not isinstance(call, ast.Call):
        return False
    func = call.func
    func_name = getattr(node, 'name', None)
    if not isinstance(func_name, str) or not func_name:
        return False
    if isinstance(func, ast.Name):
        return func.id == func_name
    receiver_names = (_SELF_CLS_NAMES if receiver_name is None
                      else {receiver_name})
    if not (isinstance(func, ast.Attribute)
            and func.attr == func_name
            and isinstance(func.value, ast.Name)):
        return False
    return (func.value.id in receiver_names
            or (owner_name is not None and func.value.id == owner_name))
def _is_pure_forward(node: ast.AST, call: ast.Call, params: set[str],
                     *, is_method: bool = False,
                     owner_name: str | None = None) -> bool:
    body = _docstring_free_stmts(node.body)
    if len(body) != 1 or not isinstance(body[0], ast.Return):
        return False
    if (node.args.defaults
            or any(default is not None for default in node.args.kw_defaults)):
        return False
    receiver_name = _implicit_receiver_name(node, is_method=is_method)
    if (not isinstance(call, ast.Call)
            or _is_self_recursive_call(
                node, call, receiver_name, owner_name)):
        return False
    vararg_name = (None if node.args.vararg is None
                   else node.args.vararg.arg)
    kwarg_name = (None if node.args.kwarg is None
                  else node.args.kwarg.arg)
    channel = [arg.arg for arg in (*node.args.posonlyargs, *node.args.args)]
    if vararg_name is not None:
        channel.append(vararg_name)
    shaped = _forward_positional_args(call.args, vararg_name, params)
    if shaped is None:
        return False
    positional_args, forwarded = shaped
    posonly_names = {arg.arg for arg in node.args.posonlyargs}
    if any(keyword.arg is not None and keyword.arg in posonly_names
           for keyword in call.keywords):
        return False
    if not _forward_keywords_ok(
            call.keywords, vararg_name, kwarg_name, params, forwarded):
        return False
    if not _forward_covers_params(forwarded, params, receiver_name):
        return False
    return _forward_positional_aligned(
        positional_args, channel, receiver_name)
def _is_abcmeta_keyword(kw: ast.keyword) -> bool:
    return kw.arg == 'metaclass' and ast_name(kw.value) == 'ABCMeta'
def _declares_abstractmethod(cls: ast.ClassDef) -> bool:
    return any(_o01_own_bindings(cls).values())
def _is_abstract_class(cls: ast.ClassDef) -> bool:
    if any(ast_name(base) in _STDLIB_ABSTRACT_BASES for base in cls.bases):
        return True
    if any(_is_abcmeta_keyword(kw) for kw in cls.keywords):
        return True
    return _declares_abstractmethod(cls)
_CLASS_CREATION_HOOK_NAMES = frozenset({
    '__new__', '__init_subclass__', '__class_getitem__',
})
def _has_class_creation_hooks(cls: ast.ClassDef) -> bool:
    if cls.keywords:
        return True
    return any(method.name in _CLASS_CREATION_HOOK_NAMES
               for method in _method_defs(cls))
def _is_enum_class(cls: ast.ClassDef) -> bool:
    return any(ast_name(base) in _STDLIB_ENUM_BASES for base in cls.bases)
def _has_branching(node: ast.AST) -> bool:
    return any(isinstance(child, _BRANCHING_NODES) for child in same_scope_bfs_nodes(node))
def _call_class_name(call: ast.AST) -> str:
    if isinstance(call, ast.Call):
        func = call.func
        if isinstance(func, ast.Name) and func.id[:1].isupper():
            return func.id
        if isinstance(func, ast.Attribute) and func.attr[:1].isupper():
            return func.attr
    return ''
def _mm01_parse_annotation_string(annotation: Any) -> Any:
    if not (isinstance(annotation, ast.Constant)
            and isinstance(annotation.value, str)):
        return annotation
    try:
        return ast.parse(annotation.value, mode='eval').body
    except PARSE_DEGRADE_EXC as _e:  # jwsgj:silent-ok
        logger.debug("suppressed annotation parse failure: %s: %s",
                   type(_e).__name__, _e)
        return None
def _mm01_annotation_root(annotation: Any) -> Any:
    ann = _mm01_parse_annotation_string(annotation)
    while ann is not None:
        if isinstance(ann, ast.Constant) and isinstance(ann.value, str):
            ann = _mm01_parse_annotation_string(ann)
            continue
        if not isinstance(ann, ast.Subscript):
            return ann
        base = ann.value
        if _base_name(base) == "Annotated":
            slice_node = ann.slice
            elts = (slice_node.elts
                    if isinstance(slice_node, ast.Tuple) else ())
            if not elts:
                return None
            ann = elts[0]
            continue
        ann = base
    return None
def _mm01_annotation_is_classvar(annotation: Any) -> bool:
    root = _mm01_annotation_root(annotation)
    if isinstance(root, ast.Name):
        return root.id == "ClassVar"
    return isinstance(root, ast.Attribute) and root.attr == "ClassVar"
GATE_DETECTORS: dict[str, Any] = {
    "B01": detect_b01_mutable_default,
    "B12": detect_b12_mutable_class_attr,
    "B24": detect_b24_mutable_replication,
    "B28": detect_b28_internal_mutable_return,
    "O01": detect_o01_single_impl_abstraction,
    "O02": detect_o02_branchless_factory,
    "O03": detect_o03_unused_param,
    "O04": detect_o04_trivial_wrapper,
    "O05": detect_o05_static_method_class,
    "O06": detect_o06_single_method_class,
    "O07": detect_o07_deep_inheritance,
    "O08": detect_o08_redundant_getter_setter,
}
def wiring_declarations() -> dict:
    return {"catalogs": {
        "gate_adapter_bindings": {
            'RB01': (detect_b01_mutable_default, "RB-01"),
        },
    }}
__all__ = [
    "GATE_DETECTORS",
    "detect_b01_mutable_default",
    "detect_b12_mutable_class_attr",
    "detect_b24_mutable_replication",
    "detect_b28_internal_mutable_return",
    "detect_o01_single_impl_abstraction",
    "detect_o02_branchless_factory",
    "detect_o03_unused_param",
    "detect_o04_trivial_wrapper",
    "detect_o05_static_method_class",
    "detect_o06_single_method_class",
    "detect_o07_deep_inheritance",
    "detect_o08_redundant_getter_setter",
]

# 循环导入断点：diag_gate_class_protocol 在模块顶层从本模块导入 32 个符号。
# 当 fix_safety_verify 以 spec_from_file_location('jwsgj.diag_gate_class', path)
# 按路径加载本文件时，顶部任何 `from jwsgj...` 都会先触发 jwsgj/__init__.py，
# 进而导入 diag_gate_class_protocol；此时本模块尚未执行到符号定义，
# 协议模块的 `from jwsgj.diag_gate_class import ...` 立即 ImportError。
# 将包内依赖延迟到全部符号定义之后，保证协议模块看到的是已完整定义的模块对象；
# 依赖仅在函数调用期解析，外部行为与导入顺序无关。
from jwsgj.diag_shared_ast_bindings import import_stmt_binds
from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    collect_param_names,
    comp_target_names,
    in_subtree,
    is_docstring_stmt,
    is_dunder_name,
    is_placeholder_stmt,
    is_static_method,
    iter_own_nodes,
    iter_target_bindings,
)
from jwsgj.diag_shared_ast_views import (
    parent_map,
    same_scope_bfs_nodes,
    subtree_nodes,
    tree_nodes,
)
from jwsgj.diag_types_defs import DiagnoseIssue
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    DiagnoseSeverity,
)
from jwsgj.prevention_scope_facts import walk_nodes

logger.info("diag_gate_class 已加载: %d 项导出", len(__all__))

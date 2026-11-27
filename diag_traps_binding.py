from __future__ import annotations

import ast
import logging
import re
from typing import Any

from jwsgj.diag_shared_ast_bindings import (
    ScopeEventIndex,
    build_scope_index,
    collect_binding_names,
    collect_shadow_bindings,
    enclosing_scope_binds,
    exec_scope_declarations,
    owner_scope,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_CALLABLES,
    TYPE_ALIAS_NODES,
    build_parent_map,
    collect_param_names,
    definition_time_exprs,
    dotted_name,
    expr_target_name,
    import_binds_of,
    is_star_import,
    iter_def_site_nodes,
    iter_scope_nodes,
    iter_unpack_target_names,
    pattern_capture_name,
    scope_chain,
    scope_roots,
    split_identifier,
    subscript_base_node,
    type_checking_body_node_ids,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import (
    _FLOW_DEFINITE,
    _flow_namedexpr_execution,
    block_never_falls_through,
    constant_truth,
    is_irrefutable_pattern,
    walk_nodes,
)

__all__ = [
    "check_CL03",
    "check_HC02",
    "check_RL03",
    "check_RT01",
    "check_RT02",
    "check_TP05",
    "check_TP11",
    "check_TP23",
    "check_TP25",
    "check_TP26",
]
_log = logging.getLogger(__name__)
_log.info(
    "diag_traps_binding 绑定生命周期与接口边界语义域已加载: %d 项导出",
    len(__all__))
_DEFAULT_FILEPATH = ""
_TP25_VERSION_RE = re.compile(r"^(?P<base>.+)_v(?P<num>\d+)$")
_TP25_SCOPE_NODES: tuple[type[ast.AST], ...] = (
    ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)
_Tp25Key = tuple[tuple[str, ...], str]
_Tp25Entry = tuple[str, tuple[str, ...], int]
_TRY_STAR_TYPE: type[ast.AST] | None = getattr(ast, "TryStar", None)
_TRY_STMT_TYPES: tuple[type[ast.AST], ...] = (
    (ast.Try, _TRY_STAR_TYPE) if _TRY_STAR_TYPE is not None else (ast.Try,))
_TP11_STMT_CONTAINERS: tuple[type[ast.AST], ...] = (
    ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef,
    ast.If, ast.For, ast.AsyncFor, ast.While, ast.With,
    ast.AsyncWith, ast.ExceptHandler, *_TRY_STMT_TYPES)
_MATCH_CASE_TYPE: type[ast.AST] | None = getattr(ast, "match_case", None)
if _MATCH_CASE_TYPE is not None:
    _TP11_STMT_CONTAINERS = _TP11_STMT_CONTAINERS + (_MATCH_CASE_TYPE,)
_TP26_HTTP_MODULES = frozenset({"requests", "httpx", "aiohttp"})
_TP26_HTTP_VERBS = frozenset({
    "get", "post", "put", "delete", "patch", "head", "options", "request",
})
_TP26_HTTP_FACTORIES = frozenset({
    "Session", "session", "Client", "AsyncClient", "ClientSession",
})
_TP26_BACKOFF_ATTRS = frozenset({"sleep", "wait"})
#: 尾部为这些调用时 handler 必然离开当前进程，不会进入下一轮重试。
_TP26_PROCESS_EXIT_CALLEES = frozenset({
    "sys.exit", "sys.abort", "builtins.exit", "builtins.quit", "exit",
    "quit", "os._exit", "os.abort", "posix._exit", "posix.abort",
})
_TP26_SCOPE_STOP = (ast.For, ast.AsyncFor, ast.While,
                    ast.FunctionDef, ast.AsyncFunctionDef,
                    ast.Lambda, ast.ClassDef)
_TP05_RUNTIME_FALLBACK_NAMES = BUILTIN_CALLABLES | frozenset({
    "__annotations__", "__builtins__", "__cached__", "__class__",
    "__doc__", "__file__", "__loader__", "__module__", "__name__",
    "__package__", "__path__", "__qualname__", "__spec__",
})
def _tp05_scope_exposes_name(name: str, scope: ast.AST,
                             scope_defined: dict[int, set[str]]) -> bool:
    bindings = scope_defined.get(id(scope), ())
    return (name in bindings
            or ("*" in bindings and not name.startswith("_")))
def _tp05_bind_import(node: ast.AST, defined: set[str]) -> None:
    defined.update(import_binds_of(node))
    if is_star_import(node):
        defined.add("*")
def _tp05_bind_name_store(node: ast.Name, defined: set[str]) -> None:
    if isinstance(node.ctx, ast.Store):
        defined.add(node.id)
def _tp05_bind_scope_decl(node: ast.AST, defined: set[str]) -> None:
    defined.update(node.names)
def _tp05_bind_capture_name(node: ast.AST, defined: set[str]) -> None:
    capture = pattern_capture_name(node)
    if capture is not None:
        defined.add(capture)
def _tp05_bind_type_param(node: ast.AST, defined: set[str]) -> None:
    name = getattr(node, "name", None)
    if isinstance(name, str) and name:
        defined.add(name)
_TP05_PATTERN_CAPTURE_NODES = tuple(
    _node_type for _node_type in (
        getattr(ast, "MatchAs", None),
        getattr(ast, "MatchStar", None),
        getattr(ast, "MatchMapping", None),
    ) if _node_type is not None)
_TP05_TYPE_PARAM_NODES = tuple(
    _node_type for _node_type in (
        getattr(ast, "TypeVar", None),
        getattr(ast, "ParamSpec", None),
        getattr(ast, "TypeVarTuple", None),
    ) if _node_type is not None)
_TP05_BIND_DISPATCH = (
    ((ast.Import, ast.ImportFrom), _tp05_bind_import),
    ((ast.Global, ast.Nonlocal), _tp05_bind_scope_decl),
    (ast.Name, _tp05_bind_name_store),
    (_TP05_PATTERN_CAPTURE_NODES, _tp05_bind_capture_name),
    (_TP05_TYPE_PARAM_NODES, _tp05_bind_type_param),
)
def _tp05_defined_from_node(node: ast.AST, defined: set[str]) -> None:
    for _types, _collector in _TP05_BIND_DISPATCH:
        if isinstance(node, _types):
            _collector(node, defined)
            return
_TP05_COMPREHENSION_NODES: tuple[type[ast.AST], ...] = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_TP05_WALRUS_STOP: tuple[type[ast.AST], ...] = (
    ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
def _tp05_expand_comprehension(cmp_node: ast.AST, inner: set[int],
                               walrus: set[str]) -> None:
    stack = list(ast.iter_child_nodes(cmp_node))
    while stack:
        cur = stack.pop()
        inner.add(id(cur))
        if isinstance(cur, ast.NamedExpr):
            walrus.update(iter_unpack_target_names(cur.target))
        for child in ast.iter_child_nodes(cur):
            if isinstance(child, _TP05_WALRUS_STOP):
                continue
            stack.append(child)
    inner.add(id(cmp_node))
def _tp05_scope_bindings(
        scope: ast.AST,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> tuple[set[str], set[str], set[str]]:
    globals_: set[str] = set()
    nonlocals_: set[str] = set()
    defined = set(collect_param_names(scope))
    for type_param in getattr(scope, "type_params", ()):
        _tp05_bind_type_param(type_param, defined)
    comprehension_ids: set[int] = set()
    walrus_names: set[str] = set()
    annotation_only_targets: set[int] = set()
    unbound_names: set[str] = set()
    for node in iter_scope_nodes(scope):
        if id(node) in runtime_inactive:
            continue
        if isinstance(node, ast.Global):
            globals_.update(node.names)
            continue
        if isinstance(node, ast.Nonlocal):
            nonlocals_.update(node.names)
            continue
        if isinstance(node, _TP05_COMPREHENSION_NODES):
            if id(node) not in comprehension_ids:
                _tp05_expand_comprehension(node, comprehension_ids,
                                           walrus_names)
            continue
        if id(node) in comprehension_ids:
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            annotation_only_targets.add(id(node.target))
            if isinstance(node.target, ast.Name):
                unbound_names.add(node.target.id)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            defined.add(node.name)
            defined.update(enclosing_scope_binds(node))
            continue
        if isinstance(node, ast.Lambda):
            defined.update(enclosing_scope_binds(node))
            continue
        if isinstance(node, ast.Name) and id(node) in annotation_only_targets:
            continue
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Del):
            unbound_names.add(node.id)
        _tp05_defined_from_node(node, defined)
    defined |= walrus_names
    if isinstance(scope, ast.Module):
        return defined, globals_, unbound_names
    excluded = globals_ | nonlocals_
    return defined - excluded, globals_, unbound_names - excluded
def _tp05_annotations_deferred(node: ast.AST, parents: dict) -> bool:
    root = node
    while parents.get(id(root)) is not None:
        root = parents[id(root)]
    return (isinstance(root, ast.Module) and any(
        isinstance(stmt, ast.ImportFrom) and stmt.module == "__future__"
        and any(alias.name == "annotations" for alias in stmt.names)
        for stmt in root.body))
def _tp05_definition_time_exprs(scope: ast.AST,
                                parents: dict) -> list[ast.AST]:
    if isinstance(scope, ast.ClassDef):
        return [
            *scope.decorator_list, *scope.bases,
            *(keyword.value for keyword in scope.keywords),
        ]
    if isinstance(scope, _TP05_DELAYED_SCOPE_NODES):
        if _tp05_annotations_deferred(scope, parents):
            return definition_time_exprs(scope)
        return list(iter_def_site_nodes(scope))
    return []
def _tp05_scope_chain(node: ast.AST, parents: dict,
                      scope_defined: dict[int, set[str]]) -> list[ast.AST]:
    chain: list[ast.AST] = []
    for scope in scope_chain(node, parents):
        if id(scope) not in scope_defined:
            continue
        if any(_tp05_node_within(node, expr, parents)
               for expr in _tp05_definition_time_exprs(scope, parents)):
            continue
        chain.append(scope)
    return chain
def _tp05_direct_delete_before(
        name: str, node: ast.Name, scope: ast.AST, parents: dict,
) -> ast.AST | None:
    nearest_scope = next(iter(scope_chain(node, parents)), None)
    ancestor: ast.AST | None = node
    while ancestor is not None and ancestor is not scope:
        parent = parents.get(id(ancestor))
        if parent is None:
            return None
        if nearest_scope is scope or parent is scope:
            for attr in ("body", "orelse", "finalbody"):
                stmts = getattr(parent, attr, None)
                if not isinstance(stmts, list):
                    continue
                indexes = {id(stmt): index for index, stmt in enumerate(stmts)}
                load_index = indexes.get(id(ancestor))
                if load_index is None:
                    continue
                for stmt in reversed(stmts[:load_index]):
                    if (isinstance(stmt, ast.Delete)
                            and name in iter_unpack_target_names(stmt.targets)):
                        return stmt
                    if isinstance(stmt, _TRY_STMT_TYPES):
                        handler = next(
                            (item for item in stmt.handlers
                             if item.name == name), None)
                        if handler is not None:
                            return handler
                break
        ancestor = parent
    return None
def _statement_list_guarantees(
        statements: list[ast.stmt], predicate,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> bool:
    return any(_statement_guarantees(stmt, predicate, runtime_inactive)
               for stmt in statements)


def _block_exits_before_following_statement(statements: list[ast.stmt]) -> bool:
    return (block_never_falls_through(statements)
            or bool(statements)
            and isinstance(statements[-1], (ast.Break, ast.Continue)))


def _statement_guarantees(
        stmt: ast.stmt, predicate,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> bool:
    """Return whether normal execution of *stmt* must satisfy predicate."""
    if id(stmt) in runtime_inactive:
        return False
    if predicate(stmt):
        return True
    if isinstance(stmt, ast.If):
        truth = constant_truth(stmt.test)
        if truth is not None:
            branch = stmt.body if truth else stmt.orelse
            return _statement_list_guarantees(
                branch, predicate, runtime_inactive)
        return (bool(stmt.orelse)
                and _statement_list_guarantees(
                    stmt.body, predicate, runtime_inactive)
                and _statement_list_guarantees(
                    stmt.orelse, predicate, runtime_inactive))
    if isinstance(stmt, _TRY_STMT_TYPES):
        if _statement_list_guarantees(
                stmt.finalbody, predicate, runtime_inactive):
            return True
        normal_path = _statement_list_guarantees(
            [*stmt.body, *stmt.orelse], predicate, runtime_inactive)
        return normal_path and all(
            _block_exits_before_following_statement(handler.body)
            or _statement_list_guarantees(
                handler.body, predicate, runtime_inactive)
            for handler in stmt.handlers)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _statement_list_guarantees(
            stmt.body, predicate, runtime_inactive)
    if isinstance(stmt, ast.Match):
        exhaustive = False
        for case in stmt.cases:
            guard_truth = constant_truth(case.guard)
            if guard_truth is False:
                continue
            if not _statement_list_guarantees(
                    case.body, predicate, runtime_inactive):
                return False
            if (is_irrefutable_pattern(case.pattern)
                    and (case.guard is None or guard_truth is True)):
                exhaustive = True
                break
        return exhaustive
    return False


def _candidate_guaranteed_before(
        candidate: ast.AST, target: ast.AST, boundary: ast.AST,
        parents: dict, predicate,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> bool:
    """Check structural dominance instead of relying on source order alone."""
    current: ast.AST | None = target
    while current is not None and current is not boundary:
        parent = parents.get(id(current))
        if parent is None:
            break
        if (candidate is parent
                and isinstance(parent, (ast.For, ast.AsyncFor,
                                        ast.With, ast.AsyncWith,
                                        ast.ExceptHandler))
                and any(_tp05_node_within(target, stmt, parents)
                        for stmt in parent.body)):
            return True
        if (_MATCH_CASE_TYPE is not None
                and isinstance(parent, _MATCH_CASE_TYPE)
                and _tp05_node_within(candidate, parent.pattern, parents)):
            return True
        for attr in ("body", "orelse", "finalbody"):
            statements = getattr(parent, attr, None)
            if not isinstance(statements, list):
                continue
            index = next((i for i, stmt in enumerate(statements)
                          if stmt is current), None)
            if index is None:
                continue
            for stmt in statements[:index]:
                if (_tp05_node_within(candidate, stmt, parents)
                        and _statement_guarantees(
                            stmt, predicate, runtime_inactive)):
                    return True
        current = parent
    return False


def _tp05_int_literal(node: ast.AST) -> int | None:
    if isinstance(node, ast.Constant):
        value = node.value
        if isinstance(value, int) and not isinstance(value, bool):
            return value
        return None
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub))):
        operand = _tp05_int_literal(node.operand)
        if operand is None:
            return None
        return operand if isinstance(node.op, ast.UAdd) else -operand
    return None

def _tp05_range_nonempty(node: ast.AST) -> bool | None:
    """``range(...)`` 全字面量参数时返回是否至少迭代一次，否则 None。"""
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == 'range'
            and not node.keywords
            and 1 <= len(node.args) <= 3):
        return None
    values: list[int] = []
    for arg in node.args:
        value = _tp05_int_literal(arg)
        if value is None:
            return None
        values.append(value)
    try:
        return len(range(*values)) > 0
    except (OverflowError, ValueError):
        return None

def _tp05_nonempty_iterable(node: ast.AST) -> bool:
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return any(not isinstance(elt, ast.Starred) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return any(key is not None for key in node.keys)
    range_nonempty = _tp05_range_nonempty(node)
    if range_nonempty is not None:
        return range_nonempty
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))


def _tp05_statement_binds(stmt: ast.stmt, name: str) -> bool:
    if (isinstance(stmt, ast.AnnAssign) and stmt.value is None) \
            or isinstance(stmt, (ast.While, ast.Delete)):
        return False
    if (isinstance(stmt, (ast.For, ast.AsyncFor))
            and not _tp05_nonempty_iterable(stmt.iter)):
        return False
    bound: set[str] = set()
    collect_binding_names(stmt, bound)
    return name in bound


def _tp05_name_rebound_between(
        name: str, delete: ast.AST, node: ast.Name, scope: ast.AST,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
        parents: dict | None = None,
) -> bool:
    if parents is None:
        parents = build_parent_map(scope)
    if isinstance(delete, ast.ExceptHandler):
        delete_pos = (delete.end_lineno, delete.end_col_offset)
    else:
        delete_pos = (delete.lineno, delete.col_offset)
    use_pos = (node.lineno, node.col_offset)
    annotation_targets = {
        id(item.target) for item in walk_nodes(scope)
        if isinstance(item, ast.AnnAssign) and item.value is None
    }
    namedexpr_execution: dict[int, int] | None = None
    def predicate(stmt: ast.stmt) -> bool:
        return _tp05_statement_binds(stmt, name)
    for item in iter_scope_nodes(scope):
        if id(item) in runtime_inactive:
            continue
        position = (getattr(item, "lineno", -1),
                    getattr(item, "col_offset", -1))
        if not delete_pos < position < use_pos or id(item) in annotation_targets:
            continue
        if isinstance(item, ast.Delete):
            continue
        if isinstance(item, ast.AnnAssign) and item.value is None:
            continue
        bound: set[str] = set()
        collect_binding_names(item, bound)
        if name not in bound:
            continue
        if isinstance(item, ast.NamedExpr):
            if namedexpr_execution is None:
                namedexpr_execution = _flow_namedexpr_execution(
                    [scope], use_pos)
            if (namedexpr_execution.get(id(item), _FLOW_DEFINITE)
                    == _FLOW_DEFINITE):
                return True
            continue
        if _candidate_guaranteed_before(
                item, node, scope, parents, predicate, runtime_inactive):
            return True
    return False
def _tp05_deleted_at_use(
        name: str, node: ast.Name, scope: ast.AST, parents: dict,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> bool:
    delete = _tp05_direct_delete_before(name, node, scope, parents)
    return (delete is not None
            and not _tp05_name_rebound_between(
                name, delete, node, scope, runtime_inactive,
                parents=parents))
def _tp05_name_defined(name: str, node: ast.Name, chain: list[ast.AST],
                       parents: dict, scope_defined: dict[int, set[str]],
                       scope_globals: dict[int, set[str]],
                       scope_unbound: dict[int, set[str]],
                       scope_events: dict[int, dict[str, list]],
                       runtime_inactive: set[int] | frozenset[int] = frozenset(),
                       ) -> bool:
    module = next((scope for scope in chain if isinstance(scope, ast.Module)), None)
    is_runtime_fallback = name in _TP05_RUNTIME_FALLBACK_NAMES
    timing_scope_ids = _tp05_timing_scope_ids(node, chain, parents)
    for scope in chain:
        deleted = _tp05_deleted_at_use(
            name, node, scope, parents, runtime_inactive)
        if name in scope_globals.get(id(scope), ()) and not isinstance(scope, ast.Module):
            if deleted and not is_runtime_fallback:
                return False
            if _tp05_name_rebound_between(
                    name, scope, node, scope, runtime_inactive,
                    parents=parents):
                return True
            return (is_runtime_fallback
                    or (module is not None
                        and name not in scope_unbound.get(id(module), ())
                        and _tp05_scope_exposes_name(name, module, scope_defined)))
        if deleted:
            if isinstance(scope, ast.ClassDef):
                continue
            return isinstance(scope, ast.Module) and is_runtime_fallback
        if (name in scope_unbound.get(id(scope), ())
                and not isinstance(scope, ast.ClassDef)):
            return isinstance(scope, ast.Module) and is_runtime_fallback
        if _tp05_scope_exposes_name(name, scope, scope_defined):
            if id(scope) not in timing_scope_ids or _tp05_has_prior_binding(
                    name, node, scope, scope_events, parents):
                return True
            if not isinstance(scope, ast.ClassDef):
                return isinstance(scope, ast.Module) and is_runtime_fallback
        if isinstance(scope, ast.Module) and is_runtime_fallback:
            return True
    return is_runtime_fallback
_TP05_NAME_SCOPE_BOUNDARY: tuple[type[ast.AST], ...] = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Module)
def _tp05_node_within(node: ast.AST, ancestor: ast.AST,
                      parents: dict) -> bool:
    cur: ast.AST | None = node
    while cur is not None:
        if cur is ancestor:
            return True
        cur = parents.get(id(cur))
    return False
def _tp05_function_annotation_exprs(scope: ast.AST) -> list[ast.AST]:
    args = scope.args
    params = [*args.posonlyargs, *args.args, *args.kwonlyargs]
    params.extend(param for param in (args.vararg, args.kwarg)
                  if param is not None)
    annotations = [param.annotation for param in params
                   if param.annotation is not None]
    if scope.returns is not None:
        annotations.append(scope.returns)
    return annotations
def _tp05_name_in_unevaluated_annotation(node: ast.Name,
                                         parents: dict) -> bool:
    current = parents.get(id(node))
    while current is not None:
        if TYPE_ALIAS_NODES and isinstance(current, TYPE_ALIAS_NODES):
            return True
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)) and any(
                _tp05_node_within(node, type_param, parents)
                for type_param in getattr(current, "type_params", ())):
            return True
        if (isinstance(current, ast.AnnAssign)
                and _tp05_node_within(node, current.annotation, parents)):
            owner: ast.AST | None = current
            while owner is not None and not isinstance(
                    owner, _TP05_NAME_SCOPE_BOUNDARY):
                owner = parents.get(id(owner))
            return (isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef))
                    or _tp05_annotations_deferred(current, parents))
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if any(_tp05_node_within(node, expr, parents)
                   for expr in _tp05_function_annotation_exprs(current)):
                return _tp05_annotations_deferred(current, parents)
            return False
        if isinstance(current, (ast.ClassDef, ast.Module)):
            return False
        current = parents.get(id(current))
    return False
_TP05_DELAYED_SCOPE_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _tp05_record_binding_events(events: dict, names,
                                activation: ast.AST) -> None:
    position = (getattr(activation, "end_lineno", -1),
                getattr(activation, "end_col_offset", -1))
    for name in names:
        events.setdefault(name, []).append((position, activation))
def _tp05_scope_binding_events(
        scope: ast.AST,
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> dict[str, list]:
    events: dict[str, list] = {}
    for name in collect_param_names(scope):
        events.setdefault(name, []).append(((-1, -1), None))
    for item in iter_scope_nodes(scope):
        if id(item) in runtime_inactive:
            continue
        if isinstance(item, ast.Delete):
            continue
        if isinstance(item, (ast.With, ast.AsyncWith)):
            for with_item in item.items:
                if with_item.optional_vars is not None:
                    _tp05_record_binding_events(
                        events,
                        iter_unpack_target_names(with_item.optional_vars),
                        with_item.context_expr)
            continue
        bound: set[str] = set()
        collect_binding_names(item, bound)
        if is_star_import(item):
            bound.add("*")
        if isinstance(item, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                             ast.NamedExpr)):
            activation = item.value
        elif isinstance(item, (ast.For, ast.AsyncFor)):
            activation = item.iter
        elif isinstance(item, ast.ExceptHandler) and item.type is not None:
            activation = item.type
        else:
            activation = item
        _tp05_record_binding_events(events, bound, activation)
    return events
def _tp05_active_global_events(
        scope: ast.AST, name: str,
        scope_events: dict[int, dict[str, list]],
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> list:
    events = list(scope_events.get(id(scope), {}).get(name, ()))
    if not events:
        return []
    positions = [position for position, _binding in events]
    deletions: list[tuple[int, int]] = []
    for item in iter_scope_nodes(scope):
        if id(item) in runtime_inactive:
            continue
        if ((isinstance(item, ast.Delete)
             and name in iter_unpack_target_names(item.targets))
                or (isinstance(item, ast.ExceptHandler)
                    and item.name == name)):
            deletions.append((item.end_lineno, item.end_col_offset))
    return [] if deletions and max(deletions) >= max(positions) else events


def _tp05_merge_global_bindings(
        scopes: list[ast.AST], scope_defined: dict[int, set[str]],
        scope_globals: dict[int, set[str]],
        scope_unbound: dict[int, set[str]],
        scope_events: dict[int, dict[str, list]],
        runtime_inactive: set[int] | frozenset[int] = frozenset(),
) -> None:
    if not scopes or not isinstance(scopes[0], ast.Module):
        return
    module = scopes[0]
    module_id = id(module)
    for scope in scopes[1:]:
        for name in scope_globals.get(id(scope), ()):
            positions = _tp05_active_global_events(
                scope, name, scope_events, runtime_inactive)
            if not positions:
                continue
            scope_defined[module_id].add(name)
            scope_unbound[module_id].discard(name)
            scope_events[module_id].setdefault(name, []).extend(positions)
    for positions in scope_events[module_id].values():
        positions.sort(key=lambda event: event[0])


def _tp05_binding_unreachable(binding: ast.AST | None, scope: ast.AST,
                              parents: dict) -> bool:
    if binding is None:
        return False
    current: ast.AST | None = binding
    while current is not None and current is not scope:
        parent = parents.get(id(current))
        if parent is None:
            return False
        for attr in ("body", "orelse", "finalbody"):
            statements = getattr(parent, attr, None)
            if not isinstance(statements, list):
                continue
            index = next((i for i, stmt in enumerate(statements)
                          if stmt is current), None)
            if index is None:
                continue
            if any(isinstance(stmt, (ast.Return, ast.Raise, ast.Break,
                                     ast.Continue))
                   for stmt in statements[:index]):
                return True
        current = parent
    return False
def _tp05_has_prior_binding(name: str, node: ast.Name, scope: ast.AST,
                            scope_events: dict[int, dict[str, list]],
                            parents: dict) -> bool:
    events = scope_events.get(id(scope), {})
    bindings = list(events.get(name, ()))
    if not name.startswith("_"):
        bindings.extend(events.get("*", ()))
    use_position = (node.lineno, node.col_offset)
    for position, binding in bindings:
        if position > use_position:
            continue
        if _tp05_binding_unreachable(binding, scope, parents):
            continue
        return True
    return False
def _tp05_timing_scope_ids(node: ast.Name, chain: list[ast.AST],
                           parents: dict) -> set[int]:
    current: ast.AST | None = node
    while current is not None:
        if isinstance(current, ast.GeneratorExp):
            first_iter = (current.generators[0].iter
                          if current.generators else None)
            if (first_iter is None
                    or not _tp05_node_within(node, first_iter, parents)):
                return set()
        elif (isinstance(current, _TP05_DELAYED_SCOPE_NODES)
              and not any(_tp05_node_within(node, expr, parents)
                          for expr in _tp05_definition_time_exprs(current, parents))):
            break
        current = parents.get(id(current))
    result: set[int] = set()
    for scope in chain:
        result.add(id(scope))
        if isinstance(scope, _TP05_DELAYED_SCOPE_NODES):
            break
    return result
def _tp05_is_name_read(node: ast.AST, parents: dict) -> bool:
    if not isinstance(node, ast.Name):
        return False
    if isinstance(node.ctx, ast.Load):
        return True
    parent = parents.get(id(node))
    return (isinstance(node.ctx, ast.Store)
            and isinstance(parent, ast.AugAssign) and parent.target is node)
def _tp05_iter_owns_node(node: ast.AST, generator: ast.comprehension,
                         parents: dict) -> bool:
    return _tp05_node_within(node, generator.iter, parents)
def _tp05_comprehension_bound(name: str, node: ast.AST,
                              parents: dict) -> bool:
    cur: ast.AST | None = parents.get(id(node))
    while cur is not None:
        if isinstance(cur, _TP05_COMPREHENSION_NODES):
            generators = cur.generators
            owner_index = next((
                index for index, generator in enumerate(generators)
                if _tp05_node_within(node, generator, parents)), None)
            for index, generator in enumerate(generators):
                if name not in iter_unpack_target_names(generator.target):
                    continue
                if owner_index is not None and owner_index < index:
                    continue
                if (owner_index == index
                        and _tp05_iter_owns_node(node, generator, parents)):
                    continue
                return True
        elif isinstance(cur, _TP05_NAME_SCOPE_BOUNDARY):
            break
        cur = parents.get(id(cur))
    return False
def _tp05_handler_target_names(handler: ast.AST | None,
                               parents: dict) -> set[str]:
    names: set[str] = set()
    current: ast.AST | None = handler
    while current is not None:
        if isinstance(current, ast.ExceptHandler) and current.name:
            names.add(current.name)
        current = parents.get(id(current))
    return names
def _tp05_innermost_handler(node: ast.AST,
                           parents: dict) -> ast.ExceptHandler | None:
    cur = parents.get(id(node))
    while cur is not None:
        if isinstance(cur, ast.ExceptHandler):
            return cur
        cur = parents.get(id(cur))
    return None
def _tp05_suggestion(name: str) -> str:
    return ("根因: 异常处理块引用了从未定义/导入的名称，"
            "该路径首次触发即二次崩溃。\n"
            f"修复策略: 补定义或导入 {name}"
            "（模块级赋值/函数参数/import），"
            "或改用已定义的等价名称\n"
            "参考标准: Python 异常处理语义 / PEP 8"
            "（异常路径不得引入未定义名称）")
def _tp05_handler_undefined(node: ast.ExceptHandler,
                            ctx: tuple[dict, dict, dict, dict, dict, set, set, str]
                            ) -> list[DiagnoseFinding]:
    (parents, scope_defined, scope_globals, scope_unbound, scope_events,
     runtime_inactive, reported, filepath) = ctx
    found: list[DiagnoseFinding] = []
    for child in walk_nodes(node):
        if not _tp05_is_name_read(child, parents):
            continue
        if id(child) in runtime_inactive:
            continue
        if _tp05_name_in_unevaluated_annotation(child, parents):
            continue
        if id(child) in reported:
            continue
        name = child.id
        innermost = _tp05_innermost_handler(child, parents)
        target_names = (_tp05_handler_target_names(innermost, parents)
                        if innermost is not None else set())
        if (innermost is not None and innermost.type is not None
                and _tp05_node_within(child, innermost.type, parents)):
            target_names = _tp05_handler_target_names(
                parents.get(id(innermost)), parents)
        if _tp05_comprehension_bound(name, child, parents):
            continue
        chain = _tp05_scope_chain(child, parents, scope_defined)
        if name in target_names:
            alias_deleted = bool(chain) and _tp05_deleted_at_use(
                name, child, chain[0], parents, runtime_inactive)
            if not alias_deleted:
                continue
        if _tp05_name_defined(
                name, child, chain, parents, scope_defined,
                scope_globals, scope_unbound, scope_events, runtime_inactive):
            continue
        reported.add(id(child))
        found.append(DiagnoseFinding(
            id="TP-05", severity="P1", dimension="trap",
            file=filepath, line=child.lineno,
            description=f"except 块引用未定义名称 {name}（异常路径触发 NameError 掩盖原始异常）",
            suggestion=_tp05_suggestion(name),
        ))
    return found
def check_TP05(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    handlers = [node for node in walk_nodes(tree)
                if isinstance(node, ast.ExceptHandler)]
    if not handlers:
        return issues
    parents = build_parent_map(tree)
    runtime_inactive = type_checking_body_node_ids(tree)
    scope_defined: dict[int, set[str]] = {}
    scope_globals: dict[int, set[str]] = {}
    scope_unbound: dict[int, set[str]] = {}
    scope_events: dict[int, dict[str, list]] = {}
    scopes = scope_roots(tree)
    for scope in scopes:
        defined, globals_, unbound = _tp05_scope_bindings(
            scope, runtime_inactive)
        scope_defined[id(scope)] = defined
        scope_events[id(scope)] = _tp05_scope_binding_events(
            scope, runtime_inactive)
        scope_globals[id(scope)] = globals_
        scope_unbound[id(scope)] = (
            unbound - defined if "*" not in defined else set())
    _tp05_merge_global_bindings(
        scopes, scope_defined, scope_globals, scope_unbound, scope_events,
        runtime_inactive)
    reported: set[int] = set()
    ctx = (parents, scope_defined, scope_globals, scope_unbound, scope_events,
           runtime_inactive, reported, filepath)
    for node in handlers:
        issues.extend(_tp05_handler_undefined(node, ctx))
    return issues
_TP23_CACHE_WORDS = frozenset({"cache", "store", "registry", "memo"})
_TP23_INVALIDATE_ATTRS = frozenset({
    "clear", "invalidate", "pop", "popitem", "discard", "remove",
})
def _is_cache_container_name(name: str | None) -> bool:
    if not name:
        return False
    leaf = _tp23_leaf_name(name)
    if leaf != leaf.lower():
        return False
    return bool(set(split_identifier(leaf)) & _TP23_CACHE_WORDS)
_TP23_SCOPE_STOP = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_TP23_MUTATOR_ATTRS = frozenset({
    "update", "setdefault", "append", "add", "extend", "insert", "put",
})
def _tp23_container_key(t: ast.AST) -> str | None:
    if isinstance(t, ast.Name):
        return t.id
    if isinstance(t, ast.Attribute):
        return dotted_name(t) or None
    return None
def _tp23_leaf_name(key: str) -> str:
    return key.rsplit(".", 1)[-1]
def _tp23_root_name(key: str) -> str:
    return key.split(".", 1)[0]
def _tp23_is_invalidation_call(node: ast.Call) -> bool:
    return (isinstance(node.func, ast.Attribute)
            and node.func.attr in _TP23_INVALIDATE_ATTRS
            and _is_cache_container_name(_tp23_container_key(node.func.value)))
def _tp23_target_names(t: ast.AST) -> set[str]:
    key = _tp23_container_key(t)
    if key is not None:
        return {key}
    if isinstance(t, (ast.Tuple, ast.List)):
        return {n for elt in t.elts for n in _tp23_target_names(elt)}
    if isinstance(t, ast.Starred):
        return _tp23_target_names(t.value)
    return set()
def _tp23_write_targets(t: ast.AST) -> list[ast.AST]:
    out: list[ast.AST] = []
    if isinstance(t, (ast.Tuple, ast.List)):
        for elt in t.elts:
            out.extend(_tp23_write_targets(elt))
    elif isinstance(t, ast.Starred):
        out.extend(_tp23_write_targets(t.value))
    elif isinstance(t, ast.Subscript):
        out.append(t)
    return out
def _iter_scope_subtree(roots, stop_types: tuple[type[ast.AST], ...], *,
                        skip_stop_roots: bool = False) -> list[ast.AST]:
    out: list[ast.AST] = []
    stack = list(reversed(list(roots)))
    while stack:
        cur = stack.pop()
        if skip_stop_roots and isinstance(cur, stop_types):
            continue
        out.append(cur)
        if isinstance(cur, stop_types):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
    return out
def _tp23_global_rebind_names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        inner = _iter_scope_subtree(
            ast.iter_child_nodes(node), _TP23_SCOPE_STOP)
        declared = {alias for item in inner if isinstance(item, ast.Global)
                    for alias in item.names if _is_cache_container_name(alias)}
        if not declared:
            continue
        for item in inner:
            if isinstance(item, ast.Assign):
                targets = {n for t in item.targets
                           for n in _tp23_target_names(t)}
            elif isinstance(item, (ast.AnnAssign, ast.AugAssign)):
                targets = _tp23_target_names(item.target)
            else:
                continue
            names |= targets & declared
    return names
def _tp23_delete_names(node: ast.Delete, is_local,
                       parents: dict, instance_bindings: frozenset[str]) -> set[str]:
    names: set[str] = set()
    for t in node.targets:
        raw_key = _tp23_container_key(subscript_base_node(t))
        if not _is_cache_container_name(raw_key):
            continue
        key = _tp23_event_key(raw_key, node, parents, instance_bindings)
        if _tp23_event_is_local(raw_key, key, node, is_local):
            continue
        names.add(key)
    return names
def _tp23_local_name_resolver(tree: ast.AST):
    parents = build_parent_map(tree)
    scope_defined: dict[int, set[str]] = {}
    scope_globals: dict[int, set[str]] = {}
    for scope in scope_roots(tree):
        defined, globals_, unbound = _tp05_scope_bindings(scope)
        scope_defined[id(scope)] = defined | unbound
        scope_globals[id(scope)] = globals_
    def is_local(key: str, node: ast.AST,
                 root: str | None) -> bool:
        root = root or _tp23_root_name(key)
        for scope in _tp05_scope_chain(node, parents, scope_defined):
            if isinstance(scope, ast.Module):
                return False
            if root in scope_globals.get(id(scope), ()):
                return False
            if _tp05_scope_exposes_name(root, scope, scope_defined):
                return True
        return False
    return is_local
def _tp23_owner_class_path(node: ast.AST, parents: dict, *,
                           stop_at_callable: bool) -> str:
    names: list[str] = []
    current = parents.get(id(node))
    while current is not None:
        if stop_at_callable and isinstance(current, _TP23_SCOPE_STOP):
            break
        if isinstance(current, ast.ClassDef):
            names.append(current.name)
        current = parents.get(id(current))
    return ".".join(reversed(names))
def _tp23_event_key(key: str, node: ast.AST, parents: dict,
                    instance_bindings: frozenset[str]) -> str:
    if "." not in key:
        return _tp23_qualify(
            key, _tp23_owner_class_path(node, parents, stop_at_callable=True))
    for prefix in ("self.", "cls."):
        if key.startswith(prefix):
            owner = _tp23_owner_class_path(node, parents,
                                           stop_at_callable=False)
            if owner:
                normalized = f"{owner}.{key[len(prefix):]}"
                if prefix == "self." and normalized in instance_bindings:
                    return key
                return normalized
            break
    return key
def _tp23_instance_attribute_bindings(
        tree: ast.AST, parents: dict,
) -> frozenset[str]:
    bound: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif (isinstance(node, (ast.AugAssign, ast.For, ast.AsyncFor))
              or (isinstance(node, ast.AnnAssign) and node.value is not None)):
            targets = [node.target]
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            targets = [item.optional_vars for item in node.items
                       if item.optional_vars is not None]
        else:
            continue
        for target in targets:
            for raw_key in _tp23_target_names(target):
                if not raw_key.startswith("self."):
                    continue
                owner = _tp23_owner_class_path(
                    node, parents, stop_at_callable=False)
                if owner:
                    bound.add(f"{owner}.{raw_key[len('self.'):]}")
    return frozenset(bound)
def _tp23_event_is_local(raw_key: str, key: str, node: ast.AST,
                         is_local) -> bool:
    normalized_receiver = key != raw_key and raw_key.startswith(("self.", "cls."))
    return (not normalized_receiver
            and is_local(key, node, _tp23_root_name(key)))
def _tp23_written_names(tree: ast.AST, is_local, parents: dict,
                        instance_bindings: frozenset[str]) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Assign):
            targets: list[ast.AST] = [
                sub for t in node.targets for sub in _tp23_write_targets(t)]
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets = _tp23_write_targets(node.target)
        elif isinstance(node, ast.AugAssign):
            targets = [node.target]
        elif (isinstance(node, ast.Call)
              and isinstance(node.func, ast.Attribute)
              and node.func.attr in _TP23_MUTATOR_ATTRS):
            targets = [node.func.value]
        else:
            continue
        for target in targets:
            raw_key = _tp23_container_key(subscript_base_node(target))
            if not _is_cache_container_name(raw_key):
                continue
            key = _tp23_event_key(raw_key, node, parents, instance_bindings)
            if _tp23_event_is_local(raw_key, key, node, is_local):
                continue
            names.add(key)
    return names
def _tp23_invalidated_names(tree: ast.AST, is_local, parents: dict,
                            instance_bindings: frozenset[str]) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call) and _tp23_is_invalidation_call(node):
            raw_key = _tp23_container_key(node.func.value)
            if raw_key:
                key = _tp23_event_key(raw_key, node, parents, instance_bindings)
                if not _tp23_event_is_local(raw_key, key, node, is_local):
                    names.add(key)
        elif isinstance(node, ast.Delete):
            names |= _tp23_delete_names(
                node, is_local, parents, instance_bindings)
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            if isinstance(node, ast.AnnAssign) and node.value is None:
                continue
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for target in targets:
                for raw_key in _tp23_target_names(target):
                    if ("." not in raw_key or raw_key.startswith("self.")
                            or not _is_cache_container_name(raw_key)):
                        continue
                    key = _tp23_event_key(raw_key, node, parents, instance_bindings)
                    if not _tp23_event_is_local(raw_key, key, node, is_local):
                        names.add(key)
    names |= _tp23_global_rebind_names(tree)
    return names
def _tp23_qualify(key: str, namespace: str) -> str:
    if not namespace or "." in key:
        return key
    return f"{namespace}.{key}"
_TP23_INSTANCE_FACTORY_FUNCS = frozenset({"field", "Field"})
_TP23_INSTANCE_FACTORY_KEYWORDS = frozenset({"default_factory", "factory"})
def _tp23_instance_factory(value: ast.AST | None) -> bool:
    """值是否为 ``field(default_factory=...)`` 型的实例级工厂字段。

    dataclasses / attrs / pydantic 对这类字段按实例各建一个容器，生命周期
    随实例回收，不属于“模块级/类级共享、长生命周期只写不失效”的缓存。
    """
    if not isinstance(value, ast.Call):
        return False
    if isinstance(value.func, ast.Name):
        factory = value.func.id
    elif isinstance(value.func, ast.Attribute):
        factory = value.func.attr
    else:
        return False
    return (factory in _TP23_INSTANCE_FACTORY_FUNCS
            and any(kw.arg in _TP23_INSTANCE_FACTORY_KEYWORDS
                    and not (isinstance(kw.value, ast.Constant)
                             and kw.value.value is None)
                    for kw in value.keywords))
def _tp23_binding(node: ast.AST, namespace: str = "") -> list[str]:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        targets = [node.target]
    else:
        return []
    if _tp23_instance_factory(node.value):
        return []
    return sorted({_tp23_qualify(name, namespace)
                   for target in targets
                   for name in _tp23_target_names(target)
                   if _is_cache_container_name(name)})
def _tp23_collect_cache_defs(tree: ast.AST) -> dict[str, list[int]]:
    cache_defs: dict[str, list[int]] = {}
    _stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while _stack:
        _cur, _namespace = _stack.pop()
        for name in _tp23_binding(_cur, _namespace):
            cache_defs.setdefault(name, []).append(_cur.lineno)
        for child in reversed(list(ast.iter_child_nodes(_cur))):
            if isinstance(child, _TP23_SCOPE_STOP):
                continue
            _child_ns = _namespace
            if isinstance(child, ast.ClassDef):
                _child_ns = (f"{_namespace}.{child.name}" if _namespace
                             else child.name)
            _stack.append((child, _child_ns))
    return cache_defs
def check_TP23(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    cache_defs = _tp23_collect_cache_defs(tree)
    if not cache_defs:
        return issues
    parents = build_parent_map(tree)
    is_local = _tp23_local_name_resolver(tree)
    instance_bindings = _tp23_instance_attribute_bindings(tree, parents)
    invalidated = _tp23_invalidated_names(
        tree, is_local, parents, instance_bindings)
    written = _tp23_written_names(tree, is_local, parents, instance_bindings)
    missing = {name: min(lines) for name, lines in cache_defs.items()
               if name not in invalidated and len(lines) == 1
               and name in written}
    if missing:
        issues.append(_tp23_report(sorted(missing),
                                  min(missing.values()), filepath))
    return issues
def _tp23_report(names: list[str], lineno: int,
                  filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TP-23", severity="P3", dimension="trap",
        file=filepath, line=lineno,
        description=f"缓存容器（{', '.join(names)}）只写无失效/清理调用"
                    "（内存增长+数据陈旧）",
        suggestion=("根因: 模块级缓存无失效路径，长生命周期进程内存单调增长。\n"
                    "修复策略: 补 TTL/容量上限淘汰；或提供 clear() 在"
                    "关键写路径调用\n参考标准: 缓存失效与容量治理（TTL/LRU）"),
    )
def check_RL03(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    bindings = _rl03_drift_bindings(tree)
    if bindings:
        issues.append(_rl03_report(bindings, filepath))
    return issues
def _rl03_drift_bindings(tree: ast.AST) -> list[tuple[int, Any]]:
    bindings = _collect_module_version_bindings(tree)
    if len({value for _, value in bindings}) > 1:
        return bindings
    return []
def _rl03_report(bindings: list[tuple[int, Any]],
                 filepath: str) -> DiagnoseFinding:
    declared = "; ".join(f"{ver!r}@L{lineno}" for lineno, ver in bindings)
    first_value = bindings[0][1]
    drift_line = next((lineno for lineno, ver in bindings[1:]
                       if ver != first_value), bindings[0][0])
    return DiagnoseFinding(
        id="RL-03", severity="P1", dimension="consistency",
        file=filepath, line=drift_line,
        description=f"同一文件内 __version__ 声明不一致：{declared}",
        suggestion=("根因: 多处 __version__ 值漂移，导入方按访问顺序"
                    "拿到不同版本，兼容分支判断随机失效。该问题属于"
                    "一致性类别。\n"
                    "修复策略: 全文件仅保留一处 __version__ 声明，"
                    "其余引用该常量\n"
                    "参考标准: PEP 396 / 单一事实来源原则"),
    )
def _collect_module_version_bindings(tree: ast.AST) -> list[tuple[int, Any]]:
    version_values: list[tuple[int, Any]] = []
    for node in iter_scope_nodes(tree):
        version_values.extend(_version_bindings_in_node(node))
    return version_values
def _version_target_value(target: ast.AST,
                          value: ast.AST | None) -> ast.AST | None:
    if isinstance(target, ast.Name):
        return value if target.id == "__version__" else None
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(elt, ast.Starred) for elt in target.elts)):
        for target_elt, value_elt in zip(target.elts, value.elts, strict=True):
            found = _version_target_value(target_elt, value_elt)
            if found is not None:
                return found
    return None
def _version_bindings_in_node(node: ast.AST) -> list[tuple[int, Any]]:
    targets = _version_assignment_targets(node)
    if not targets:
        return []
    value = getattr(node, "value", None)
    if value is None:
        return []
    bound: list[tuple[int, Any]] = []
    for target in targets:
        version_value = _version_target_value(target, value)
        if isinstance(version_value, ast.Constant):
            bound.append((node.lineno, version_value.value))
    return bound
def _version_assignment_targets(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.Assign):
        return node.targets
    if isinstance(node, ast.AnnAssign):
        return [node.target]
    return []
def check_TP25(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for (_scope, base), entries in sorted(_tp25_collect_versions(tree).items()):
        if len({params for _, params, _ in entries}) > 1:
            issues.append(_tp25_report(base, entries, filepath))
    return issues
def _tp25_collect_versions(tree: ast.AST) -> dict[_Tp25Key, list[_Tp25Entry]]:
    versions: dict[_Tp25Key, list[_Tp25Entry]] = {}
    _tp25_walk_scope(tree, (), versions)
    return versions
def _tp25_walk_scope(
    node: ast.AST,
    scope: tuple[str, ...],
    versions: dict[_Tp25Key, list[_Tp25Entry]],
) -> None:
    stack: list[tuple[ast.AST, tuple[str, ...]]] = [(node, scope)]
    while stack:
        cur, cur_scope = stack.pop()
        children = list(ast.iter_child_nodes(cur))
        _tp25_record_versions(children, cur_scope, versions)
        for child in reversed(children):
            stack.append((child, _tp25_child_scope(child, cur_scope)))
def _tp25_record_versions(children: list[ast.AST], scope: tuple[str, ...],
                          versions: dict[_Tp25Key, list[_Tp25Entry]]) -> None:
    for child in children:
        if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        match = _TP25_VERSION_RE.match(child.name)
        if match:
            versions.setdefault((scope, match.group("base")), []).append(
                (child.name, _tp25_param_names(child.args), child.lineno))
def _tp25_child_scope(child: ast.AST, scope: tuple[str, ...]) -> tuple[str, ...]:
    if isinstance(child, _TP25_SCOPE_NODES):
        return scope + (child.name,)
    return scope
def _tp25_param_names(args: ast.arguments) -> tuple[str, ...]:
    positional = [*args.posonlyargs, *args.args]
    defaulted = positional[len(positional) - len(args.defaults):]
    defaults = {id(param): default
                for param, default in zip(defaulted, args.defaults, strict=True)}
    defaults.update({id(param): default
                     for param, default in zip(
                         args.kwonlyargs, args.kw_defaults, strict=True)
                     if default is not None})
    def _name(param: ast.arg) -> str:
        default = defaults.get(id(param))
        return (param.arg if default is None
                else f"{param.arg}={ast.unparse(default)}")
    names = [_name(param) for param in args.posonlyargs]
    if args.posonlyargs:
        names.append("/")
    names.extend(_name(param) for param in args.args)
    if args.vararg:
        names.append("*" + args.vararg.arg)
    elif args.kwonlyargs:
        names.append("*")
    names.extend(_name(param) for param in args.kwonlyargs)
    if args.kwarg:
        names.append("**" + args.kwarg.arg)
    return tuple(names)
def _tp25_report(base: str, entries: list[tuple[str, tuple[str, ...], int]],
                 filepath: str) -> DiagnoseFinding:
    detail = "; ".join(f"{name}({', '.join(params)})"
                       for name, params, _ in entries)
    return DiagnoseFinding(
        id="TP-25", severity="P1", dimension="trap",
        file=filepath, line=entries[0][2],
        description=f"多版本函数参数签名不一致（{base}_v*）：{detail}",
        suggestion=("根因: 同名多版本实现参数不同步，按版本路由的调用"
                    "方拿到静默错误输出。该问题属于多版本一致性陷阱类别。\n"
                    "修复策略: 统一各版本参数签名（多余参数给默认值）；"
                    "废弃版本加 DeprecationWarning；共用同一套测试\n"
                    "参考标准: 多版本接口一致性（单一事实来源）"),
    )
def check_CL03(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    local_bindings, global_names, class_scopes = \
        collect_shadow_bindings(tree)
    scope_index = build_scope_index(tree)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Compare)
                and _cl03_uses_dir_membership(
                    node, local_bindings, global_names, class_scopes,
                    scope_index)):
            issues.append(_cl03_report(node.lineno, filepath))
    return issues
def _cl03_builtin_dir_shadowed(
        call: ast.Call,
        local_bindings: dict,
        global_names: dict,
        class_scopes: frozenset,
        scope_index: dict[int, str]) -> bool:
    scope = scope_index.get(id(call), "")
    if "dir" in local_bindings.get(scope, frozenset()):
        return True
    if owner_scope(scope, "dir", local_bindings, global_names, class_scopes):
        return True
    return "dir" in local_bindings.get("", frozenset())
def _cl03_uses_dir_membership(
        node: ast.Compare,
        local_bindings: dict,
        global_names: dict,
        class_scopes: frozenset,
        scope_index: dict[int, str]) -> bool:
    prev_operand = node.left
    for op, comp in zip(node.ops, node.comparators, strict=True):
        if (isinstance(op, (ast.In, ast.NotIn))
                and _cl03_is_dir_call(
                    comp, local_bindings, global_names, class_scopes,
                    scope_index)
                and isinstance(prev_operand, (ast.Constant, ast.Name))):
            return True
        prev_operand = comp
    return False
def _cl03_is_dir_call(
        node: ast.AST,
        local_bindings: dict,
        global_names: dict,
        class_scopes: frozenset,
        scope_index: dict[int, str]) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "dir"
            and not _cl03_builtin_dir_shadowed(
                node, local_bindings, global_names, class_scopes,
                scope_index))
def _cl03_report(lineno: int, filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="CL-03", severity="P3", dimension="trap",
        file=filepath, line=lineno,
        description=("用 dir() 做变量/属性存在性检测（dir() 返回名字列表，"
                     "不含外层/全局名字，同名遮蔽与动态属性会误判）"),
        suggestion=("根因: dir() 语义被误用为反射工具。\n"
                    "修复策略: 属性用 hasattr()/getattr(obj, 'x', default)；"
                    "全局名用 'x' in globals()；局部名直接 try/except NameError\n"
                    "参考标准: Python 语言参考 dir() 文档"),
    )
def check_TP11(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for stmts in _tp11_iter_stmt_lists(tree):
        issues.extend(_tp11_consecutive_issues(stmts, filepath))
    return issues
def _tp11_consecutive_issues(stmts: list[ast.stmt],
                             filepath: str) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    prev: str | None = None
    chain_head: ast.stmt | None = None
    for stmt in stmts:
        name = None
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            name = _bare_replace_target(stmt.value)
        if name is not None and name == prev:
            chain_head = chain_head or stmt
            continue
        if chain_head is not None and prev is not None:
            issues.append(_tp11_report(prev, chain_head, filepath))
        chain_head = None
        prev = name
    if chain_head is not None and prev is not None:
        issues.append(_tp11_report(prev, chain_head, filepath))
    return issues
def _tp11_inplace_call(call: ast.Call) -> bool:
    """``inplace=True``（pandas 等）原地修改且返回 None，不存在返回值丢失。"""
    return any(kw.arg == "inplace" and constant_truth(kw.value) is True
               for kw in call.keywords)
def _bare_replace_target(call: ast.Call) -> str | None:
    if isinstance(call.func, ast.Attribute) and call.func.attr == "replace":
        if _tp11_inplace_call(call):
            return None
        return dotted_name(call.func.value) or None
    return None
def _tp11_iter_stmt_lists(tree: ast.AST):
    for node in walk_nodes(tree):
        if not isinstance(node, _TP11_STMT_CONTAINERS):
            continue
        for _attr in ("body", "orelse", "finalbody"):
            stmts = getattr(node, _attr, None)
            if isinstance(stmts, list):
                yield stmts
def _tp11_report(name: str, stmt: ast.AST, filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TP-11", severity="P1", dimension="trap",
        file=filepath, line=stmt.lineno,
        description=f"{name}.replace(...) 返回值未接收，替换结果静默丢失",
        suggestion=("根因: str 是不可变对象，replace 返回新对象，"
                    "裸调用语句的替换全部无效。\n"
                    "修复策略: s = s.replace(a, b) 接收返回值；"
                    "多处替换可合并为循环或 str.translate\n"
                    "参考标准: Python str 不可变语义（Ruff B018）"),
    )
def _http_module_aliases(tree: ast.AST,
                         modules: frozenset[str]) -> frozenset[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            root = alias.name.split(".")[0]
            if root not in modules:
                continue
            if alias.asname is not None and alias.name != root:
                continue
            names.add(alias.asname or root)
    return frozenset(names)
def _tp26_binding_pair(node: ast.AST) -> tuple[list[ast.AST], ast.AST | None]:
    if isinstance(node, ast.Assign):
        return node.targets, node.value
    if isinstance(node, ast.AnnAssign):
        return [node.target], node.value
    return [], None
def _tp26_aligned_target_values(
        target: ast.AST, value: ast.AST) -> list[tuple[ast.AST, ast.AST]]:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(elt, ast.Starred) for elt in target.elts)):
        return [pair for target_elt, value_elt in zip(
            target.elts, value.elts, strict=True)
            for pair in _tp26_aligned_target_values(target_elt, value_elt)]
    return [(target, value)]
def _tp26_binding_values(node: ast.AST) -> list[tuple[ast.AST, ast.AST]]:
    targets, value = _tp26_binding_pair(node)
    if value is None:
        return []
    return [pair for target in targets
            for pair in _tp26_aligned_target_values(target, value)]
_TP26_MODULE_BINDING = "module"
_TP26_FACTORY_BINDING = "factory"
_TP26_SESSION_BINDING = "session"
_TP26_VERB_BINDING_PREFIX = "verb:"
_Tp26EventMap = dict[str, list[tuple[tuple[int, int], str | None]]]
class _Tp26SessionBindings(ScopeEventIndex):
    def __init__(self, tree: ast.AST,
                 http_modules: frozenset[str] = _TP26_HTTP_MODULES) -> None:
        super().__init__(tree)
        self._tree = tree
        self._scopes = scope_roots(tree)
        self._http_modules = http_modules
        self.module_aliases = _http_module_aliases(tree, http_modules)
        self._declarations: dict[
            int, tuple[frozenset[str], frozenset[str]]] = {}
        (self._attr_events,
         self._constructor_attr_events) = self._collect_attribute_events(tree)
    def _is_session_factory(self, node: ast.AST) -> bool:
        if not isinstance(node, ast.Call):
            return False
        if isinstance(node.func, ast.Name):
            return (self._binding_kind(node.func.id, node)
                    == _TP26_FACTORY_BINDING)
        if not isinstance(node.func, ast.Attribute):
            return False
        if node.func.attr not in _TP26_HTTP_FACTORIES:
            return False
        dotted = dotted_name(node.func.value)
        return bool(dotted) and self._binding_kind(
            dotted.split(".")[0], node) == _TP26_MODULE_BINDING
    def _collect_attribute_events(
            self, tree: ast.AST
    ) -> tuple[dict[str, list[tuple[tuple[int, int], bool]]],
               dict[str, list[tuple[tuple[int, int], bool]]]]:
        events: dict[str, list[tuple[tuple[int, int], bool]]] = {}
        constructor_events: dict[str, list[tuple[tuple[int, int], bool]]] = {}
        def record(name: str, node: ast.AST, is_http: bool) -> None:
            key = self._attribute_key(name, node)
            self._add_event(events, key, node, is_http)
            if self._enclosing_function_name(node) == "__init__":
                self._add_event(constructor_events, key, node, is_http)
        for node in walk_nodes(tree):
            if isinstance(node, (ast.With, ast.AsyncWith)):
                for item in node.items:
                    is_http = self._is_session_factory(item.context_expr)
                    for name in _tp26_attribute_target_names(item.optional_vars):
                        record(name, node, is_http)
                continue
            for target, value in _tp26_binding_values(node):
                is_http = self._is_session_factory(value)
                for name in _tp26_attribute_target_names(target):
                    record(name, node, is_http)
        for table in (events, constructor_events):
            for values in table.values():
                values.sort(key=lambda event: event[0])
        return events, constructor_events
    def _attribute_key(self, dotted: str, node: ast.AST) -> str:
        owner = self._enclosing_class(node)
        return f"{owner}.{dotted}" if owner else dotted
    def _enclosing_class(self, node: ast.AST) -> str:
        cur = self._parents.get(id(node))
        while cur is not None:
            if isinstance(cur, ast.ClassDef):
                return cur.name
            cur = self._parents.get(id(cur))
        return ""
    def _enclosing_function_name(self, node: ast.AST) -> str:
        cur = self._parents.get(id(node))
        while cur is not None:
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return cur.name
            cur = self._parents.get(id(cur))
        return ""
    def is_attribute_session(self, dotted: str | None, node: ast.AST) -> bool:
        if not dotted:
            return False
        key = self._attribute_key(dotted, node)
        events = self._attr_events.get(key) or self._attr_events.get(dotted)
        if events:
            found, value = self._prior_value(events, node)
            if found:
                return bool(value)
        constructor_events = (self._constructor_attr_events.get(key)
                              or self._constructor_attr_events.get(dotted))
        if (constructor_events
                and self._enclosing_function_name(node) != "__init__"):
            return bool(constructor_events[-1][1])
        return False
    def _scope_declarations(
            self, scope: ast.AST) -> tuple[frozenset[str], frozenset[str]]:
        cached = self._declarations.get(id(scope))
        if cached is None:
            cached = exec_scope_declarations(scope)
            self._declarations[id(scope)] = cached
        return cached
    def _binding_kind(self, name: str, node: ast.AST) -> str | None:
        delayed = False
        for scope in self._chain(node):
            next_delayed = delayed or isinstance(
                scope, _TP05_DELAYED_SCOPE_NODES)
            events = self._scope_events(scope).get(name)
            if isinstance(scope, ast.Module):
                events = list(events or ())
                for declared_scope in self._scopes:
                    if declared_scope is scope:
                        continue
                    _local, declared_globals = self._scope_declarations(
                        declared_scope)
                    if name not in declared_globals:
                        continue
                    events.extend(
                        self._scope_events(declared_scope).get(name) or ())
                events.sort(key=lambda event: event[0])
            if events:
                if delayed:
                    found, value = True, events[-1][1]
                else:
                    found, value = self._prior_value(events, node)
                if found:
                    return value
            local, global_names = self._scope_declarations(scope)
            if not isinstance(scope, ast.Module) and name in global_names:
                delayed = next_delayed
                continue
            if name in local:
                return None
            delayed = next_delayed
        return None
    def is_session(self, name: str, node: ast.AST) -> bool:
        return self._binding_kind(name, node) in {
            _TP26_MODULE_BINDING, _TP26_SESSION_BINDING}
    def _add_post_value_event(self, events: _Tp26EventMap, name: str,
                              node: ast.AST, value: str | None) -> None:
        end_line = getattr(node, "end_lineno", None)
        end_col = getattr(node, "end_col_offset", None)
        if end_line is None or end_col is None:
            self._add_event(events, name, node, value)
            return
        events.setdefault(name, []).append(((end_line, end_col), value))
    def _scope_events(self, scope: ast.AST) -> _Tp26EventMap:
        cached = self._events.get(id(scope))
        if cached is not None:
            return cached
        events: _Tp26EventMap = {}
        self._events[id(scope)] = events
        for name in collect_param_names(scope):
            self._add_event(events, name, scope, None)
        for node in iter_scope_nodes(scope):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names:
                    if isinstance(node, ast.Import):
                        root = alias.name.split(".")[0]
                        bound = alias.asname or root
                        is_http = (root in self._http_modules
                                   and (alias.asname is None or alias.name == root))
                        kind = _TP26_MODULE_BINDING if is_http else None
                    else:
                        bound = alias.asname or alias.name
                        module = node.module or ""
                        from_http = node.level == 0 and any(
                            module == name or module.startswith(name + ".")
                            for name in self._http_modules)
                        if from_http and alias.name in _TP26_HTTP_FACTORIES:
                            kind = _TP26_FACTORY_BINDING
                        elif from_http and alias.name in _TP26_HTTP_VERBS:
                            kind = _TP26_VERB_BINDING_PREFIX + alias.name
                        else:
                            kind = None
                    self._add_event(events, bound, node, kind)
                continue
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                self._add_event(events, node.name, node, None)
                continue
            if isinstance(node, (ast.With, ast.AsyncWith)):
                for item in node.items:
                    kind = (_TP26_SESSION_BINDING
                            if self._is_session_factory(item.context_expr) else None)
                    for name in iter_unpack_target_names(item.optional_vars):
                        self._add_event(events, name, node, kind)
                continue
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                for target, value in _tp26_binding_values(node):
                    kind = (_TP26_SESSION_BINDING
                            if self._is_session_factory(value) else None)
                    for name in iter_unpack_target_names(target):
                        self._add_post_value_event(events, name, node, kind)
                continue
            bound_names: set[str] = set()
            collect_binding_names(node, bound_names, include_imports=False)
            for name in bound_names:
                self._add_event(events, name, node, None)
        for values in events.values():
            values.sort(key=lambda event: event[0])
        return events
def _tp26_attribute_target_names(target: ast.AST | None) -> list[str]:
    if target is None:
        return []
    if isinstance(target, ast.Attribute):
        dotted = dotted_name(target)
        return [dotted] if dotted else []
    if isinstance(target, (ast.Tuple, ast.List)):
        return [name for elt in target.elts
                for name in _tp26_attribute_target_names(elt)]
    if isinstance(target, ast.Starred):
        return _tp26_attribute_target_names(target.value)
    return []
def _tp26_http_method(
        node: ast.AST, receivers: _Tp26SessionBindings) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    if isinstance(node.func, ast.Name):
        kind = receivers._binding_kind(node.func.id, node)
        if kind and kind.startswith(_TP26_VERB_BINDING_PREFIX):
            return kind[len(_TP26_VERB_BINDING_PREFIX):]
        return None
    if not isinstance(node.func, ast.Attribute):
        return None
    if node.func.attr not in _TP26_HTTP_VERBS:
        return None
    recv = node.func.value
    if isinstance(recv, ast.Call) and receivers._is_session_factory(recv):
        return node.func.attr
    if isinstance(recv, ast.Name):
        return (node.func.attr
                if receivers.is_session(recv.id, node) else None)
    dotted = dotted_name(recv)
    if dotted and dotted.split(".")[0] in receivers.module_aliases:
        return (node.func.attr
                if receivers.is_session(dotted.split(".")[0], node) else None)
    return (node.func.attr
            if receivers.is_attribute_session(dotted, node) else None)
def _tp26_is_backoff_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if isinstance(node.func, ast.Name):
        return node.func.id in _TP26_BACKOFF_ATTRS
    if not isinstance(node.func, ast.Attribute):
        return False
    if node.func.attr in _TP26_BACKOFF_ATTRS:
        return True
    dotted = dotted_name(node.func)
    return bool(dotted) and dotted.startswith("backoff.")
def _tp26_is_len_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "len")
def _tp26_is_index_traversal(call: ast.Call) -> bool:
    return any(_tp26_is_len_call(arg) for arg in call.args[:2])
def _tp26_is_counter_test(test: ast.AST) -> bool:
    if isinstance(test, ast.Constant):
        return bool(test.value)
    if isinstance(test, ast.Compare):
        return any(
            isinstance(operand, ast.Constant)
            and isinstance(operand.value, (int, float))
            and not isinstance(operand.value, bool)
            for operand in (test.left, *test.comparators))
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _tp26_is_counter_test(test.operand)
    return False
def _tp26_is_retry_loop(node) -> bool:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        it = node.iter
        if not (isinstance(it, ast.Call)
                and isinstance(it.func, ast.Name)
                and it.func.id == "range"):
            return False
        return not _tp26_is_index_traversal(it)
    if isinstance(node, ast.While):
        return _tp26_is_counter_test(node.test)
    return False
def _tp26_protected_http_calls(http_calls: list, try_nodes: list) -> list:
    protected_ids: set[int] = set()
    for try_node in try_nodes:
        for stmt in try_node.body:
            stmt_nodes = _iter_scope_subtree(
                [stmt], _TP26_SCOPE_STOP, skip_stop_roots=True)
            protected_ids.update(id(x) for x in stmt_nodes)
    return sorted((c for c in http_calls if id(c) in protected_ids),
                  key=lambda call: (call.lineno, call.col_offset))
def check_TP26(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    receivers = _Tp26SessionBindings(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            continue
        finding = _tp26_loop_finding(node, filepath, receivers)
        if finding is not None:
            issues.append(finding)
    return issues
def _tp26_loop_finding(node: ast.For | ast.AsyncFor | ast.While,
                       filepath: str,
                       receivers: _Tp26SessionBindings
                       ) -> DiagnoseFinding | None:
    if not _tp26_is_retry_loop(node):
        return None
    protected = _tp26_protected_calls(node, receivers)
    if not protected:
        return None
    return _tp26_report(protected[0].lineno, filepath)
def _tp26_process_exit_call(stmt: ast.AST) -> bool:
    """语句是否为不返回的进程退出调用（sys.exit / os._exit 等）。"""
    return (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
            and dotted_name(stmt.value.func) in _TP26_PROCESS_EXIT_CALLEES)
def _tp26_handler_exits_round(handler: ast.ExceptHandler) -> bool:
    body = getattr(handler, "body", None) or []
    if not body:
        return False
    last = body[-1]
    # raise/return/break 之外，sys.exit(1) 这类进程退出调用同样不会重试：
    # 漏判会把“失败即退出”的循环误报为无退避重试。
    return (isinstance(last, (ast.Raise, ast.Return, ast.Break))
            or _tp26_process_exit_call(last))
def _tp26_catches_exception(node: ast.AST) -> bool:
    handlers = getattr(node, "handlers", None) or []
    if not handlers:
        return False
    return any(not _tp26_handler_exits_round(handler) for handler in handlers)
def _tp26_catches_all_exceptions(node: ast.AST) -> bool:
    for handler in getattr(node, "handlers", None) or ():
        if _tp26_handler_exits_round(handler):
            continue
        exception_types = (handler.type.elts
                           if isinstance(handler.type, ast.Tuple)
                           else [handler.type])
        if any(exception_type is None
               or dotted_name(exception_type) in {
                   "Exception", "BaseException",
                   "builtins.Exception", "builtins.BaseException",
               }
               for exception_type in exception_types):
            return True
    return False
def _tp26_call_has_inner_catch_all(call: ast.Call, outer: ast.AST,
                                   parents: dict) -> bool:
    current = parents.get(id(call))
    while current is not None and current is not outer:
        if (isinstance(current, _TRY_STMT_TYPES)
                and _tp26_catches_all_exceptions(current)
                and any(_tp05_node_within(call, stmt, parents)
                        for stmt in current.body)):
            return True
        current = parents.get(id(current))
    return False
def _tp26_protected_calls(node: ast.AST,
                          receivers: _Tp26SessionBindings
                          ) -> list[ast.Call]:
    body_nodes = _iter_scope_subtree(node.body, _TP26_SCOPE_STOP,
                                     skip_stop_roots=True)
    try_nodes = [n for n in body_nodes
                 if isinstance(n, _TRY_STMT_TYPES)
                 and _tp26_catches_exception(n)]
    http_calls = [n for n in body_nodes
                  if _tp26_http_method(n, receivers) is not None]
    unbacked_tries = _tp26_unbacked_try_nodes(
        node, body_nodes, try_nodes, http_calls, receivers._parents)
    return _tp26_protected_http_calls(http_calls, unbacked_tries)
def _tp26_statement_guarantees_backoff(
        stmt: ast.stmt, backoffs: list[ast.AST], parents: dict,
) -> bool:
    for backoff in backoffs:
        if not _tp05_node_within(backoff, stmt, parents):
            continue
        current: ast.AST | None = backoff
        guaranteed = True
        while current is not stmt:
            parent = parents.get(id(current))
            if parent is None:
                guaranteed = False
                break
            if isinstance(current, ast.stmt) and current is not stmt:
                guaranteed = False
                break
            if ((isinstance(parent, ast.BoolOp)
                 and current is not parent.values[0])
                    or (isinstance(parent, ast.IfExp)
                        and current is not parent.test)
                    or isinstance(parent, (_TP05_COMPREHENSION_NODES,
                                           ast.Lambda))):
                guaranteed = False
                break
            current = parent
        if guaranteed:
            return True
    return False


def _tp26_backoff_guaranteed_before(
        backoff: ast.AST, target: ast.AST, boundary: ast.AST,
        backoffs: list[ast.AST], parents: dict,
) -> bool:
    def predicate(stmt: ast.stmt) -> bool:
        return _tp26_statement_guarantees_backoff(stmt, backoffs, parents)
    return _candidate_guaranteed_before(
        backoff, target, boundary, parents, predicate)


def _tp26_handler_has_finally_backoff(
        handler: ast.ExceptHandler, backoffs: list[ast.AST],
        loop: ast.AST, parents: dict) -> bool:
    current: ast.AST | None = handler
    while current is not None and current is not loop:
        if isinstance(current, _TRY_STMT_TYPES):
            def predicate(stmt: ast.stmt) -> bool:
                return _tp26_statement_guarantees_backoff(
                    stmt, backoffs, parents)
            if _statement_list_guarantees(current.finalbody, predicate):
                return True
        current = parents.get(id(current))
    return False
def _tp26_continue_lacks_backoff(
        try_node: ast.AST, backoffs: list[ast.AST],
        protected: list[ast.Call], loop: ast.AST, parents: dict) -> bool:
    for handler in getattr(try_node, "handlers", None) or ():
        handler_nodes = _iter_scope_subtree(
            handler.body, _TP26_SCOPE_STOP, skip_stop_roots=True)
        continues = [node for node in handler_nodes
                     if isinstance(node, ast.Continue)]
        if not continues:
            continue
        handler_backoffs = [node for node in handler_nodes
                            if _tp26_is_backoff_call(node)]
        for continue_node in continues:
            if any(_tp26_backoff_guaranteed_before(
                    backoff, continue_node, handler,
                    handler_backoffs, parents)
                   for backoff in handler_backoffs):
                continue
            if _tp26_handler_has_finally_backoff(
                    handler, backoffs, loop, parents):
                continue
            if all(any(_tp26_backoff_guaranteed_before(
                    backoff, call, loop, backoffs, parents)
                   for backoff in backoffs) for call in protected):
                continue
            return True
    return False
def _tp26_backoff_handles_exception(
        backoff: ast.AST, call: ast.Call, boundary: ast.AST,
        parents: dict) -> bool:
    current = parents.get(id(backoff))
    while current is not None:
        if isinstance(current, _TRY_STMT_TYPES):
            call_in_body = any(
                _tp05_node_within(call, stmt, parents)
                for stmt in current.body)
            if call_in_body:
                handled = any(
                    _tp05_node_within(backoff, handler, parents)
                    for handler in current.handlers)
                finalized = any(
                    _tp05_node_within(backoff, stmt, parents)
                    for stmt in current.finalbody)
                if handled or finalized:
                    return True
        if current is boundary:
            break
        current = parents.get(id(current))
    return False
def _tp26_backoff_outside_failure_path(
        backoff: ast.AST, boundary: ast.AST, parents: dict,
) -> bool:
    current: ast.AST | None = backoff
    while current is not None:
        if (isinstance(current, _TRY_STMT_TYPES)
                and any(_tp05_node_within(backoff, stmt, parents)
                        for stmt in getattr(current, "orelse", ()) or ())):
            return True
        if isinstance(current, ast.ExceptHandler):
            return True
        if current is boundary:
            break
        current = parents.get(id(current))
    return False
def _tp26_failure_backoffs(
        backoffs: list[ast.AST], try_node: ast.AST,
        protected: list[ast.Call], parents: dict) -> list[ast.AST]:
    effective: list[ast.AST] = []
    for backoff in backoffs:
        if any(_tp26_backoff_handles_exception(backoff, call, try_node, parents)
               for call in protected):
            effective.append(backoff)
            continue
        if _tp26_backoff_outside_failure_path(backoff, try_node, parents):
            continue
        in_try_body = any(
            _tp05_node_within(backoff, stmt, parents)
            for stmt in getattr(try_node, "body", ()) or ())
        backoff_position = (backoff.lineno, backoff.col_offset)
        skipped_after_call = in_try_body and any(
            backoff_position > (call.lineno, call.col_offset)
            and not _tp26_backoff_handles_exception(
                backoff, call, try_node, parents)
            for call in protected)
        if not skipped_after_call:
            effective.append(backoff)
    return effective
def _tp26_unbacked_try_nodes(
        loop: ast.AST, body_nodes: list[ast.AST], try_nodes: list[ast.AST],
        http_calls: list[ast.AST], parents: dict) -> list[ast.AST]:
    all_backoffs = [node for node in body_nodes if _tp26_is_backoff_call(node)]
    unbacked: list[ast.AST] = []
    for try_node in try_nodes:
        owned_calls = [call for call in http_calls
                       if not _tp26_call_has_inner_catch_all(
                           call, try_node, parents)]
        protected = _tp26_protected_http_calls(owned_calls, [try_node])
        if not protected:
            continue
        backoffs = _tp26_failure_backoffs(
            all_backoffs, try_node, protected, parents)
        if (not backoffs or _tp26_continue_lacks_backoff(
                try_node, backoffs, protected, loop, parents)):
            unbacked.append(try_node)
    return unbacked
def _tp26_report(lineno: int, filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TP-26", severity="P2", dimension="trap",
        file=filepath, line=lineno,
        description="重试循环内网络调用无退避间隔（失败后立即重试形成请求风暴）",
        suggestion=("根因: 对端过载或熔断时立即重试会放大流量（重试风暴），"
                    "压垮下游并拖垮自身线程池。\n"
                    "修复策略: except 分支加 time.sleep(退避) 或指数退避"
                    "（backoff 库）；配 max_retries 上限与抖动（jitter）\n"
                    "参考标准: AWS Architecture Blog / Google SRE 重试章节"),
    )
_HC02_REQUEST_MODULES = frozenset({"requests"})
_HC02_LITERAL_CONTAINERS = (ast.Dict, ast.List, ast.Tuple, ast.Set)
def _hc02_key_desc(key: ast.AST) -> str:
    return key.value if isinstance(key, ast.Constant) else "<key>"
def _hc02_bool_value_paths(value: ast.expr, prefix: str) -> list[str]:
    paths: list[str] = []
    stack: list[tuple[ast.expr, str]] = [(value, prefix)]
    while stack:
        node, cur_prefix = stack.pop()
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            paths.append(cur_prefix)
            continue
        if not isinstance(node, _HC02_LITERAL_CONTAINERS):
            continue
        if isinstance(node, ast.Dict):
            children: list[tuple[ast.expr, str]] = []
            for key, val in zip(node.keys, node.values, strict=False):
                if key is None:
                    continue
                children.append(
                    (val, f"{cur_prefix}·{_hc02_key_desc(key)!r}"))
            stack.extend(reversed(children))
        else:
            elts = [(elt, f"{cur_prefix}[{i}]")
                    for i, elt in enumerate(node.elts)]
            stack.extend(reversed(elts))
    return paths
def _hc02_payload_pairs(value: ast.expr) -> list[tuple[ast.AST, ast.AST]]:
    if isinstance(value, ast.Dict):
        return [(key, val) for key, val in
                zip(value.keys, value.values, strict=False) if key is not None]
    if not isinstance(value, (ast.List, ast.Tuple)):
        return []
    pairs: list[tuple[ast.AST, ast.AST]] = []
    for elt in value.elts:
        if (isinstance(elt, (ast.Tuple, ast.List)) and len(elt.elts) == 2
                and not any(isinstance(item, ast.Starred) for item in elt.elts)):
            pairs.append((elt.elts[0], elt.elts[1]))
    return pairs
def _hc02_kw_issues(method: str, kw: ast.keyword, call_lineno: int,
                    filepath: str) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if kw.arg not in ("params", "data"):
        return issues
    for key, val in _hc02_payload_pairs(kw.value):
        for path in _hc02_bool_value_paths(val, repr(_hc02_key_desc(key))):
            issues.append(DiagnoseFinding(
                id="HC-02", severity="P1", dimension="hardcoding",
                file=filepath, line=call_lineno,
                description=(f"requests.{method}() {kw.arg} 中键 "
                             f"{path} 为 bool 值（将序列化为 "
                             "'True'/'False' 发送）"),
                suggestion=("根因: Python bool 序列化为 'True'/'False'，"
                            "多数 Web API 仅识别 'true'/'false'，导致参数"
                            "被静默忽略。该问题属于接口健壮性类别。\n"
                            f"修复策略: 将 {kw.arg} 中 bool 值转为字符串 "
                            "str(value).lower()，或发送前统一转换\n"
                            "参考标准: requests 文档 / JSON 规范"),
            ))
    return issues
def check_HC02(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    receivers = _Tp26SessionBindings(tree, _HC02_REQUEST_MODULES)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        method = _tp26_http_method(node, receivers)
        if method is None:
            continue
        for kw in node.keywords:
            issues.extend(_hc02_kw_issues(method, kw, node.lineno, filepath))
    return issues
_RT02_QUERY_CALLEES = frozenset({"execute", "query", "fetchone", "fetchall"})
def check_RT02(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
            continue
        if node.func.attr not in ("values", "keys", "items"):
            continue
        if not isinstance(node.func.value, ast.Call):
            continue
        callee = expr_target_name(node.func.value.func)
        if callee in _RT02_QUERY_CALLEES:
            issues.append(DiagnoseFinding(
                id="RT-02", severity="P2", dimension="return_type",
                file=filepath, line=node.lineno,
                description=(f"查询结果直接调用 .{node.func.attr}()："
                             "返回值可能是 list/tuple 而非 dict"),
                suggestion=("根因: execute/fetchone/fetchall 返回 list[tuple] 或"
                            "Row 对象，直接调用 dict 视图方法触发 "
                            "AttributeError。该问题属于健壮性类别。\n"
                            "修复策略: 先判类型再取值；Row 场景用配套访问器"
                            "或转为 dict(row)\n"
                            "参考标准: DB-API 2.0 / sqlite3 文档"),
            ))
    return issues
def _rt01_dict_depth(node: ast.Dict) -> int:
    best = 1
    stack: list[tuple[ast.Dict, int]] = [(node, 1)]
    while stack:
        cur, depth = stack.pop()
        best = max(best, depth)
        for v in cur.values:
            if isinstance(v, ast.Dict):
                stack.append((v, depth + 1))
    return best
def check_RT01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.returns is not None:
            continue
        for child in iter_scope_nodes(node):
            if (isinstance(child, ast.Return) and isinstance(child.value, ast.Dict)
                    and _rt01_dict_depth(child.value) >= 3):
                issues.append(DiagnoseFinding(
                    id="RT-01", severity="P3", dimension="trap",
                    file=filepath, line=child.lineno,
                    description=f"函数 {node.name} 返回 ≥3 层嵌套 dict 字面量，无结构契约",
                    suggestion=("根因: 深嵌套 dict 返回值靠消费方层层 .get() 取值，"
                                "键名漂移静默得 None。\n"
                                "修复策略: 改用 dataclass/TypedDict 定义结构；"
                                "或至少提取 build_*_dict 构造函数\n"
                                "参考标准: Google Python 风格指南"),
                ))
                break
    return issues
def wiring_declarations() -> dict[str, dict[str, dict[str, Any]]]:
    return {
        "catalogs": {
            "aicoder_direct": {"TP-26": check_TP26},
            "traps_bindings": {
                "CL03": check_CL03, "HC02": check_HC02, "RT01": check_RT01,
                "RT02": check_RT02, "RL03": check_RL03,
                "TP05": check_TP05, "TP11": check_TP11, "TP23": check_TP23,
                "TP25": check_TP25, "TP26": check_TP26,
            },
        },
    }

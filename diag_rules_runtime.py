from __future__ import annotations

import ast
import logging
import ntpath
from collections.abc import Callable, Iterator
from itertools import combinations
from typing import NamedTuple, TypeVar

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    dotted_name,
    expr_target_name,
    in_subtree,
    is_docstring_stmt,
    is_main_check,
    iter_scope_nodes,
    node_position,
    resolve_import_binding,
    scope_roots,
)
from jwsgj.diag_shared_ast_views import (
    OPEN_FAMILY_MODULES,
    call_scope_map,
    collect_lexical_scope_table,
    drain_frame_stack,
    non_builtin_open_call_ids,
    scope_import_tables,
    scope_node_bound_names,
    tree_nodes,
)
from jwsgj.diag_shared_ast_views import (
    parent_map as _shared_parent_map,
)
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    extract_code_lines,
    join_source_lines,
)
from jwsgj.diag_shared_source_scan import (
    get_code_snippet,
)
from jwsgj.diag_types_defs import DiagnoseFinding, finding_scan_exempt
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
_T = TypeVar("_T")
__all__ = [
    "check_CV01", "check_DG02", "check_EP02", "check_EX08",
    "check_FS02", "check_LE03", "check_LE04", "check_NS01",
    "check_UH01",
]
_DEFAULT_FILEPATH = ""
_BINDING_STATEMENT_TYPES = (
    ast.stmt, ast.ExceptHandler, ast.withitem,
    ast.MatchAs, ast.MatchStar, ast.MatchMapping,
)
def _rule_scan_skip(tree: ast.AST | None, filepath: str) -> bool:
    return tree is None or finding_scan_exempt(filepath)
def _single_target_value(node: ast.AST, name: str) -> ast.AST | None:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
        targets = [node.target]
    else:
        return None
    if (len(targets) != 1 or not isinstance(targets[0], ast.Name)
            or targets[0].id != name):
        return None
    if isinstance(node, ast.AugAssign):
        return ast.BinOp(left=targets[0], op=node.op, right=node.value)
    return getattr(node, "value", None)
def _binding_in_effect_here(node: ast.AST, cand: ast.AST) -> bool:
    """``node`` 是否位于候选绑定语句 ``cand`` 中“绑定已生效”的区域。

    ``x = x + 1`` 的右值、``for p in [p]`` 的迭代源等在绑定生效**前**求值，
    不能把 cand 自身当作其先前绑定；但 For/AsyncFor/ExceptHandler/
    FunctionDef 等复合语句的目标名在其 body/orelse/finalbody 执行前就已
    绑定，体内的使用必须把 cand 视为先前绑定——否则会越过循环/异常目标，
    误取更早的同名绑定（``p = "a/b"; for p in paths: open(p, "w")`` 被误报）。
    """
    for attr in ("body", "orelse", "finalbody"):
        block = getattr(cand, attr, None)
        if isinstance(block, list) and any(
                in_subtree(node, stmt) for stmt in block):
            return True
    return False
class _RuntimeBindings:
    def __init__(self, tree: ast.Module) -> None:
        self.tree = tree
        self.table = collect_lexical_scope_table(tree)
        self.call_scopes = call_scope_map(self.table)
        self.imports = scope_import_tables(tree)
        self.parents = _shared_parent_map(tree)
        self._prior_binding_cache: dict[int, ast.AST | None] = {}
        self._sequential_binding_cache: dict[tuple[int, str], tuple] = {}
        self._resolving_paths: set[int] = set()
    def scope_for(self, node: ast.AST) -> ast.AST:
        return self.call_scopes.get(id(node), self.tree)
    def _nearest_scope(self, node: ast.AST) -> ast.AST | None:
        cur = self.parents.get(node)
        # Lambda 是独立词法作用域（见 collect_lexical_scope_table 的
        # _push_def_scope）：缺省它会让 lambda 体内的名称越过 Lambda 作用域，
        # 被解析到外层同名绑定，lambda 形参也查不到（FS-02 误报根因）。
        while cur is not None and not isinstance(
                cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                      ast.ClassDef, ast.Lambda, ast.Module)):
            cur = self.parents.get(cur)
        return cur
    def _statement_block(self, stmt: ast.AST) -> list | None:
        parent = self.parents.get(stmt)
        if parent is None:
            return None
        for field in ("body", "orelse", "finalbody"):
            block = getattr(parent, field, None)
            if isinstance(block, list) and any(item is stmt for item in block):
                return block
        return None
    def _binding_dominates(self, stmt: ast.AST, use: ast.AST) -> bool:
        block = self._statement_block(stmt)
        if block is None:
            return False
        for index, item in enumerate(block):
            if item is stmt:
                return any(in_subtree(use, later)
                           for later in block[index + 1:])
        return False
    def _outer_scope_binding(self, scope: ast.AST,
                             name: str) -> ast.AST | None:
        parent = self.table.parent.get(scope)
        while parent is not None:
            if isinstance(parent, ast.ClassDef):
                parent = self.table.parent.get(parent)
                continue
            bound_nodes = [
                cand for cand in iter_scope_nodes(parent)
                if isinstance(cand, _BINDING_STATEMENT_TYPES)
                and name in scope_node_bound_names(cand)
            ]
            if len(bound_nodes) > 1:
                return None
            if bound_nodes:
                return _single_target_value(bound_nodes[0], name)
            # 外层作用域以非语句形式绑定了同名（形参、推导式目标等）时，
            # 该名称已被遮蔽且没有静态右值：必须返回 None（动态值），不能
            # 继续向外取到更外层/模块的同名绑定。``global``/``nonlocal``
            # 声明名在 _absorb_scope_declarations 中已从本作用域 bound 移除，
            # 不受此检查影响。
            if name in self.table.bound.get(parent, frozenset()):
                return None
            parent = self.table.parent.get(parent)
        return None
    @staticmethod
    def _in_first_iterable(node: ast.AST, comp: ast.AST) -> bool:
        generators = getattr(comp, "generators", None)
        first_iter = getattr(generators[0], "iter", None) if generators else None
        return first_iter is not None and in_subtree(node, first_iter)
    def _resolve_prior_binding(self, node: ast.Name) -> ast.AST | None:
        scope = self._nearest_scope(node)
        if scope is None:
            return None
        # 推导式是独立词法作用域（iter_scope_nodes 在其边界停止）：若 node
        # 位于绑定了同名目标的推导式内，该名称由推导式目标绑定、无静态右值，
        # 不能越过它取外层同名绑定；仅首个生成器的迭代源在外层作用域求值。
        cur = self.parents.get(node)
        while cur is not None and cur is not scope:
            if (isinstance(cur, COMP_SCOPE_NODES)
                    and node.id in self.table.bound.get(cur, frozenset())
                    and not self._in_first_iterable(node, cur)):
                return None
            cur = self.parents.get(cur)
        use_pos = node_position(node)
        last_value: ast.AST | None = None
        last_stmt: ast.AST | None = None
        for cand in iter_scope_nodes(scope):
            if not isinstance(cand, _BINDING_STATEMENT_TYPES):
                continue
            if node.id not in scope_node_bound_names(cand):
                continue
            if in_subtree(node, cand) and not _binding_in_effect_here(node, cand):
                continue
            line = getattr(cand, "lineno", None)
            if line is None:
                parent = self.parents.get(cand)
                line = getattr(parent, "lineno", None)
                if line is None:
                    return None
                pos = (line, getattr(parent, "col_offset", 0))
            else:
                pos = (line, getattr(cand, "col_offset", 0))
            if pos >= use_pos:
                continue
            value = _single_target_value(cand, node.id)
            last_value = value
            last_stmt = cand if value is not None else None
        if last_value is None or last_stmt is None:
            if node.id in self.table.bound.get(scope, frozenset()):
                return None
            return self._outer_scope_binding(scope, node.id)
        if not self._binding_dominates(last_stmt, node):
            return None
        return last_value
    def prior_binding_value(self, node: ast.Name) -> ast.AST | None:
        key = id(node)
        if key not in self._prior_binding_cache:
            self._prior_binding_cache[key] = self._resolve_prior_binding(node)
        return self._prior_binding_cache[key]
    def resolve_path_name(
            self, node: ast.Name,
            build: Callable[[ast.AST], _T]) -> _T | None:
        key = id(node)
        if key in self._resolving_paths:
            return None
        value = self.prior_binding_value(node)
        if value is None:
            return None
        self._resolving_paths.add(key)
        try:
            return build(value)
        finally:
            self._resolving_paths.discard(key)
    @staticmethod
    def _sequential_binding_position(node: ast.AST) -> tuple[int, int]:
        value = None
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                             ast.NamedExpr)):
            value = node.value
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            value = node.iter
        elif isinstance(node, ast.withitem):
            value = node.context_expr
        anchor = value or node
        return (getattr(anchor, "end_lineno", None)
                or getattr(anchor, "lineno", 0),
                getattr(anchor, "end_col_offset", None)
                or getattr(anchor, "col_offset", 0))
    def _sequential_binding_events(self, scope: ast.AST,
                                   name: str) -> tuple:
        key = (id(scope), name)
        if key not in self._sequential_binding_cache:
            events = []
            for cand in iter_scope_nodes(scope):
                if (isinstance(cand, _BINDING_STATEMENT_TYPES)
                        and name in scope_node_bound_names(cand)):
                    events.append((self._sequential_binding_position(cand),
                                   isinstance(cand, (ast.Import, ast.ImportFrom))))
            events.sort(key=lambda event: event[0])
            self._sequential_binding_cache[key] = tuple(events)
        return self._sequential_binding_cache[key]
    def _sequential_shadows(self, node: ast.AST, scope: ast.AST,
                            name: str, imported: bool) -> bool:
        use_pos = node_position(node)
        latest = None
        for event in self._sequential_binding_events(scope, name):
            if event[0] >= use_pos:
                continue
            latest = event
        if latest is None:
            return False
        return not latest[1] if imported else True
    def _shadows_at(self, node: ast.AST, scope: ast.AST, name: str,
                    imported: bool) -> bool:
        direct = scope
        crossed_function = False
        while scope is not None:
            if isinstance(scope, ast.ClassDef) and scope is not direct:
                scope = self.table.parent.get(scope)
                continue
            delayed = isinstance(
                scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
            bindings = (self.table.shadow_bound if imported
                        else self.table.bound)
            if not isinstance(scope, (ast.Module, ast.ClassDef)) or crossed_function:
                if name in bindings.get(scope, frozenset()):
                    return True
            elif self._sequential_shadows(node, scope, name, imported):
                return True
            crossed_function = crossed_function or delayed
            scope = self.table.parent.get(scope)
        return False
    def module_member(self, node: ast.AST, module: str, member: str,
                      scope: ast.AST, *, allow_unbound: bool = False,
                      allow_unbound_bare: bool = False) -> bool:
        if isinstance(node, ast.Name):
            return self._name_module_member(
                node, module, member, scope,
                allow_unbound_bare=allow_unbound_bare)
        return self._attribute_module_member(
            node, module, member, scope, allow_unbound=allow_unbound)
    def _name_module_member(self, node: ast.Name, module: str, member: str,
                            scope: ast.AST, *,
                            allow_unbound_bare: bool) -> bool:
        binding = resolve_import_binding(
            self.imports, self.parents, node, node.id)
        if (binding is not None and binding[0] == "from"
                and f"{binding[1]}.{binding[2]}" == f"{module}.{member}"
                and not self._shadows_at(node, scope, node.id, True)):
            return True
        return (allow_unbound_bare and node.id == member
                and not self._shadows_at(node, scope, node.id, False))
    def _attribute_module_member(self, node: ast.AST, module: str, member: str,
                                 scope: ast.AST, *,
                                 allow_unbound: bool) -> bool:
        if not isinstance(node, ast.Attribute) or node.attr != member:
            return False
        receiver = dotted_name(node.value)
        if not receiver:
            return False
        root = receiver.split(".", 1)[0]
        if (allow_unbound and dotted_name(node) == f"{module}.{member}"
                and not self._shadows_at(node, scope, root, False)):
            return True
        if self._shadows_at(node, scope, root, True):
            return False
        binding = resolve_import_binding(
            self.imports, self.parents, node, root)
        if binding is None:
            return False
        base = (binding[1] if binding[0] == "import"
                else f"{binding[1]}.{binding[2]}")
        return base + receiver[len(root):] == module
def _le03_broad_elem(ctx_call: ast.Call,
                     bindings: _RuntimeBindings) -> tuple[str, bool] | None:
    scope = bindings.scope_for(ctx_call)
    for arg in ctx_call.args:
        starred = isinstance(arg, ast.Starred)
        if starred:
            # 解包目标可为任意可迭代字面量；``suppress(*{Exception})``
            # 的 Set 此前被整体跳过导致 LE-03 漏报。
            if not isinstance(arg.value, (ast.Tuple, ast.List, ast.Set)):
                continue
            elems = arg.value.elts
        else:
            elems = arg.elts if isinstance(arg, ast.Tuple) else [arg]
        in_tuple = starred or isinstance(arg, ast.Tuple)
        for elem in elems:
            for name in ("Exception", "BaseException"):
                if bindings.module_member(
                        elem, "builtins", name, scope, allow_unbound=True,
                        allow_unbound_bare=True):
                    return name, in_tuple
    return None
def check_LE03(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    logger.debug("规则入口 check_LE03 执行")
    issues: list[DiagnoseFinding] = []
    bindings = _RuntimeBindings(tree)
    for node in tree_nodes(tree):
        if isinstance(node, (ast.With, ast.AsyncWith)):
            _le03_scan_with_node(issues, node, bindings, filepath)
    return issues
def _le03_scan_with_node(issues: list, node: ast.AST,
                         bindings: _RuntimeBindings, filepath: str) -> None:
    for item in node.items:
        ctx = item.context_expr
        if not (isinstance(ctx, ast.Call) and ctx.args):
            continue
        scope = bindings.scope_for(ctx)
        if not bindings.module_member(
                ctx.func, "contextlib", "suppress", scope, allow_unbound=True):
            continue
        hit = _le03_broad_elem(ctx, bindings)
        if hit is None:
            continue
        issues.append(_le03_make_issue(node, *hit, filepath))
def _le03_make_issue(node: ast.AST, elem_id: str, in_tuple: bool,
                     filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="LE-03", severity="P2", dimension="logging",
        file=filepath, line=node.lineno,
        description=(f"contextlib.suppress 参数含 {elem_id}（捕获过宽，静默吞掉所有异常）"
                     if in_tuple
                     else f"contextlib.suppress({elem_id}) 捕获过宽（静默吞掉所有异常）"),
        suggestion=("根因: suppress(Exception) 会静默吞掉一切异常（含编程错误），问题被完全掩盖。该问题属于日志/异常处理类别。\n"
                    "修复策略: 仅 suppress 预期异常: suppress(FileNotFoundError, PermissionError)\n"
                    "参考标准: contextlib 文档 / tryceratops TRY301"),
    )
def _is_ignore_constant(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and node.value == "ignore"
def _le04_positional_args(args: list[ast.expr]) -> list[ast.expr] | None:
    expanded: list[ast.expr] = []
    for arg in args:
        if not isinstance(arg, ast.Starred):
            expanded.append(arg)
            continue
        if not isinstance(arg.value, (ast.Tuple, ast.List)):
            return None
        expanded.extend(arg.value.elts)
    return expanded
def _le04_action_repr(node: ast.Call) -> str | None:
    args = _le04_positional_args(node.args)
    if args and _is_ignore_constant(args[0]):
        return "'ignore'"
    if any(kw.arg == "action" and _is_ignore_constant(kw.value)
           for kw in node.keywords):
        return "action='ignore'"
    return None
_LE04_POSITIONAL_SLOTS: dict[str, tuple[str, ...]] = {
    "filterwarnings": ("message", "category", "module", "lineno", "append"),
    "simplefilter": ("category", "lineno", "append"),
}
def _le04_has_filter(node: ast.Call, method: str,
                     bindings: _RuntimeBindings) -> bool:
    scope = bindings.scope_for(node)
    for kw in node.keywords:
        if kw.arg is None:
            if _le04_expanded_filter_present(
                    kw.value, bindings, scope):
                return True
            continue
        if _le04_narrows(kw.arg, kw.value, bindings, scope):
            return True
    slots = _LE04_POSITIONAL_SLOTS.get(method, ())
    args = _le04_positional_args(node.args)
    if args is None:
        args = node.args
    return any(_le04_narrows(slot, value, bindings, scope)
               for slot, value in zip(slots, args[1:], strict=False))
def _le04_narrows(slot: str, value: ast.AST,
                  bindings: _RuntimeBindings, scope: ast.AST) -> bool:
    if slot == "message" or slot == "module":
        return not (isinstance(value, ast.Constant) and value.value == "")
    if slot == "lineno":
        return not (isinstance(value, ast.Constant) and value.value == 0)
    if slot == "category":
        broad_warning = (
            bindings.module_member(
                value, "builtins", "Warning", scope, allow_unbound=True,
                allow_unbound_bare=True)
            or bindings.module_member(
                value, "warnings", "Warning", scope, allow_unbound=True)
        )
        return not broad_warning
    return False
def _le04_expanded_filter_present(
        value: ast.AST, bindings: _RuntimeBindings,
        scope: ast.AST) -> bool:
    if isinstance(value, ast.Dict):
        for key, item in zip(value.keys, value.values, strict=True):
            if key is None:
                if _le04_expanded_filter_present(item, bindings, scope):
                    return True
            elif (isinstance(key, ast.Constant)
                  and isinstance(key.value, str)):
                if _le04_narrows(key.value, item, bindings, scope):
                    return True
            else:
                return True
        return False
    if (isinstance(value, ast.Call) and len(value.args) <= 1
            and bindings.module_member(
                value.func, "builtins", "dict", scope, allow_unbound=True,
                allow_unbound_bare=True)):
        if value.args and _le04_expanded_filter_present(
                value.args[0], bindings, scope):
            return True
        for kw in value.keywords:
            if kw.arg is None:
                if _le04_expanded_filter_present(kw.value, bindings, scope):
                    return True
            elif _le04_narrows(kw.arg, kw.value, bindings, scope):
                return True
        return False
    return True
_LE04_METHOD_NAMES: tuple[str, ...] = tuple(_LE04_POSITIONAL_SLOTS)
def check_LE04(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    issues: list[DiagnoseFinding] = []
    bindings = _RuntimeBindings(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        _callee = _le04_callee_label(node, bindings)
        if _callee is None:
            continue
        _label, _method = _callee
        _action = _le04_action_repr(node)
        if (_action is not None
                and not _le04_has_filter(node, _method, bindings)):
            issues.append(_le04_make_issue(node, _label, _action, filepath))
    return issues
def _le04_callee_label(node: ast.Call,
                       bindings: _RuntimeBindings) -> tuple[str, str] | None:
    func = node.func
    scope = bindings.scope_for(node)
    for method in _LE04_METHOD_NAMES:
        if bindings.module_member(
                func, "warnings", method, scope, allow_unbound=True):
            label = func.id if isinstance(func, ast.Name) else f"warnings.{method}"
            return label, method
    return None
def _le04_make_issue(node: ast.Call, callee: str, action: str,
                     filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="LE-04", severity="P2", dimension="logging",
        file=filepath, line=node.lineno,
        description=f"{callee}({action}) 无过滤条件全局静默警告",
        suggestion=("根因: 全局忽略所有警告会掩盖弃用告警与真实问题。该问题属于日志/异常处理类别。\n"
                    "修复策略: 精确过滤: warnings.filterwarnings('ignore', category=DeprecationWarning, module='pkg.x')\n"
                    "参考标准: warnings 文档"),
    )
_EX08_UNSUPPORTED_TYPE = object()
def _ex08_type_frame_step(node: ast.AST, stack: list[ast.AST],
                          out: list) -> None:
    if isinstance(node, ast.Name):
        out.append(node.id)
    elif isinstance(node, ast.Attribute):
        out.append(dotted_name(node) or _ast_shape_key(node))
    elif isinstance(node, ast.Subscript):
        out.append(_ast_shape_key(node))
    elif isinstance(node, ast.Tuple):
        stack.extend(reversed(node.elts))
    elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        stack.append(node.right)
        stack.append(node.left)
    else:
        out.append(_EX08_UNSUPPORTED_TYPE)
def _ex08_type_names(handler: ast.ExceptHandler) -> list[str] | None:
    t = handler.type
    if t is None:
        return None
    names = drain_frame_stack(t, _ex08_type_frame_step)
    if any(name is _EX08_UNSUPPORTED_TYPE for name in names):
        return None
    return names
def _shape_list_frames(items: list) -> list:
    frames: list = []
    for index in range(len(items) - 1, -1, -1):
        frames.append(items[index])
        if index:
            frames.append(",")
    return frames
def _shape_ast_frames(node: ast.AST) -> list:
    frames: list = []
    for name, value in reversed(list(ast.iter_fields(node))):
        frames.append(repr(value) if isinstance(value, str) else value)
        frames.append(name + "=")
    return frames
def _ast_shape_key(root: ast.AST | list) -> str:
    out: list[str] = []
    stack: list = [root]
    while stack:
        item = stack.pop()
        if isinstance(item, str):
            out.append(item)
            continue
        if item is None:
            out.append("None")
            continue
        if isinstance(item, list):
            out.append("[")
            stack.append("]")
            stack.extend(_shape_list_frames(item))
            continue
        if isinstance(item, ast.AST):
            out.extend((type(item).__name__, "("))
            stack.append(")")
            stack.extend(_shape_ast_frames(item))
            continue
        out.append(repr(item))
    return "".join(out)
def _ex08_is_trivial_body(handler: ast.ExceptHandler) -> bool:
    body = handler.body
    if len(body) != 1:
        return False
    stmt = body[0]
    if isinstance(stmt, ast.Pass):
        return True
    return (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
            and stmt.value.value in (None, Ellipsis))
def _ex08_is_pairable(handler: ast.ExceptHandler,
                      type_names: list[str] | None) -> bool:
    return type_names is not None and not _ex08_is_trivial_body(handler)
def _ex08_aliases_pairable(handlers: list[ast.ExceptHandler],
                           group: list[int]) -> bool:
    aliases = {handlers[index].name for index in group}
    if len(aliases) <= 1:
        return True
    referenced = {
        node.id
        for index in group
        for statement in handlers[index].body
        for node in walk_nodes(statement)
        if isinstance(node, ast.Name)
    }
    return aliases.isdisjoint(referenced)
def _ex08_duplicate_groups(
        handlers: list[ast.ExceptHandler]) -> tuple[list[list[int]], list]:
    keys = [_ast_shape_key(handler.body) for handler in handlers]
    types = [_ex08_type_names(handler) for handler in handlers]
    groups: list[list[int]] = []
    group: list[int] = []
    def flush_group() -> None:
        type_sets = {tuple(sorted(set(types[index]))) for index in group}
        if (len(type_sets) > 1
                and _ex08_aliases_pairable(handlers, group)):
            groups.append(list(group))
    for index, handler in enumerate(handlers):
        if not _ex08_is_pairable(handler, types[index]):
            flush_group()
            group = []
            continue
        if group and keys[group[-1]] != keys[index]:
            flush_group()
            group = []
        group.append(index)
    flush_group()
    return groups, types
def _ex08_make_duplicate_finding(
        handlers: list[ast.ExceptHandler], group: list[int], types: list,
        source_lines: list[str], filepath: str) -> DiagnoseFinding:
    lines = "、".join(f"L{handlers[index].lineno}" for index in group)
    merged_types = sorted({name for index in group for name in types[index]})
    aliases = {handlers[index].name for index in group}
    alias = aliases.pop() if len(aliases) == 1 else None
    alias_suffix = f" as {alias}" if alias is not None else ""
    anchor = handlers[group[-1]]
    return DiagnoseFinding(
        id="EX-08", severity="P2", dimension="exception_handling",
        file=filepath, line=anchor.lineno,
        description=(f"except 处理块重复：{lines} 捕获不同异常但处理逻辑"
                     f"完全相同，可合并为 except ({', '.join(merged_types)})"
                     f"{alias_suffix}: 共用一个处理块"),
        suggestion=("根因: 多个 except 分支处理逻辑完全相同，属于重复代码。该问题属于异常处理类别。\n"
                    "修复策略: 合并为 except (Type1, Type2): 共用一个处理块；"
                    "若未来分支需要差异化处理再拆分\n"
                    "参考标准: PEP 8 / pylint / SonarQube"),
        code_snippet=get_code_snippet(source_lines, anchor.lineno),
    )
def check_EX08(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    issues: list[DiagnoseFinding] = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Try):
            continue
        handlers = node.handlers
        if len(handlers) < 2:
            continue
        groups, types = _ex08_duplicate_groups(handlers)
        issues.extend(
            _ex08_make_duplicate_finding(
                handlers, group, types, source_lines, filepath)
            for group in groups)
    return issues
def _ep02_type_checking_positive(test: ast.AST,
                                 bindings: _RuntimeBindings) -> bool:
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        return any(_ep02_type_checking_positive(value, bindings)
                   for value in test.values)
    return bindings.module_member(
        test, "typing", "TYPE_CHECKING", bindings.tree)
def _ep02_is_dunder_assignment(node: ast.AST) -> bool:
    if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        return False
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    if not targets:
        return False
    return all(isinstance(t, ast.Name) and t.id.startswith("__") and t.id.endswith("__")
               for t in targets)
_EP02_EXEMPT_NODE_TYPES = (
    ast.Import, ast.ImportFrom, ast.FunctionDef,
    ast.AsyncFunctionDef, ast.ClassDef, ast.Pass,
)
_EP02_LOG_METHODS = frozenset({
    'debug', 'info', 'warning', 'error', 'critical', 'exception', 'log'})
_EP02_ENV_READERS = frozenset({'environ', 'getenv', 'getcwd', 'getcwdb'})
def _ep02_call_is_bootstrap(func: ast.AST) -> bool:
    if isinstance(func, ast.Name):
        return func.id.startswith('_')
    if isinstance(func, ast.Attribute):
        base: ast.AST = func.value
        while isinstance(base, ast.Attribute):
            base = base.value
        if isinstance(base, ast.Name) and base.id.startswith('_'):
            return True
        return func.attr in _EP02_LOG_METHODS or func.attr == 'register'
    return False
def _ep02_is_bootstrap_stmt(node: ast.AST) -> bool:
    if isinstance(node, ast.If):
        return any(isinstance(sub, ast.Attribute) and sub.attr in _EP02_ENV_READERS
                   or isinstance(sub, ast.Name) and sub.id in _EP02_ENV_READERS
                   for sub in tree_nodes(node.test))
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        return _ep02_call_is_bootstrap(node.value.func)
    if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.value is not None \
            and isinstance(node.value, ast.Call):
        return _ep02_call_is_bootstrap(node.value.func)
    return False
def _ep02_is_exempt_stmt(node: ast.AST, guards: list[ast.If],
                         bindings: _RuntimeBindings) -> bool:
    if isinstance(node, _EP02_EXEMPT_NODE_TYPES):
        return True
    if _ep02_is_bootstrap_stmt(node):
        return True
    if is_docstring_stmt(node):
        return True
    if isinstance(node, ast.If):
        if _ep02_type_checking_positive(node.test, bindings):
            return True
        if node in guards:
            return True
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return True
    return _ep02_is_dunder_assignment(node)
def _ep02_count_logic_stmts(stmts: list[ast.stmt], guards: list[ast.If],
                            bindings: _RuntimeBindings) -> int:
    count = 0
    for node in stmts:
        if isinstance(node, ast.If) and (
                _ep02_type_checking_positive(node.test, bindings)
                or node in guards):
            count += _ep02_count_logic_stmts(node.orelse, guards, bindings)
        elif isinstance(node, ast.If) and _ep02_is_bootstrap_stmt(node):
            count += _ep02_count_logic_stmts(node.body, guards, bindings)
            count += _ep02_count_logic_stmts(node.orelse, guards, bindings)
        elif isinstance(node, TRY_TYPES):
            blocks = [node.body, node.orelse, node.finalbody]
            blocks.extend(handler.body for handler in node.handlers)
            count += sum(_ep02_count_logic_stmts(block, guards, bindings)
                         for block in blocks)
        elif not _ep02_is_exempt_stmt(node, guards, bindings):
            count += 1
            if isinstance(node, ast.Match):
                count += sum(
                    _ep02_count_logic_stmts(case.body, guards, bindings)
                    for case in node.cases)
            else:
                for field in ("body", "orelse"):
                    block = getattr(node, field, None)
                    if isinstance(block, list):
                        count += _ep02_count_logic_stmts(
                            block, guards, bindings)
    return count
def check_EP02(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    issues: list[DiagnoseFinding] = []
    normalized = (filepath or "").replace("\\", "/")
    if normalized.rsplit("/", 1)[-1] != "__init__.py":
        return issues
    if not isinstance(tree, ast.Module):
        return issues
    bindings = _RuntimeBindings(tree)
    guards = [node for node in tree.body
              if isinstance(node, ast.If) and is_main_check(node.test)]
    logic_stmts = _ep02_count_logic_stmts(tree.body, guards, bindings)
    if logic_stmts > 10:
        issues.append(DiagnoseFinding(
            id="EP-02", severity="P2", dimension="module-design",
            file=filepath, line=1,
            title="__init__.py 中包含过多业务逻辑",
            description=(f"__init__.py 有 {logic_stmts} 条模块级非 import/非定义语句，"
                         "增加模块加载时间和副作用"),
            suggestion=("根因: __init__.py 承载业务逻辑会拖慢包导入并放大循环导入风险。"
                        "该问题属于包设计类别。\n"
                        "修复策略: 将业务逻辑移到独立子模块，__init__.py 仅保留导入、"
                        "dunder 声明与必要的再导出\n"
                        "参考标准: PEP 8 / Python 包设计最佳实践"),
            rule_ref="PEP 8 / package design",
        ))
    return issues
def _runtime_sequence_branch(parent: ast.AST, child: ast.AST,
                             specs: tuple) -> tuple | None:
    for field_name, label, identify_child in specs:
        candidates = getattr(parent, field_name, ())
        if not isinstance(candidates, (list, tuple)):
            candidates = (candidates,)
        for candidate in candidates:
            if child is candidate:
                marker = (id(parent), label)
                return marker + ((id(child),) if identify_child else ())
    return None
_RUNTIME_BRANCH_SPECS = (
    ((ast.If, ast.IfExp), (
        ("body", "body", False), ("orelse", "else", False),
    )),
    ((ast.For, ast.AsyncFor, ast.While), (
        ("body", "body", False), ("orelse", "else", False),
    )),
    (TRY_TYPES, (
        ("body", "body", False), ("handlers", "handler", True),
        ("orelse", "else", False),
    )),
    ((ast.With, ast.AsyncWith), (("body", "with", False),)),
)
def _runtime_conditional_child(parent: ast.AST,
                               child: ast.AST) -> tuple | None:
    if isinstance(parent, TRY_TYPES) and not parent.handlers:
        return None
    for node_types, specs in _RUNTIME_BRANCH_SPECS:
        if isinstance(parent, node_types):
            return _runtime_sequence_branch(parent, child, specs)
    if isinstance(parent, ast.Match):
        for index, case in enumerate(parent.cases):
            if child is case:
                return (id(parent), "case", index)
    if isinstance(parent, ast.BoolOp):
        for index, value in enumerate(parent.values[1:], 1):
            if child is value:
                return (id(parent), "short_circuit", index)
    return None
def _runtime_execution_path(node: ast.AST, parents: dict,
                            scope: ast.AST) -> tuple:
    path: list[tuple] = []
    cur = node
    while cur is not scope and cur in parents:
        parent = parents[cur]
        marker = _runtime_conditional_child(parent, cur)
        if marker is not None:
            path.append(marker)
        cur = parent
    return tuple(reversed(path))
def _runtime_path_is_prefix(prefix: tuple, path: tuple) -> bool:
    return len(prefix) <= len(path) and path[:len(prefix)] == prefix
def _runtime_ancestor_child(node: ast.AST, ancestor: ast.AST,
                            parents: dict, scope: ast.AST) -> ast.AST | None:
    cur = node
    while cur is not scope:
        parent = parents.get(cur)
        if parent is ancestor:
            return cur
        if parent is None:
            return None
        cur = parent
    return None
def _fs02_iter_exec_body(scope: ast.AST) -> Iterator[tuple[ast.AST, bool]]:
    stop = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    body = getattr(scope, "body", None)
    stack: list[tuple[ast.AST, bool]] = (
        [(item, False) for item in body] if isinstance(body, list)
        else [(scope, False)])
    while stack:
        cur, in_class = stack.pop()
        yield cur, in_class
        if isinstance(cur, stop):
            continue
        child_in_class = in_class or isinstance(cur, ast.ClassDef)
        stack.extend((child, child_in_class)
                     for child in ast.iter_child_nodes(cur))
def _fs02_scope_calls(scope: ast.AST) -> list[ast.Call]:
    return [n for n, _in_class in _fs02_iter_exec_body(scope)
            if isinstance(n, ast.Call)]
def _fs02_call_function_def(
        call: ast.Call, bindings: _RuntimeBindings,
        *, _lookup_invocation: bool = True
        ) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    if not isinstance(call.func, ast.Name):
        return None
    name = call.func.id
    direct = bindings.scope_for(call)
    child_scope = direct
    scope = direct
    while scope is not None:
        if isinstance(scope, ast.ClassDef) and scope is not direct:
            scope = bindings.table.parent.get(scope)
            continue
        if name not in bindings.table.bound.get(scope, frozenset()):
            child_scope = scope
            scope = bindings.table.parent.get(scope)
            continue
        candidates = [
            node for node in iter_scope_nodes(scope)
            if isinstance(node, _BINDING_STATEMENT_TYPES)
            and name in scope_node_bound_names(node)]
        invocation = None
        if scope is not direct and _lookup_invocation:
            invocation = _fs02_earliest_call_to(scope, child_scope, bindings)
        if scope is direct or invocation is not None:
            use_pos = node_position(call if scope is direct else invocation)
            prior = [node for node in candidates
                     if bindings._sequential_binding_position(node) < use_pos]
            if not prior:
                return None
            candidate = max(
                prior, key=bindings._sequential_binding_position)
        else:
            if len(candidates) != 1:
                return None
            candidate = candidates[0]
        return (candidate if isinstance(
            candidate, (ast.FunctionDef, ast.AsyncFunctionDef)) else None)
    return None
def _fs02_calls_to(scope: ast.AST, target: ast.AST,
                   bindings: _RuntimeBindings) -> list[ast.Call]:
    name = getattr(target, "name", "")
    if not name:
        return []
    return [
        call for call in _fs02_scope_calls(scope)
        if isinstance(call.func, ast.Name) and call.func.id == name
        and (not isinstance(target, ast.AsyncFunctionDef)
             or isinstance(bindings.parents.get(call), ast.Await))
        and _fs02_call_function_def(
            call, bindings, _lookup_invocation=False) is target]
def _fs02_earliest_call_to(
        scope: ast.AST, target: ast.AST,
        bindings: _RuntimeBindings) -> ast.Call | None:
    matches = _fs02_calls_to(scope, target, bindings)
    return min(matches, key=node_position) if matches else None
def _fs02_call_argument_parts(
        node: ast.AST | None, bindings: _RuntimeBindings,
        params: dict[str, object] | None = None) -> list | None:
    parts = _fs02_path_parts(node, bindings, params)
    if parts is not None:
        return parts
    dynamic = _fs02_dynamic_part(node, bindings)
    return None if dynamic is _FS02_DYNAMIC else [dynamic]
def _fs02_bind_call_literals(call: ast.Call, target: ast.AST,
                             bindings: _RuntimeBindings,
                             caller_params: dict[str, object] | None = None
                             ) -> tuple[dict[str, object], frozenset[str]]:
    spec = getattr(target, "args", None)
    if spec is None:
        return {}, frozenset()
    positional = [*getattr(spec, "posonlyargs", ()), *spec.args]
    kwonly = [*spec.kwonlyargs]
    bound: dict[str, object] = {}
    unknown: set[str] = set()
    star_seen = False
    for index, value in enumerate(call.args):
        if isinstance(value, ast.Starred):
            star_seen = True
            unknown.update(param.arg for param in positional[index:])
            break
        if index >= len(positional):
            continue
        param = positional[index]
        parts = _fs02_call_argument_parts(value, bindings, caller_params)
        if parts is None:
            unknown.add(param.arg)
        else:
            bound[param.arg] = tuple(parts)
    if star_seen:
        unknown.update(param.arg for param in positional)
    for kw in call.keywords:
        if not kw.arg:
            unknown.update(param.arg for param in positional)
            unknown.update(param.arg for param in kwonly)
            continue
        parts = _fs02_call_argument_parts(
            kw.value, bindings, caller_params)
        if parts is None:
            unknown.add(kw.arg)
        else:
            bound[kw.arg] = tuple(parts)
    provided = frozenset(bound) | frozenset(unknown)
    positional_defaults = zip(
        positional[len(positional) - len(spec.defaults):], spec.defaults,
        strict=False)
    default_items = [*positional_defaults, *zip(
        kwonly, spec.kw_defaults, strict=False)]
    for param, value in default_items:
        if param.arg in provided or value is None:
            continue
        parts = _fs02_call_argument_parts(value, bindings)
        if parts is not None:
            bound[param.arg] = tuple(parts)
    return bound, provided
def _fs02_anchor_after_statement(anchor: ast.AST, statement: ast.AST,
                                 scope: ast.AST, parents: dict) -> bool:
    cur = anchor
    while cur is not scope and cur in parents:
        parent = parents[cur]
        for field in ("body", "orelse", "finalbody"):
            block = getattr(parent, field, None)
            if not isinstance(block, list):
                continue
            cur_index = next((index for index, item in enumerate(block)
                              if item is cur), None)
            statement_index = next(
                (index for index, item in enumerate(block)
                 if item is statement), None)
            if cur_index is not None and statement_index is not None:
                return statement_index < cur_index
        cur = parent
    return False
def _fs02_non_swallowing_try_guarantee(call: ast.Call, anchor: ast.AST,
                                       scope: ast.AST, parents: dict) -> bool:
    cur = call
    while cur is not scope and cur in parents:
        parent = parents[cur]
        if isinstance(parent, TRY_TYPES) and parent.handlers:
            call_child = _runtime_ancestor_child(call, parent, parents, scope)
            diverges = all(
                handler.body and isinstance(
                    handler.body[-1],
                    (ast.Raise, ast.Return, ast.Break, ast.Continue))
                for handler in parent.handlers)
            if (call_child is not None
                    and any(stmt is call_child for stmt in parent.body)
                    and _runtime_execution_path(call, parents, parent)
                    == ((id(parent), "body"),)
                    and diverges
                    and _fs02_anchor_after_statement(
                        anchor, parent, scope, parents)):
                return True
        cur = parent
    return False
def _fs02_call_is_guaranteed(call: ast.Call, anchor: ast.AST | None,
                             scope: ast.AST, parents: dict) -> bool:
    if (anchor is not None and _fs02_non_swallowing_try_guarantee(
            call, anchor, scope, parents)):
        return True
    call_path = _runtime_execution_path(call, parents, scope)
    if anchor is None:
        return not call_path
    cur = anchor
    while cur is not scope and cur in parents:
        parent = parents[cur]
        if isinstance(parent, TRY_TYPES):
            call_child = _runtime_ancestor_child(call, parent, parents, scope)
            if (call_child is not None
                    and any(stmt is call_child for stmt in parent.body)):
                if any(stmt is cur for stmt in parent.finalbody):
                    return False
                call_try_path = _runtime_execution_path(call, parents, parent)
                if (any(stmt is cur for stmt in parent.orelse)
                        and call_try_path == ((id(parent), "body"),)):
                    return True
        cur = parent
    anchor_path = _runtime_execution_path(anchor, parents, scope)
    return _runtime_path_is_prefix(call_path, anchor_path)
class _FS02Evidence:
    def __init__(self, tree: ast.AST, parent_map: dict) -> None:
        self.parent_map = parent_map
        self.bindings = _RuntimeBindings(tree)
        self._cache: dict[
            tuple[int, tuple[int, int] | None, frozenset, str | tuple | None,
                  tuple[tuple[str, object], ...], int | None], bool] = {}
    def scope_creates_dir(
        self,
        scope: ast.AST,
        before: tuple[int, int] | None = None,
        visiting: frozenset = frozenset(),
        required_dir: str | tuple | None = None,
        param_literals: tuple[tuple[str, object], ...] = (),
        anchor: ast.AST | None = None,
    ) -> bool:
        key = (id(scope), before, visiting, required_dir, param_literals,
               id(anchor) if anchor is not None else None)
        if key in self._cache:
            return self._cache[key]
        params = dict(param_literals)
        calls = _fs02_scope_calls(scope)
        calls = [call for call in calls
                 if (before is None or node_position(call) <= before)
                 and _fs02_call_is_guaranteed(
                     call, anchor, scope, self.parent_map)]
        creates = (any(
            _fs02_mkdir_covers(c, required_dir, self.bindings, params)
            for c in calls)
                   or self._called_local_creates_dir(
                       calls, visiting, required_dir, params))
        self._cache[key] = creates
        return creates
    def _called_local_creates_dir(self, calls: list[ast.Call],
                                 visiting: frozenset,
                                 required_dir: str | tuple | None,
                                 params: dict[str, object] | None) -> bool:
        for call in calls:
            inner = _fs02_call_function_def(call, self.bindings)
            if inner is None or id(inner) in visiting:
                continue
            if (isinstance(inner, ast.AsyncFunctionDef)
                    and not isinstance(self.parent_map.get(call), ast.Await)):
                continue
            bound, _provided = _fs02_bind_call_literals(
                call, inner, self.bindings, params)
            if self.scope_creates_dir(
                    inner, visiting=visiting | {id(inner)},
                    required_dir=required_dir,
                    param_literals=tuple(sorted(bound.items()))):
                return True
        return False
    def chain_creates_dir(self, node: ast.AST) -> bool:
        required_dir = _fs02_required_dir(node, self.bindings)
        cur = self.parent_map.get(node)
        child_scope: ast.AST | None = None
        while cur is not None:
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Module)):
                if child_scope is None:
                    if self.scope_creates_dir(
                            cur, before=node_position(node),
                            required_dir=required_dir, anchor=node):
                        return True
                else:
                    calls = _fs02_calls_to(cur, child_scope, self.bindings)
                    if calls:
                        # 所有可见调用点都必须先建目录；只检查最早一处会把
                        # 后续未覆盖的调用静默漏掉。
                        for call in calls:
                            bound, _provided = _fs02_bind_call_literals(
                                call, child_scope, self.bindings)
                            call_required = _fs02_substitute_required(
                                required_dir, bound)
                            if not self.scope_creates_dir(
                                    cur, before=node_position(call),
                                    required_dir=call_required, anchor=call):
                                return False
                        return True
                child_scope = cur
            cur = self.parent_map.get(cur)
        return False
_FS02_PATH_CTOR_NAMES = frozenset(
    {"Path", "PurePath", "PosixPath", "WindowsPath"})
_FS02_PATH_METHODS = frozenset({
    "joinpath", "resolve", "absolute", "expanduser",
    "with_name", "with_stem", "with_suffix",
})
_FS02_PARENT_METHODS = frozenset({"parent"})
_FS02_IDENTITY_PATH_METHODS = frozenset({
    "resolve", "absolute", "expanduser",
})
_FS02_DIRNAME_ARG_NAMES = ("p", "path", "name")
_FS02_FINAL_COMPONENT_METHODS = frozenset({
    "with_name", "with_stem", "with_suffix",
})
_FS02_DYNAMIC = object()
class _FS02DynamicPart(NamedTuple):
    shape: str
    binding: int | None
    name: str | None = None
def _fs02_is_dynamic(part: object) -> bool:
    return part is _FS02_DYNAMIC or isinstance(part, _FS02DynamicPart)
def _fs02_dynamic_part(node: ast.AST | None,
                       bindings: _RuntimeBindings) -> object:
    if node is None:
        return _FS02_DYNAMIC
    origin = (bindings.prior_binding_value(node)
              if isinstance(node, ast.Name) else None)
    lexical_scope = bindings._nearest_scope(node) or bindings.tree
    binding = id(origin) if origin is not None else id(lexical_scope)
    shape = _ast_shape_key(node)
    if any(isinstance(part, ast.Call) for part in walk_nodes(node)):
        # 含调用节点的结果不可静态求值，但同一调用点仍是稳定身份：
        # 用源码位置区分不同调用点，避免把 a() 与 b() 误判为同一目录。
        line, column = node_position(node)
        shape = f"{shape}@{line}:{column}"
    name = node.id if isinstance(node, ast.Name) else None
    return _FS02DynamicPart(shape, binding, name)
def _fs02_substitute_required(required_dir: object, bound: dict) -> object:
    """用调用实参绑定替换 callee 形参的动态占位，供 caller 作用域比对。"""
    if not isinstance(required_dir, tuple) or not bound:
        return required_dir
    parts: list = []
    for part in required_dir:
        if (isinstance(part, _FS02DynamicPart) and part.name
                and part.name in bound):
            parts.extend(bound[part.name])
        else:
            parts.append(part)
    return tuple(parts)
def _fs02_path_ctor_name(func: ast.AST, bindings: _RuntimeBindings,
                         scope: ast.AST) -> str | None:
    for name in sorted(_FS02_PATH_CTOR_NAMES):
        if bindings.module_member(
                func, "pathlib", name, scope, allow_unbound=True,
                allow_unbound_bare=True):
            return name
    return None
def _fs02_is_path_expr(node: ast.AST | None,
                       bindings: _RuntimeBindings) -> bool:
    if isinstance(node, ast.Call):
        scope = bindings.scope_for(node)
        if _fs02_path_ctor_name(node.func, bindings, scope) is not None:
            return True
        func = node.func
        return (isinstance(func, ast.Attribute)
                and func.attr in _FS02_PATH_METHODS
                and _fs02_is_path_expr(func.value, bindings))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return (_fs02_is_path_expr(node.left, bindings)
                or _fs02_is_path_expr(node.right, bindings))
    if isinstance(node, ast.Attribute) and node.attr == "parent":
        return _fs02_is_path_expr(node.value, bindings)
    if isinstance(node, ast.Name):
        return bool(bindings.resolve_path_name(
            node, lambda value: _fs02_is_path_expr(value, bindings)))
    return False
def _fs02_path_expr_receiver(call: ast.Call,
                             bindings: _RuntimeBindings) -> ast.AST | None:
    func = call.func
    if (isinstance(func, ast.Attribute)
            and _fs02_is_path_expr(func.value, bindings)):
        return func.value
    return None
def _fs02_mode_value(call: ast.Call,
                     bindings: _RuntimeBindings) -> str | None:
    for kw in call.keywords:
        if kw.arg == "mode" and isinstance(kw.value, ast.Constant) \
                and isinstance(kw.value.value, str):
            return kw.value.value
    index = 0 if _fs02_path_expr_receiver(call, bindings) is not None else 1
    if len(call.args) > index:
        arg = call.args[index]
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            return arg.value
    return None
def _fs02_mode_write(call: ast.Call, bindings: _RuntimeBindings) -> bool:
    mode = _fs02_mode_value(call, bindings)
    return bool(mode) and any(c in mode for c in "wax+")
def _fs02_segment(pieces: list) -> object:
    pieces = [piece for piece in pieces
              if not isinstance(piece, str) or piece]
    if not pieces:
        return ""
    if not any(_fs02_is_dynamic(piece) for piece in pieces):
        return "".join(pieces)
    if any(piece is _FS02_DYNAMIC for piece in pieces):
        return _FS02_DYNAMIC
    if len(pieces) == 1:
        return pieces[0]
    shape = "|".join(
        piece if isinstance(piece, str)
        else f"<{piece.shape}:{piece.binding}>"
        if isinstance(piece, _FS02DynamicPart) else "<dynamic>"
        for piece in pieces)
    return _FS02DynamicPart(shape, None)
def _fs02_joined_parts(node: ast.JoinedStr, bindings: _RuntimeBindings,
                       params: dict[str, object] | None) -> list:
    segments: list = []
    current: list = []
    for part in node.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            pieces = part.value.replace("\\", "/").split("/")
            for index, piece in enumerate(pieces):
                if index:
                    segments.append(_fs02_segment(current))
                    current = []
                current.append(piece)
            continue
        value = part.value if isinstance(part, ast.FormattedValue) else None
        pieces = _fs02_path_parts(value, bindings, params)
        for index, piece in enumerate(
                pieces if pieces is not None
                else [_fs02_dynamic_part(value, bindings)]):
            if index:
                segments.append(_fs02_segment(current))
                current = []
            current.append(piece)
    segments.append(_fs02_segment(current))
    return segments
def _fs02_join_parts(base: list, extra: list) -> list:
    if all(isinstance(part, str) for part in [*base, *extra]):
        joined = ntpath.join("/".join(base), "/".join(extra))
        return joined.replace("\\", "/").split("/")
    drive_absolute = (
        bool(extra) and isinstance(extra[0], str) and len(extra[0]) == 2
        and extra[0][0].isalpha() and extra[0][1] == ":")
    if extra and (extra[0] == "" or drive_absolute):
        return list(extra)
    return [*base, *extra]
def _fs02_concat_parts(args: list, bindings: _RuntimeBindings,
                       params: dict[str, object] | None) -> list:
    parts: list = []
    for arg in args:
        sub = _fs02_path_parts(arg, bindings, params)
        arg_parts = (sub if sub is not None
                     else [_fs02_dynamic_part(arg, bindings)])
        parts = _fs02_join_parts(parts, arg_parts)
    return parts
def _fs02_string_add_parts(node: ast.BinOp, bindings: _RuntimeBindings,
                           params: dict[str, object] | None) -> list | None:
    left = _fs02_path_parts(node.left, bindings, params)
    right = _fs02_path_parts(node.right, bindings, params)
    if left is None and right is None:
        return None
    left_parts = (left if left is not None
                  else [_fs02_dynamic_part(node.left, bindings)])
    right_parts = (right if right is not None
                   else [_fs02_dynamic_part(node.right, bindings)])
    if not left_parts or not right_parts:
        return None
    boundary = _fs02_segment([left_parts[-1], right_parts[0]])
    return [*left_parts[:-1], boundary, *right_parts[1:]]
def _fs02_path_division_parts(node: ast.BinOp, bindings: _RuntimeBindings,
                              params: dict[str, object] | None
                              ) -> list | None:
    left = _fs02_path_parts(node.left, bindings, params)
    right = _fs02_path_parts(node.right, bindings, params)
    if left is None and right is None:
        return None
    left_parts = (left if left is not None
                  else [_fs02_dynamic_part(node.left, bindings)])
    right_parts = (right if right is not None
                   else [_fs02_dynamic_part(node.right, bindings)])
    return _fs02_join_parts(left_parts, right_parts)
def _fs02_path_call_parts(node: ast.Call, bindings: _RuntimeBindings,
                          params: dict[str, object] | None) -> list | None:
    scope = bindings.scope_for(node)
    if _fs02_path_ctor_name(node.func, bindings, scope) is not None:
        return _fs02_concat_parts(node.args, bindings, params)
    if bindings.module_member(
            node.func, "os.path", "join", scope, allow_unbound=True):
        return _fs02_concat_parts(node.args, bindings, params)
    if bindings.module_member(
            node.func, "os.path", "dirname", scope, allow_unbound=True):
        return _fs02_parent_parts(
            _fs02_first_path_arg(node), bindings, params)
    if not isinstance(node.func, ast.Attribute):
        return None
    if node.func.attr == "joinpath":
        base = _fs02_path_parts(node.func.value, bindings, params)
        if base is None:
            return None
        extra = _fs02_concat_parts(node.args, bindings, params)
        return _fs02_join_parts(base, extra)
    if node.func.attr in _FS02_FINAL_COMPONENT_METHODS:
        base = _fs02_path_parts(node.func.value, bindings, params)
        if base is None or not base or len(node.args) != 1 or node.keywords:
            return None
        return [*base[:-1], _FS02_DYNAMIC]
    if node.func.attr in _FS02_PARENT_METHODS:
        return _fs02_parent_parts(node.func.value, bindings, params)
    if node.func.attr in _FS02_IDENTITY_PATH_METHODS:
        return _fs02_path_parts(node.func.value, bindings, params)
    return None
def _fs02_path_parts(node: ast.AST | None, bindings: _RuntimeBindings,
                     params: dict[str, object] | None = None) -> list | None:
    if isinstance(node, ast.Constant):
        if isinstance(node.value, str):
            return node.value.replace("\\", "/").split("/")
        return None
    if isinstance(node, ast.JoinedStr):
        return _fs02_joined_parts(node, bindings, params)
    if isinstance(node, ast.Name):
        if params and node.id in params:
            value = params[node.id]
            if isinstance(value, str):
                return value.replace("\\", "/").split("/")
            return list(value)
        return bindings.resolve_path_name(
            node, lambda value: _fs02_path_parts(value, bindings, params))
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Div):
            return _fs02_path_division_parts(node, bindings, params)
        if isinstance(node.op, ast.Add):
            return _fs02_string_add_parts(node, bindings, params)
    if isinstance(node, ast.Call):
        return _fs02_path_call_parts(node, bindings, params)
    if (isinstance(node, ast.Attribute)
            and node.attr in _FS02_PARENT_METHODS):
        return _fs02_parent_parts(node.value, bindings, params)
    return None
def _fs02_parent_parts(node: ast.AST | None, bindings: _RuntimeBindings,
                       params: dict[str, object] | None) -> list | None:
    base = _fs02_path_parts(node, bindings, params)
    if base is None:
        return None
    return base[:-1] or [""]
def _fs02_first_path_arg(node: ast.Call) -> ast.AST | None:
    if node.args:
        return node.args[0]
    return next((kw.value for kw in node.keywords
                 if kw.arg in _FS02_DIRNAME_ARG_NAMES), None)
def _fs02_parts_nested(parts: list) -> bool:
    parent = parts[:-1]
    if not any(_fs02_is_dynamic(part) for part in parent):
        normalized = ntpath.normpath("/".join(parent)).replace("\\", "/")
        _drive, tail = ntpath.splitdrive(normalized)
        if normalized in ("", ".", "..") or tail in ("", "/"):
            return False
    return any(_fs02_is_dynamic(part) or part not in ("", ".", "..")
               for part in parent)
def _fs02_static_prefix(parts: list) -> str | None:
    prefix: list[str] = []
    for part in parts:
        if _fs02_is_dynamic(part):
            break
        prefix.append(part)
    return "/".join(prefix) or None
def _fs02_path_is_nested(arg: ast.AST,
                         bindings: _RuntimeBindings) -> bool:
    parts = _fs02_path_parts(arg, bindings)
    return parts is not None and _fs02_parts_nested(parts)
def _fs02_open_path_arg(node: ast.Call,
                        bindings: _RuntimeBindings) -> ast.AST | None:
    receiver = _fs02_path_expr_receiver(node, bindings)
    if receiver is not None:
        return receiver
    if node.args:
        return node.args[0]
    return next((kw.value for kw in node.keywords if kw.arg == "file"), None)
_FS02_OPEN_MODULES = OPEN_FAMILY_MODULES | {"builtins"}
def _fs02_is_supported_open_call(node: ast.Call,
                                 bindings: _RuntimeBindings) -> bool:
    func = node.func
    if expr_target_name(func) != "open":
        return False
    if isinstance(func, ast.Name):
        return True
    scope = bindings.scope_for(node)
    if (_fs02_path_expr_receiver(node, bindings) is not None
            or _fs02_path_ctor_name(func.value, bindings, scope) is not None):
        return True
    return any(bindings.module_member(
        func, module, "open", scope, allow_unbound=True)
        for module in sorted(_FS02_OPEN_MODULES))
def _fs02_is_open_write_nested(node: ast.AST,
                               bindings: _RuntimeBindings) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if not _fs02_is_supported_open_call(node, bindings):
        return False
    path_arg = _fs02_open_path_arg(node, bindings)
    if path_arg is None:
        return False
    return (_fs02_mode_write(node, bindings)
            and _fs02_path_is_nested(path_arg, bindings))
def _fs02_required_dir(node: ast.Call,
                       bindings: _RuntimeBindings) -> str | tuple | None:
    parts = _fs02_path_parts(_fs02_open_path_arg(node, bindings), bindings)
    if parts is None:
        return None
    parent = parts[:-1]
    if not parent:
        return None
    if any(_fs02_is_dynamic(part) for part in parent):
        return tuple(parent)
    return "/".join(parent).replace("\\", "/") or None
def _fs02_literal_from(node: ast.AST | None, bindings: _RuntimeBindings,
                       params: dict[str, object] | None = None) -> str | None:
    parts = _fs02_path_parts(node, bindings, params)
    return None if parts is None else _fs02_static_prefix(parts)
def _fs02_mkdir_path_arg(call: ast.Call,
                         bindings: _RuntimeBindings) -> ast.AST | None:
    receiver = _fs02_path_expr_receiver(call, bindings)
    if receiver is not None:
        return receiver
    return call.args[0] if call.args else next(
        (kw.value for kw in call.keywords
         if kw.arg in ("name", "path", "dir")), None)
def _fs02_dynamic_dir_covers(created: list, required: tuple,
                             recursive: bool) -> bool:
    if any(part is _FS02_DYNAMIC for part in [*created, *required]):
        return False
    def normalize(parts) -> tuple:
        normalized = []
        for index, part in enumerate(parts):
            if _fs02_is_dynamic(part) or part not in ("", "."):
                normalized.append(part)
                continue
            drive_root = (
                index == 1 and isinstance(parts[0], str)
                and len(parts[0]) == 2 and parts[0][0].isalpha()
                and parts[0][1] == ":")
            leading_root = all(previous == "" for previous in parts[:index])
            if part == "" and (leading_root or drive_root):
                normalized.append(part)
        return tuple(normalized)
    c, r = normalize(created), normalize(required)
    if not r:
        return True
    if not recursive:
        return c == r
    return len(c) >= len(r) and c[:len(r)] == r
def _fs02_dir_covers(created: str, required: str, recursive: bool) -> bool:
    def _norm(value: str) -> str:
        normalized = value.replace("\\", "/")
        return ntpath.normpath(normalized).replace("\\", "/")
    c, r = _norm(created), _norm(required)
    if not r or r == "/":
        return True
    if not c:
        return False
    return r == c or (recursive and c.startswith(r + "/"))
_FS02_MKDIR_MEMBERS: tuple[str, ...] = ("makedirs", "mkdir")
def _fs02_mkdir_flavor(call: ast.Call,
                       bindings: _RuntimeBindings) -> str | None:
    func = call.func
    scope = bindings.scope_for(call)
    if isinstance(func, ast.Name):
        for member in _FS02_MKDIR_MEMBERS:
            if bindings.module_member(func, "os", member, scope):
                return member
        return None
    if not isinstance(func, ast.Attribute):
        return None
    for member in _FS02_MKDIR_MEMBERS:
        if bindings.module_member(
                func, "os", member, scope, allow_unbound=True):
            return member
    if func.attr != "mkdir":
        return None
    if _fs02_is_path_expr(func.value, bindings):
        return "mkdir"
    return None
def _fs02_mkdir_covers(call: ast.Call, required_dir: str | tuple | None,
                       bindings: _RuntimeBindings,
                       params: dict[str, object] | None) -> bool:
    flavor = _fs02_mkdir_flavor(call, bindings)
    if required_dir is None or flavor is None:
        return False
    arg = _fs02_mkdir_path_arg(call, bindings)
    recursive = flavor == "makedirs"
    if (flavor == "mkdir" and isinstance(call.func, ast.Attribute)
            and _fs02_is_path_expr(call.func.value, bindings)):
        recursive = any(
            kw.arg == "parents" and isinstance(kw.value, ast.Constant)
            and bool(kw.value.value) for kw in call.keywords)
    if isinstance(required_dir, tuple):
        created = _fs02_call_argument_parts(arg, bindings, params)
        return (created is not None
                and _fs02_dynamic_dir_covers(created, required_dir, recursive))
    literal = _fs02_literal_from(arg, bindings, params)
    if literal is None:
        return False
    return _fs02_dir_covers(literal, required_dir, recursive)
def _fs02_finding(node: ast.Call, source_lines: list[str],
                  filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="FS-02", severity="P2", dimension="robustness",
        file=filepath, line=node.lineno,
        title="open() 写模式嵌套目录路径未确保目录存在",
        description=("写模式 open() 的目标路径含子目录，但作用域内未见可覆盖 "
                     "目标父目录的 os.makedirs/mkdir 调用；目录不存在时运行时抛 "
                     "FileNotFoundError，写入任务整体失败"),
        suggestion=("根因: 写入嵌套目录前未创建目录。该问题属于健壮性类别。\n"
                    "修复策略: 写入前调用 "
                    "os.makedirs(os.path.dirname(path), exist_ok=True)"
                    "（幂等安全）；目录确定已存在时可用注释显式说明\n"
                    "参考标准: PEP 8"),
        code_snippet=get_code_snippet(source_lines, node.lineno),
        rule_ref="runtime FileNotFoundError prevention",
    )
def check_FS02(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    issues: list[DiagnoseFinding] = []
    evidence = _FS02Evidence(tree, _shared_parent_map(tree))
    shadowed_ids = non_builtin_open_call_ids(tree)
    for node in tree_nodes(tree):
        if not _fs02_is_open_write_nested(node, evidence.bindings):
            continue
        if id(node) in shadowed_ids:
            continue
        if evidence.chain_creates_dir(node):
            continue
        issues.append(_fs02_finding(node, source_lines, filepath))
    return issues
def _dg02_mapping_keys(arg: ast.AST) -> set[str]:
    if isinstance(arg, ast.Dict):
        return {key.value for key in arg.keys
                if isinstance(key, ast.Constant)
                and isinstance(key.value, str)}
    if isinstance(arg, (ast.List, ast.Tuple, ast.Set)):
        return {pair.elts[0].value for pair in arg.elts
                if isinstance(pair, (ast.Tuple, ast.List))
                and len(pair.elts) == 2
                and isinstance(pair.elts[0], ast.Constant)
                and isinstance(pair.elts[0].value, str)}
    return set()
def _dg02_literal_keys(call: ast.Call) -> set[str]:
    keys: set[str] = set()
    for arg in call.args:
        keys |= _dg02_mapping_keys(arg)
    for kw in call.keywords:
        if kw.arg is None:
            keys |= _dg02_mapping_keys(kw.value)
        else:
            keys.add(kw.arg)
    return keys
def _dg02_path_child(node: ast.AST, ancestor: ast.AST,
                     parents: dict) -> ast.AST | None:
    cur = node
    parent = parents.get(cur)
    while parent is not None and parent is not ancestor:
        cur = parent
        parent = parents.get(cur)
    return cur if parent is ancestor else None
def _dg02_if_slot(ancestor: ast.If, cur: ast.AST) -> int | None:
    if any(stmt is cur for stmt in ancestor.body):
        return 0
    if any(stmt is cur for stmt in ancestor.orelse):
        return 1
    return None
def _dg02_ifexp_slot(ancestor: ast.IfExp, cur: ast.AST) -> int | None:
    if ancestor.body is cur:
        return 0
    if ancestor.orelse is cur:
        return 1
    return None
def _dg02_owned_body_slot(node: ast.AST, owners: list, cur: ast.AST,
                          parents: dict, offset: int) -> int | None:
    for index, owner in enumerate(owners):
        if owner is not cur:
            continue
        inner = _dg02_path_child(node, owner, parents)
        if inner is not None and any(
                statement is inner for statement in owner.body):
            return offset + index
        return None
    return None
def _dg02_try_slot(node: ast.AST, ancestor: ast.Try,
                   cur: ast.AST, parents: dict) -> int | None:
    if any(stmt is cur for stmt in ancestor.body):
        return 0
    if any(stmt is cur for stmt in ancestor.orelse):
        return 1 + len(ancestor.handlers)
    return _dg02_owned_body_slot(node, ancestor.handlers, cur, parents, 1)
def _dg02_branch_slot(node: ast.AST, ancestor: ast.AST,
                      parents: dict) -> int | None:
    cur = _dg02_path_child(node, ancestor, parents)
    if cur is None:
        return None
    if isinstance(ancestor, ast.If):
        return _dg02_if_slot(ancestor, cur)
    if isinstance(ancestor, ast.IfExp):
        return _dg02_ifexp_slot(ancestor, cur)
    if isinstance(ancestor, ast.Try):
        return _dg02_try_slot(node, ancestor, cur, parents)
    if isinstance(ancestor, ast.Match):
        return _dg02_owned_body_slot(node, ancestor.cases, cur, parents, 0)
    return None
def _dg02_lca(a: ast.AST, b: ast.AST, parents: dict) -> ast.AST | None:
    chain_a: set[ast.AST] = set()
    cur: ast.AST | None = a
    while cur is not None:
        chain_a.add(cur)
        cur = parents.get(cur)
    cur = b
    while cur is not None:
        if cur in chain_a:
            return cur
        cur = parents.get(cur)
    return None
def _dg02_pair_exclusive(a: ast.Call, b: ast.Call,
                         parents: dict) -> bool:
    if a is b:
        return False
    lca = _dg02_lca(a, b, parents)
    if not isinstance(lca, (ast.If, ast.IfExp, ast.Try, ast.Match)):
        return False
    slot_a = _dg02_branch_slot(a, lca, parents)
    slot_b = _dg02_branch_slot(b, lca, parents)
    if None in (slot_a, slot_b) or slot_a == slot_b:
        return False
    return not (isinstance(lca, ast.Try) and (slot_a == 0 or slot_b == 0))
def _dg02_first_coexisting_pair(
        writers: list[tuple[int, ast.Call]], parents: dict, *,
        target: str, key: str, scope: ast.AST,
        bindings: _RuntimeBindings) -> tuple[int, int] | None:
    for (first_ln, first), (override_ln, override) in combinations(writers, 2):
        if _dg02_pair_exclusive(first, override, parents):
            continue
        if _dg02_target_reset_between(
                target, key, first, override, scope, parents, bindings):
            continue
        return first_ln, override_ln
    return None
def _dg02_collect_target_updates(
        scope: ast.AST) -> dict[str, list[tuple[int, set[str], ast.Call]]]:
    per_target: dict[str, list[tuple[int, set[str], ast.Call]]] = {}
    for node in iter_scope_nodes(scope):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "update"):
            continue
        target = dotted_name(node.func.value)
        if not target:
            continue
        per_target.setdefault(target, []).append(
            (node.lineno, _dg02_literal_keys(node), node))
    return per_target
def _dg02_override_finding(
    target: str,
    key: str,
    first_ln: int,
    override_ln: int,
    source_lines: list[str],
    filepath: str,
) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="DG-02", severity="P2", dimension="correctness",
        file=filepath, line=override_ln,
        description=(f"字典 '{target}' 在同一作用域被多次 update 且键 "
                     f"'{key}' 重复写入（L{first_ln} → L{override_ln}），"
                     f"后调用的值会静默覆盖前者，可能导致数据隐式丢失"),
        suggestion=("根因: 多次 update 写入同名键，前值被静默覆盖。该问题属于正确性类别。\n"
                    "修复策略: 确认覆盖是否有意——状态流转改为显式赋值 cfg['k'] = v 并注释；"
                    "无意覆盖则合并为一次 update({...}) 或 {**d, 'k': v} 显式合并并记录键变化\n"
                    "参考标准: PEP 8 / pylint / SonarQube"),
        code_snippet=get_code_snippet(source_lines, override_ln),
    )
def _dg02_key_writers(calls: list[tuple[int, set[str], ast.Call]],
                      key: str) -> list[tuple[int, ast.Call]]:
    return sorted(((ln, call) for ln, keys, call in calls if key in keys),
                  key=lambda item: item[0])
def _rebinding_targets(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, (ast.Assign, ast.Delete)):
        return list(node.targets)
    if isinstance(node, (ast.AugAssign, ast.NamedExpr)):
        return [node.target]
    if isinstance(node, ast.AnnAssign):
        return [node.target] if node.value is not None else []
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    return []
def _rebinding_names(target: ast.AST) -> set[str]:
    if isinstance(target, (ast.Tuple, ast.List)):
        return {name for elt in target.elts
                for name in _rebinding_names(elt)}
    if isinstance(target, ast.Starred):
        return _rebinding_names(target.value)
    name = dotted_name(target)
    return {name} if name else set()
def _node_rebinding_names(node: ast.AST) -> set[str]:
    names = {name for target in _rebinding_targets(node)
             for name in _rebinding_names(target)}
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        names.update(alias.asname or alias.name.split(".")[0]
                     for alias in node.names if alias.name != "*")
    elif (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef))
          or isinstance(node, ast.ExceptHandler) and node.name):
        names.add(node.name)
    return names
def _dg02_end_position(node: ast.AST) -> tuple[int, int]:
    anchor = node
    if isinstance(node, (ast.For, ast.AsyncFor)):
        anchor = node.iter
    elif isinstance(node, (ast.With, ast.AsyncWith)) and node.items:
        anchor = node.items[-1].context_expr
    elif isinstance(node, ast.ExceptHandler) and node.type is not None:
        anchor = node.type
    return (getattr(anchor, "end_lineno", None) or anchor.lineno,
            getattr(anchor, "end_col_offset", None) or anchor.col_offset)
def _dg02_loop_guarantees_binding(node: ast.AST) -> bool:
    if not isinstance(node, ast.For):
        return False
    iterable = node.iter
    if isinstance(iterable, ast.Constant):
        return isinstance(iterable.value, (str, bytes)) and bool(iterable.value)
    if isinstance(iterable, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(elt, ast.Starred) for elt in iterable.elts)
    if isinstance(iterable, ast.Dict):
        return any(key is not None for key in iterable.keys)
    return False
def _dg02_rebinding_execution_path(node: ast.AST, parents: dict,
                                   scope: ast.AST) -> tuple:
    path = _runtime_execution_path(node, parents, scope)
    if (isinstance(node, (ast.For, ast.AsyncFor))
            and not _dg02_loop_guarantees_binding(node)):
        return path + ((id(node), "body"),)
    return path
def _dg02_key_reset(node: ast.AST, target: str, key: str) -> bool:
    if isinstance(node, ast.Delete):
        return any(
            isinstance(item, ast.Subscript)
            and dotted_name(item.value) == target
            and isinstance(item.slice, ast.Constant)
            and item.slice.value == key
            for item in node.targets)
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and dotted_name(node.func.value) == target):
        return False
    if node.func.attr == "clear":
        return True
    return (node.func.attr == "pop" and bool(node.args)
            and isinstance(node.args[0], ast.Constant)
            and node.args[0].value == key)
def _dg02_rebinding_preserves_keys(
        node: ast.AST, target: str, bindings: _RuntimeBindings) -> bool:
    if isinstance(node, ast.AugAssign):
        return (isinstance(node.op, ast.BitOr)
                and dotted_name(node.target) == target)
    if not isinstance(node, (ast.Assign, ast.AnnAssign)) or node.value is None:
        return False
    value = node.value
    if dotted_name(value) == target:
        return True
    if isinstance(value, ast.Call):
        if (not value.args and not value.keywords
                and isinstance(value.func, ast.Attribute)
                and value.func.attr == "copy"
                and dotted_name(value.func.value) == target):
            return True
        if (len(value.args) == 1 and not value.keywords
                and dotted_name(value.args[0]) == target
                and bindings.module_member(
                    value.func, "builtins", "dict", bindings.scope_for(value),
                    allow_unbound=True, allow_unbound_bare=True)):
            return True
    return (isinstance(value, ast.BinOp) and isinstance(value.op, ast.BitOr)
            and target in {dotted_name(value.left), dotted_name(value.right)})
def _dg02_target_reset_between(
        target: str, key: str, first: ast.Call, override: ast.Call,
        scope: ast.AST, parents: dict,
        bindings: _RuntimeBindings) -> bool:
    first_pos = (first.lineno, first.col_offset)
    override_pos = (override.lineno, override.col_offset)
    first_path = _runtime_execution_path(first, parents, scope)
    override_path = _runtime_execution_path(override, parents, scope)
    for node in iter_scope_nodes(scope):
        names = _node_rebinding_names(node)
        star_import = (isinstance(node, ast.ImportFrom)
                       and any(alias.name == "*" for alias in node.names))
        key_reset = _dg02_key_reset(node, target, key)
        if not names and not star_import and not key_reset:
            continue
        if not first_pos < _dg02_end_position(node) < override_pos:
            continue
        if names and _dg02_rebinding_preserves_keys(node, target, bindings):
            continue
        if not (star_import or key_reset or any(
                target == name or target.startswith(name + ".")
                for name in names)):
            continue
        rebind_path = _dg02_rebinding_execution_path(node, parents, scope)
        if (_runtime_path_is_prefix(rebind_path, first_path)
                or _runtime_path_is_prefix(rebind_path, override_path)):
            return True
    return False
def _dg02_scope_issues(scope: ast.AST,
                       parents: dict,
                       bindings: _RuntimeBindings,
                       source_lines: list[str],
                       filepath: str,
                       seen: set[tuple[str, str, int]]) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    for target, calls in _dg02_collect_target_updates(scope).items():
        if len(calls) < 2:
            continue
        all_keys = {k for _, keys, _c in calls for k in keys}
        for key in sorted(all_keys):
            writers = _dg02_key_writers(calls, key)
            if len(writers) < 2:
                continue
            first_pair = _dg02_first_coexisting_pair(
                writers, parents, target=target, key=key, scope=scope,
                bindings=bindings)
            if first_pair is None:
                continue
            first_ln, override_ln = first_pair
            anchor = (target, key, first_ln)
            if anchor in seen:
                continue
            seen.add(anchor)
            issues.append(_dg02_override_finding(
                target, key, first_ln, override_ln, source_lines, filepath))
    return issues
def check_DG02(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    scopes = scope_roots(tree)
    parents = _shared_parent_map(tree)
    bindings = _RuntimeBindings(tree)
    issues: list[DiagnoseFinding] = []
    seen: set[tuple[str, str, int]] = set()
    for scope in scopes:
        issues.extend(
            _dg02_scope_issues(
                scope, parents, bindings, source_lines, filepath, seen))
    return issues
_NONEABLE_CHAIN_METHODS = frozenset({"get", "find", "search", "match", "fullmatch"})
_NS01_STRING_TYPES = frozenset({"str", "bytes", "bytearray"})
_NS01_STRING_RETURN_METHODS = frozenset({
    "capitalize", "casefold", "center", "decode", "encode", "expandtabs",
    "format", "format_map", "join", "ljust", "lower", "lstrip",
    "removeprefix", "removesuffix", "replace", "rjust", "rstrip",
    "strip", "swapcase", "title", "translate", "upper", "zfill",
})
def _ns01_is_string_annotation(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Name):
        return node.id in _NS01_STRING_TYPES
    if isinstance(node, ast.Attribute):
        return node.attr in _NS01_STRING_TYPES
    if isinstance(node, ast.Constant):
        return node.value in _NS01_STRING_TYPES
    if isinstance(node, ast.Subscript):
        owner = node.value
        if ((isinstance(owner, ast.Name) and owner.id == "Optional")
                or (isinstance(owner, ast.Attribute)
                    and owner.attr == "Optional")):
            return _ns01_is_string_annotation(node.slice)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return (_ns01_is_string_annotation(node.left)
                or _ns01_is_string_annotation(node.right))
    return False
def _ns01_is_string_syntax(node: ast.AST | None,
                           bindings: _RuntimeBindings,
                           scope: ast.AST,
                           known: frozenset[str] | set[str] = frozenset()
                           ) -> bool:
    if isinstance(node, ast.Name):
        return node.id in known
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (str, bytes))
    if isinstance(node, ast.JoinedStr):
        return True
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Add):
            return (_ns01_is_string_syntax(node.left, bindings, scope, known)
                    and _ns01_is_string_syntax(
                        node.right, bindings, scope, known))
        if isinstance(node.op, ast.Mod):
            return _ns01_is_string_syntax(node.left, bindings, scope, known)
        if isinstance(node.op, ast.Mult):
            left_string = _ns01_is_string_syntax(
                node.left, bindings, scope, known)
            right_string = _ns01_is_string_syntax(
                node.right, bindings, scope, known)
            left_count = (isinstance(node.left, ast.Constant)
                          and isinstance(node.left.value, int))
            right_count = (isinstance(node.right, ast.Constant)
                           and isinstance(node.right.value, int))
            return ((left_string and right_count)
                    or (right_string and left_count))
    if isinstance(node, ast.IfExp):
        return (_ns01_is_string_syntax(node.body, bindings, scope, known)
                and _ns01_is_string_syntax(node.orelse, bindings, scope, known))
    if isinstance(node, ast.Subscript):
        return _ns01_is_string_syntax(node.value, bindings, scope, known)
    if isinstance(node, ast.Call):
        if any(bindings.module_member(
                node.func, "builtins", name, scope, allow_unbound=True,
                allow_unbound_bare=True) for name in _NS01_STRING_TYPES):
            return True
        func = node.func
        return (isinstance(func, ast.Attribute)
                and func.attr in _NS01_STRING_RETURN_METHODS
                and _ns01_is_string_syntax(func.value, bindings, scope, known))
    return False
def _ns01_is_string_sequence(
        node: ast.AST | None, bindings: _RuntimeBindings, scope: ast.AST,
        known: frozenset[str] | set[str]) -> bool:
    return (isinstance(node, (ast.List, ast.Tuple, ast.Set))
            and all(not isinstance(element, ast.Starred)
                    and _ns01_is_string_syntax(
                        element, bindings, scope, known)
                    for element in node.elts))
def _ns01_unpacked_string_names(
        target: ast.AST, value: ast.AST | None,
        bindings: _RuntimeBindings, scope: ast.AST,
        known: frozenset[str] | set[str]) -> set[str]:
    if isinstance(target, ast.Name):
        return ({target.id} if _ns01_is_string_syntax(
            value, bindings, scope, known) else set())
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)):
        return set()
    names: set[str] = set()
    for target_item, value_item in zip(target.elts, value.elts, strict=True):
        names.update(_ns01_unpacked_string_names(
            target_item, value_item, bindings, scope, known))
    return names
class _NS01ReceiverEvidence:
    def __init__(self, tree: ast.AST, bindings: _RuntimeBindings) -> None:
        self.bindings = bindings
        self.bound: dict[int, set[str]] = {}
        self.strings: dict[int, set[str]] = {}
        self.non_strings: dict[int, set[str]] = {}
        self.parameter_strings: dict[int, set[str]] = {}
        for scope in scope_roots(tree):
            self._index_scope(scope)
    def _index_scope(self, scope: ast.AST) -> None:
        bound: set[str] = set()
        strings: set[str] = set()
        non_strings: set[str] = set()
        # 无签名作用域（模块/类体）不应留下未绑定名称。
        parameter_strings: set[str] = set()
        spec = getattr(scope, "args", None)
        if spec is not None:
            args = [*spec.posonlyargs, *spec.args, *spec.kwonlyargs]
            args.extend(arg for arg in (spec.vararg, spec.kwarg) if arg)
            bound.update(arg.arg for arg in args)
            parameter_strings = {arg.arg for arg in args
                                 if _ns01_is_string_annotation(arg.annotation)}
            strings.update(parameter_strings)
        for node in iter_scope_nodes(scope):
            if isinstance(node, ast.AnnAssign):
                names = _rebinding_names(node.target)
            else:
                names = _node_rebinding_names(node)
            if not names:
                continue
            bound.update(names)
            known = strings - non_strings
            string_names: set[str] = set()
            value = getattr(node, "value", None)
            if isinstance(node, ast.AnnAssign):
                if (_ns01_is_string_annotation(node.annotation)
                        and (value is None or _ns01_is_string_syntax(
                            value, self.bindings, scope, known))):
                    string_names = names
            elif isinstance(node, (ast.Assign, ast.NamedExpr)):
                targets = (node.targets if isinstance(node, ast.Assign)
                           else (node.target,))
                for target in targets:
                    string_names.update(_ns01_unpacked_string_names(
                        target, value, self.bindings, scope, known))
            elif (isinstance(node, (ast.For, ast.AsyncFor))
                  and (_ns01_is_string_syntax(
                       node.iter, self.bindings, scope, known)
                       or isinstance(node.target, ast.Name)
                       and _ns01_is_string_sequence(
                           node.iter, self.bindings, scope, known))):
                string_names = names
            strings.update(string_names)
            non_strings.update(names - string_names)
        self.bound[id(scope)] = bound
        self.strings[id(scope)] = strings - non_strings
        self.non_strings[id(scope)] = non_strings
        self.parameter_strings[id(scope)] = (
            parameter_strings if spec is not None else set())
    def _name_is_string(self, name: str, scope: ast.AST,
                        use: ast.AST) -> bool:
        direct = scope
        while scope is not None:
            if not isinstance(scope, ast.ClassDef) or scope is direct:
                key = id(scope)
                if scope is direct and name in self.parameter_strings.get(
                        key, set()):
                    use_pos = node_position(use)
                    prior_events = any(
                        event[0] < use_pos for event in
                        self.bindings._sequential_binding_events(scope, name))
                    if not prior_events:
                        return True
                if name in self.non_strings.get(key, set()):
                    return False
                if name in self.bound.get(key, set()):
                    return name in self.strings.get(key, set())
            scope = self.bindings.table.parent.get(scope)
        return False
    def is_string(self, node: ast.AST, scope: ast.AST) -> bool:
        if _ns01_is_string_syntax(node, self.bindings, scope):
            return True
        if isinstance(node, ast.Name):
            if self.bindings.prior_binding_value(node) is not None:
                # 先前绑定的右值必须按其自身词法作用域求值：scope_for
                # 只对 Call 节点查 call_scopes，对 Name 等一律返回模块，
                # 使 ``local = text``（text 为函数内 str 参数）被放到模块层
                # 判定为非字符串而误报 NS-01。
                return bool(self.bindings.resolve_path_name(
                    node, lambda value: self.is_string(
                        value,
                        (self.bindings._nearest_scope(value) or scope)
                        if value in self.bindings.parents else scope)))
            return self._name_is_string(node.id, scope, node)
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr in _NS01_STRING_RETURN_METHODS):
            return self.is_string(node.func.value, scope)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Mod):
                return self.is_string(node.left, scope)
            return (self.is_string(node.left, scope)
                    and self.is_string(node.right, scope))
        if isinstance(node, ast.IfExp):
            return (self.is_string(node.body, scope)
                    and self.is_string(node.orelse, scope))
        if isinstance(node, ast.Subscript):
            return self.is_string(node.value, scope)
        return False
def _ns01_chain_target(
        node: ast.AST,
        evidence: _NS01ReceiverEvidence) -> tuple[str, str, str] | None:
    if not isinstance(node, (ast.Attribute, ast.Subscript)):
        return None
    call = node.value
    if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Attribute):
        return None
    method = call.func.attr
    if method not in _NONEABLE_CHAIN_METHODS:
        return None
    receiver = call.func.value
    if method == "find" and evidence.is_string(
            receiver, evidence.bindings.scope_for(call)):
        return None
    if isinstance(node, ast.Attribute):
        return method, "属性", f".{node.attr}"
    return method, "下标", "[...]"
def check_NS01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    issues: list[DiagnoseFinding] = []
    bindings = _RuntimeBindings(tree)
    evidence = _NS01ReceiverEvidence(tree, bindings)
    for node in tree_nodes(tree):
        chain = _ns01_chain_target(node, evidence)
        if chain is None:
            continue
        method, access_kind, access_hint = chain
        issues.append(DiagnoseFinding(
            id="NS-01", severity="P2", dimension="null_safety",
            file=filepath, line=node.lineno,
            description=(f"可空返回值链式{access_kind}访问: .{method}() 在无结果/"
                         f"缺键时返回 None，直接 {access_hint} 访问将抛 "
                         f"AttributeError/TypeError"),
            suggestion=("根因: .get()/re.search()/.match()/.fullmatch() 及部分对象的 "
                        ".find() 在无结果时返回 None，未判空直接链式访问；"
                        "str/bytes.find() 则返回 -1。该问题属于 None 处理类别。\n"
                        "修复策略: 先判空再访问——v = x.get(k); if v is not None: v.attr；"
                        "或布尔守护 (x.get(k) or {}).get('sub')；re 结果用 "
                        "m = re.search(p, s) 后 if m: m.group(1)\n"
                        "参考标准: PEP 8 / Optional / mypy / NT-02 同族判空口径"),
            code_snippet=get_code_snippet(source_lines, node.lineno),
        ))
    return issues
def _cv01_mode_arg(node: ast.Call) -> ast.AST | None:
    for kw in node.keywords:
        if kw.arg == "mode":
            return kw.value
    if len(node.args) >= 2:
        return node.args[1]
    return None
_CV01_LOOSE_WRITE_MASK = 0o022
def _cv01_int_literal(node: ast.AST | None) -> int | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub))
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, int)):
        value = node.operand.value
        return -value if isinstance(node.op, ast.USub) else value
    return None
def _cv01_is_loose_perm(perm: int) -> bool:
    return bool((perm & 0o777) & _CV01_LOOSE_WRITE_MASK)
def _make_cv01_issue(node: ast.Call, perm: int,
                     source_lines: list[str] | str,
                     filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="CV-01", severity="P1", dimension="file_security",
        file=filepath, line=node.lineno,
        description=f"os.chmod()权限{oct(perm)}过于宽松",
        code_snippet=extract_code_lines(source_lines, node.lineno),
        suggestion='根因: 代码使用了不规范或有风险的实现方式。该问题属于文件安全类别。\n修复策略: 使用最小权限原则: 目录0o750, 文件0o640\n参考标准: cross-validation methodology',
        rule_ref="Bandit B103",
    )
def check_CV01(tree: ast.AST | None,
               source_lines: list[str] | str | None,
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    issues = []
    bindings = _RuntimeBindings(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if not bindings.module_member(
                node.func, "os", "chmod", bindings.scope_for(node),
                allow_unbound=True):
            continue
        perm = _cv01_int_literal(_cv01_mode_arg(node))
        if perm is None or not _cv01_is_loose_perm(perm):
            continue
        issues.append(_make_cv01_issue(node, perm, source_lines, filepath))
    return issues
_UNHASHABLE_NODES = (ast.List, ast.Dict, ast.Set, ast.ListComp, ast.SetComp,
                     ast.DictComp)
_UH01_UNHASHABLE_CTORS = frozenset({"bytearray", "dict", "list", "set"})
_UH01_CONTAINER_RULES: dict[type, tuple[str, str, str]] = {
    ast.Dict: ("不可哈希对象作 dict 键", "字典键", "keys"),
    ast.Set: ("不可哈希对象作 set 元素", "集合元素", "elts"),
    ast.DictComp: ("不可哈希对象作 dict 键", "字典推导式键", "key"),
    ast.SetComp: ("不可哈希对象作 set 元素", "集合推导式元素", "elt"),
}
def _is_unhashable_node(node: ast.AST,
                        bindings: _RuntimeBindings) -> bool:
    if isinstance(node, _UNHASHABLE_NODES):
        return True
    if isinstance(node, ast.Tuple):
        return any(
            _is_unhashable_node(element, bindings)
            for element in _uh01_expanded_literal_elements(node, bindings))
    if isinstance(node, ast.Call):
        scope = bindings.scope_for(node)
        if any(bindings.module_member(
                node.func, "builtins", name, scope, allow_unbound=True,
                allow_unbound_bare=True) for name in _UH01_UNHASHABLE_CTORS):
            return True
        if not bindings.module_member(
                node.func, "builtins", "tuple", scope, allow_unbound=True,
                allow_unbound_bare=True):
            return False
        if len(node.args) != 1 or node.keywords:
            return False
        iterable = node.args[0]
        return (isinstance(iterable, (ast.List, ast.Tuple, ast.Set))
                and any(
                    _is_unhashable_node(element, bindings)
                    for element in _uh01_expanded_literal_elements(
                        iterable, bindings)))
    return False
def _uh01_candidate_nodes(node: ast.AST, attr: str) -> list:
    values = getattr(node, attr)
    if isinstance(values, list):
        return [v for v in values if v is not None]
    return [values]
class _UH01Offender(NamedTuple):
    title: str
    subject: str
    type_name: str
    node: ast.AST
def _uh01_expanded_literal_elements(
        node: ast.AST, bindings: _RuntimeBindings) -> list:
    candidates = []
    for child in _uh01_candidate_nodes(node, "elts"):
        if isinstance(child, ast.Starred):
            value = child.value
            scope = bindings.scope_for(value)
            if (isinstance(value, ast.Call) and len(value.args) == 1
                    and not value.keywords
                    and any(bindings.module_member(
                        value.func, "builtins", name, scope,
                        allow_unbound=True, allow_unbound_bare=True)
                            for name in ("list", "tuple"))):
                value = value.args[0]
            if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
                candidates.extend(
                    _uh01_expanded_literal_elements(value, bindings))
                continue
        candidates.append(child)
    return candidates
def _uh01_unhashable_offenders(
        node: ast.AST,
        bindings: _RuntimeBindings) -> list[_UH01Offender]:
    rule = _UH01_CONTAINER_RULES.get(type(node))
    if rule is None:
        return []
    title, subject, attr = rule
    candidates = (_uh01_expanded_literal_elements(node, bindings)
                  if isinstance(node, ast.Set)
                  else _uh01_candidate_nodes(node, attr))
    return [_UH01Offender(title, subject, type(child).__name__, child)
            for child in candidates
            if _is_unhashable_node(child, bindings)]
def _uh01_finding(filepath: str, source: str,
                  offender: _UH01Offender) -> DiagnoseFinding:
    node = offender.node
    return DiagnoseFinding(
        id="UH-01", severity="P0", dimension="type_safety",
        file=filepath, line=node.lineno, col_offset=node.col_offset,
        title=offender.title,
        description=(f"{offender.subject} 使用不可哈希类型 "
                     f"({offender.type_name}), 运行时将抛出 TypeError."),
        suggestion='根因: 键或集合元素要求可哈希, 可变对象不满足该约束。该问题属于类型安全类别。\n修复策略: 改用 tuple() 或 frozenset() 等可哈希等价形态。\n参考标准: PEP 8 / pylint / SonarQube',
        rule_ref="Python TypeError",
        code_snippet=extract_code_lines(source, node.lineno))
def check_UH01(tree: ast.AST | None,
               source_lines: list[str] | str | None,
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if _rule_scan_skip(tree, filepath):
        return []
    source = join_source_lines(source_lines)
    bindings = _RuntimeBindings(tree)
    return [_uh01_finding(filepath, source, offender)
            for node in tree_nodes(tree)
            for offender in _uh01_unhashable_offenders(node, bindings)]
def wiring_declarations() -> dict:
    return {"catalogs": {
        "recovered_bindings": {
            'DG02': check_DG02, 'EP02': check_EP02, 'EX08': check_EX08,
            'FS02': check_FS02, 'LE03': check_LE03, 'LE04': check_LE04,
            'NS01': check_NS01,
        },
        "rule_bindings": {
            'CV01': check_CV01, 'UH01': check_UH01,
        },
    }}

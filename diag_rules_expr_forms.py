import ast
import logging
import tokenize
from collections.abc import Callable, Iterable, Iterator
from fractions import Fraction
from functools import partial
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    assign_targets_value,
    collect_param_names,
    definition_time_exprs,
    dotted_name,
    expr_target_name,
    is_none_literal,
    iter_class_scope_methods,
    iter_evaluation_scope_chain,
)
from jwsgj.diag_shared_ast_views import (
    call_scope_map,
    collect_lexical_scope_table,
    parent_map,
    scope_import_tables,
    tree_nodes,
    unparse_or_type_name,
)
from jwsgj.diag_shared_source_core import (
    extract_code_lines,
)
from jwsgj.diag_shared_source_scan import (
    get_code_snippet,
    is_suppressed,
    parse_suppressions,
    tokenize_source_cached,
)
from jwsgj.diag_types_defs import DiagnoseFinding, finding_scan_exempt
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "check_BZ01", "check_DB05", "check_DF03", "check_DG01", "check_FL01",
    "check_IC01", "check_NM02", "check_NT01", "check_RB14", "check_RB17",
    "check_RC01", "check_TP17", "check_TP19", "check_TY02", "check_TY03",
]
logger = logging.getLogger(__name__)
logger.info("diag_rules_expr_forms 已加载：%d 项导出", len(__all__))
_DEFAULT_FILEPATH = ""
class _ExprScopeContext(NamedTuple):
    table: Any
    call_scopes: dict[int, ast.AST]
    imports: dict
    parents: dict[int, ast.AST]
def _expr_scope_context(tree: ast.AST) -> _ExprScopeContext:
    if tree is None:
        return _ExprScopeContext(None, {}, {}, {})
    table = collect_lexical_scope_table(tree)
    return _ExprScopeContext(
        table, call_scope_map(table), scope_import_tables(tree),
        {id(node): parent for node, parent in parent_map(tree).items()})
def _expr_scopes(node: ast.AST, context: _ExprScopeContext) -> Iterator[ast.AST]:
    parent = context.parents.get(id(node))
    if isinstance(parent, ast.Call) and parent.func is node:
        node = parent
    if not isinstance(node, ast.Call):
        yield from iter_evaluation_scope_chain(node, context.parents)
        return
    scope = context.call_scopes.get(id(node))
    crossed_function = False
    while scope is not None:
        if isinstance(scope, ast.ClassDef) and crossed_function:
            scope = context.table.parent.get(scope)
            continue
        yield scope
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            crossed_function = True
        scope = context.table.parent.get(scope)
def _expr_name_shadowed(node: ast.AST, name: str,
                        context: _ExprScopeContext) -> bool:
    return any(name in context.table.shadow_bound.get(scope, frozenset())
               for scope in _expr_scopes(node, context))
def _expr_import_binding(node: ast.AST, name: str,
                         context: _ExprScopeContext):
    for scope in _expr_scopes(node, context):
        binding = context.imports.get(scope, {}).get(name)
        if binding is not None:
            return binding
    return None
def _expr_builtin_call(node: ast.AST, names: frozenset[str],
                       context: _ExprScopeContext) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in names
            and not _expr_name_shadowed(node, node.func.id, context)
            and _expr_import_binding(node, node.func.id, context) is None)
def _expr_import_identity(expr: ast.AST,
                          context: _ExprScopeContext) -> str | None:
    name = dotted_name(expr)
    if not name:
        return None
    head, separator, rest = name.partition(".")
    if _expr_name_shadowed(node=expr, name=head, context=context):
        return None
    binding = _expr_import_binding(expr, head, context)
    if binding is None:
        return None
    if not separator:
        return (f"{binding[1]}.{binding[2]}"
                if binding[0] == "from" else None)
    return f"{binding[1]}.{rest}" if binding[0] == "import" else None
def _walk_nodes(tree: ast.AST | None, *types: type) -> Iterator[ast.AST]:
    if tree is None:
        return iter(())
    nodes = tree_nodes(tree)
    if not types:
        return iter(nodes)
    return (node for node in nodes if isinstance(node, types))
def _iter_frame_nodes(roots: Iterable[ast.AST]) -> Iterator[ast.AST]:
    stack: list[ast.AST] = list(roots)
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            stack.extend(definition_time_exprs(cur))
            continue
        yield cur
        stack.extend(ast.iter_child_nodes(cur))
def _iter_frame_calls(roots: Iterable[ast.AST]) -> Iterator[ast.Call]:
    return (node for node in _iter_frame_nodes(roots)
            if isinstance(node, ast.Call))
def _iter_leaf_targets(targets: Iterable[ast.AST]) -> Iterator[ast.AST]:
    for tgt in targets:
        if isinstance(tgt, (ast.Tuple, ast.List)):
            yield from _iter_leaf_targets(tgt.elts)
        elif isinstance(tgt, ast.Starred):
            yield from _iter_leaf_targets([tgt.value])
        else:
            yield tgt
_RB14_SIDE_EFFECT_NAMES = frozenset({
    "append", "extend", "insert", "remove", "pop", "update",
    "clear", "add", "discard", "write", "print",
})
_RB14_IDIOM_CONSUMERS = frozenset({"any", "all", "filter"})
def _collect_dedup_idiom_add_ids(
        tree: ast.AST, context: _ExprScopeContext) -> set[int]:
    out: set[int] = set()
    consumer_ids = _idiom_consumer_comp_ids(tree, context)
    for comp in tree_nodes(tree):
        if not isinstance(comp, COMP_SCOPE_NODES):
            continue
        for gen in getattr(comp, "generators", ()) or ():
            for cond in gen.ifs:
                out |= _dedup_idiom_add_ids_in_cond(cond)
        if id(comp) in consumer_ids:
            for element in _comp_element_exprs(comp):
                out |= _dedup_idiom_add_ids_in_cond(element)
    return out
def _idiom_consumer_comp_ids(
        tree: ast.AST, context: _ExprScopeContext) -> set[int]:
    found: set[int] = set()
    for node in tree_nodes(tree):
        if not _expr_builtin_call(node, _RB14_IDIOM_CONSUMERS, context):
            continue
        for arg in node.args:
            if isinstance(arg, COMP_SCOPE_NODES):
                found.add(id(arg))
    return found
def _comp_element_exprs(comp: ast.AST) -> list[ast.expr]:
    if isinstance(comp, ast.DictComp):
        return [comp.key, comp.value]
    element = getattr(comp, "elt", None)
    return [element] if isinstance(element, ast.expr) else []
def _dedup_idiom_add_ids_in_cond(cond: ast.expr) -> set[int]:
    out: set[int] = set()
    for sub in walk_nodes(cond):
        if isinstance(sub, ast.BoolOp) and isinstance(
                sub.op, (ast.And, ast.Or)):
            out |= _dedup_idiom_add_ids_in_boolop(sub)
    return out
def _dedup_idiom_containers(
        values: list[ast.expr],
        membership_op: type[ast.cmpop]) -> dict[str, set[str]]:
    containers: dict[str, set[str]] = {}
    for value in values:
        if not (isinstance(value, ast.Compare) and len(value.ops) == 1
                and len(value.comparators) == 1
                and isinstance(value.ops[0], membership_op)):
            continue
        container = value.comparators[0]
        if not isinstance(container, ast.Name):
            continue
        containers.setdefault(container.id, set()).add(
            ast.dump(value.left, include_attributes=False))
    return containers
def _dedup_idiom_add_ids(values: list[ast.expr],
                          containers: dict[str, set[str]]) -> set[int]:
    return {id(value) for value in values
            if _dedup_idiom_is_add(value, containers)}
def _dedup_idiom_is_add(sub: ast.AST,
                        containers: dict[str, set[str]]) -> bool:
    if not (isinstance(sub, ast.Call)
            and isinstance(sub.func, ast.Attribute)
            and sub.func.attr == "add"
            and isinstance(sub.func.value, ast.Name)
            and len(sub.args) == 1
            and not sub.keywords):
        return False
    members = containers.get(sub.func.value.id)
    return bool(members) and ast.dump(sub.args[0], include_attributes=False) in members
def _dedup_idiom_add_ids_in_boolop(sub: ast.BoolOp) -> set[int]:
    membership_op = ast.In if isinstance(sub.op, ast.Or) else ast.NotIn
    containers = _dedup_idiom_containers(sub.values, membership_op)
    if not containers:
        return set()
    if isinstance(sub.op, ast.Or):
        return _dedup_idiom_add_ids(sub.values, containers)
    guarded: set[int] = set()
    for value in sub.values:
        if not (isinstance(value, ast.UnaryOp)
                and isinstance(value.op, ast.Not)):
            continue
        if _dedup_idiom_is_add(value.operand, containers):
            guarded.add(id(value.operand))
    return guarded
def _rb14_should_report(child: ast.Call, idiom_ids: set[int],
                        seen: set[int]) -> str | None:
    name = expr_target_name(child.func)
    if name not in _RB14_SIDE_EFFECT_NAMES:
        return None
    if id(child) in idiom_ids or id(child) in seen:
        return None
    seen.add(id(child))
    return name
def _rb14_finding(name: str, child: ast.Call,
                  source_lines: str | list[str],
                  filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="RB-14",
        severity="P2",
        dimension="resource",
        file=filepath,
        line=child.lineno,
        col_offset=child.col_offset,
        title="列表推导式中调用有副作用的函数",
        description=f"推导式中调用{name}()",
        suggestion="使用for循环替代",
        code_snippet=get_code_snippet(source_lines, child.lineno),
        rule_ref="RB-14",
    )
def check_RB14(tree: ast.AST, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    _seen_calls: set[int] = set()
    context = _expr_scope_context(tree)
    _idiom_add_ids = _collect_dedup_idiom_add_ids(tree, context)
    for node in _walk_nodes(tree, *COMP_SCOPE_NODES):
        for child in _iter_frame_calls([node]):
            name = _rb14_should_report(child, _idiom_add_ids, _seen_calls)
            if name is not None:
                issues.append(_rb14_finding(name, child, source_lines, filepath))
    return issues
_RB17_NAMESPACE_NAMES = frozenset({"globals", "locals", "vars"})
def _ns_call_name(node: ast.AST, context: _ExprScopeContext) -> str | None:
    if not _expr_builtin_call(node, _RB17_NAMESPACE_NAMES, context):
        return None
    if node.func.id == "vars" and (node.args or node.keywords):
        return None
    return node.func.id
class _RB17Detail(NamedTuple):
    title: str
    description: str
    cause: str
def _rb17_finding(source_lines: str | list[str], filepath: str, lineno: int,
                  detail: _RB17Detail,
                  col_offset: int = 0) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="RB-17",
        severity="P2",
        dimension="robustness",
        file=filepath,
        line=lineno,
        col_offset=col_offset,
        title=detail.title,
        description=detail.description,
        code_snippet=get_code_snippet(source_lines, lineno),
        suggestion=(
            f"根因: {detail.cause}。该问题属于重构最佳实践类别。\n"
            "修复策略: 使用显式字典或对象属性管理状态\n"
            "参考标准: PEP 8 / pylint / clean code"
        ),
        rule_ref="RB-17",
    )
def check_RB17(tree: ast.AST, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    context = _expr_scope_context(tree)
    issues.extend(_rb17_subscript_writes(
        tree, source_lines, filepath, context))
    issues.extend(_rb17_update_writes(
        tree, source_lines, filepath, context))
    return issues
def _write_targets(node: ast.AST) -> list:
    if isinstance(node, ast.Assign):
        return node.targets
    if isinstance(node, (ast.AugAssign, ast.For, ast.AsyncFor,
                         ast.comprehension)):
        return [node.target]
    if isinstance(node, ast.AnnAssign):
        return [node.target] if node.value is not None else []
    if isinstance(node, ast.Delete):
        return node.targets
    if isinstance(node, ast.withitem):
        return [node.optional_vars] if node.optional_vars is not None else []
    return []
def _rb17_subscript_writes(tree: ast.AST, source_lines: str | list[str],
                           filepath: str, context: _ExprScopeContext) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree):
        for tgt in _iter_leaf_targets(_write_targets(node)):
            if not isinstance(tgt, ast.Subscript):
                continue
            call_name = _ns_call_name(tgt.value, context)
            if call_name:
                issues.append(_rb17_finding(
                    source_lines, filepath, tgt.lineno,
                    _RB17Detail(
                        title=f"使用 {call_name}() 动态修改命名空间",
                        description=f"{call_name}()[...] 赋值/删除绕过正常作用域规则，"
                                    "命名空间被动态修改，难以静态追踪且不安全。",
                        cause="动态修改全局/局部命名空间",
                    ), tgt.col_offset))
    return issues
_RB17_NS_WRITE_METHODS = frozenset({
    "update", "setdefault", "pop", "popitem", "clear",
    "__setitem__", "__delitem__",
})
def _rb17_update_writes(tree: ast.AST, source_lines: str | list[str],
                        filepath: str, context: _ExprScopeContext) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree, ast.Call):
        if not (isinstance(node.func, ast.Attribute)
                and node.func.attr in _RB17_NS_WRITE_METHODS):
            continue
        call_name = _ns_call_name(node.func.value, context)
        if call_name:
            method = node.func.attr
            if method == "update":
                title = f"使用 {call_name}().update() 批量修改命名空间"
            else:
                title = f"使用 {call_name}().{method}() 动态修改命名空间"
            issues.append(_rb17_finding(
                source_lines, filepath, node.lineno,
                _RB17Detail(
                    title=title,
                    description=f"{call_name}().{method}() 修改命名空间条目，"
                                "绕过正常作用域规则，难以静态追踪且不安全。",
                    cause="动态修改命名空间",
                ), node.col_offset))
    return issues
_RC01_EXTERNAL_CALLS = frozenset({
    "open", "socket", "connect", "request", "urlopen",
    "create_connection",
})
def _rc01_make_finding(name: str, sub: ast.Call,
                       source: str | list[str],
                       filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="RC-01",
        severity="P2",
        dimension="resource_safety",
        file=filepath,
        line=sub.lineno,
        col_offset=sub.col_offset,
        title=f"__del__中访问外部资源: {name}()",
        description=f"__del__中调用{name}(),解释器关闭时该资源/模块可能已不可用,"
        f"引发无法捕获的异常.",
        suggestion="根因: 资源释放在不确定的__del__时机执行。\n"
        "修复策略: 在显式close()/__exit__()中释放外部资源,\n"
        "__del__仅作兜底且需包裹try/except。\n参考标准: PEP 442",
        rule_ref="RC-01",
        code_snippet=extract_code_lines(source, sub.lineno),
    )
def _rc01_del_methods(tree: ast.AST):
    for node in _walk_nodes(tree, ast.ClassDef):
        for item in iter_class_scope_methods(node):
            if (isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and item.name == "__del__"):
                yield item
def _rc01_external_calls(method: ast.AST):
    for sub in _iter_frame_calls(method.body):
        name = expr_target_name(sub.func)
        if name in _RC01_EXTERNAL_CALLS:
            yield name, sub
def check_RC01(tree: ast.AST, source: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    for method in _rc01_del_methods(tree):
        for name, sub in _rc01_external_calls(method):
            issues.append(_rc01_make_finding(name, sub, source, filepath))
    return issues
_MUTABLE_LITERALS = (
    ast.List,
    ast.Dict,
    ast.Set,
    ast.ListComp,
    ast.DictComp,
    ast.SetComp,
)
_DG01_MUTABLE_CTORS = frozenset({"list", "dict", "set", "bytearray"})
_DG01_MUTATING_ATTRS = frozenset({
    "append",
    "extend",
    "update",
    "add",
    "insert",
    "remove",
    "setdefault",
    "clear",
    "sort",
    "reverse",
    "pop",
    "popitem",
    "discard",
    "__setitem__",
    "__delitem__",
    "difference_update",
    "intersection_update",
    "symmetric_difference_update",
})
def _dg01_finding(node: ast.AST, mutation: str, receiver_label: str,
                  source: str | list[str], filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="DG-01",
        severity="P1",
        dimension="robustness",
        file=filepath,
        line=node.lineno,
        col_offset=node.col_offset,
        title=(f"{receiver_label}.get(k, 可变默认值){mutation}"
               "可能被丢弃"),
        description="对 dict.get() 返回的临时默认值做原地修改；键缺失时修改落在临时对象上，"
        "不会写回字典（典型遗漏 if k in d / setdefault 分支）。",
        suggestion="根因: 未区分键存在与缺失两种路径,对临时对象原地修改。\n"
        "修复策略: 改用 d.setdefault(k, []) 先取引用再修改,\n"
        "或 if k not in d: d[k] = [] 显式初始化。\n参考标准: Pylint W0199",
        rule_ref="DG-01",
        code_snippet=extract_code_lines(source, node.lineno),
    )
def check_DG01(tree: ast.AST, source: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    context = _expr_scope_context(tree)
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree, ast.Call):
        func = node.func
        if not (isinstance(func, ast.Attribute)
                and func.attr in _DG01_MUTATING_ATTRS):
            continue
        get_call = _dg01_get_call(func.value)
        if get_call is None:
            continue
        default = _dg01_default_arg(get_call)
        if _dg01_is_mutable_default(default, context):
            issues.append(_dg01_finding(
                node, f".{func.attr}() 的原地修改",
                _dg01_receiver_label(get_call), source, filepath))
    for node in _walk_nodes(tree):
        for target in _iter_leaf_targets(_write_targets(node)):
            if not isinstance(target, ast.Subscript):
                continue
            get_call = _dg01_get_call(target.value)
            if get_call is None:
                continue
            default = _dg01_default_arg(get_call)
            if _dg01_is_mutable_default(default, context):
                issues.append(_dg01_finding(
                    target, " 的下标写入/删除",
                    _dg01_receiver_label(get_call), source, filepath))
    return issues
def _dg01_is_mutable_default(node: ast.AST | None,
                             context: _ExprScopeContext) -> bool:
    if isinstance(node, _MUTABLE_LITERALS):
        return True
    return _expr_builtin_call(node, _DG01_MUTABLE_CTORS, context)
def _dg01_get_call(receiver: ast.AST) -> ast.Call | None:
    if (isinstance(receiver, ast.Call)
            and isinstance(receiver.func, ast.Attribute)
            and receiver.func.attr == "get"):
        return receiver
    if isinstance(receiver, ast.Subscript):
        return _dg01_get_call(receiver.value)
    return None
def _dg01_default_arg(get_call: ast.Call):
    if len(get_call.args) >= 2:
        return get_call.args[1]
    return next(
        (kw.value for kw in get_call.keywords if kw.arg == "default"),
        None,
    )
def _dg01_receiver_label(get_call: ast.Call) -> str:
    return unparse_or_type_name(get_call.func.value) or "d"
def _iter_eq_operand_pairs(
        node: ast.Compare) -> Iterator[tuple[ast.cmpop, ast.expr]]:
    operands = (node.left, *node.comparators)
    for index, op in enumerate(node.ops):
        yield op, operands[index]
        yield op, operands[index + 1]
def _as_source_lines(source_lines: str | list[str] | None) -> list[str]:
    if isinstance(source_lines, str):
        return source_lines.splitlines()
    return [line.rstrip("\r\n") for line in (source_lines or ())]
def check_IC01(tree: ast.AST, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    lines = _as_source_lines(source_lines)
    if not lines:
        return []
    tokens = tokenize_source_cached("\n".join(lines))
    if tokens is None:
        return []
    return _ImplicitConcatScanner(lines, filepath).scan(tokens)
class _LiteralRunState:
    __slots__ = ("prev", "reported")
    def __init__(self) -> None:
        self.prev: tuple[int, int] | None = None
        self.reported = False
class _ImplicitConcatScanner:
    def __init__(self, source_lines: list[str], filepath: str):
        self._source_lines = source_lines
        self._filepath = filepath
        self.issues: list[DiagnoseFinding] = []
        self._fstring_start = getattr(tokenize, "FSTRING_START", None)
        self._fstring_end = getattr(tokenize, "FSTRING_END", None)
        self._ctx: list[_LiteralRunState] = [_LiteralRunState()]
        self._body_heights: list[int] = []
    def scan(self, tokens) -> list[DiagnoseFinding]:
        for tok in tokens:
            if tok.type == tokenize.STRING:
                self._literal_boundary(tok)
                continue
            if self._fstring_start is not None and tok.type == self._fstring_start:
                self._on_fstring_start(tok)
                continue
            if self._fstring_end is not None and tok.type == self._fstring_end:
                self._on_fstring_end()
                continue
            if tok.type == tokenize.COMMENT:
                continue
            self._on_other(tok)
        return list(self.issues)
    def _report(self, prev_pos: tuple[int, int], tok: tokenize.TokenInfo) -> None:
        self.issues.append(DiagnoseFinding(
            id="IC-01", severity="P2", dimension="general",
            file=self._filepath, line=tok.start[0],
            code_snippet=get_code_snippet(self._source_lines, tok.start[0]),
            description=(f"隐式字符串拼接（第 {prev_pos[1]}-{tok.start[1]} 列）："
                         "相邻字符串字面量自动拼接"),
            suggestion=("根因: 相邻字符串字面量无运算符即自动拼接，列表/调用场景多为丢逗号 BUG。该问题属于代码质量类别。\n"
                        "修复策略: 确认为丢逗号则补 ','；确认为有意拼接则显式用 '+' 或合并为一个字符串\n"
                        "参考标准: Ruff ISC001 / PEP 8"),
        ))
    def _literal_boundary(self, tok: tokenize.TokenInfo) -> None:
        ctx = self._ctx[-1]
        if ctx.prev is not None:
            # 只报**同一行**的相邻字面量（Ruff ISC001 语义）。跨行隐式拼接是
            # `print("长消息"
            #        "续行")` 这类有意的换行排版，语义与可读性都没有问题；
            # 把它判成缺陷会让所有按行宽折行的中文消息全部命中。
            if not ctx.reported and ctx.prev[0] == tok.start[0]:
                self._report(ctx.prev, tok)
                ctx.reported = True
            ctx.prev = (tok.start[0], tok.start[1])
            return
        ctx.prev = (tok.start[0], tok.start[1])
    def _on_fstring_start(self, tok: tokenize.TokenInfo) -> None:
        self._literal_boundary(tok)
        self._ctx.append(_LiteralRunState())
        self._body_heights.append(len(self._ctx))
    def _on_fstring_end(self) -> None:
        if not self._body_heights:
            return
        body_index = self._body_heights.pop() - 1
        del self._ctx[body_index:]
    def _on_other(self, tok: tokenize.TokenInfo) -> None:
        if tok.type == tokenize.NL:
            return
        if self._body_heights and tok.type == tokenize.OP and tok.string == "{":
            self._ctx.append(_LiteralRunState())
            return
        if self._body_heights and tok.type == tokenize.OP and tok.string == "}":
            self._pop_expression_context()
            return
        ctx = self._ctx[-1]
        ctx.prev = None
        ctx.reported = False
    def _pop_expression_context(self) -> None:
        if len(self._ctx) > self._body_heights[-1]:
            self._ctx.pop()
class _CompareRule(NamedTuple):
    rule_id: str
    matches: Callable[[Any], bool]
    message: Callable[[Any], str]
    suggestion: str
def _compare_constant_findings(tree: ast.AST, source_lines: list[str],
                               filepath: str, rule: _CompareRule) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree, ast.Compare):
        for op, operand in _iter_eq_operand_pairs(node):
            if not isinstance(op, (ast.Eq, ast.NotEq)):
                continue
            if not (isinstance(operand, ast.Constant)
                    and rule.matches(operand.value)):
                continue
            issues.append(DiagnoseFinding(
                id=rule.rule_id, severity="P2", dimension="general",
                file=filepath, line=node.lineno,
                description=rule.message(operand.value),
                code_snippet=get_code_snippet(source_lines, node.lineno),
                suggestion=rule.suggestion,
            ))
            break
    return issues
_NT01_SUGGESTION = (
    "根因: None 是单例，== 可能被自定义 __eq__ 重载产生意外结果。该问题属于代码质量类别。\n"
    "修复策略: 改用 `is None` / `is not None`\n"
    "参考标准: PEP 8 / Ruff E711")
_BZ01_SUGGESTION = (
    "根因: == 可被 __eq__ 重载，且 truthy 非 bool 值与 True 的 == 结果有歧义。该问题属于代码质量类别。\n"
    "修复策略: 直接使用 `if x:` / `if not x:`；需要严格 bool 判定时用 `is True`\n"
    "参考标准: Ruff E712 / PEP 8")
def check_NT01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    return _compare_constant_findings(
        tree, source_lines, filepath,
        _CompareRule(
            "NT-01",
            lambda value: value is None,
            lambda _value: "None 比较使用 == / !=（应使用 is / is not）",
            _NT01_SUGGESTION))
def check_BZ01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    return _compare_constant_findings(
        tree, source_lines, filepath,
        _CompareRule(
            "BZ-01",
            lambda value: isinstance(value, bool),
            lambda value: f"布尔陷阱: 与常量 {value} 用 == / != 比较",
            _BZ01_SUGGESTION))
def _signed_float_literal(node: ast.AST) -> float | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, float):
        return node.value
    if not (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub))
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, float)):
        return None
    value = node.operand.value
    return -value if isinstance(node.op, ast.USub) else value
def check_NM02(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    context = _expr_scope_context(tree)
    source_text = "\n".join(_as_source_lines(source_lines))
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree, ast.BinOp):
        mixed = _nm02_binop_finding(
            node, source_lines, filepath, context)
        if mixed is not None:
            issues.append(mixed)
    for node in _walk_nodes(tree, ast.Call):
        if not _nm02_is_decimal_call(node, context):
            continue
        ctor = _nm02_ctor_finding(
            node, source_lines, filepath, source_text)
        if ctor is not None:
            issues.append(ctor)
    return issues
def _nm02_is_decimal_call(node: ast.AST,
                          context: _ExprScopeContext) -> bool:
    return (isinstance(node, ast.Call)
            and _expr_import_identity(node.func, context) == "decimal.Decimal")
def _nm02_binop_finding(node: ast.BinOp, source_lines: list[str],
                        filepath: str,
                        context: _ExprScopeContext) -> DiagnoseFinding | None:
    left_dec = _nm02_is_decimal_call(node.left, context)
    right_dec = _nm02_is_decimal_call(node.right, context)
    left_f = _signed_float_literal(node.left) is not None
    right_f = _signed_float_literal(node.right) is not None
    if not ((left_dec and right_f) or (left_f and right_dec)):
        return None
    return DiagnoseFinding(
        id="NM-02", severity="P2", dimension="numeric",
        file=filepath, line=node.lineno,
        description="Decimal 与 float 字面量直接混合运算（运行时 TypeError）",
        code_snippet=get_code_snippet(source_lines, node.lineno),
        suggestion=("根因: Decimal 与 float 的直接算术运算不受支持，会抛 TypeError；"
                    "先统一为 Decimal 才能保持十进制语义。该问题属于数值精度类别。\n"
                    "修复策略: 统一类型并用字符串构造 Decimal，例如 Decimal('0.5') + d\n"
                    "参考标准: decimal 文档 / PEP 327"),
    )
def _nm02_ctor_finding(node: ast.Call, source_lines: list[str],
                       filepath: str, source_text: str) -> DiagnoseFinding | None:
    value_arg = node.args[0] if node.args else None
    if value_arg is None:
        value_arg = next(
            (kw.value for kw in node.keywords if kw.arg == "value"),
            None,
        )
    if value_arg is None:
        return None
    ctor_float = _signed_float_literal(value_arg)
    literal_text = _fl01_literal_text(value_arg, source_text)
    if (ctor_float is None
            or not _fl01_is_non_exact(ctor_float, literal_text)):
        return None
    return DiagnoseFinding(
        id="NM-02", severity="P2", dimension="numeric",
        file=filepath, line=node.lineno,
        description=(f"Decimal({literal_text or repr(ctor_float)}) 以 float 构造"
                     "（继承二进制精度误差）"),
        code_snippet=get_code_snippet(source_lines, node.lineno),
        suggestion=("根因: Decimal(0.1) 先生成浮点近似值再转换，精度已丢失。该问题属于数值精度类别。\n"
                    "修复策略: 使用字符串构造 Decimal('0.1')\n"
                    "参考标准: decimal 文档"),
    )
def _is_optional_subscript(node: ast.AST,
                           context: _ExprScopeContext) -> bool:
    return (isinstance(node, ast.Subscript)
            and _expr_import_identity(node.value, context) == "typing.Optional")
def _ty02_union_parts(node: ast.AST) -> Iterator[ast.AST]:
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        yield from _ty02_union_parts(node.left)
        yield from _ty02_union_parts(node.right)
    else:
        yield node
def _ty02_is_redundant(node: ast.AST,
                       context: _ExprScopeContext) -> bool:
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr)):
        return False
    parts = tuple(_ty02_union_parts(node))
    return (any(_is_optional_subscript(part, context)
                for part in parts)
            and any(is_none_literal(part) for part in parts))
def _ty02_finding(node: ast.BinOp, source_lines: list[str],
                  filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TY-02", severity="P2", dimension="typing",
        file=filepath, line=node.lineno,
        title="Optional[X] | None 类型注解冗余",
        description="Optional[X] | None 双重可选注解，Optional[X] 本身已含 None",
        suggestion=("根因: Optional[X] 是 X | None 的别名，再 | None 属冗余嵌套，"
                    "干扰读者对可选性的判断。该问题属于类型注解类别。\n"
                    "修复策略: 直接使用 Optional[X] 或 X | None（二选一）\n"
                    "参考标准: PEP 484 / mypy"),
        code_snippet=get_code_snippet(source_lines, node.lineno),
    )
def check_TY02(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    context = _expr_scope_context(tree)
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree, ast.BinOp):
        parent = context.parents.get(id(node))
        if (isinstance(parent, ast.BinOp)
                and isinstance(parent.op, ast.BitOr)):
            continue
        if _ty02_is_redundant(node, context):
            issues.append(_ty02_finding(node, source_lines, filepath))
    return issues
_DF03_NON_SET_LITERALS = (
    ast.Constant, ast.List, ast.Tuple, ast.Dict, ast.JoinedStr,
    ast.ListComp, ast.DictComp, ast.GeneratorExp,
)
_DF03_SET_FACTORY_NAMES = frozenset({"set", "frozenset"})
def _df03_is_set_operand(node: ast.AST,
                         context: _ExprScopeContext) -> bool:
    if isinstance(node, (ast.Set, ast.SetComp)):
        return True
    return _expr_builtin_call(node, _DF03_SET_FACTORY_NAMES, context)
def _df03_non_set_operand(node: ast.BinOp,
                          context: _ExprScopeContext
                          ) -> tuple[str, ast.AST] | None:
    left_set = _df03_is_set_operand(node.left, context)
    right_set = _df03_is_set_operand(node.right, context)
    if left_set == right_set:
        return None
    side, operand = ("右", node.right) if left_set else ("左", node.left)
    if isinstance(operand, _DF03_NON_SET_LITERALS):
        return side, operand
    return None
def check_DF03(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    set_op_types = (ast.BitAnd, ast.BitOr, ast.BitXor, ast.Sub)
    context = _expr_scope_context(tree)
    for node in _walk_nodes(tree, ast.BinOp):
        if not isinstance(node.op, set_op_types):
            continue
        hit = _df03_non_set_operand(node, context)
        if hit is None:
            continue
        bad, operand = hit
        op_name = type(node.op).__name__
        issues.append(DiagnoseFinding(
            id="DF-03", severity="P2", dimension="defensive",
            file=filepath, line=node.lineno,
            title="集合与非集合类型直接运算",
            description=(f"set 字面量与{bad}操作数字面量（{unparse_or_type_name(operand)}）直接"
                         f"执行 {op_name} 运算，运行时必然 TypeError"),
            suggestion=("根因: set 的 &/|/^/- 仅接受 set/frozenset 操作数，与非集合"
                        "字面量运算在运行时抛 TypeError。该问题属于防御式编程类别。\n"
                        "修复策略: 确保操作数类型一致——字面量侧改写为 set(...)，"
                        "或改用 in 判定/集合方法\n"
                        "参考标准: Python 数据模型 / set 运算语义"),
            code_snippet=get_code_snippet(source_lines, node.lineno),
            rule_ref="DF-03",
        ))
    return issues
def _make_db05_issue(filepath: str, lineno: int,
                     source: str | list[str]) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="DB-05", severity="P0", dimension="database",
        file=filepath, line=lineno,
        message="SQLite PRAGMA 不支持参数化占位符 (?)",
        description=(
            "SQLite 的 PRAGMA 语句不支持 ? 参数化占位符。"
            "conn.execute('PRAGMA busy_timeout=?', (val,)) 会抛 sqlite3.OperationalError。"
        ),
        suggestion=("根因: PRAGMA 语句不支持参数绑定，执行时抛 "
                    "sqlite3.OperationalError（语法错误）。\n"
                    "修复策略: 仅对经类型校验或白名单约束的可信值生成 PRAGMA 字面量，"
                    "例如 conn.execute(f'PRAGMA busy_timeout={timeout_ms}')\n"
                    "参考标准: SQLite PRAGMA 语句文档"),
        code_snippet=extract_code_lines(source, lineno),
    )
def check_DB05(tree: ast.AST, source: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    for node in _walk_nodes(tree, ast.Call):
        if not (isinstance(node.func, ast.Attribute)
                and node.func.attr in ("execute", "executemany")):
            continue
        if not node.args:
            continue
        if _db05_is_pragma_param_sql(node.args[0]):
            issues.append(_make_db05_issue(filepath, node.lineno, source))
    return issues
def _db05_skip_quoted(text: str, start: int, quote: str) -> int:
    index = start + 1
    while index < len(text):
        if text[index] != quote:
            index += 1
            continue
        if index + 1 < len(text) and text[index + 1] == quote:
            index += 2
            continue
        return index + 1
    return len(text)
def _db05_after_token(text: str, index: int, token: str) -> int:
    closing = text.find(token, index + 1)
    return len(text) if closing < 0 else closing + len(token)
def _db05_has_pragma_prefix(text: str) -> bool:
    index = 0
    while index < len(text):
        while index < len(text) and text[index].isspace():
            index += 1
        if text.startswith("--", index):
            index = _db05_after_token(text, index + 1, "\n")
            continue
        if text.startswith("/*", index):
            index = _db05_after_token(text, index + 1, "*/")
            continue
        break
    keyword = "PRAGMA"
    end = index + len(keyword)
    if text[index:end].upper() != keyword:
        return False
    return end >= len(text) or not (
        text[end].isalnum() or text[end] in "_$")
def _db05_non_code_end(text: str, index: int) -> int | None:
    char = text[index]
    if char in ("'", '"', "`"):
        return _db05_skip_quoted(text, index, char)
    if text.startswith("--", index):
        return _db05_after_token(text, index + 1, "\n")
    if text.startswith("/*", index):
        return _db05_after_token(text, index + 1, "*/")
    if char == "[":
        return _db05_after_token(text, index, "]")
    return None
def _db05_has_qmark_placeholder(text: str) -> bool:
    index = 0
    while index < len(text):
        skipped_end = _db05_non_code_end(text, index)
        if skipped_end is not None:
            index = skipped_end
            continue
        if text[index] == "?":
            return True
        index += 1
    return False
def _db05_is_pragma_param_sql(sql_arg: ast.AST) -> bool:
    sql_text, literal_text, _complete = _db05_sql_texts(sql_arg)
    return bool(sql_text and literal_text is not None
                and _db05_has_qmark_placeholder(literal_text)
                and _db05_has_pragma_prefix(sql_text))
def _db05_concat_sql_texts(
        sql_arg: ast.BinOp) -> tuple[str | None, str | None, bool]:
    left_prefix, left_literal, left_complete = _db05_sql_texts(sql_arg.left)
    right_prefix, right_literal, right_complete = _db05_sql_texts(sql_arg.right)
    prefix = left_prefix
    if left_complete and left_prefix is not None:
        prefix = left_prefix + (right_prefix or "")
    literal_parts = [part for part in (left_literal, right_literal)
                     if part is not None]
    literal_text = "".join(literal_parts) if literal_parts else None
    return prefix, literal_text, left_complete and right_complete
def _db05_joined_sql_texts(
        sql_arg: ast.JoinedStr) -> tuple[str, str, bool]:
    prefix_parts: list[str] = []
    literal_parts: list[str] = []
    complete = True
    for part in sql_arg.values:
        if not isinstance(part, ast.Constant):
            complete = False
            continue
        text = str(part.value)
        literal_parts.append(text)
        if complete:
            prefix_parts.append(text)
    return "".join(prefix_parts), "".join(literal_parts), complete
def _db05_sql_texts(sql_arg: ast.AST) -> tuple[str | None, str | None, bool]:
    if isinstance(sql_arg, ast.Constant) and isinstance(sql_arg.value, str):
        return sql_arg.value, sql_arg.value, True
    if isinstance(sql_arg, ast.BinOp) and isinstance(sql_arg.op, ast.Add):
        return _db05_concat_sql_texts(sql_arg)
    if isinstance(sql_arg, ast.JoinedStr):
        return _db05_joined_sql_texts(sql_arg)
    return None, None, False
_FL01_EXACT_CACHE: dict[str, bool] = {}
_FL01_EXACT_CACHE_MAX = 4096
def _fl01_literal_text(node: ast.AST, source_text: str) -> str | None:
    if not source_text:
        return None
    text = ast.get_source_segment(source_text, node)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        operand_text = ast.get_source_segment(source_text, node.operand)
        if operand_text and operand_text.strip():
            sign = "-" if isinstance(node.op, ast.USub) else "+"
            text = sign + operand_text.strip()
    return text.strip() if text and text.strip() else None
def _fl01_is_non_exact(value: float, literal_text: str | None = None) -> bool:
    text = literal_text or repr(value)
    key = f"{value!r}@{text}"
    cached = _FL01_EXACT_CACHE.get(key)
    if cached is not None:
        return cached
    try:
        exact = Fraction(text) == Fraction.from_float(value)
    except (ValueError, ZeroDivisionError, OverflowError) as _e:
        logger.debug("[FL01] Fraction 解析失败（inf/nan 等），按精确处理跳过: %r (%s)", value, _e)
        exact = True
    _non_exact = not exact
    if len(_FL01_EXACT_CACHE) >= _FL01_EXACT_CACHE_MAX:
        _FL01_EXACT_CACHE.clear()
    _FL01_EXACT_CACHE[key] = _non_exact
    return _non_exact
def _fl01_first_non_exact(
        compare: ast.Compare, source_text: str) -> tuple[float, str | None] | None:
    for op, operand in _iter_eq_operand_pairs(compare):
        if not isinstance(op, (ast.Eq, ast.NotEq)):
            continue
        value = _signed_float_literal(operand)
        literal_text = _fl01_literal_text(operand, source_text)
        if (value is not None
                and _fl01_is_non_exact(value, literal_text)):
            return value, literal_text
    return None
def check_FL01(tree: ast.AST | None, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    source_text = "\n".join(_as_source_lines(source_lines))
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Compare):
            continue
        hit = _fl01_first_non_exact(node, source_text)
        if hit is None:
            continue
        hit_value, hit_text = hit
        issues.append(DiagnoseFinding(
            id="FL-01", severity="P2", dimension="numeric",
            file=filepath, line=node.lineno,
            description=(f"非精确浮点字面量 {hit_text or repr(hit_value)} "
                         "参与 ==/!= 比较"
                         "（二进制舍入误差致条件意外命中或永不命中）"),
            code_snippet=get_code_snippet(source_lines, node.lineno),
            suggestion=("根因: 0.1/0.3 等十进制值在二进制浮点中是近似表示，"
                        "== 比较的是舍入后的位模式而非数学相等。\n"
                        "修复策略: 用 math.isclose(a, b, rel_tol=1e-9) 容差比较；"
                        "金额等精确十进制场景改用 decimal.Decimal\n"
                        "参考标准: IEEE 754 / PEP 485"),
        ))
    return issues
_TY03_NONSTR_RETURN_BUILTINS = frozenset({
    "len", "ord", "int", "float", "complex", "bool", "bytes",
    "bytearray", "memoryview", "list", "tuple", "dict", "set",
    "frozenset",
})
def _ty03_fold_add_chain(node: ast.expr, memo: dict[ast.AST, bool],
                          leaf_of, combine) -> bool:
    if node in memo:
        return memo[node]
    stack: list[tuple[ast.AST, bool]] = [(node, False)]
    while stack:
        cur, expanded = stack.pop()
        if expanded:
            memo[cur] = combine(memo[cur.left], memo[cur.right])
            continue
        if cur in memo:
            continue
        if isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Add):
            stack.append((cur, True))
            stack.append((cur.right, False))
            stack.append((cur.left, False))
        else:
            memo[cur] = leaf_of(cur)
    return memo[node]
def _ty03_str_leaf(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, str)
    return isinstance(node, ast.JoinedStr)
_TY03_NODE_KINDS = {
    ast.List: "list", ast.Tuple: "tuple", ast.Dict: "dict", ast.Set: "set",
    ast.ListComp: "list", ast.SetComp: "set", ast.DictComp: "dict",
    ast.GeneratorExp: "generator",
}
_TY03_NONSTR_LITERAL_NODES = tuple(_TY03_NODE_KINDS)
def _ty03_nonstr_leaf(node: ast.AST,
                      context: _ExprScopeContext) -> bool:
    if isinstance(node, ast.Constant):
        return (isinstance(node.value, (int, float, complex, bool, bytes))
                or node.value is None or node.value is Ellipsis)
    if isinstance(node, _TY03_NONSTR_LITERAL_NODES):
        return True
    return (_ty03_signed_numeric_literal(node)
            or _expr_builtin_call(
                node, _TY03_NONSTR_RETURN_BUILTINS, context))
def _ty03_signed_numeric_literal(node: ast.AST) -> bool:
    return (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, (int, float, complex, bool)))
def _ty03_is_deterministic_typeerror(
        node: ast.expr,
        str_memo: dict[ast.AST, bool],
        nonstr_memo: dict[ast.AST, bool],
        context: _ExprScopeContext) -> bool:
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    definite_str = partial(_ty03_fold_add_chain, memo=str_memo,
                           leaf_of=_ty03_str_leaf, combine=bool.__and__)
    left_str = definite_str(node.left)
    right_str = definite_str(node.right)
    if left_str == right_str:
        return False
    other = node.right if left_str else node.left
    return _ty03_fold_add_chain(
        other, nonstr_memo,
        partial(_ty03_nonstr_leaf, context=context), bool.__and__)
def _ty03_operand_kind(other: ast.expr) -> str:
    node_kind = _TY03_NODE_KINDS.get(type(other))
    if node_kind is not None:
        return node_kind
    if isinstance(other, ast.Constant):
        return type(other.value).__name__
    if isinstance(other, ast.UnaryOp):
        return type(other.operand.value).__name__
    if isinstance(other, ast.Call):
        return "内置非 str 返回值"
    return "数值表达式"
def check_TY03(tree: ast.AST | None, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    context = _expr_scope_context(tree)
    str_memo: dict[ast.AST, bool] = {}
    nonstr_memo: dict[ast.AST, bool] = {}
    for node in tree_nodes(tree):
        if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Add):
            continue
        if not _ty03_is_deterministic_typeerror(
                node, str_memo, nonstr_memo, context):
            continue
        left_str = str_memo[node.left]
        if _ty03_is_deterministic_typeerror(
                node.left if left_str else node.right,
                str_memo, nonstr_memo, context):
            continue
        other = node.right if left_str else node.left
        operand_kind = _ty03_operand_kind(other)
        issues.append(DiagnoseFinding(
            id="TY-03", severity="P1", dimension="typing",
            file=filepath, line=node.lineno,
            description=f"字符串与非 str 操作数直接拼接（{operand_kind}），运行时 TypeError",
            code_snippet=get_code_snippet(source_lines, node.lineno),
            suggestion=("根因: + 不做隐式类型转换，str 与 int/float/bool 相加"
                        "直接抛 TypeError。\n"
                        "修复策略: 拼接前显式转换 str(value) 或改用 f-string"
                        "（自动调用 __format__）\n参考标准: Python 语言参考"
                        " 二进制算术运算"),
        ))
    return issues
_MODULE_ROOT = "MODULE_ROOT"
def _is_numeric_zero_value(value: object) -> bool:
    return (isinstance(value, (int, float, complex))
            and not isinstance(value, bool)
            and value == 0)
def _numeric_zero_literal(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return _is_numeric_zero_value(node.value)
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))
            and isinstance(node.operand, ast.Constant)):
        return _is_numeric_zero_value(node.operand.value)
    return False
_TP17_SCORE_VARS = frozenset({
    "score", "precision", "recall", "f1", "accuracy", "confidence",
    "quality_score", "f1_score",
})
_TP17_STATUS_TARGETS = frozenset({"status", "verdict", "state"})
_TP17_STATUS_WORDS = frozenset({
    "degraded", "cancelled", "partial", "blocked", "pending", "error",
    "fail", "skip", "unknown", "failed",
})
_TP17_STATUS_WORDS_U = frozenset({w.upper() for w in _TP17_STATUS_WORDS})
_TP19_SENSITIVE_KWARGS = frozenset({
    "threshold", "min_score", "timeout", "max_retries", "limit",
})
def _tp17_enclosing_scope(node: ast.AST,
                          parents: dict[ast.AST, ast.AST]) -> ast.AST | str:
    cur = parents.get(node)
    while cur is not None and not isinstance(cur, (
            ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
            ast.Module, ast.ClassDef)):
        cur = parents.get(cur)
    return cur if cur is not None else _MODULE_ROOT
def _tp17_target_key(t: ast.AST) -> tuple[str, ...] | None:
    if isinstance(t, ast.Name):
        return ("name", t.id)
    if (isinstance(t, ast.Attribute)
            and isinstance(t.value, ast.Name)):
        return ("attr", t.value.id, t.attr)
    return None
def _tp17_target_name(target: ast.expr) -> str | None:
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        return target.attr
    return None
def _tp17_targets_value(
        node: ast.AST) -> tuple[list[ast.AST], ast.AST] | None:
    if isinstance(node, ast.NamedExpr):
        return [node.target], node.value
    return assign_targets_value(node)
def _tp17_write_keys(n: ast.AST) -> tuple[tuple[str, ...], ...]:
    if isinstance(n, ast.AugAssign):
        targets: Iterable[ast.AST] = (n.target,)
    else:
        parts = _tp17_targets_value(n)
        if parts is None:
            return ()
        targets = parts[0]
    return tuple(k for k in (_tp17_target_key(t)
                             for t in _iter_leaf_targets(targets))
                 if k is not None)
def _tp17_scope_writes(key: tuple[str, ...], node: ast.AST,
                       parents: dict[ast.AST, ast.AST],
                       tree: ast.AST) -> Iterator[ast.AST]:
    scope = _tp17_enclosing_scope(node, parents)
    for n in tree_nodes(tree):
        if n is node or key not in _tp17_write_keys(n):
            continue
        if _tp17_enclosing_scope(n, parents) is not scope:
            continue
        yield n
def _tp17_statement_location(node: ast.AST,
                             parents: dict[ast.AST, ast.AST]):
    current = node
    while current is not None and not isinstance(current, ast.stmt):
        current = parents.get(current)
    parent = parents.get(current) if current is not None else None
    if parent is None:
        return None
    for field in ("body", "orelse", "finalbody"):
        statements = getattr(parent, field, None)
        if (isinstance(statements, list)
                and any(stmt is current for stmt in statements)):
            return statements, current
    return None
def _tp17_statement_settles_key(stmt: ast.stmt,
                                key: tuple[str, ...]) -> bool:
    if (isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign))
            and key in _tp17_write_keys(stmt)
            and (isinstance(stmt, ast.AugAssign)
                 or not _tp17_write_preserves_key(stmt, key))):
        return True
    if isinstance(stmt, ast.Return):
        return not _tp17_value_reads_key(stmt, key)
    if not isinstance(stmt, ast.If):
        return False
    if isinstance(stmt.test, ast.Constant):
        branch = stmt.body if bool(stmt.test.value) else stmt.orelse
        return _tp17_block_settles_key(branch, key)
    return (bool(stmt.orelse)
            and _tp17_block_settles_key(stmt.body, key)
            and _tp17_block_settles_key(stmt.orelse, key))
def _tp17_block_settles_key(statements: list[ast.stmt],
                            key: tuple[str, ...]) -> bool:
    return any(_tp17_statement_settles_key(stmt, key)
               for stmt in statements)
def _tp17_write_has_unsettled_if_path(
        write: ast.AST, key: tuple[str, ...],
        parents: dict[ast.AST, ast.AST]) -> bool:
    scope = _tp17_enclosing_scope(write, parents)
    current = write
    while current is not scope:
        parent = parents.get(current)
        if parent is None:
            break
        if (isinstance(parent, ast.If)
                and (current in parent.body or current in parent.orelse)
                and not _tp17_statement_settles_key(parent, key)):
            return True
        current = parent
    return False
def _tp17_mutated_later(target: ast.expr, node: ast.AST,
                        parents: dict[ast.AST, ast.AST], tree: ast.AST) -> bool:
    key = _tp17_target_key(target)
    if key is None:
        return False
    location = _tp17_statement_location(node, parents)
    statements, current = location if location is not None else (None, None)
    if statements is not None:
        start = statements.index(current)
        for later in statements[start + 1:]:
            if (isinstance(later, ast.If)
                    and _tp17_statement_settles_key(later, key)
                    and not _tp17_intervening_value_read(
                        node, later, parents, tree, key)
                    and not _tp17_block_has_early_exit(later.body, key)
                    and not _tp17_block_has_early_exit(later.orelse, key)):
                return True
            if _tp17_block_has_early_exit([later], key):
                break
    for write in _tp17_scope_writes(key, node, parents, tree):
        if ((write.lineno, write.col_offset)
                <= (node.lineno, node.col_offset)):
            continue
        if (not isinstance(write, ast.AugAssign)
                and _tp17_write_preserves_key(write, key)):
            continue
        reads_current = (isinstance(write, ast.AugAssign)
                         or _tp17_value_reads_key(write, key))
        write_location = _tp17_statement_location(write, parents)
        if (statements is not None and write_location is not None
                and write_location[0] is statements):
            start = statements.index(current)
            end = statements.index(write_location[1])
            if end <= start:
                continue
            if _tp17_block_has_early_exit(
                    statements[start + 1:end], key):
                continue
        elif (not reads_current
              or _tp17_intervening_function_exit(
                  node, write, parents, tree, key)
              or _tp17_write_has_unsettled_if_path(write, key, parents)):
            continue
        if _tp17_intervening_value_read(node, write, parents, tree, key):
            continue
        return True
    return False
_TP17_FUNCTION_EXIT_TYPES = (ast.Return, ast.Raise)
_TP17_LOOP_EXIT_TYPES = (ast.Break, ast.Continue)
_TP17_LOOP_TYPES = (ast.For, ast.AsyncFor, ast.While)
_TP17_NESTED_DEF_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.Lambda, ast.ClassDef)
def _tp17_exit_consumes_key(node: ast.AST,
                            key: tuple[str, ...]) -> bool:
    if isinstance(node, ast.Return):
        return _tp17_value_reads_key(node, key)
    return True
def _tp17_intervening_value_read(
        node: ast.AST, write: ast.AST,
        parents: dict[ast.AST, ast.AST], tree: ast.AST,
        key: tuple[str, ...]) -> bool:
    scope = _tp17_enclosing_scope(node, parents)
    start = (node.lineno, node.col_offset)
    end = (write.lineno, write.col_offset)
    for candidate in tree_nodes(tree):
        if not isinstance(candidate, (ast.Name, ast.Attribute)):
            continue
        position = (candidate.lineno, candidate.col_offset)
        if not start < position < end:
            continue
        if (_tp17_target_key(candidate) != key
                or _tp17_enclosing_scope(candidate, parents) is not scope):
            continue
        if isinstance(candidate.ctx, ast.Load):
            return True
        parent = parents.get(candidate)
        if isinstance(parent, ast.AugAssign) and parent.target is candidate:
            return True
    return False
def _tp17_intervening_function_exit(
        node: ast.AST, write: ast.AST,
        parents: dict[ast.AST, ast.AST], tree: ast.AST,
        key: tuple[str, ...]) -> bool:
    scope = _tp17_enclosing_scope(node, parents)
    start = (node.lineno, node.col_offset)
    end = (write.lineno, write.col_offset)
    for candidate in tree_nodes(tree):
        if not isinstance(candidate, _TP17_FUNCTION_EXIT_TYPES):
            continue
        position = (candidate.lineno, candidate.col_offset)
        if (start < position < end
                and _tp17_enclosing_scope(candidate, parents) is scope
                and _tp17_exit_consumes_key(candidate, key)):
            return True
    return False
def _tp17_block_has_early_exit(stmts: list,
                               key: tuple[str, ...]) -> bool:
    stack: list[tuple[ast.AST, int]] = [(stmt, 0) for stmt in stmts]
    while stack:
        cur, loop_depth = stack.pop()
        if isinstance(cur, _TP17_NESTED_DEF_TYPES):
            continue
        if (isinstance(cur, _TP17_FUNCTION_EXIT_TYPES)
                and _tp17_exit_consumes_key(cur, key)):
            return True
        if loop_depth == 0 and isinstance(cur, _TP17_LOOP_EXIT_TYPES):
            return True
        for field_name, value in ast.iter_fields(cur):
            child_depth = loop_depth + int(
                isinstance(cur, _TP17_LOOP_TYPES) and field_name == "body")
            if isinstance(value, list):
                stack.extend((child, child_depth) for child in value
                             if isinstance(child, ast.AST))
            elif isinstance(value, ast.AST):
                stack.append((value, child_depth))
    return False
def _tp17_value_reads_key(write: ast.AST, key: tuple[str, ...]) -> bool:
    value = getattr(write, "value", None)
    if value is None:
        return False
    return any(_tp17_target_key(sub) == key for sub in walk_nodes(value)
               if isinstance(sub, (ast.Name, ast.Attribute)))
def _tp17_status_word_value(val: ast.expr) -> bool:
    return (isinstance(val, ast.Constant) and isinstance(val.value, str)
            and val.value.strip().lower() in _TP17_STATUS_WORDS)
def _tp17_enum_status_value(val: ast.expr) -> bool:
    if isinstance(val, ast.Attribute) and val.attr == "value":
        val = val.value
    return (isinstance(val, ast.Attribute)
            and val.attr.upper() in _TP17_STATUS_WORDS_U)
def _tp17_is_status_decl(assign_node: ast.Assign | ast.AnnAssign) -> bool:
    targets = (assign_node.targets if isinstance(assign_node, ast.Assign)
               else (assign_node.target,))
    val = assign_node.value
    if _tp17_status_word_value(val) or _tp17_enum_status_value(val):
        return True
    return (isinstance(val, ast.Constant)
            and any((_tp17_target_name(t) or "").lower() in _TP17_STATUS_TARGETS
                    for t in targets))
def _tp17_sentinel_nearby(node: ast.AST, tree: ast.AST,
                           parents: dict[ast.AST, ast.AST]) -> bool:
    scope = _tp17_enclosing_scope(node, parents)
    return any(
        isinstance(n, (ast.Assign, ast.AnnAssign)) and _tp17_is_status_decl(n)
        and abs(n.lineno - node.lineno) <= 6
        and _tp17_enclosing_scope(n, parents) is scope
        for n in tree_nodes(tree)
    )
def _tp17_branch_renormalize(target: ast.expr, node: ast.AST,
                             parents: dict[ast.AST, ast.AST],
                             tree: ast.AST) -> bool:
    p = parents.get(node)
    if not isinstance(p, (ast.If, ast.Try, ast.ExceptHandler)):
        return False
    key = _tp17_target_key(target)
    if key is None:
        return False
    if _tp17_key_is_param(key, node, parents):
        return True
    return any(w.lineno < node.lineno
               for w in _tp17_scope_writes(key, node, parents, tree))
def _tp17_key_is_param(key: tuple[str, ...], node: ast.AST,
                       parents: dict[ast.AST, ast.AST]) -> bool:
    scope = _tp17_enclosing_scope(node, parents)
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    return key[0] == "name" and key[1] in collect_param_names(scope)
def _tp17_suppress_map(source_lines: str | list[str] | None) -> dict:
    lines = _as_source_lines(source_lines)
    if not lines:
        return {}
    return parse_suppressions("\n".join(lines))
def _tp17_class_or_init_field(t: ast.expr, node: ast.AST,
                              parents: dict[ast.AST, ast.AST]) -> bool:
    scope = _tp17_enclosing_scope(node, parents)
    if isinstance(scope, ast.ClassDef):
        return True
    return (isinstance(t, ast.Attribute)
            and isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
            and scope.name == "__init__")
def _tp17_is_exempt_assignment(t: ast.expr,
                               node: ast.AST,
                               suppress_map: dict,
                               parents: dict[ast.AST, ast.AST],
                               tree: ast.AST) -> bool:
    if is_suppressed(suppress_map, node.lineno, "TP-17"):
        return True
    if _tp17_class_or_init_field(t, node, parents):
        return True
    if _tp17_mutated_later(t, node, parents, tree):
        return True
    if _tp17_sentinel_nearby(node, tree, parents):
        return True
    return _tp17_branch_renormalize(t, node, parents, tree)
def _tp17_aligned_target_values(
        target: ast.expr, value: ast.AST
) -> Iterator[tuple[ast.expr, ast.AST]]:
    if not isinstance(target, (ast.Tuple, ast.List)):
        yield target, value
        return
    if not isinstance(value, (ast.Tuple, ast.List)):
        return
    target_items = target.elts
    value_items = value.elts
    starred = [index for index, item in enumerate(target_items)
               if isinstance(item, ast.Starred)]
    if not starred:
        if len(target_items) != len(value_items):
            return
        pairs = list(zip(target_items, value_items))
    else:
        if len(starred) != 1 or len(value_items) < len(target_items) - 1:
            return
        star_index = starred[0]
        trailing = len(target_items) - star_index - 1
        pairs = list(zip(target_items[:star_index],
                         value_items[:star_index]))
        if trailing:
            pairs.extend(zip(target_items[star_index + 1:],
                             value_items[-trailing:]))
    for target_item, value_item in pairs:
        yield from _tp17_aligned_target_values(target_item, value_item)
def _tp17_write_preserves_key(write: ast.AST,
                              key: tuple[str, ...]) -> bool:
    parts = _tp17_targets_value(write)
    if parts is None:
        return False
    targets, value = parts
    matched = False
    last_source: ast.AST | None = None
    for root_target in targets:
        for target, source in _tp17_aligned_target_values(root_target, value):
            if _tp17_target_key(target) != key:
                continue
            matched = True
            last_source = source
    return matched and _tp17_target_key(last_source) == key
def _tp17_unpacked_zero_targets(target: ast.expr,
                                value: ast.AST) -> Iterator[ast.expr]:
    for target_item, value_item in _tp17_aligned_target_values(target, value):
        if _numeric_zero_literal(value_item):
            yield target_item
def _tp17_placeholder_targets(node: ast.AST) -> tuple[ast.expr, ...]:
    parts = _tp17_targets_value(node)
    if parts is None:
        return ()
    targets, value = parts
    return tuple(
        target
        for root_target in targets
        for target in _tp17_unpacked_zero_targets(root_target, value)
    )
def _tp17_finding(target_name: str, line: int, filepath: str,
                  source_lines: str | list[str]) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TP-17", severity="P2", dimension="trap",
        file=filepath, line=line,
        description=f"指标 {target_name} 硬编码 0.0（未计算被当作计算结果）",
        code_snippet=get_code_snippet(source_lines, line),
        suggestion=("根因: 指标未计算时以 0.0 占位写入结果，下游无法区分"
                    "「没算」与「算了得 0 分」。\n"
                    "修复策略: 未计算时用 None 并在消费侧显式处理；"
                    "或用 sentinel 常量标注未计算态\n"
                    "参考标准: 可观测性设计（未计算态与零值必须可区分）"),
    )
def check_TP17(tree: ast.AST | None, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    parents = parent_map(tree)
    suppress_map: dict | None = None
    for node in tree_nodes(tree):
        for t in _tp17_placeholder_targets(node):
            target_name = _tp17_target_name(t)
            if target_name not in _TP17_SCORE_VARS:
                continue
            if suppress_map is None:
                suppress_map = _tp17_suppress_map(source_lines)
            if _tp17_is_exempt_assignment(t, node, suppress_map,
                                          parents, tree):
                continue
            issues.append(
                _tp17_finding(target_name, node.lineno, filepath,
                              source_lines))
    return issues
def _tp19_finding(kw: ast.keyword, filepath: str,
                  source_lines: str | list[str]) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TP-19", severity="P2", dimension="trap",
        file=filepath, line=kw.value.lineno,
        description=(f"关键参数 {kw.arg}=0 硬编码"
                     "（阈值/超时/上限归零改变业务语义）"),
        code_snippet=get_code_snippet(source_lines, kw.value.lineno),
        suggestion=("根因: 敏感参数归零使守卫逻辑恒真/恒假或立即超时，"
                    "静默绕过保护。\n"
                    "修复策略: 显式传业务语义值；确需禁用时用独立布尔开关"
                    "（如 enabled=False）而非参数归零\n"
                    "参考标准: 防御式编程（阈值/超时不得用 0 表示禁用）"),
    )
def check_TP19(tree: ast.AST | None, source_lines: str | list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        for kw in node.keywords:
            if _tp19_is_zeroed_sensitive_kwarg(kw):
                issues.append(_tp19_finding(kw, filepath, source_lines))
    return issues
def _tp19_is_zeroed_sensitive_kwarg(kw: ast.keyword) -> bool:
    return (kw.arg in _TP19_SENSITIVE_KWARGS
            and _numeric_zero_literal(kw.value))
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "diag4_direct": {
                'DB-05': check_DB05, 'DG-01': check_DG01,
            },
            "aicoder_direct": {
                'FL-01': check_FL01, 'TY-03': check_TY03,
            },
            "recovered_bindings": {
                'IC01': check_IC01, 'NT01': check_NT01, 'BZ01': check_BZ01,
                'NM02': check_NM02, 'TY02': check_TY02, 'DF03': check_DF03,
            },
            "traps_bindings": {
                'FL01': check_FL01, 'TP17': check_TP17,
                'TP19': check_TP19, 'TY03': check_TY03,
            },
            "rule_bindings": {
                'DB05': check_DB05, 'DG01': check_DG01,
                'RB14': check_RB14, 'RB17': check_RB17, 'RC01': check_RC01,
            },
        },
    }

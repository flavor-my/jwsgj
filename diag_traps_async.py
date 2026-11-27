from __future__ import annotations

import ast
import logging
import re
from collections.abc import Iterator
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    build_parent_map,
    call_tail_name,
    definition_time_exprs,
    dotted_name,
    get_call_name,
    iter_def_site_nodes,
    iter_unpack_target_names,
    module_postpones_annotations,
)
from jwsgj.diag_shared_ast_views import (
    call_scope_map,
    collect_lexical_scope_table,
    drain_frame_stack,
    scope_shadows_import,
    tree_nodes,
)
from jwsgj.diag_shared_ast_views import (
    parent_map as _shared_parent_map,
)
from jwsgj.diag_shared_source_core import (
    extract_code_lines,
)
from jwsgj.diag_shared_source_scan import (
    get_code_snippet,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    FindingRecord,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    "check_AY01",
    "check_AY03",
    "check_AY05",
    "check_AY06",
    "check_AY07",
    "check_IT01",
    "check_RD04",
    "check_RD14",
    "check_RD17",
    "check_X3",
]
_log.info("diag_traps_async asyncio 与迭代结构规则域已加载: %d 项导出", len(__all__))
_TRANSPARENT_RESULT_PARENTS = (
    ast.BoolOp, ast.IfExp,
    ast.Tuple, ast.List, ast.Set, ast.Dict,
)
_TRANSFORMING_RESULT_PARENTS = (
    ast.BinOp, ast.UnaryOp, ast.Compare, ast.FormattedValue,
)
_RESULT_ERASING_CALLS = frozenset({"bool", "format", "print", "repr", "str"})
# Task/Executor 的结果对象只要被这些方法消费，异常就不再静默：
# ``task.result()``/``task.exception()`` 会取回异常，
# ``task.add_done_callback(cb)`` 把结果交给回调。AY-01（create_task）与
# AY-06（Executor.submit）共用同一判定，避免同一引擎两套结论。
_TASK_RESULT_OBSERVERS = frozenset({"result", "exception", "add_done_callback"})
_TRANSPARENT_RESULT_RECEIVERS = (ast.Attribute, ast.Call, ast.Subscript)
def _is_result_receiver(parent: ast.AST, current: ast.AST) -> bool:
    if not isinstance(parent, _TRANSPARENT_RESULT_RECEIVERS):
        return False
    if isinstance(parent, ast.Call):
        return parent.func is current
    return parent.value is current
def _result_discarded(
        node: ast.AST, parent_map: dict, *,
        observing_methods: frozenset[str] = frozenset(),
) -> bool:
    current = node
    parent = parent_map.get(current)
    while parent is not None:
        if isinstance(parent, _TRANSFORMING_RESULT_PARENTS):
            return True
        if (isinstance(parent, ast.BoolOp) and isinstance(parent.op, ast.And)
                and current is not parent.values[-1]):
            return True
        if (isinstance(parent, (ast.IfExp, ast.If, ast.While, ast.Assert))
                and parent.test is current):
            return True
        if (isinstance(parent, ast.comprehension)
                and any(current is condition for condition in parent.ifs)):
            return True
        if isinstance(parent, _TRANSPARENT_RESULT_PARENTS):
            current, parent = parent, parent_map.get(parent)
            continue
        if (isinstance(parent, ast.Attribute) and parent.value is current
                and parent.attr in observing_methods):
            observer_call = parent_map.get(parent)
            if (isinstance(observer_call, ast.Call)
                    and observer_call.func is parent):
                return False
        if (isinstance(parent, ast.Call)
                and isinstance(parent.func, ast.Name)
                and parent.func.id in _RESULT_ERASING_CALLS
                and any(current is arg for arg in parent.args)):
            return True
        if _is_result_receiver(parent, current):
            current, parent = parent, parent_map.get(parent)
            continue
        break
    return parent is None or isinstance(parent, ast.Expr)
_COMPREHENSION_SCOPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_ASYNCIO_DEFAULT_MODULES = frozenset({"asyncio"})
_CONCURRENT_DEFAULT_MODULES = frozenset({"concurrent"})
def _binding_scope(node: ast.AST, table: Any, pm: dict) -> ast.AST | None:
    scope = pm.get(node)
    while scope is not None and scope not in table.bound:
        scope = pm.get(scope)
    while (isinstance(scope, ast.ExceptHandler)
           or (isinstance(node, ast.NamedExpr)
               and isinstance(scope, _COMPREHENSION_SCOPES))):
        scope = table.parent[scope]
    return scope
class _ScopedImportResolver:
    __slots__ = ("_default_modules", "_imports", "call_scopes", "table")
    def __init__(self, tree: ast.AST, *,
                 default_modules: frozenset[str] = frozenset()) -> None:
        self.table = collect_lexical_scope_table(tree)
        self.call_scopes = call_scope_map(self.table)
        self._default_modules = default_modules
        self._imports: dict[ast.AST, dict[str, str]] = {}
        parents = _shared_parent_map(tree)
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            scope = _binding_scope(node, self.table, parents)
            if scope is None:
                continue
            bindings = self._imports.setdefault(scope, {})
            if isinstance(node, ast.Import):
                for alias in node.names:
                    local = alias.asname or alias.name.split(".", 1)[0]
                    bindings[local] = alias.name if alias.asname else local
                continue
            if node.level or not node.module:
                continue
            for alias in node.names:
                if alias.name == "*":
                    continue
                local = alias.asname or alias.name
                bindings[local] = f"{node.module}.{alias.name}"
    def _visible_import(self, name: str, scope: ast.AST) -> str | None:
        direct = scope
        while scope is not None:
            if not isinstance(scope, ast.ClassDef) or scope is direct:
                binding = self._imports.get(scope, {}).get(name)
                if binding is not None:
                    return binding
            scope = self.table.parent.get(scope)
        return None
    def resolve(self, node: ast.Call) -> str | None:
        scope = self.call_scopes.get(id(node))
        name = dotted_name(node.func)
        if scope is None or not name:
            return None
        head, _, rest = name.partition(".")
        if scope_shadows_import(self.table, scope, head):
            return None
        imported = self._visible_import(head, scope)
        if imported is None:
            if head not in self._default_modules:
                return None
            imported = head
        return f"{imported}.{rest}" if rest else imported
def _iter_call_nodes(tree: Any) -> Iterator[ast.Call]:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            yield node
def _tail_name(dotted: str) -> str:
    return dotted.rsplit(".", 1)[-1]
def _ay_finding(rule_id: str, node: Any, description: str,
                suggestion: str, filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id=rule_id, severity="P1", dimension="asyncio",
        file=filepath, line=node.lineno,
        description=description, suggestion=suggestion,
    )
_AY01_SUGGESTION = (
    "根因: asyncio.create_task()结果未保存(fire-and-forget), 任务异常将被静默丢弃。"
    "该问题属于异步编程类别。\n"
    "修复策略: 保存Task引用: task = asyncio.create_task(coro) 并添加 done_callback 处理异常\n"
    "参考标准: PEP 8 / asyncio"
)
_AY03_SUGGESTION = (
    "根因: asyncio.gather()未设return_exceptions(异常可能被静默吞噬)。"
    "该问题属于异步编程类别。\n"
    "修复策略: 添加return_exceptions=True或使用asyncio.TaskGroup\n"
    "参考标准: PEP 8 / asyncio"
)
_AY05_SUGGESTION = (
    "根因: asyncio.run()在async函数内调用(会崩溃)。该问题属于异步编程类别。\n"
    "修复策略: 使用await代替asyncio.run()\n"
    "参考标准: PEP 8 / asyncio"
)
_AY06_SUGGESTION = (
    "根因: Executor.submit()结果未保存(异常被静默吞噬)。"
    "该问题属于异步编程类别。\n"
    "修复策略: 保存Future对象并调用future.result()或添加回调\n"
    "参考标准: PEP 8 / asyncio"
)
_AY07_SUGGESTION = (
    "根因: 事件循环策略被硬编码, 跨版本兼容性断裂(free-threading构建"
    "行为变更, Python 3.15+ 多个policy已弃用)。\n"
    "修复策略: 使用 asyncio.run() 让运行时自动选择策略; 确需自定义时"
    "按平台条件选择并在测试矩阵中锚定\n"
    "参考标准: PEP 703 / asyncio官方文档"
)
def _is_asyncio_module_path(module_path: str) -> bool:
    return module_path == "asyncio" or module_path.startswith("asyncio.")
def _ay_asyncio_member(canonical: str | None,
                       members: tuple[str, ...]) -> str | None:
    if not canonical:
        return None
    module, _, member = canonical.rpartition(".")
    if not _is_asyncio_module_path(module) or member not in members:
        return None
    return member
_AY07_POLICY_CALL_NAMES = frozenset({
    "set_event_loop_policy",
    "WindowsSelectorEventLoopPolicy",
    "WindowsProactorEventLoopPolicy",
    "DefaultEventLoopPolicy",
})
def _ay07_collect_hits(tree: Any) -> list[tuple[ast.Call, str]]:
    hits: list[tuple[ast.Call, str]] = []
    resolver = _ScopedImportResolver(
        tree, default_modules=_ASYNCIO_DEFAULT_MODULES)
    for node in _iter_call_nodes(tree):
        member = _ay_asyncio_member(
            resolver.resolve(node), _AY07_POLICY_CALL_NAMES)
        if member is None:
            continue
        func_name = get_call_name(node) or member
        if _tail_name(func_name) != member:
            func_name = f"{func_name} (asyncio.{member})"
        hits.append((node, func_name))
    return hits
def _ay07_is_nested_hit(node: ast.Call, hit_nodes: set,
                        parents: dict) -> bool:
    ancestor = parents.get(node)
    while ancestor is not None and ancestor not in hit_nodes:
        ancestor = parents.get(ancestor)
    return ancestor is not None
def _ay07_make_finding(node: ast.Call, func_name: str,
                       filepath: Any) -> DiagnoseFinding:
    return _ay_finding(
        "AY-07", node,
        (f"AY-07: asyncio事件循环策略硬编码/已弃用 ({func_name}). "
         f"free-threading构建中策略行为变更; Python 3.15+ 多个policy已弃用. "
         f"建议使用asyncio.run()自动选择策略, 或按平台条件选择."),
        _AY07_SUGGESTION, filepath)
def check_AY07(tree: Any, source_lines: Any, filepath: Any) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    hits = _ay07_collect_hits(tree)
    _parents = _shared_parent_map(tree)
    hit_nodes = {n for n, _ in hits}
    for node, func_name in hits:
        if _ay07_is_nested_hit(node, hit_nodes, _parents):
            continue
        issues.append(_ay07_make_finding(node, func_name, filepath))
    return issues
def check_AY01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    _parent_map = _shared_parent_map(tree)
    resolver = _ScopedImportResolver(
        tree, default_modules=_ASYNCIO_DEFAULT_MODULES)
    for node in _iter_call_nodes(tree):
        if _ay_asyncio_member(resolver.resolve(node), ("create_task",)):
            if not _result_discarded(
                    node, _parent_map,
                    observing_methods=_TASK_RESULT_OBSERVERS):
                continue
            issues.append(_ay_finding(
                "AY-01", node,
                "asyncio.create_task()结果未保存(fire-and-forget)",
                _AY01_SUGGESTION, filepath))
    return issues
def _ay03_literal_truthiness(node: ast.AST) -> bool | None:
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        operand = _ay03_literal_truthiness(node.operand)
        return None if operand is None else not operand
    try:
        value = ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError):
        return None
    return bool(value)
def _ay03_exceptions_discarded(node: ast.Call) -> bool:
    return_exc = next(
        (kw for kw in node.keywords if kw.arg == "return_exceptions"), None)
    if return_exc is not None:
        return _ay03_literal_truthiness(return_exc.value) is False
    return not any(kw.arg is None for kw in node.keywords)
def check_AY03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    resolver = _ScopedImportResolver(
        tree, default_modules=_ASYNCIO_DEFAULT_MODULES)
    for node in _iter_call_nodes(tree):
        if (_ay_asyncio_member(resolver.resolve(node), ("gather",))
                and _ay03_exceptions_discarded(node)):
            issues.append(_ay_finding(
                "AY-03", node,
                "asyncio.gather()未设return_exceptions(异常可能被静默吞噬)",
                _AY03_SUGGESTION, filepath))
    return issues
_AY05_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _ay05_node_in_definition_sites(
        node: ast.AST, owner: ast.AST,
        annotations_evaluated: bool) -> bool:
    sites = (iter_def_site_nodes(owner) if annotations_evaluated
             else definition_time_exprs(owner))
    return any(candidate is node
               for site in sites for candidate in walk_nodes(site))
def _ay05_exec_scope(node: Any, parent_map: dict,
                     annotations_evaluated: bool) -> Any:
    owner = node
    child = None
    while owner is not None:
        nxt = parent_map.get(owner)
        if isinstance(owner, _AY05_SCOPE_NODES):
            body = owner.body
            in_body = (any(child is statement for statement in body)
                       if isinstance(body, list) else child is body)
            if in_body:
                return owner
            if not _ay05_node_in_definition_sites(
                    node, owner, annotations_evaluated):
                return None
        child, owner = owner, nxt
    return owner
def check_AY05(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    _parent_map = _shared_parent_map(tree)
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    resolver = _ScopedImportResolver(
        tree, default_modules=_ASYNCIO_DEFAULT_MODULES)
    for node in _iter_call_nodes(tree):
        if _ay_asyncio_member(resolver.resolve(node), ("run",)):
            owner = _ay05_exec_scope(
                node, _parent_map, annotations_evaluated)
            if isinstance(owner, ast.AsyncFunctionDef):
                issues.append(_ay_finding(
                    "AY-05", node, "asyncio.run()在async函数内调用(会崩溃)",
                    _AY05_SUGGESTION, filepath))
    return issues
_AY06_EXECUTOR_CTOR_NAMES = frozenset({
    "concurrent.futures.ThreadPoolExecutor",
    "concurrent.futures.ProcessPoolExecutor",
})
_AY06_EXCEPTION_OBSERVERS = _TASK_RESULT_OBSERVERS
def _ay06_unpack_pairs(target: ast.AST,
                       value: ast.AST) -> list[tuple[Any, ast.AST]]:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(e, ast.Starred) for e in target.elts)
            and not any(isinstance(e, ast.Starred) for e in value.elts)):
        return list(zip(target.elts, value.elts, strict=True))
    return [(target, value)]
def _ay06_node_bindings(node: ast.AST) -> list[tuple[Any, ast.AST]]:
    if isinstance(node, ast.Assign):
        return [pair for target in node.targets
                for pair in _ay06_unpack_pairs(target, node.value)]
    if isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        if node.value is None:
            return []
        return _ay06_unpack_pairs(node.target, node.value)
    if not isinstance(node, (ast.With, ast.AsyncWith)):
        return []
    return [(it.optional_vars, it.context_expr)
            for it in node.items
            if it.optional_vars is not None]
_AY06_EXECUTOR_NAME_WHITELIST = frozenset({"executor", "pool", "thread_pool"})
_AY06_BINDING_NONEXECUTOR = -1
_AY06_BINDING_UNKNOWN = 0
_AY06_BINDING_EXECUTOR = 1

def _ay06_dotted_keys(expr: Any) -> set[str]:
    while isinstance(expr, ast.Subscript):
        expr = expr.value
    dotted = dotted_name(expr)
    return {dotted} if dotted else set()
class _AY06ExecutorEvidence(NamedTuple):
    resolver: _ScopedImportResolver
    by_scope: dict[ast.AST, set[str]]
    attributes: set[str]
    bindings: dict[tuple[ast.AST, str], list[tuple[tuple[int, int], int, bool]]]
_AY06_CONDITIONAL_PARENTS = (
    ast.If, ast.For, ast.AsyncFor, ast.While, ast.Try, ast.ExceptHandler,
    *((ast.TryStar,) if hasattr(ast, 'TryStar') else ()),
    *((ast.Match,) if hasattr(ast, 'Match') else ()),
)
def _ay06_binding_is_conditional(node: ast.AST, scope: ast.AST,
                                 pm: dict) -> bool:
    parent = pm.get(node)
    while parent is not None and parent is not scope:
        if isinstance(parent, _AY06_CONDITIONAL_PARENTS):
            return True
        parent = pm.get(parent)
    return False
def _ay06_collect_executor_names(
        tree: Any, resolver: _ScopedImportResolver,
        pm: dict) -> _AY06ExecutorEvidence:
    table = resolver.table
    by_scope: dict[ast.AST, set[str]] = {}
    attributes: set[str] = set()
    bindings: dict[tuple[ast.AST, str], list] = {}
    for node in walk_nodes(tree):
        for target, value in _ay06_node_bindings(node):
            is_call = isinstance(value, ast.Call)
            is_executor = (is_call and resolver.resolve(value)
                           in _AY06_EXECUTOR_CTOR_NAMES)
            scope = _binding_scope(node, table, pm)
            if scope is None:
                continue
            keys = _ay06_dotted_keys(target)
            if isinstance(target, (ast.Name, ast.Attribute)):
                position = (node.lineno, getattr(node, 'col_offset', 0) or 0)
                conditional = _ay06_binding_is_conditional(node, scope, pm)
                state = (_AY06_BINDING_NONEXECUTOR
                         if isinstance(value, ast.Constant)
                         else _AY06_BINDING_EXECUTOR if is_executor
                         else _AY06_BINDING_UNKNOWN)
                for key in keys:
                    bindings.setdefault((scope, key), []).append(
                        (position, state, conditional))
            if not is_executor:
                continue
            base = target
            while isinstance(base, ast.Subscript):
                base = base.value
            if isinstance(base, ast.Name):
                by_scope.setdefault(scope, set()).update(keys)
            else:
                attributes.update(keys)
    return _AY06ExecutorEvidence(resolver, by_scope, attributes, bindings)
def _ay06_scoped_name_is_executor(name: str, scope: ast.AST,
                                  evidence: _AY06ExecutorEvidence) -> bool:
    direct = scope
    while scope is not None:
        bound = evidence.resolver.table.bound.get(scope, frozenset())
        if (not (isinstance(scope, ast.ClassDef) and scope is not direct)
                and name in bound):
            return name in evidence.by_scope.get(scope, frozenset())
        scope = evidence.resolver.table.parent.get(scope)
    return False
def _ay06_local_binding_state(
        receiver: ast.AST, scope: ast.AST, call: ast.Call,
        evidence: _AY06ExecutorEvidence) -> int | None:
    if not isinstance(receiver, (ast.Name, ast.Attribute)):
        return None
    keys = _ay06_dotted_keys(receiver)
    if len(keys) != 1:
        return None
    entries = evidence.bindings.get((scope, next(iter(keys))), ())
    if not entries:
        return None
    call_pos = (call.lineno, getattr(call, 'col_offset', 0) or 0)
    before = [entry for entry in entries if entry[0] < call_pos]
    if not before:
        # 调用之前本作用域没有任何绑定：该名字此刻指向外层/属性绑定，本地
        # 无信息可贡献，必须返回 None（未知）交由 known_executor 裁决。
        # 不能返回 False——False == _AY06_BINDING_UNKNOWN(0)，会被调用方
        # 当成"本地已重绑为未知对象"而把已知 executor 判成非 executor。
        return None
    _position, state, conditional = max(before, key=lambda entry: entry[0])
    return None if conditional else state
def _ay06_receiver_is_executor(
        receiver: Any, evidence: _AY06ExecutorEvidence,
        scope: ast.AST, call: ast.Call) -> bool:
    if (isinstance(receiver, ast.Call)
            and evidence.resolver.resolve(receiver)
            in _AY06_EXECUTOR_CTOR_NAMES):
        return True
    base = receiver
    while isinstance(base, ast.Subscript):
        base = base.value
    known_executor = False
    if isinstance(base, ast.Name):
        known_executor = _ay06_scoped_name_is_executor(
            base.id, scope, evidence)
    keys = _ay06_dotted_keys(receiver)
    known_executor = known_executor or bool(keys & evidence.attributes)
    local_state = _ay06_local_binding_state(
        receiver, scope, call, evidence)
    if local_state == _AY06_BINDING_NONEXECUTOR:
        return False
    if local_state == _AY06_BINDING_EXECUTOR:
        return True
    if local_state == _AY06_BINDING_UNKNOWN and known_executor:
        return False
    if known_executor:
        return True
    if isinstance(base, ast.Name) and base.id in _AY06_EXECUTOR_NAME_WHITELIST:
        return True
    return any(_tail_name(key) in _AY06_EXECUTOR_NAME_WHITELIST
               for key in keys)
def _ay06_is_submit_call(
        node: ast.Call, evidence: _AY06ExecutorEvidence) -> bool:
    func = node.func
    scope = evidence.resolver.call_scopes.get(id(node))
    return (isinstance(func, ast.Attribute)
            and func.attr == "submit" and scope is not None
            and _ay06_receiver_is_executor(func.value, evidence, scope, node))
def check_AY06(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    _parent_map = _shared_parent_map(tree)
    resolver = _ScopedImportResolver(
        tree, default_modules=_CONCURRENT_DEFAULT_MODULES)
    evidence = _ay06_collect_executor_names(tree, resolver, _parent_map)
    for node in _iter_call_nodes(tree):
        if not _ay06_is_submit_call(node, evidence):
            continue
        if not _result_discarded(
                node, _parent_map,
                observing_methods=_AY06_EXCEPTION_OBSERVERS):
            continue
        issues.append(_ay_finding(
            "AY-06", node,
            "Executor.submit()结果未保存(异常被静默吞噬)",
            _AY06_SUGGESTION, filepath))
    return issues
_IT01_DEL_SUGGESTION = (
    "根因: 在迭代过程中删除元素, 导致迭代器失效或跳过元素。\n"
    "修复策略:\n"
    "1. 列表推导式过滤(首选): lst = [x for x in lst if not should_remove(x)]\n"
    "2. 收集索引后逆序删除(如需原地修改):\n"
    "   indices = [i for i, x in enumerate(lst) if should_remove(x)]\n"
    "   for i in sorted(indices, reverse=True): del lst[i]\n"
    "3. 使用dict/filter重建: lst = list(filter(predicate, lst))\n"
    "4. 遍历副本: for item in lst[:]: lst.remove(item) if condition\n"
    "参考: CWE-835 / Python FAQ Modifying List"
)
_MUTATING_METHODS = frozenset({
    'add', 'append', 'clear', 'difference_update', 'discard', 'extend',
    'insert', 'intersection_update', 'pop', 'popitem', 'remove', 'reverse',
    'setdefault', 'sort', 'symmetric_difference_update', 'update',
})
_IT01_MUTATE_SUGGESTION_HEAD = (
    "根因: for循环内修改被迭代容器会导致RuntimeError或元素跳过。"
    "该问题属于迭代安全类别。\n"
)
def _it01_mutate_suggestion(container_label: str) -> str:
    return (f"{_IT01_MUTATE_SUGGESTION_HEAD}"
            f"修复策略: 改用 for item in list({container_label}): "
            "或收集到新列表后批量操作.\n"
            "参考标准: PEP 8 / Python迭代器协议")
def _it01_chain_segments(expr: ast.AST) -> tuple[str, ...] | None:
    segs: list[str] = []
    node = expr
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        if isinstance(node, ast.Attribute):
            segs.append(node.attr)
        else:
            try:
                ast.literal_eval(node.slice)
            except (ValueError, TypeError, SyntaxError):
                return None
            segs.append(f"[{ast.unparse(node.slice)}]")
        node = node.value
    if not isinstance(node, ast.Name):
        return None
    segs.append(node.id)
    segs.reverse()
    return tuple(segs)
def _it01_same_chain(a: ast.AST, b: ast.AST) -> bool:
    sa = _it01_chain_segments(a)
    if sa is None:
        return False
    return sa == _it01_chain_segments(b)
def _it01_chain_label(expr: ast.AST) -> str:
    segs = _it01_chain_segments(expr)
    if segs is None:
        return "<expr>"
    return segs[0] + "".join(
        segment if segment.startswith("[") else f".{segment}"
        for segment in segs[1:])
def _it01_is_mutating_attr_call(stmt: ast.AST) -> bool:
    return (isinstance(stmt, ast.Call)
            and isinstance(stmt.func, ast.Attribute)
            and stmt.func.attr in _MUTATING_METHODS)
def _it01_mutating_call(stmt: ast.AST, iter_name: str) -> str | None:
    if not _it01_is_mutating_attr_call(stmt):
        return None
    receiver = stmt.func.value
    if isinstance(receiver, ast.Name) and receiver.id == iter_name:
        return stmt.func.attr
    return None
class _IT01MutationForm(NamedTuple):
    title: str
    description: str
    suggestion: str
class _IT01EmitContext(NamedTuple):
    source: Any
    filepath: Any
    emit: Any
    annotations_evaluated: bool = True
def _it01_container_mutation_form(label: str, method: str, *,
                                  root: bool = False) -> _IT01MutationForm:
    if root:
        return _IT01MutationForm(
            f"modifying iterated container root: {label}.{method}()",
            "for循环内修改被迭代容器会导致RuntimeError或元素跳过.",
            _it01_mutate_suggestion(label))
    return _IT01MutationForm(
        f"modifying iterated container: {label}.{method}()",
        (f"for循环内调用 {label}.{method}() 原地修改"
         "被迭代容器, 会导致RuntimeError、元素跳过或无限循环."),
        _it01_mutate_suggestion(label))
_IT01_AUGASSIGN_OPERATORS = {
    ast.Add: "+=", ast.Sub: "-=", ast.Mult: "*=",
    ast.BitOr: "|=", ast.BitAnd: "&=", ast.BitXor: "^=",
}
def _it01_mutating_augassign(stmt: ast.AST,
                             iter_expr: ast.AST) -> str | None:
    if not isinstance(stmt, ast.AugAssign):
        return None
    if not _it01_same_chain(stmt.target, iter_expr):
        return None
    return _IT01_AUGASSIGN_OPERATORS.get(type(stmt.op))
def _it01_augassign_form(label: str,
                         operator: str) -> _IT01MutationForm:
    return _IT01MutationForm(
        f"modifying iterated container: {label} {operator} <value>",
        (f"for循环内对被迭代容器执行 {label} {operator} ...；"
         "list/set/dict 等可变容器会原地修改，"
         "导致 RuntimeError、元素跳过或无限循环."),
        _it01_mutate_suggestion(label))
def _it01_report_mutation(ctx: _IT01EmitContext, stmt: ast.stmt,
                          for_node: ast.For | ast.AsyncFor,
                          form: _IT01MutationForm,
                          key: tuple) -> None:
    try:
        if _it01_has_following_break(stmt, for_node):
            return
    except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as _probe_exc:
        _log.debug("IT-01 break/return 探测失败(%s)，回退不豁免继续报: %s",
                   type(_probe_exc).__name__, ctx.filepath, exc_info=True)
    finding = DiagnoseFinding(
        id="IT-01", severity="P1", dimension="iteration",
        file=ctx.filepath, line=stmt.lineno, col_offset=stmt.col_offset,
        title=form.title, description=form.description,
        code_snippet=extract_code_lines(ctx.source, stmt.lineno),
        suggestion=form.suggestion,
        rule_ref="CWE-835 / Python FAQ: Modifying list while iterating")
    ctx.emit(finding, key)
_IT01_VIEW_METHODS = frozenset({"items", "keys", "values"})
_IT01_ITER_WRAPPER_ARG_INDEX: dict[str, int] = {
    "enumerate": 0, "iter": 0, "reversed": 0, "map": 1, "filter": 1,
}
_IT01_RESOLVE_MAX_DEPTH = 8
def _it01_expand_iter_source(expr: Any) -> Any:
    if not isinstance(expr, ast.Call):
        return None
    func = expr.func
    if (isinstance(func, ast.Attribute)
            and func.attr in _IT01_VIEW_METHODS
            and not expr.args and not expr.keywords):
        return func.value
    if isinstance(func, ast.Name):
        index = _IT01_ITER_WRAPPER_ARG_INDEX.get(func.id)
        if index is not None and len(expr.args) > index:
            return expr.args[index]
    return None
def _it01_resolve_chain_source(expr: Any):
    if isinstance(expr, ast.Name):
        return expr.id, None, True
    chain = _it01_chain_segments(expr)
    if chain:
        return chain[0], chain, False
    return None, None, False
def _it01_iter_source_leaves(expr: Any, depth: int = 0) -> list[Any]:
    if depth >= _IT01_RESOLVE_MAX_DEPTH:
        return [expr]
    if (isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name)
            and expr.func.id == "zip" and expr.args):
        return [leaf for arg in expr.args
                for leaf in _it01_iter_source_leaves(arg, depth + 1)]
    if (isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name)
            and expr.func.id == "map" and len(expr.args) > 2):
        return [leaf for arg in expr.args[1:]
                for leaf in _it01_iter_source_leaves(arg, depth + 1)]
    expanded = _it01_expand_iter_source(expr)
    if expanded is not None:
        return _it01_iter_source_leaves(expanded, depth + 1)
    return [expr]
def _it01_resolve_iter_sources(node) -> list[tuple[Any, Any, Any, bool]]:
    resolved = []
    for source in _it01_iter_source_leaves(node.iter):
        name, chain, is_name = _it01_resolve_chain_source(source)
        resolved.append((source, name, chain, is_name))
    return resolved
def _it01_delete_form(target, iter_name) -> _IT01MutationForm | None:
    if isinstance(target, ast.Name) and target.id == iter_name:
        return _IT01MutationForm(
            f"deleting iterated container: {iter_name}",
            ("for循环内del被迭代容器名: 名字绑定被删除，后续迭代/引用"
             "依赖迭代器持有的原对象，极易 NameError 或逻辑错乱."),
            _IT01_DEL_SUGGESTION)
    if (isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Name)
            and target.value.id == iter_name):
        return _IT01MutationForm(
            f"deleting element of iterated container: {iter_name}[...]",
            ("for循环内del被迭代容器元素(原地删除): list 会跳过元素，"
             "dict/set 改变大小会抛 RuntimeError."),
            _IT01_DEL_SUGGESTION)
    return None
def _it01_handle_delete_stmt(ctx: _IT01EmitContext, stmt,
                             for_node, iter_name) -> None:
    for target in stmt.targets:
        form = _it01_delete_form(target, iter_name)
        if form is None:
            continue
        _it01_report_mutation(ctx, stmt, for_node, form,
                              (id(stmt), id(target)))
def _it01_check_name_source(ctx: _IT01EmitContext, node,
                            iter_name, iter_expr) -> None:
    for stmt in _iter_immediate_nodes(
            list(node.body),
            annotations_evaluated=ctx.annotations_evaluated):
        if isinstance(stmt, ast.Delete):
            _it01_handle_delete_stmt(ctx, stmt, node, iter_name)
            continue
        operator = _it01_mutating_augassign(stmt, iter_expr)
        if operator is not None:
            _it01_report_mutation(
                ctx, stmt, node,
                _it01_augassign_form(iter_name, operator),
                (id(stmt), None))
            continue
        method = _it01_mutating_call(stmt, iter_name)
        if method is not None:
            _it01_report_mutation(
                ctx, stmt, node,
                _it01_container_mutation_form(iter_name, method),
                (id(stmt), None))
def _it01_chain_delete_form(target: Any,
                            iter_expr: ast.AST) -> _IT01MutationForm | None:
    if isinstance(target, ast.Subscript) and _it01_same_chain(
            target.value, iter_expr):
        label = _it01_chain_label(iter_expr)
        return _IT01MutationForm(
            f"deleting element of iterated container: {label}[...]",
            (f"for循环内del被迭代容器 {label}[...] 元素(原地删除): "
             "list 会跳过元素，dict/set 改变大小会抛 RuntimeError."),
            _IT01_DEL_SUGGESTION)
    if _it01_same_chain(target, iter_expr):
        label = _it01_chain_label(iter_expr)
        return _IT01MutationForm(
            f"deleting iterated container: {label}",
            (f"for循环内del被迭代容器属性 {label}: 只解绑属性名，"
             "迭代器仍持原对象，循环后续引用即 AttributeError."),
            _IT01_DEL_SUGGESTION)
    return None
def _it01_handle_chain_delete(ctx: _IT01EmitContext, stmt,
                              for_node, iter_expr) -> None:
    for target in stmt.targets:
        form = _it01_chain_delete_form(target, iter_expr)
        if form is None:
            continue
        _it01_report_mutation(ctx, stmt, for_node, form,
                              (id(stmt), id(target)))
def _it01_check_attr_source(ctx: _IT01EmitContext, node, iter_name,
                            iter_chain, iter_expr) -> None:
    single_level = (iter_chain is not None and len(iter_chain) == 2
                    and not iter_chain[1].startswith("["))
    for stmt in _iter_immediate_nodes(
            list(node.body),
            annotations_evaluated=ctx.annotations_evaluated):
        if isinstance(stmt, ast.Delete):
            _it01_handle_chain_delete(ctx, stmt, node, iter_expr)
            continue
        operator = _it01_mutating_augassign(stmt, iter_expr)
        if operator is not None:
            label = _it01_chain_label(iter_expr)
            _it01_report_mutation(
                ctx, stmt, node,
                _it01_augassign_form(label, operator),
                (id(stmt), None))
            continue
        if (_it01_is_mutating_attr_call(stmt)
                and _it01_same_chain(stmt.func.value, iter_expr)):
            label = _it01_chain_label(iter_expr)
            _it01_report_mutation(
                ctx, stmt, node,
                _it01_container_mutation_form(label, stmt.func.attr),
                (id(stmt), None))
            continue
        if not single_level:
            continue
        method = _it01_mutating_call(stmt, iter_name)
        if method is None:
            continue
        _it01_report_mutation(
            ctx, stmt, node,
            _it01_container_mutation_form(iter_name, method, root=True),
            (id(stmt), None))
def check_IT01(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    reported: set = set()
    def _emit_once(finding, key) -> None:
        if finding is None or key in reported:
            return
        reported.add(key)
        issues.append(finding)
    ctx = _IT01EmitContext(
        source=source, filepath=filepath, emit=_emit_once,
        annotations_evaluated=annotations_evaluated)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            continue
        for iter_expr, iter_name, iter_chain, iter_is_name in (
                _it01_resolve_iter_sources(node)):
            if not iter_name or iter_name in set(
                    iter_unpack_target_names(node.target)):
                continue
            if iter_is_name:
                _it01_check_name_source(ctx, node, iter_name, iter_expr)
            else:
                _it01_check_attr_source(ctx, node, iter_name, iter_chain,
                                        iter_expr)
    return issues
def _it01_exit_stmts_in_try(node: Any) -> list:
    stmts = [*node.body, *node.orelse, *node.finalbody]
    for handler in node.handlers:
        stmts.extend(handler.body)
    return stmts
def _it01_exit_stmts_in_block(node: Any) -> list:
    stmts = list(node.body)
    stmts.extend(getattr(node, "orelse", None) or ())
    return stmts
def _it01_exit_stmts_in_match(node: Any) -> list:
    return [stmt for case in node.cases for stmt in case.body]
_IT01_LOOP_TYPES = (ast.For, ast.AsyncFor, ast.While)
_IT01_EXIT_SCAN_HANDLERS: dict[type, Any] = {
    ast.With: _it01_exit_stmts_in_block,
    ast.AsyncWith: _it01_exit_stmts_in_block,
    ast.If: _it01_exit_stmts_in_block,
    ast.Try: _it01_exit_stmts_in_try,
}
if hasattr(ast, "TryStar"):
    _IT01_EXIT_SCAN_HANDLERS[ast.TryStar] = _it01_exit_stmts_in_try
if hasattr(ast, "Match"):
    _IT01_EXIT_SCAN_HANDLERS[ast.Match] = _it01_exit_stmts_in_match
def _it01_if_branch_label(ancestor: ast.If, child: ast.AST) -> Any:
    if any(child is stmt for stmt in ancestor.body):
        return "body"
    if any(child is stmt for stmt in ancestor.orelse):
        return "orelse"
    return None
def _it01_match_branch_label(ancestor: Any, child: ast.AST) -> Any:
    for index, case in enumerate(ancestor.cases):
        if child is case or any(child is stmt for stmt in case.body):
            return index
    return None
_IT01_TRY_TYPES = ((ast.Try, ast.TryStar) if hasattr(ast, "TryStar")
                   else (ast.Try,))
def _it01_try_handler_branch_label(ancestor: ast.AST,
                                   child: ast.AST) -> int | None:
    for index, handler in enumerate(ancestor.handlers):
        if child is handler:
            return index
    return None
def _it01_branch_label(ancestor: ast.AST, child: ast.AST) -> Any:
    if isinstance(ancestor, ast.If):
        return _it01_if_branch_label(ancestor, child)
    match_type = getattr(ast, "Match", None)
    if match_type is not None and isinstance(ancestor, match_type):
        return _it01_match_branch_label(ancestor, child)
    if isinstance(ancestor, _IT01_TRY_TYPES):
        return _it01_try_handler_branch_label(ancestor, child)
    return None
def _it01_branch_identities(node: ast.AST, root: ast.AST,
                            parents: dict) -> dict[int, Any]:
    branches: dict[int, Any] = {}
    child = node
    ancestor = parents.get(child)
    while ancestor is not None:
        label = _it01_branch_label(ancestor, child)
        if label is not None:
            branches[id(ancestor)] = label
        if ancestor is root:
            break
        child, ancestor = ancestor, parents.get(ancestor)
    return branches
def _it01_same_execution_branch(stmt: ast.AST, exit_stmt: ast.AST,
                                for_node: ast.AST, parents: dict) -> bool:
    stmt_branches = _it01_branch_identities(stmt, for_node, parents)
    exit_branches = _it01_branch_identities(exit_stmt, for_node, parents)
    return all(
        ancestor in stmt_branches and stmt_branches[ancestor] == branch
        for ancestor, branch in exit_branches.items())
def _it01_block_guarantees_exit(statements: list[ast.stmt]) -> bool:
    if not statements:
        return False
    statement = statements[-1]
    if isinstance(statement, (ast.Break, ast.Return, ast.Raise)):
        return True
    return (isinstance(statement, ast.If) and bool(statement.orelse)
            and _it01_block_guarantees_exit(statement.body)
            and _it01_block_guarantees_exit(statement.orelse))
def _it01_handlers_guarantee_exit(try_node: ast.AST) -> bool:
    for handler in try_node.handlers:
        if any(isinstance(node, ast.Continue) for node in walk_nodes(handler)):
            return False
        if not _it01_block_guarantees_exit(handler.body):
            return False
    return True
def _it01_continue_targets_loop(node: ast.Continue, for_node: ast.AST,
                                parents: dict) -> bool:
    child = node
    ancestor = parents.get(child)
    while ancestor is not None and ancestor is not for_node:
        if isinstance(ancestor, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef)):
            return False
        if (isinstance(ancestor, _IT01_LOOP_TYPES)
                and not any(child is statement
                            for statement in ancestor.orelse)):
            return False
        child, ancestor = ancestor, parents.get(ancestor)
    return ancestor is for_node
def _it01_finalbody_may_resume(try_node: ast.AST, for_node: ast.AST,
                               parents: dict) -> bool:
    return any(
        isinstance(descendant, ast.Continue)
        and _it01_continue_targets_loop(descendant, for_node, parents)
        for statement in try_node.finalbody
        for descendant in walk_nodes(statement)
    )
def _it01_exception_path_may_resume(
        exit_stmt: ast.AST, for_node: ast.AST, parents: dict) -> bool:
    child = exit_stmt
    ancestor = parents.get(child)
    while ancestor is not None:
        if isinstance(ancestor, _IT01_TRY_TYPES):
            in_finalbody = any(
                child is statement for statement in ancestor.finalbody)
            if (not in_finalbody
                    and _it01_finalbody_may_resume(
                        ancestor, for_node, parents)):
                return True
            if (ancestor.handlers
                    and (any(child is statement
                             for statement in ancestor.body)
                         or any(child is statement
                                for statement in ancestor.orelse))
                    and not _it01_handlers_guarantee_exit(ancestor)):
                return True
        if ancestor is for_node:
            break
        child, ancestor = ancestor, parents.get(ancestor)
    return False
def _it01_has_following_break(stmt: Any, for_node: Any) -> bool:
    if not hasattr(stmt, "lineno") or not hasattr(for_node, "body"):
        return False
    parents = _shared_parent_map(for_node)
    return _it01_direct_break_or_return(
        for_node.body, stmt.lineno, stmt=stmt, for_node=for_node,
        parents=parents)
def _it01_branches_overlap(first: ast.AST, second: ast.AST,
                           for_node: ast.AST, parents: dict) -> bool:
    first_branches = _it01_branch_identities(first, for_node, parents)
    second_branches = _it01_branch_identities(second, for_node, parents)
    return all(
        ancestor not in first_branches or first_branches[ancestor] == branch
        for ancestor, branch in second_branches.items())
def _it01_if_guarantees_loop_exit(node: ast.AST) -> bool:
    if not isinstance(node, ast.If) or not node.orelse:
        return False
    if not (_it01_block_guarantees_exit(node.body)
            and _it01_block_guarantees_exit(node.orelse)):
        return False
    return not any(isinstance(descendant, ast.Continue)
                   for descendant in walk_nodes(node))
def _it01_direct_break_or_return(nodes: Any, stmt_line: int, *,
                                 stmt: ast.AST,
                                 for_node: ast.AST,
                                 parents: dict) -> bool:
    events: list[tuple[ast.AST, ast.AST | None]] = []
    pending: list[tuple[Any, ast.AST | None]] = [(n, None) for n in nodes]
    stmt_loop = parents.get(stmt)
    while (stmt_loop is not None and stmt_loop is not for_node
           and not isinstance(stmt_loop, _IT01_LOOP_TYPES)):
        stmt_loop = parents.get(stmt_loop)
    if stmt_loop is for_node:
        stmt_loop = None
    while pending:
        n, owner_loop = pending.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        if _it01_if_guarantees_loop_exit(n):
            events.append((n, owner_loop))
        if isinstance(n, (ast.Break, ast.Continue, ast.Return, ast.Raise)):
            events.append((n, owner_loop))
            continue
        if isinstance(n, _IT01_LOOP_TYPES):
            pending.extend((s, owner_loop) for s in n.orelse)
            pending.extend((s, n) for s in n.body)
            continue
        expand = _IT01_EXIT_SCAN_HANDLERS.get(type(n))
        if expand is not None:
            pending.extend((s, owner_loop) for s in expand(n))
    stmt_position = (stmt_line, getattr(stmt, "col_offset", 0))
    for exit_stmt, owner_loop in events:
        if isinstance(exit_stmt, ast.If):
            if owner_loop is not stmt_loop:
                continue
            if (owner_loop is not None
                    and any(isinstance(descendant, ast.Break)
                            for descendant in walk_nodes(exit_stmt))):
                continue
        elif not isinstance(exit_stmt, (ast.Break, ast.Return, ast.Raise)):
            continue
        if owner_loop is not None and isinstance(exit_stmt, ast.Break):
            continue
        if (isinstance(exit_stmt, (ast.Return, ast.Raise))
                and owner_loop is not stmt_loop):
            continue
        exit_position = (getattr(exit_stmt, "lineno", -1),
                         getattr(exit_stmt, "col_offset", -1))
        if exit_position < stmt_position:
            continue
        if not _it01_same_execution_branch(
                stmt, exit_stmt, for_node, parents):
            continue
        if _it01_exception_path_may_resume(exit_stmt, for_node, parents):
            continue
        preempted = any(
            isinstance(other, (ast.Break, ast.Continue))
            and other_loop is stmt_loop
            and (isinstance(other, ast.Continue) or owner_loop is not None)
            and stmt_position <= (
                getattr(other, "lineno", -1),
                getattr(other, "col_offset", -1)) < exit_position
            and _it01_branches_overlap(stmt, other, for_node, parents)
            for other, other_loop in events)
        if not preempted:
            return True
    return False
def _rd_max_nesting(node: Any) -> int:
    max_depth = 0
    stack: list[tuple[Any, int]] = [(node, 0)]
    while stack:
        cur, depth = stack.pop()
        max_depth = max(max_depth, depth)
        for child in ast.iter_child_nodes(cur):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                stack.append((child, depth + 1))
            else:
                stack.append((child, depth))
    return max_depth
def _iter_outermost_functions(tree: Any):
    parents = _shared_parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        ancestor = parents.get(node)
        nested = False
        while ancestor is not None:
            if isinstance(ancestor, (ast.FunctionDef, ast.AsyncFunctionDef,
                                     ast.Lambda)):
                nested = True
                break
            ancestor = parents.get(ancestor)
        if not nested:
            yield node
def check_RD17(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    for top in _iter_outermost_functions(tree):
        nesting = _rd_max_nesting(top)
        if nesting >= 3:
            issues.append(FindingRecord(
                id="RD-17", severity="P2", dimension="maintainability",
                file=filepath, line=top.lineno,
                title=f"函数 '{top.name}' 嵌套定义深度 {nesting} 层(>=3)，认知复杂度过高",
                description="深层嵌套的函数定义使闭包状态难以追踪，内层函数无法独立"
                            "测试，认知复杂度过高（ISO/IEC 25010 可维护性）。",
                suggestion="提取嵌套函数为模块级; 使用类封装共享状态; "
                           "或使用闭包工厂模式扁平化。",
                rule_ref="ISO/IEC 25010-可维护性/Context Engineering",
            ))
    return issues
_RD04_CONST_ELEM_THRESHOLD = 5
_RD_SNIPPET_CONTEXT = 1
_RD14_HTTP_CALLS = frozenset({
    "requests.get", "requests.post", "requests.put", "requests.delete",
    "requests.patch", "requests.head", "requests.request", "requests.Session",
    "httpx.get", "httpx.post", "httpx.put", "httpx.delete", "httpx.patch",
    "httpx.head", "httpx.request", "httpx.Client", "httpx.AsyncClient",
    "urllib.request.urlopen", "socket.create_connection",
    "http.client.HTTPConnection", "http.client.HTTPSConnection",
    "aiohttp.ClientSession",
})
_RD14_MODULES = frozenset(
    _name.rsplit(".", 1)[0] for _name in _RD14_HTTP_CALLS)
def _rd14_canonical_call(name: str) -> str | None:
    if name in _RD14_HTTP_CALLS:
        return name
    head, _, tail = name.rpartition(".")
    if not head:
        return None
    for module in _RD14_MODULES:
        if head == module or head.startswith(module + "."):
            candidate = f"{module}.{tail}"
            if candidate in _RD14_HTTP_CALLS:
                return candidate
    return None
def _definition_execution_exprs(cur: ast.AST,
                                   annotations_evaluated: bool):
    if not isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
        return []
    if annotations_evaluated:
        return list(iter_def_site_nodes(cur))
    return definition_time_exprs(cur)
_EAGER_ITERABLE_CALL_NAMES = frozenset((
    'all', 'any', 'dict', 'frozenset', 'list', 'max', 'min', 'next',
    'set', 'sorted', 'sum', 'tuple',
))
def _consumed_iter_expression(node: ast.AST):
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return node.iter
    if isinstance(node, ast.YieldFrom):
        return node.value
    if isinstance(node, ast.Call):
        func = node.func
        if (isinstance(func, ast.Name)
                and func.id in _EAGER_ITERABLE_CALL_NAMES and node.args):
            return node.args[0]
    return None
def _iter_immediate_nodes(body: list[ast.stmt],
                         *,
                         annotations_evaluated: bool = True):
    stack = [(stmt, False) for stmt in body]
    while stack:
        cur, driven_generator = stack.pop()
        definition_exprs = _definition_execution_exprs(
            cur, annotations_evaluated)
        if definition_exprs:
            stack.extend((expr, False) for expr in definition_exprs)
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            continue
        yield cur
        consumed = _consumed_iter_expression(cur)
        stack.extend(
            (child, child is consumed and isinstance(child, ast.GeneratorExp))
            for child in _immediate_children(cur, driven_generator))
def _immediate_children(node: ast.AST, driven_generator: bool = False):
    if isinstance(node, ast.GeneratorExp):
        if driven_generator:
            return ast.iter_child_nodes(node)
        return (node.generators[0].iter,) if node.generators else ()
    return ast.iter_child_nodes(node)
def _loop_iteration_nodes(node: ast.stmt) -> list:
    nodes = list(node.body)
    if isinstance(node, ast.While):
        nodes.append(node.test)
    return nodes
def _rd14_scan_loop_body(
        node: ast.stmt, resolver: _ScopedImportResolver,
        annotations_evaluated: bool) -> dict[str, int]:
    hit_lines: dict[str, int] = {}
    for cur in _iter_immediate_nodes(
            _loop_iteration_nodes(node),
            annotations_evaluated=annotations_evaluated):
        if not isinstance(cur, ast.Call):
            continue
        resolved = resolver.resolve(cur)
        canonical = _rd14_canonical_call(resolved) if resolved else None
        if canonical is None:
            continue
        hit_lines[canonical] = min(
            hit_lines.get(canonical, cur.lineno), cur.lineno)
    return hit_lines
def _rd04_const_elem_count(value: ast.expr) -> int | None:
    if isinstance(value, (ast.List, ast.Set, ast.Tuple)):
        return _rd04_const_items_count(value.elts)
    if isinstance(value, ast.Dict):
        pairs = list(zip(value.keys, value.values, strict=True))
        if any(not (k is None or _rd04_is_const_item(k))
               for k, _ in pairs):
            return None
        return _rd04_const_items_count(v for _, v in pairs)
    return None
def _rd04_const_items_count(items) -> int | None:
    count = 0
    for item in items:
        if not _rd04_is_const_item(item):
            return None
        count += 1
    return count
def _rd04_is_const_item(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub))):
        return (isinstance(node.operand, ast.Constant)
                and isinstance(node.operand.value, (int, float, complex)))
    return (isinstance(node, (ast.List, ast.Set, ast.Tuple, ast.Dict))
            and _rd04_const_elem_count(node) is not None)
def _rd04_scan_loop_body(node: ast.stmt,
                           annotations_evaluated: bool) -> list:
    hits = []
    for cur in _iter_immediate_nodes(
            _loop_iteration_nodes(node),
            annotations_evaluated=annotations_evaluated):
        hits.extend(_rd04_assign_hits(cur))
    return hits
def _rd04_hit_target_names(node: ast.AST) -> list:
    if isinstance(node, ast.NamedExpr):
        return [node.target.id] if isinstance(node.target, ast.Name) else []
    if isinstance(node, ast.AnnAssign):
        return [node.target.id] if isinstance(node.target, ast.Name) else []
    if isinstance(node, ast.Assign):
        return [t.id for t in node.targets if isinstance(t, ast.Name)]
    return []
def _rd04_assign_hits(node: ast.AST) -> list:
    if not isinstance(node, (ast.NamedExpr, ast.Assign, ast.AnnAssign)):
        return []
    value = node.value
    if value is None:
        return []
    names = _rd04_hit_target_names(node)
    if not names:
        return []
    count = _rd04_const_elem_count(value)
    if count is None or count < _RD04_CONST_ELEM_THRESHOLD:
        return []
    return [(node, count, name) for name in names]
def _rd04_subscript_base(target: ast.AST) -> str | None:
    if not isinstance(target, ast.Subscript):
        return None
    value = target.value
    while isinstance(value, ast.Subscript):
        value = value.value
    if isinstance(value, ast.NamedExpr):
        value = value.target
    return value.id if isinstance(value, ast.Name) else None
def _rd04_call_recv_base(recv: ast.AST) -> str | None:
    if isinstance(recv, ast.Name):
        return recv.id
    if isinstance(recv, ast.NamedExpr) and isinstance(recv.target, ast.Name):
        return recv.target.id
    return _rd04_subscript_base(recv)
def _rd04_assign_target_names(targets: list) -> set:
    return {t.id for t in targets if isinstance(t, ast.Name)}
def _rd04_attr_base(target: ast.AST) -> str | None:
    if not isinstance(target, ast.Attribute):
        return None
    value = target.value
    while isinstance(value, (ast.Attribute, ast.Subscript)):
        value = value.value
    if isinstance(value, ast.NamedExpr):
        value = value.target
    return value.id if isinstance(value, ast.Name) else None
def _rd04_subscript_depth(target: ast.AST) -> int:
    depth = 0
    while isinstance(target, ast.Subscript):
        depth += 1
        target = target.value
    return depth
def _rd04_attribute_depth(target: ast.Attribute) -> int:
    depth = 0
    value = target.value
    while isinstance(value, (ast.Attribute, ast.Subscript)):
        if isinstance(value, ast.Subscript):
            depth += 1
        value = value.value
    return depth
def _rd04_target_write_operations(targets: list, *,
                                  subscript_strict: bool) -> set:
    operations: set = set()
    for target in targets:
        base = _rd04_subscript_base(target)
        if base is not None:
            operations.add((
                base, _rd04_subscript_depth(target), subscript_strict))
        base = _rd04_attr_base(target)
        if base is not None:
            operations.add((base, _rd04_attribute_depth(target), False))
    return operations
def _rd04_write_operations_of(node: ast.AST) -> set:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _rd04_target_write_operations(
            [node.target], subscript_strict=True)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return _rd04_target_write_operations(
            [item.optional_vars for item in node.items
             if item.optional_vars is not None], subscript_strict=True)
    if isinstance(node, ast.AugAssign):
        target = node.target
        return ({(target.id, 0, False)} if isinstance(target, ast.Name)
                else _rd04_target_write_operations(
                    [target], subscript_strict=False))
    if isinstance(node, ast.Assign):
        return _rd04_target_write_operations(
            node.targets, subscript_strict=True)
    if isinstance(node, ast.AnnAssign):
        if node.value is None:
            return set()
        return _rd04_target_write_operations(
            [node.target], subscript_strict=True)
    if isinstance(node, ast.Delete):
        return _rd04_target_write_operations(
            node.targets, subscript_strict=True)
    return set()
def _rd04_write_operations(
        loop: ast.AST, annotations_evaluated: bool) -> set:
    operations: set = set()
    for node in _iter_immediate_nodes(
            _loop_iteration_nodes(loop),
            annotations_evaluated=annotations_evaluated):
        operations |= _rd04_write_operations_of(node)
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if not (isinstance(func, ast.Attribute)
                and func.attr in _MUTATING_METHODS):
            continue
        base = _rd04_call_recv_base(func.value)
        if base is not None:
            operations.add((
                base, _rd04_subscript_depth(func.value), False))
    return operations
def _rd04_alias_distance(value: ast.AST, aliases: dict) -> int | None:
    if isinstance(value, ast.Name):
        return aliases.get(value.id)
    if isinstance(value, ast.Starred):
        return _rd04_alias_distance(value.value, aliases)
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        children = list(value.elts)
    elif isinstance(value, ast.Dict):
        children = []
        for key, item in zip(value.keys, value.values, strict=True):
            if key is not None:
                children.append(key)
            children.append(item)
    else:
        return None
    distances = []
    for child in children:
        distance = _rd04_alias_distance(child, aliases)
        if distance is not None:
            distances.append(distance + 1)
    return min(distances, default=None)
def _rd04_iter_alias_distance(expr: ast.AST, aliases: dict) -> int | None:
    if isinstance(expr, (ast.Tuple, ast.List, ast.Set)):
        distances = []
        for element in expr.elts:
            starred = isinstance(element, ast.Starred)
            value = element.value if starred else element
            distance = _rd04_alias_distance(value, aliases)
            if distance is not None:
                distances.append(distance - 1 if starred else distance)
        return min(distances, default=None)
    distance = _rd04_alias_distance(expr, aliases)
    return distance - 1 if distance is not None else None
def _admit_aliases(names, aliases: dict, distance: int) -> bool:
    grew = False
    for name in names:
        if name in aliases and aliases[name] <= distance:
            continue
        aliases[name] = distance
        grew = True
    return grew
def _rd04_mutated_via_alias(
        loop: ast.AST, hit_name: str, writers: set,
        annotations_evaluated: bool) -> bool:
    aliases = {hit_name: 0}
    max_rounds = sum(
        isinstance(node, ast.Name) for node in walk_nodes(loop)) + 1
    for _ in range(max_rounds):
        if not _spread_alias_round(
                loop, aliases, annotations_evaluated):
            break
    for name, depth, strict in writers:
        if name not in aliases:
            continue
        distance = aliases[name]
        if (depth > distance if strict else depth >= distance):
            return True
    return False
def _spread_alias_round(
        loop: ast.AST, aliases: dict, annotations_evaluated: bool) -> bool:
    grew = False
    for n in _iter_immediate_nodes(
            _loop_iteration_nodes(loop),
            annotations_evaluated=annotations_evaluated):
        if isinstance(n, ast.Assign):
            grew |= _spread_assign_aliases(n, aliases)
            continue
        if isinstance(n, ast.AnnAssign):
            grew |= _spread_annassign_aliases(n, aliases)
            continue
        if isinstance(n, (ast.For, ast.AsyncFor)):
            distance = _rd04_iter_alias_distance(n.iter, aliases)
            if distance is not None:
                grew |= _admit_aliases(
                    list(iter_unpack_target_names(n.target)),
                    aliases, distance)
            continue
        if isinstance(n, ast.NamedExpr):
            grew |= _spread_namedexpr_aliases(n, aliases)
    return grew
def _spread_namedexpr_aliases(n: ast.NamedExpr, aliases: dict) -> bool:
    if not isinstance(n.target, ast.Name):
        return False
    distance = _rd04_alias_distance(n.value, aliases)
    return (False if distance is None else _admit_aliases(
        {n.target.id}, aliases, distance))
def _spread_assign_aliases(n: ast.Assign, aliases: dict) -> bool:
    single_unpack = (len(n.targets) == 1
                     and isinstance(n.targets[0], (ast.Tuple, ast.List)))
    if n.targets and not single_unpack:
        distance = _rd04_alias_distance(n.value, aliases)
        return (False if distance is None else _admit_aliases(
            _rd04_assign_target_names(n.targets), aliases, distance))
    return _spread_unpack_aliases(n, aliases)
def _spread_annassign_aliases(n: ast.AnnAssign, aliases: dict) -> bool:
    if n.value is None:
        return False
    distance = _rd04_alias_distance(n.value, aliases)
    return (False if distance is None else _admit_aliases(
        _rd04_assign_target_names([n.target]), aliases, distance))
def _spread_unpack_aliases(n: ast.Assign, aliases: dict) -> bool:
    pairs = _unpack_pair_sides(n)
    if pairs is None:
        return False
    grew = False
    for tgt, val_elt in pairs:
        distance = _rd04_alias_distance(val_elt, aliases)
        if distance is not None:
            grew |= _admit_aliases({tgt.id}, aliases, distance)
    return grew
def _is_plain_unpack_target(node: ast.AST) -> bool:
    return (isinstance(node, (ast.Tuple, ast.List)) and bool(node.elts)
            and all(isinstance(e, ast.Name) for e in node.elts))
def _is_plain_unpack_value(node: ast.AST, width: int) -> bool:
    return (isinstance(node, (ast.Tuple, ast.List))
            and len(node.elts) == width
            and not any(isinstance(e, ast.Starred) for e in node.elts))
def _unpack_pair_sides(n: ast.Assign):
    if len(n.targets) != 1:
        return None
    target = n.targets[0]
    if not _is_plain_unpack_target(target):
        return None
    if not _is_plain_unpack_value(n.value, len(target.elts)):
        return None
    return list(zip(target.elts, n.value.elts, strict=True))
def _has_enclosing_loop(parents: dict, node: ast.AST) -> bool:
    child = node
    cur = parents.get(id(child))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            return False
        if isinstance(cur, (ast.For, ast.AsyncFor, ast.While)):
            if any(child is stmt for stmt in cur.orelse):
                child, cur = cur, parents.get(id(cur))
                continue
            return True
        child = cur
        cur = parents.get(id(cur))
    return False
def _iter_topmost_loops(tree: ast.Module, parents: dict) -> list:
    loops = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            continue
        if not _has_enclosing_loop(parents, node):
            loops.append(node)
    return loops
def check_RD04(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    parents = build_parent_map(tree)
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    for loop in _iter_topmost_loops(tree, parents):
        hits = _rd04_scan_loop_body(loop, annotations_evaluated)
        if not hits:
            continue
        writers = _rd04_write_operations(loop, annotations_evaluated)
        for assign, count, name in hits:
            if _rd04_mutated_via_alias(
                    loop, name, writers, annotations_evaluated):
                continue
            snippet = get_code_snippet(
                source_lines, assign.lineno, context=_RD_SNIPPET_CONTEXT)
            issues.append(FindingRecord(
                id="RD-04", severity="P3", dimension="performance",
                file=filepath, line=assign.lineno,
                title=f"循环内重复创建常量大对象 '{name}'（{count} 个常量元素）",
                description=f"变量 '{name}' 在循环体内被赋值为全常量字面量"
                            f"（{count} 个元素），每次迭代重建同一对象，"
                            f"可提升到循环外仅创建一次。",
                suggestion=f"将 '{name}' 的初始化提升到循环外；若需逐次清空，"
                           "考虑 .clear() 复用既有容器。",
                code_snippet=snippet,
                rule_ref="ISO/IEC 25010-性能效率",
            ))
    return issues
_RD14_CLIENT_CTORS = frozenset({
    "requests.Session", "httpx.Client", "httpx.AsyncClient",
    "aiohttp.ClientSession", "http.client.HTTPConnection",
    "http.client.HTTPSConnection",
})
def _rd14_finding_text(canonical: str) -> tuple[str, str]:
    if canonical in _RD14_CLIENT_CTORS:
        return (
            f"循环内重复构造网络客户端 {canonical}()（每轮新建连接池/会话）",
            (f"{canonical}() 出现在循环体内，每轮迭代新建客户端对象，"
             "连接池、TLS/会话状态随之重建，资源开销随迭代次数线性增长。"),
        )
    return (
        f"循环内网络调用 {canonical}()（O(n) 次网络往返）",
        (f"{canonical}() 出现在循环体内，随迭代次数线性放大网络往返延迟"
         "与失败面。"),
    )
def check_RD14(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    resolver = _ScopedImportResolver(tree)
    parents = build_parent_map(tree)
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    for loop in _iter_topmost_loops(tree, parents):
        hit_lines = _rd14_scan_loop_body(
            loop, resolver, annotations_evaluated)
        for canonical, line in sorted(hit_lines.items(),
                                      key=lambda item: (item[1], item[0])):
            snippet = get_code_snippet(
                source_lines, line, context=_RD_SNIPPET_CONTEXT)
            title, description = _rd14_finding_text(canonical)
            issues.append(FindingRecord(
                id="RD-14", severity="P2", dimension="performance",
                file=filepath, line=line,
                title=title,
                description=description,
                suggestion="使用批量 API/Session 复用将多次请求合并为一次；"
                           "或将连接建立提到循环外。",
                code_snippet=snippet,
                rule_ref="ISO/IEC 25010-性能效率",
            ))
    return issues
_X3_TASK_FN_NAMES = frozenset({
    "timer_task", "schedule_task", "add_timer", "create_timer_task",
    "add_scheduled_task", "register_timer",
})
_X3_ZH_HINT_WORDS: tuple[str, ...] = (
    "每天", "每日", "每周", "每月", "每小时", "定时", "定期", "周期性",
    "提醒我", "设置提醒", "创建定时任务", "循环执行", "重复执行", "每隔",
)
_X3_EN_HINT_WORDS: tuple[str, ...] = (
    "daily", "weekly", "monthly", "hourly", "every day", "every week",
    "every month", "every hour", "remind me", "set a reminder", "recurring",
    "periodic", "repeat", "repeatedly",
)
_X3_HINT_WORDS = _X3_ZH_HINT_WORDS + _X3_EN_HINT_WORDS
_X3_DYNAMIC_BOUNDARY = "\0"
_X3_SCHEDULE_KEYWORDS = frozenset({
    "schedule", "cron", "interval", "interval_seconds", "every",
})
def _joined_str_text(node: ast.JoinedStr) -> str:
    return "".join(
        part.value
        if isinstance(part, ast.Constant) and isinstance(part.value, str)
        else _X3_DYNAMIC_BOUNDARY
        for part in node.values)
def _x3_binop_frame_step(cur: ast.AST, stack: list[ast.AST],
                         parts: list[str]) -> None:
    if isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Add):
        stack.append(cur.right)
        stack.append(cur.left)
    elif isinstance(cur, ast.Constant) and isinstance(cur.value, str):
        parts.append(cur.value)
    elif isinstance(cur, ast.JoinedStr):
        parts.append(_joined_str_text(cur))
    else:
        parts.append(_X3_DYNAMIC_BOUNDARY)
def _x3_prompt_text(value_node: ast.AST) -> str | None:
    if isinstance(value_node, ast.Constant) and isinstance(value_node.value, str):
        return value_node.value
    if isinstance(value_node, ast.JoinedStr):
        return _joined_str_text(value_node)
    if isinstance(value_node, ast.BinOp) and isinstance(value_node.op, ast.Add):
        return "".join(drain_frame_stack(value_node, _x3_binop_frame_step))
    return None
def _x3_hit_words_of(text: str) -> list[str]:
    folded = text.casefold()
    zh_text = text.replace(_X3_DYNAMIC_BOUNDARY, "")
    zh_hits = [word for word in _X3_ZH_HINT_WORDS if word in zh_text]
    en_hits = [word for word in _X3_EN_HINT_WORDS
               if re.search(r"(?<![A-Za-z])" + re.escape(word)
                            + r"(?![A-Za-z])", folded)]
    return zh_hits + en_hits
def _x3_keyword_prompt_text(node: ast.Call) -> tuple[bool, str | None]:
    for kw in node.keywords:
        if kw.arg == "prompt":
            return True, _x3_prompt_text(kw.value)
    return False, None
_X3_POSITIONAL_PROMPT_INDEX = {"timer_task": 2}
def _x3_positional_prompt_texts(node: ast.Call, fn_name: str) -> list[str]:
    fixed_index = _X3_POSITIONAL_PROMPT_INDEX.get(fn_name)
    if fn_name == "timer_task" and len(node.args) >= 4:
        fixed_index = 3
    if fixed_index is not None:
        candidates = ([node.args[fixed_index]]
                      if len(node.args) > fixed_index else [])
    elif node.args:
        candidates = [node.args[0]]
        if len(node.args) > 1:
            candidates.append(node.args[-1])
    else:
        candidates = []
    out: list[str] = []
    for _c in candidates:
        _pt = _x3_prompt_text(_c)
        if _pt is not None:
            out.append(_pt)
    return out
def _x3_hit_words(node: ast.Call, fn_name: str) -> list[str]:
    _has_kw, _pt = _x3_keyword_prompt_text(node)
    if _has_kw:
        return _x3_hit_words_of(_pt) if _pt is not None else []
    _hit_set: set[str] = set()
    for _text in _x3_positional_prompt_texts(node, fn_name):
        _hit_set.update(_x3_hit_words_of(_text))
    return [w for w in _X3_HINT_WORDS if w in _hit_set]
def _x3_scan_task_calls(tree: ast.AST):
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        fn_name = call_tail_name(node)
        named_task = fn_name in _X3_TASK_FN_NAMES
        semantic_task = (
            _x3_keyword_prompt_text(node)[0]
            and any(kw.arg in _X3_SCHEDULE_KEYWORDS for kw in node.keywords))
        if named_task or semantic_task:
            yield node, fn_name
def check_X3(tree: ast.AST | None, source_lines: list[str],
             filepath: str) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node, fn_name in _x3_scan_task_calls(tree):
        hit_words = _x3_hit_words(node, fn_name)
        if not hit_words:
            continue
        issues.append(_x3_make_issue(node, fn_name, hit_words,
                                     source_lines, filepath))
    return issues
def _x3_make_issue(node: ast.Call, fn_name: str, hit_words: list[str],
                   source_lines: list[str], filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="X3", severity="P0", dimension="correctness",
        file=filepath, line=node.lineno,
        title=f"{fn_name} prompt 含定时暗示词（无限循环风险）",
        description=(f"{fn_name}() 的 prompt 含定时暗示词 {'/'.join(hit_words[:3])}："
                     "任务执行时 Agent 将按暗示词再次创建定时任务，"
                     "递归增殖导致无限循环；周期性应由 schedule 参数表达"),
        suggestion=("根因: 定时任务的 prompt 携带了周期性意图，违反"
                    "「prompt 必须是纯一次性任务指令」约定。该问题属于"
                    "任务契约类别。\n"
                    "修复策略: prompt 改写为一次性纯任务指令"
                    "（如「查询北京今天的天气并生成报告」），周期性由 "
                    "schedule/cron 参数表达\n"
                    "参考标准: Agent 定时任务工具契约（prompt 纯任务指令 + "
                    "schedule 表达周期）"),
        code_snippet=get_code_snippet(source_lines, node.lineno),
        rule_ref="scheduled-task infinite-loop guard",
    )
def wiring_declarations() -> dict:
    return {"catalogs": {
        "recovered_bindings": {"X3": check_X3},
        "rule_bindings": {
            "AY01": check_AY01, "AY03": check_AY03,
            "AY05": check_AY05, "AY06": check_AY06, "AY07": check_AY07,
            "IT01": check_IT01, "RD04": check_RD04,
            "RD14": check_RD14, "RD17": check_RD17,
        },
    }}

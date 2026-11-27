from __future__ import annotations  # noqa: I001
import ast
import logging
from collections import Counter
from collections.abc import Callable, Mapping
from typing import Any, NamedTuple
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    ast_name,
    attr_chain_key,
    definition_site_walrus_names,
    definition_time_exprs,
    dotted_name,
    get_call_name,
    is_none_literal,
    iter_scope_nodes,
    scope_chain,
    split_identifier,
)
from jwsgj.diag_shared_ast_views import (
    ImportFacts,
    call_scope_map,
    collect_lexical_scope_table,
    import_facts,
    iter_nodes,
    materialized_index,
    qualified_and_bare_call_targets,
    scope_node_bound_names,
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
from jwsgj.diag_types_defs import DiagnoseFinding, finding_scan_exempt
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
__all__ = [
    "check_AB01",
    "check_AY02",
    "check_CN01",
    "check_IO01",
    "check_IO03",
    "check_LK02",
    "check_LK03",
    "check_NW03",
    "check_NW04",
    "check_SE27",
    "check_TO01",
    "check_TO02",
    "check_TO03",
    "check_TO04",
    "check_TP27",
]
_log.info("diag_traps_blocking 等待与阻塞安全规则域已加载: %d 项导出", len(__all__))
_AY02_SUGGESTION = (
    "根因: 在async函数中使用了同步阻塞调用, 会阻塞事件循环影响并发性能。\n"
    "修复策略:\n"
    "1. 替换为异步等价API(首选):\n"
    "   time.sleep → await asyncio.sleep\n"
    "   requests.get → aiohttp.ClientSession.get\n"
    "   open() → aiofiles.open()\n"
    "2. 使用run_in_executor包装同步调用:\n"
    "   await loop.run_in_executor(None, blocking_func, arg)\n"
    "3. 使用anyio兼容层: await anyio.to_thread.run_sync(blocking_func)\n"
    "参考标准: asyncio文档（不要阻塞事件循环）"
)
class _AsyncRuleSpec(NamedTuple):
    rule_id: str
    severity: str
    dimension: str
    suggestion: str
    describe: Callable[[str, str, bool], str]
def _ay02_describe(_fn_name: str, callee: str, _awaited: bool) -> str:
    return f"async函数内调用同步阻塞API: {callee}"
def _ab01_describe(fn_name: str, callee: str, awaited: bool) -> str:
    suffix = ("（await 包裹不改变其同步阻塞本质，属伪异步幻觉）"
              if awaited else "")
    return (f"协程函数 {fn_name} 内同步阻塞调用 {callee}"
            f"{suffix}（事件循环被卡死）")
_AY02_SPEC = _AsyncRuleSpec("AY-02", "P1", "asyncio", _AY02_SUGGESTION,
                            _ay02_describe)
def check_AY02(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    facts = _blocking_facts(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.AsyncFunctionDef):
            continue
        issues.extend(_async_blocking_findings(
            node, filepath, _AY02_SPEC,
            facts.bare_aliases, facts.module_aliases, facts.shadowed,
            facts=facts))
    return issues
_HTTP_VERBS = frozenset({
    "get", "post", "put", "delete", "patch", "head", "options", "request",
})
_REQUESTS_API_MODULES = ("requests", "requests.api")
_LK03_SUBPROCESS_FN = frozenset({
    "run", "call", "check_call", "check_output", "Popen",
})
_LK03_NAMED_BLOCKING = frozenset({
    "time.sleep", "urllib.request.urlopen", "socket.create_connection",
    "os.system",
})
_LK03_BUILTIN_BLOCKING = frozenset({"open"})
_LK03_BLOCKING_MODULE_ROOTS = frozenset({
    *_REQUESTS_API_MODULES, "subprocess",
    *(dotted.rsplit(".", 1)[0] for dotted in _LK03_NAMED_BLOCKING),
})
def _is_blocking_dotted(dotted: str) -> bool:
    parts = dotted.split(".")
    if len(parts) >= 2:
        head, tail = parts[0], parts[-1]
        if head == "requests" and tail in _HTTP_VERBS:
            return True
        if head == "subprocess" and tail in _LK03_SUBPROCESS_FN:
            return True
    return dotted in _LK03_NAMED_BLOCKING or dotted in _LK03_BUILTIN_BLOCKING
class _ScopedValue(NamedTuple):
    lineno: int
    col: int
    branches: tuple[tuple[int, int], ...]
    value: Any
class _BlockingFacts(NamedTuple):
    facts: ImportFacts
    bare_aliases: dict[str, str]
    module_aliases: dict[str, str]
    local_binds: set[str]
    thread_mods: set[str]
    pool_binds: set[str]
    shadowed: set[str]
    lexical: Any
    call_scopes: dict[int, ast.AST]
    scoped_imports: dict[tuple[int, str], list[_ScopedValue]]
    scoped_shadows: dict[tuple[int, str], list[_ScopedValue]]
_IMPORT_BINDING_SCOPES = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.Lambda, ast.ClassDef)
_IMPORT_FUNCTION_SCOPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _import_binding_scope(node: ast.AST, parents: dict,
                          tree: ast.AST) -> ast.AST:
    cur = node
    while cur is not None:
        if isinstance(cur, _IMPORT_BINDING_SCOPES):
            return cur
        cur = parents.get(cur)
    return tree
def _source_branch_context(node: ast.AST, scope: ast.AST,
                           parents: dict) -> tuple[tuple[int, int], ...]:
    branches: list[tuple[int, int]] = []
    cur = node
    while cur is not None and cur is not scope:
        parent = parents.get(cur)
        marker = None
        if isinstance(parent, (ast.If, ast.For, ast.AsyncFor, ast.While)):
            blocks = (parent.body, parent.orelse)
        elif isinstance(parent, TRY_NODE_TYPES):
            blocks = (parent.body, parent.orelse)
            marker = next((2 + index for index, handler in enumerate(
                parent.handlers) if cur is handler), None)
        elif isinstance(parent, ast.Match):
            blocks = ()
            marker = next((index for index, case in enumerate(
                parent.cases) if cur is case), None)
        else:
            blocks = ()
        if marker is None:
            marker = next((index for index, block in enumerate(blocks)
                           if cur in block), None)
        if marker is not None:
            branches.append((id(parent), marker))
        cur = parent
    return tuple(reversed(branches))
def _possible_latest_events(events: list[_ScopedValue]) -> list[_ScopedValue]:
    ordered = sorted(events, key=lambda event: (event.lineno, event.col))
    return [event for index, event in enumerate(ordered)
            if not any(
                later.branches == event.branches[:len(later.branches)]
                for later in ordered[index + 1:])]
#: 词法作用域链节点；推导式/except 等其余词法作用域夹在调用与链节点之间。
_LEXICAL_CHAIN_SCOPES = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)
def _inner_scope_rebinds(call: ast.AST | None, name: str,
                         call_scopes: Mapping, lexical: Any) -> bool:
    """推导式/except 等词法内层作用域对 name 的重绑定是否先于外层绑定生效。"""
    if call is None or lexical is None or not name:
        return False
    scope = call_scopes.get(id(call))
    while scope is not None and not isinstance(scope, _LEXICAL_CHAIN_SCOPES):
        if name in lexical.shadow_bound.get(scope, set()):
            return True
        scope = lexical.parent.get(scope)
    return False
def _scoped_import_bindings(
        tree: ast.AST) -> dict[tuple[int, str], list[_ScopedValue]]:
    if not isinstance(tree, ast.Module):
        return {}
    parents = _shared_parent_map(tree)
    imports: dict[tuple[int, str], list[_ScopedValue]] = {}
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        scope = _import_binding_scope(node, parents, tree)
        entries: list[tuple[str, tuple[str, ...]]] = []
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.asname:
                    entries.append((alias.asname, (alias.name,)))
                    continue
                top = alias.name.split(".", 1)[0]
                paths = (top,) if alias.name == top else (top, alias.name)
                entries.append((top, paths))
        elif not node.level and node.module:
            entries.extend(
                (alias.asname or alias.name,
                 (f"{node.module}.{alias.name}",))
                for alias in node.names if alias.name != "*")
        branches = _source_branch_context(node, scope, parents)
        for local, paths in entries:
            imports.setdefault((id(scope), local), []).append(_ScopedValue(
                node.lineno, node.col_offset, branches, paths))
    return imports
def _scoped_shadow_bindings(tree: ast.AST, lexical: Any) -> dict:
    if not isinstance(tree, ast.Module) or lexical is None:
        return {}
    parents = _shared_parent_map(tree)
    bindings: dict[tuple[int, str], list[_ScopedValue]] = {}
    def _record(node: ast.AST, scope: ast.AST, names: set[str]) -> None:
        lineno = getattr(node, "lineno", None)
        if lineno is None:
            lineno = getattr(parents.get(node), "lineno", 0)
        col = getattr(node, "col_offset", None)
        if col is None:
            col = getattr(parents.get(node), "col_offset", 0)
        for name in names:
            target = scope
            while target is not None:
                if (isinstance(target, _IMPORT_BINDING_SCOPES)
                        and name in lexical.shadow_bound.get(target, set())):
                    break
                target = lexical.parent.get(target)
            if target is None:
                continue
            branches = _source_branch_context(node, target, parents)
            bindings.setdefault((id(target), name), []).append(_ScopedValue(
                lineno, col, branches, None))
    for node in tree_nodes(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            scope = _import_binding_scope(
                parents.get(node) or tree, parents, tree)
            names = definition_site_walrus_names(node, False)
            if not isinstance(node, ast.Lambda):
                names.add(node.name)
            _record(node, scope, names)
            continue
        if isinstance(node, (ast.comprehension, ast.ExceptHandler)):
            continue
        scope = _import_binding_scope(node, parents, tree)
        _record(node, scope, scope_node_bound_names(node))
    return bindings
_BLOCKING_FACTS_ATTR = "_jwsgj_blocking_facts"
def _blocking_facts(tree: ast.AST) -> _BlockingFacts:
    cached = getattr(tree, _BLOCKING_FACTS_ATTR, None)
    if isinstance(cached, _BlockingFacts):
        return cached
    facts = import_facts(tree, module_roots=_LK03_BLOCKING_MODULE_ROOTS)
    shadowed = facts.shadowed
    bare_aliases: dict[str, str] = {}
    for local, targets in facts.members.items():
        for target in targets:
            if _is_blocking_dotted(target):
                bare_aliases[local] = target
    module_aliases: dict[str, str] = {}
    for local, paths in facts.modules.items():
        for path in paths:
            if (local != path and local not in paths
                    and path in _LK03_BLOCKING_MODULE_ROOTS):
                module_aliases[local] = path
    local_binds = {local for local, targets in facts.members.items()
                   if "threading.local" in targets}
    thread_mods = {local for local, paths in facts.modules.items()
                   if local != "threading" and "threading" in paths}
    pool_binds = {local for local, targets in facts.members.items()
                  if "concurrent.futures.ThreadPoolExecutor" in targets}
    pool_binds.update(
        f"{path if local in paths else local}.ThreadPoolExecutor"
        for local, paths in facts.modules.items()
        for path in paths
        if path == "concurrent.futures")
    pool_binds.update(
        f"{local}.ThreadPoolExecutor"
        for local, targets in facts.members.items()
        if "concurrent.futures" in targets)
    lexical = (collect_lexical_scope_table(tree)
               if isinstance(tree, ast.Module) else None)
    call_scopes = call_scope_map(lexical) if lexical is not None else {}
    scoped_imports = _scoped_import_bindings(tree)
    scoped_shadows = _scoped_shadow_bindings(tree, lexical)
    built = _BlockingFacts(facts, bare_aliases, module_aliases, local_binds,
                           thread_mods, pool_binds, shadowed, lexical,
                           call_scopes, scoped_imports, scoped_shadows)
    try:
        setattr(tree, _BLOCKING_FACTS_ATTR, built)
    except AttributeError as _e:
        _log.debug("_blocking_facts 缓存挂载降级: %s", _e)
    return built
def _call_root_is_shadowed(node: ast.Call,
                           facts: _BlockingFacts) -> bool:
    root = dotted_name(node.func).partition(".")[0]
    if not root:
        return False
    if facts.lexical is None:
        return root in facts.shadowed
    scope = facts.call_scopes.get(id(node))
    if scope is None:
        return root in facts.shadowed
    direct = True
    deferred = False
    while scope is not None:
        if isinstance(scope, _IMPORT_BINDING_SCOPES):
            if not (isinstance(scope, ast.ClassDef) and not direct):
                events = [
                    *facts.scoped_imports.get((id(scope), root), ()),
                    *facts.scoped_shadows.get((id(scope), root), ()),
                ]
                if not events:
                    if root in facts.lexical.shadow_bound.get(scope, set()):
                        return True
                else:
                    prior = (list(events) if deferred else [
                        event for event in events
                        if (event.lineno, event.col) <= (
                            node.lineno, node.col_offset)])
                    if prior:
                        latest = _possible_latest_events(prior)
                        # 只有"所有可能生效的最近绑定"都是非导入重绑定时才算确定遮蔽；
                        # 条件重绑定（if/try/for 分支内赋值）与导入同为可能生效，
                        # 不能让名字变成"确定不是导入对象"，否则 TO-01/SE-27/LK-03/NW-03 漏报。
                        return bool(latest) and all(
                            event.value is None for event in latest)
                    if isinstance(scope, _IMPORT_FUNCTION_SCOPES):
                        return True
                if isinstance(scope, _IMPORT_FUNCTION_SCOPES):
                    deferred = True
            direct = False
        elif root in facts.lexical.shadow_bound.get(scope, set()):
            return True
        scope = facts.lexical.parent.get(scope)
    return False
def _visible_import_matches(node: ast.Call, facts: _BlockingFacts,
                            accepted_roots: set[str] | frozenset[str]) -> bool:
    if facts.lexical is None:
        return True
    scope = facts.call_scopes.get(id(node))
    if scope is None:
        return True
    root = dotted_name(node.func).partition(".")[0]
    direct = True
    deferred = False
    while scope is not None:
        if isinstance(scope, _IMPORT_BINDING_SCOPES):
            if not (isinstance(scope, ast.ClassDef) and not direct):
                events = facts.scoped_imports.get((id(scope), root), ())
                if events:
                    prior = (list(events) if deferred else [
                        event for event in events
                        if (event.lineno, event.col) <= (
                            node.lineno, node.col_offset)])
                    if not prior:
                        return False
                    paths = {path for event in _possible_latest_events(prior)
                             for path in event.value}
                    return any(path.partition(".")[0] in accepted_roots
                               for path in paths)
            if isinstance(scope, _IMPORT_FUNCTION_SCOPES):
                deferred = True
            direct = False
        scope = facts.lexical.parent.get(scope)
    return root in accepted_roots
def _blocking_module_alias_callee(dotted: str,
                                 module_aliases: Mapping[str, str] | None) -> str:
    if not module_aliases or "." not in dotted:
        return ""
    head, _, rest = dotted.partition(".")
    resolved_mod = module_aliases.get(head)
    if resolved_mod is None or resolved_mod == head:
        return ""
    resolved = f"{resolved_mod}.{rest}"
    return resolved if _is_blocking_dotted(resolved) else ""
def _blocking_bare_alias_callee(dotted: str,
                                bare_aliases: Mapping[str, str] | None) -> str:
    if not bare_aliases or "." in dotted:
        return ""
    return bare_aliases.get(dotted, "")
def _lk03_blocking_callee(node: ast.Call,
                          bare_aliases: Mapping[str, str] | None = None,
                          module_aliases: Mapping[str, str] | None = None,
                          shadowed: set[str] | frozenset[str] | None = None,
                          facts: _BlockingFacts | None = None,
                          ) -> str:
    dotted = dotted_name(node.func)
    if (not dotted or (facts is None and shadowed is not None
                       and dotted.partition(".")[0] in shadowed)
            or (facts is not None and _call_root_is_shadowed(node, facts))):
        return ""
    callee = ((dotted if _is_blocking_dotted(dotted) else "")
              or _blocking_module_alias_callee(dotted, module_aliases)
              or _blocking_bare_alias_callee(dotted, bare_aliases))
    if (callee and facts is not None and not _visible_import_matches(
            node, facts, {callee.partition(".")[0]})):
        return ""
    return callee
def _is_numeric_const(node: Any) -> bool:
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (int, float))
            and not isinstance(node.value, bool))
def _def_time_nodes(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.ClassDef):
        return [*node.decorator_list, *node.bases,
                *(kw.value for kw in node.keywords)]
    return definition_time_exprs(node)
_EMPTY_NAMES: frozenset[str] = frozenset()
_LOCK_NAME_SEGMENTS = frozenset({"lock", "rlock", "mutex", "semaphore"})
_LOCK_CTX_CTORS = frozenset({
    "Lock", "RLock", "Semaphore", "BoundedSemaphore", "Condition",
})
def _finding(rule_id: str, severity: str, line: int, filepath: str,
            description: str, suggestion: str,
            dimension: str = "concurrency") -> DiagnoseFinding:
    return DiagnoseFinding(
        id=rule_id, severity=severity, dimension=dimension,
        file=filepath, line=line,
        description=description, suggestion=suggestion)
def _lock_semantic_name(name: str) -> bool:
    return bool(name) and bool(
        set(split_identifier(name)) & _LOCK_NAME_SEGMENTS)
def _lock_ctor_names(
        tree: ast.AST, facts: ImportFacts,
        blocking: _BlockingFacts | None = None) -> frozenset[str]:
    aio_mods, aio_ctors = _to04_asyncio_bindings(facts)
    sync_mods = _to04_sync_module_bindings(facts)
    sync_ctors = _to04_ctor_bindings(
        facts, ("threading", "multiprocessing"), _LOCK_CTX_CTORS)
    names: set[str] = set()
    for node in tree_nodes(tree):
        for target, call in _to04_call_target_pairs(node):
            fn = call.func
            if isinstance(fn, ast.Attribute):
                if fn.attr not in _LOCK_CTX_CTORS:
                    continue
            elif isinstance(fn, ast.Name):
                if fn.id not in _LOCK_CTX_CTORS and fn.id not in sync_ctors:
                    continue
            else:
                continue
            if _is_asyncio_ctor(fn, aio_mods, aio_ctors):
                continue
            if not _ctor_confirmed(
                    fn, aio_mods, sync_mods, aio_ctors, sync_ctors):
                continue
            if (blocking is not None
                    and (_call_root_is_shadowed(call, blocking)
                         or not _visible_import_matches(
                             call, blocking, {"threading", "multiprocessing"}))):
                continue
            tn = dotted_name(target)
            if tn:
                names.add(tn)
    return frozenset(names)
def _is_acquire_expr(expr: ast.expr) -> bool:
    return (isinstance(expr, ast.Call)
            and isinstance(expr.func, ast.Attribute)
            and expr.func.attr == "acquire")
def _lock_name_of_expr(
        expr: ast.expr,
        lock_names: frozenset[str] = _EMPTY_NAMES) -> str:
    if isinstance(expr, ast.Name):
        return (expr.id
                if (_lock_semantic_name(expr.id) or expr.id in lock_names)
                else "")
    if isinstance(expr, ast.Attribute):
        dotted = dotted_name(expr)
        return (dotted
                if (_lock_semantic_name(expr.attr) or dotted in lock_names)
                else "")
    if _is_acquire_expr(expr):
        return dotted_name(expr.func.value)
    return ""
def _is_lock_context(
        expr: ast.expr,
        lock_names: frozenset[str] = _EMPTY_NAMES) -> bool:
    if _lock_name_of_expr(expr, lock_names) or _is_acquire_expr(expr):
        return True
    return isinstance(expr, ast.Call) and _lock_semantic_name(
        dotted_name(expr.func))
def _lk02_collect_sequences(
        tree: ast.AST,
        lock_names: frozenset[str] = _EMPTY_NAMES,
) -> list[tuple[tuple[str, ...], int]]:
    sequences: list[tuple[tuple[str, ...], int]] = []
    scope_types = (ast.FunctionDef, ast.AsyncFunctionDef,
                   ast.Lambda, ast.ClassDef)
    def release_one(held: tuple[str, ...], name: str) -> tuple[str, ...]:
        for index in range(len(held) - 1, -1, -1):
            if held[index] == name:
                return (*held[:index], *held[index + 1:])
        return held
    def walk_statement(
            statement: ast.stmt, held: tuple[str, ...],
            trace: list[tuple[str, ...]] | None = None,
    ) -> list[tuple[str, ...]]:
        if isinstance(statement, scope_types):
            body = getattr(statement, "body", None)
            if isinstance(body, list):
                if isinstance(statement, ast.ClassDef):
                    return walk_block(body, held, trace)
                walk_block(body)
            return [held]
        if isinstance(statement, (ast.With, ast.AsyncWith)):
            items = tuple(
                name for name in (
                    _lock_name_of_expr(item.context_expr, lock_names)
                    for item in statement.items)
                if name)
            entered = (*held, *items)
            if items:
                sequences.append((entered, statement.lineno))
                if trace is not None:
                    trace.append(entered)
            exited = []
            for end in walk_block(statement.body, entered, trace):
                for name in reversed(items):
                    end = release_one(end, name)
                exited.append(end)
            return exited
        value = (statement.value if isinstance(
            statement, (ast.Expr, ast.Assign, ast.AnnAssign, ast.Return))
            else None)
        if _is_acquire_expr(value):
            name = _lock_name_of_expr(value, lock_names)
            if name:
                acquired = (*held, name)
                sequences.append((acquired, statement.lineno))
                return [acquired]
            return [held]
        if (isinstance(value, ast.Call)
                and isinstance(value.func, ast.Attribute)
                and value.func.attr == "release"):
            return [release_one(held, dotted_name(value.func.value))]
        if isinstance(statement, ast.If):
            if _is_acquire_expr(statement.test):
                name = _lock_name_of_expr(statement.test, lock_names)
                if name:
                    acquired = (*held, name)
                    sequences.append((acquired, statement.lineno))
                    return (walk_block(statement.body, acquired, trace)
                            + walk_block(statement.orelse, held, trace))
            return (walk_block(statement.body, held, trace)
                    + walk_block(statement.orelse, held, trace))
        if isinstance(statement, TRY_NODE_TYPES):
            outcomes = []
            handler_entries = [held]
            body_outcomes = walk_block(
                statement.body, held, handler_entries)
            if trace is not None:
                trace.extend(handler_entries)
            for normal in body_outcomes:
                outcomes.extend(walk_block(statement.orelse, normal, trace))
            for handler in statement.handlers:
                for entry in dict.fromkeys(handler_entries):
                    outcomes.extend(walk_block(handler.body, entry, trace))
            if statement.finalbody:
                final = []
                for outcome in outcomes:
                    final.extend(walk_block(
                        statement.finalbody, outcome, trace))
                return final
            return outcomes
        if isinstance(statement, (ast.For, ast.AsyncFor, ast.While)):
            body_entry = held
            if isinstance(statement, ast.While) and _is_acquire_expr(statement.test):
                name = _lock_name_of_expr(statement.test, lock_names)
                if name:
                    body_entry = (*held, name)
                    sequences.append((body_entry, statement.lineno))
            loop_states = [held]
            for outcome in walk_block(statement.body, body_entry, trace):
                if outcome not in loop_states:
                    loop_states.append(outcome)
            outcomes = []
            for outcome in loop_states:
                outcomes.extend(walk_block(statement.orelse, outcome, trace))
            return list(dict.fromkeys(outcomes))
        if isinstance(statement, ast.Match):
            outcomes = [held]
            for case in statement.cases:
                for outcome in walk_block(case.body, held, trace):
                    if outcome not in outcomes:
                        outcomes.append(outcome)
            return outcomes
        for field in ("body", "orelse"):
            block = getattr(statement, field, None)
            if (isinstance(block, list) and block
                    and isinstance(block[0], ast.stmt)):
                walk_block(block, held, trace)
        for handler in getattr(statement, "handlers", ()):
            walk_block(handler.body, held, trace)
        for case in getattr(statement, "cases", ()):
            walk_block(case.body, held, trace)
        return [held]
    def walk_block(
            statements: list[ast.stmt], prefix: tuple[str, ...] = (),
            trace: list[tuple[str, ...]] | None = None,
    ) -> list[tuple[str, ...]]:
        states = [tuple(prefix)]
        for statement in statements:
            if trace is not None:
                trace.extend(states)
            following = []
            for held in states:
                following.extend(walk_statement(statement, held, trace))
            if trace is not None:
                trace.extend(following)
            states = list(dict.fromkeys(following))
        return states
    body = getattr(tree, "body", None)
    if isinstance(body, list):
        walk_block(body)
    return sequences
def _lk02_build_pairs(sequences: list[tuple[tuple[str, ...], int]]
                      ) -> tuple[Counter, dict[tuple[str, str], int]]:
    pairs: Counter = Counter()
    pair_lines: dict[tuple[str, str], int] = {}
    for seq, line in sequences:
        ordered = list(dict.fromkeys(seq))
        for i in range(len(ordered)):
            for j in range(i + 1, len(ordered)):
                key = (ordered[i], ordered[j])
                pairs[key] += 1
                pair_lines.setdefault(key, line)
    return pairs, pair_lines
def check_LK02(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    blocking = _blocking_facts(tree)
    sequences = _lk02_collect_sequences(
        tree, _lock_ctor_names(tree, blocking.facts, blocking))
    pairs, pair_lines = _lk02_build_pairs(sequences)
    reported: set[tuple[str, str]] = set()
    for (a, b) in pairs:
        if pairs.get((b, a), 0) > 0:
            canonical = tuple(sorted((a, b)))
            if canonical in reported:
                continue
            reported.add(canonical)
            issues.append(_finding(
                "LK-02", "P1", pair_lines.get((a, b), 1), filepath,
                f"多锁获取无统一顺序：{a} 与 {b} 在不同位置以相反"
                "顺序获取（死锁风险）",
                "根因: 多锁获取顺序不一致，两个线程各自持有一把锁并"
                "等待对方时形成循环等待。该问题属于并发安全类别。\n"
                "修复策略: 定义全局锁顺序常量，所有代码路径按相同顺序"
                "获取锁；或合并为单一锁/使用 with a, b: 固定顺序\n"
                "参考标准: PEP 8 / threading 文档 / Coffman 条件"))
    return issues
def _cn01_is_thread_local_ref(dotted: str, local_binds: set[str],
                              thread_mods: set[str]) -> bool:
    if dotted == "threading.local" or dotted in local_binds:
        return True
    return (dotted.endswith(".local")
            and dotted.partition(".")[0] in thread_mods)
def _cn01_thread_local_lines(tree: ast.AST, facts: _BlockingFacts):
    for node in walk_nodes(tree):
        candidates: list[ast.expr] = []
        if isinstance(node, ast.Call):
            candidates.append(node.func)
        elif isinstance(node, ast.ClassDef):
            candidates.extend(node.bases)
        for candidate in candidates:
            if isinstance(node, ast.Call) and _call_root_is_shadowed(node, facts):
                continue
            dotted = dotted_name(candidate)
            if (not dotted or (not isinstance(node, ast.Call)
                               and dotted.partition(".")[0] in facts.shadowed)):
                continue
            if _cn01_is_thread_local_ref(
                    dotted, facts.local_binds, facts.thread_mods):
                if (isinstance(node, ast.Call)
                        and not _visible_import_matches(
                            node, facts, {"threading"})):
                    continue
                yield node.lineno
                break
def _is_pool_executor_ref(dotted: str, pool_binds: set[str] | frozenset) -> bool:
    return bool(dotted) and dotted in pool_binds
def _cn01_make_finding(filepath: str, source_lines: Any,
                       line: int) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="CN-01", severity="P1", dimension="concurrency",
        file=filepath, line=line,
        description=("threading.local 与 ThreadPoolExecutor 同文件使用："
                     "worker 线程写入对提交方不可见且跨任务残留"),
        suggestion=("根因: 线程池复用 worker 线程，threading.local 的数据"
                    "生命周期与线程绑定而非与任务绑定。该问题属于并发安全类别。\n"
                    "修复策略: 用线程池 Future 的返回值传递任务数据；任务级"
                    "状态通过参数传入、结果通过返回值传出\n"
                    "参考标准: concurrent.futures 文档"),
        code_snippet=get_code_snippet(source_lines, line))
def check_CN01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    facts = _blocking_facts(tree)
    local_line = next(_cn01_thread_local_lines(tree, facts), 0)
    has_executor = False
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        dotted = dotted_name(node.func)
        if not dotted or _call_root_is_shadowed(node, facts):
            continue
        has_executor = (has_executor
                        or (_is_pool_executor_ref(dotted, facts.pool_binds)
                            and _visible_import_matches(
                                node, facts, {"concurrent"})))
    if local_line and has_executor:
        issues.append(_cn01_make_finding(filepath, source_lines, local_line))
    return issues
def _lk03_scan_root(root: ast.AST, found: list, bare_aliases,
                    module_aliases, shadowed, facts=None) -> None:
    if isinstance(root, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        for surface in _def_time_nodes(root):
            _lk03_scan_root(surface, found, bare_aliases, module_aliases,
                            shadowed, facts)
        return
    if isinstance(root, ast.ClassDef):
        for surface in [*_def_time_nodes(root), *root.body]:
            _lk03_scan_root(surface, found, bare_aliases, module_aliases,
                            shadowed, facts)
        return
    _lk03_check_call(root, found, bare_aliases, module_aliases, shadowed, facts)
    for node in iter_scope_nodes(root):
        _lk03_check_call(node, found, bare_aliases, module_aliases, shadowed,
                         facts)
        for surface in _def_time_nodes(node):
            _lk03_scan_root(surface, found, bare_aliases, module_aliases,
                            shadowed, facts)
def _lk03_check_call(node: ast.AST, found: list, bare_aliases,
                     module_aliases, shadowed, facts=None) -> None:
    if not isinstance(node, ast.Call):
        return
    callee = _lk03_blocking_callee(
        node, bare_aliases, module_aliases, shadowed, facts)
    if callee:
        found.append((callee, node.lineno))
def _lk03_scan_critical_section(w: ast.With | ast.AsyncWith,
                                bare_aliases, module_aliases, shadowed,
                                lock_names: frozenset[str] = _EMPTY_NAMES,
                                facts=None) -> list[tuple[str, int]]:
    first_lock_idx = next((idx for idx, it in enumerate(w.items)
                           if _is_lock_context(
                               it.context_expr, lock_names)), -1)
    found: list[tuple[str, int]] = []
    for idx, it in enumerate(w.items):
        if idx <= first_lock_idx:
            continue
        _lk03_scan_root(it.context_expr, found, bare_aliases, module_aliases,
                        shadowed, facts)
        if it.optional_vars is not None:
            _lk03_scan_root(it.optional_vars, found, bare_aliases,
                            module_aliases, shadowed, facts)
    for stmt in w.body:
        _lk03_scan_root(stmt, found, bare_aliases, module_aliases, shadowed,
                        facts)
    return found
def check_LK03(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    blocking = _blocking_facts(tree)
    bare_aliases, module_aliases = (blocking.bare_aliases,
                                    blocking.module_aliases)
    lock_names = _lock_ctor_names(tree, blocking.facts, blocking)
    reported: set[tuple[str, int]] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.With, ast.AsyncWith)):
            continue
        if not any(_is_lock_context(it.context_expr, lock_names)
                   for it in node.items):
            continue
        for callee, line in _lk03_scan_critical_section(
                node, bare_aliases, module_aliases, blocking.shadowed,
                lock_names, facts=blocking):
            if (callee, line) in reported:
                continue
            reported.add((callee, line))
            issues.append(_finding(
                "LK-03", "P1", line, filepath,
                f"锁临界区内执行耗时阻塞调用 {callee}()（持锁等待 IO）",
                "根因: 阻塞调用持锁等待期间，其余线程全部停在锁上，"
                "并发度塌缩为串行，一次网络抖动放大为全局停顿。\n"
                "修复策略: 耗时 IO 移出临界区（锁内取任务/快照，"
                "锁外执行 IO，再锁内写回）；确需同步等待时为调用"
                "加超时参数约束临界区时长\n参考标准: threading 文档"))
    return issues
class _TP27PoolInstances(NamedTuple):
    names: frozenset[str]
    attributes: frozenset[str]
    bindings: dict[tuple[int, str], list[_ScopedValue]]
    parents: dict
def _tp27_pool_name_visible(expr: ast.expr,
                            instances: _TP27PoolInstances) -> bool:
    name = dotted_name(expr)
    if not name:
        return False
    scopes = scope_chain(expr, instances.parents)
    if not scopes:
        return name in instances.names
    deferred = False
    for scope in scopes:
        events = instances.bindings.get((id(scope), name), ())
        if events:
            prior = (list(events) if deferred else [
                event for event in events
                if (event.lineno, event.col) <= (
                    expr.lineno, expr.col_offset)])
            if not prior and isinstance(scope, _IMPORT_FUNCTION_SCOPES):
                return False
            if prior:
                return any(event.value
                           for event in _possible_latest_events(prior))
        if isinstance(scope, _IMPORT_FUNCTION_SCOPES):
            deferred = True
    return "." in name and name in instances.attributes
def _tp27_is_pool_ctx(
        expr: ast.expr, pool_binds: frozenset[str] | set[str] = _EMPTY_NAMES,
        shadowed: frozenset[str] | set[str] = _EMPTY_NAMES,
        pool_instances: frozenset[str] | set[str] | _TP27PoolInstances = _EMPTY_NAMES,
        facts: _BlockingFacts | None = None) -> bool:
    if not isinstance(expr, ast.Call):
        if isinstance(pool_instances, _TP27PoolInstances):
            return _tp27_pool_name_visible(expr, pool_instances)
        return dotted_name(expr) in pool_instances
    dotted = dotted_name(expr.func)
    if ((facts is None and dotted.partition(".")[0] in shadowed)
            or (facts is not None and _call_root_is_shadowed(expr, facts))):
        return False
    return (_is_pool_executor_ref(dotted, pool_binds)
            and (facts is None or _visible_import_matches(
                expr, facts, {"concurrent"})))
_TP27_TIMEOUT_TAILS = frozenset({"as_completed", "result"})
def _tp27_keyword_timeout(node: ast.Call) -> ast.AST | None:
    for kw in node.keywords:
        if kw.arg == "timeout":
            return kw.value
    return None
def _tp27_positional_timeout(node: ast.Call, tail: str) -> ast.AST | None:
    pos_idx = 0 if tail == "result" else 1
    if len(node.args) <= pos_idx:
        return None
    candidate = node.args[pos_idx]
    return None if isinstance(candidate, ast.Starred) else candidate
def _tp27_timeout_line(node: ast.AST) -> int | None:
    if not isinstance(node, ast.Call):
        return None
    tail = ast_name(node.func)
    if tail not in _TP27_TIMEOUT_TAILS:
        return None
    timeout_val = _tp27_keyword_timeout(node)
    if timeout_val is None:
        timeout_val = _tp27_positional_timeout(node, tail)
    if timeout_val is None or is_none_literal(timeout_val):
        return None
    return node.lineno
def _tp27_pool_instance_names(
        tree: ast.AST, pool_binds: set[str], shadowed: set[str],
        facts: _BlockingFacts | None = None) -> _TP27PoolInstances:
    names: set[str] = set()
    attributes: set[str] = set()
    bindings: dict[tuple[int, str], list[_ScopedValue]] = {}
    parent_nodes = _shared_parent_map(tree)
    parents = {id(node): parent for node, parent in parent_nodes.items()}
    for node in tree_nodes(tree):
        calls = {id(target): call
                 for target, call in _to04_call_target_pairs(node) or ()}
        for target in _to04_rebinding_targets(node):
            name = dotted_name(target)
            if not name:
                continue
            call = calls.get(id(target))
            is_pool = (call is not None and _tp27_is_pool_ctx(
                call, pool_binds, shadowed, facts=facts))
            if is_pool:
                names.add(name)
                if "." in name:
                    attributes.add(name)
            scopes = scope_chain(node, parents)
            if scopes:
                branches = _source_branch_context(
                    node, scopes[0], parent_nodes)
                bindings.setdefault((id(scopes[0]), name), []).append(
                    _ScopedValue(node.lineno, node.col_offset,
                                 branches, is_pool))
    return _TP27PoolInstances(
        frozenset(names), frozenset(attributes), bindings, parents)
def check_TP27(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    facts = _blocking_facts(tree)
    pool_binds, shadowed = facts.pool_binds, facts.shadowed
    pool_instances = _tp27_pool_instance_names(
        tree, pool_binds, shadowed, facts)
    reported_lines: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.With):
            continue
        if not any(_tp27_is_pool_ctx(
                it.context_expr, pool_binds, shadowed, pool_instances, facts)
                   for it in node.items):
            continue
        first_hit = next((ln for sub in iter_scope_nodes(node)
                          if (ln := _tp27_timeout_line(sub)) is not None),
                         None)
        # 嵌套线程池 with 的作用域子树彼此包含：同一条 timeout 调用会被外层
        # with 再次命中，按命中行去重，保证一行只报一次（与 LK-03 口径一致）。
        if first_hit is None or first_hit in reported_lines:
            continue
        reported_lines.add(first_hit)
        issues.append(_finding(
            "TP-27", "P2", first_hit, filepath,
            "with 线程池内依赖 as_completed/result 的 timeout "
            "控制整体时长（超时形同虚设）",
            "根因: with 退出时 shutdown(wait=True) 仍会无限等待"
            "挂死线程；timeout 参数只让等待方抛 TimeoutError，"
            "线程本身不被终止，超时后主流程照样卡死在 with 出口。\n"
            "修复策略: 手动生命周期——executor = ThreadPoolExecutor()"
            " 后 try/finally，finally 中 executor.shutdown("
            "wait=False, cancel_futures=True)，配合监控线程兜底\n"
            "参考标准: concurrent.futures 文档"
            "（Executor.shutdown 与 with 退出等待语义）"))
    return issues
class _AsyncBlockingHit(NamedTuple):
    callee: str
    line: int
    awaited: bool
    node: ast.Call
class _AB01ScanContext(NamedTuple):
    found: list[_AsyncBlockingHit]
    seen: set[tuple[str, int]]
    bare_aliases: Mapping[str, str] | None
    module_aliases: Mapping[str, str] | None
    shadowed: set[str] | frozenset[str] | None
    facts: _BlockingFacts | None = None
def _ab01_iter_children(node: ast.AST, is_top: bool):
    if is_top and isinstance(node, ast.AsyncFunctionDef):
        return node.body
    return ast.iter_child_nodes(node)
def _ab01_record(node: ast.AST, parent: ast.AST | None,
                 scan: _AB01ScanContext) -> None:
    if not isinstance(node, ast.Call):
        return
    callee = _lk03_blocking_callee(node, scan.bare_aliases,
                                   scan.module_aliases, scan.shadowed,
                                   scan.facts)
    if not callee or (callee, node.lineno) in scan.seen:
        return
    scan.seen.add((callee, node.lineno))
    scan.found.append(_AsyncBlockingHit(
        callee, node.lineno, isinstance(parent, ast.Await), node))
def _ab01_visit(node: ast.AST, scan: _AB01ScanContext,
                top: bool = True) -> None:
    stack: list[tuple[ast.AST, ast.AST | None, bool]] = [(node, None, top)]
    while stack:
        n, par, is_top = stack.pop()
        if not is_top and isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                                         ast.Lambda)):
            for surface in reversed(_def_time_nodes(n)):
                stack.append((surface, par, False))
            continue
        if not is_top and isinstance(n, ast.ClassDef):
            for surface in reversed([*_def_time_nodes(n), *n.body]):
                stack.append((surface, par, False))
            continue
        _ab01_record(n, par, scan)
        for child in reversed(list(_ab01_iter_children(n, is_top))):
            stack.append((child, n, False))
def _async_blocking_hits(fn_node: ast.AsyncFunctionDef,
                         bare_aliases: Mapping[str, str] | None = None,
                         module_aliases: Mapping[str, str] | None = None,
                         shadowed: set[str] | frozenset[str] | None = None,
                         facts: _BlockingFacts | None = None,
                         ) -> list[_AsyncBlockingHit]:
    found: list[_AsyncBlockingHit] = []
    _ab01_visit(fn_node, _AB01ScanContext(
        found, set(), bare_aliases, module_aliases, shadowed, facts))
    return found
_AB01_SUGGESTION = (
    "根因: 协程内同步阻塞调用期间整个事件循环被卡死，"
    "其余协程全部停摆，并发度塌缩为串行；await 一个同步"
    "阻塞调用并不会使其变异步（AI 幻觉高发形态，如 "
    "await requests.get(url) 直接 TypeError 或假异步）。\n"
    "修复策略: time.sleep→asyncio.sleep；requests/"
    "urlopen→httpx.AsyncClient/aiohttp；无法改造的同步 "
    "IO 用 asyncio.to_thread()/run_in_executor 包裹\n"
    "参考标准: asyncio 文档（不要阻塞事件循环）")
_AB01_SPEC = _AsyncRuleSpec("AB-01", "P1", "concurrency",
                            _AB01_SUGGESTION, _ab01_describe)
def _async_blocking_findings(
        fn_node: ast.AsyncFunctionDef, filepath: Any, spec: _AsyncRuleSpec,
        bare_aliases: Mapping[str, str] | None,
        module_aliases: Mapping[str, str] | None,
        shadowed: set[str] | frozenset[str],
        facts: _BlockingFacts | None = None,
) -> list[DiagnoseFinding]:
    return [
        _finding(spec.rule_id, spec.severity, line, filepath,
                 spec.describe(fn_node.name, callee, awaited),
                 spec.suggestion, dimension=spec.dimension)
        for callee, line, awaited, _node in _async_blocking_hits(
            fn_node, bare_aliases, module_aliases, shadowed, facts)]
def check_AB01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    facts = _blocking_facts(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.AsyncFunctionDef):
            issues.extend(_async_blocking_findings(
                node, filepath, _AB01_SPEC,
                facts.bare_aliases, facts.module_aliases, facts.shadowed,
                facts=facts))
    return issues
_TO02_SUBPROCESS_VERBS = _LK03_SUBPROCESS_FN - frozenset({"Popen"})
_TO03_SLEEP_VERBS = frozenset({"sleep"})
_TIMEOUT_DIMENSION = "timeout_safety"
_TIMEOUT_RULE_FIELDS: dict[str, tuple[str, str]] = {
    "TO-01": ("P1", "timeout-requests"),
    "TO-02": ("P1", "timeout-subprocess"),
    "TO-03": ("P2", "timeout-long-sleep"),
    "TO-04": ("P2", "timeout-blocking-api"),
}
_TO_REF_STANDARD = 'PEP 8 / Bandit B501'
def _to_suggestion(root_cause: str, strategy: str) -> str:
    return (f"根因: {root_cause}。该问题属于超时处理类别。\n"
            f"修复策略: {strategy}\n"
            f"参考标准: {_TO_REF_STANDARD}")
def _timeout_issue(rule_id: str, node: ast.Call, filepath: str,
                   source_lines: Any, title: str, description: str,
                   suggestion: str) -> dict:
    severity, rule_ref = _TIMEOUT_RULE_FIELDS[rule_id]
    return {
        "rule_id": rule_id, "severity": severity,
        "dimension": _TIMEOUT_DIMENSION,
        "file": filepath, "line": node.lineno,
        "title": title,
        "description": description,
        "code_snippet": extract_code_lines(source_lines, node.lineno),
        "suggestion": suggestion,
        "rule_ref": rule_ref,
    }
def _split_canonical(target: str) -> tuple[str, str]:
    module, _, member = target.rpartition(".")
    return module, member
def _timeout_call_spec(node: ast.Call,
                       facts: ImportFacts,
                       blocking: _BlockingFacts | None = None,
                       ) -> tuple[str, tuple[str, ...]] | None:
    func = node.func
    if (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)):
        local = func.value.id
        display = f"{local}.{func.attr}"
        canonicals = tuple(
            f"{module}.{func.attr}"
            for module in facts.modules.get(local, ()))
    elif isinstance(func, ast.Attribute):
        display = dotted_name(func)
        receiver = dotted_name(func.value)
        if not display or not receiver:
            return None
        local = receiver.partition(".")[0]
        paths = facts.modules.get(local, ())
        if local in paths:
            canonicals = ((display,) if any(
                path == local or receiver == path
                or receiver.startswith(f"{path}.") for path in paths)
                          else ())
        else:
            suffix = receiver[len(local):]
            canonicals = tuple(
                f"{path}{suffix}.{func.attr}" for path in paths)
    elif isinstance(func, ast.Name):
        local = func.id
        display = local
        canonicals = facts.members.get(local, ())
    else:
        return None
    if ((blocking is None and local in facts.shadowed)
            or (blocking is not None and _call_root_is_shadowed(node, blocking))):
        return None
    return display, canonicals
def _iter_timeout_calls(tree: ast.AST | None, module_name: str,
                        verbs: frozenset):
    if tree is None:
        return
    blocking = _blocking_facts(tree)
    facts = blocking.facts
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        spec = _timeout_call_spec(node, facts, blocking)
        if spec is None:
            continue
        if not _visible_import_matches(node, blocking, {module_name}):
            continue
        display, canonicals = spec
        for canonical in canonicals:
            member_module, member = _split_canonical(canonical)
            modules = (_REQUESTS_API_MODULES if module_name == 'requests'
                       else (module_name,))
            if member in verbs and member_module in modules:
                yield node, display
                break
def _iter_missing_timeout_calls(tree: ast.AST | None, module_name: str,
                                verbs: frozenset):
    for node, display in _iter_timeout_calls(tree, module_name, verbs):
        if not _has_timeout_kwarg(node):
            yield node, display
def check_TO01(tree: ast.AST | None, source_lines: Any,
               filepath: str) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node, display in _iter_missing_timeout_calls(
            tree, 'requests', _HTTP_VERBS):
        issues.append(_timeout_issue(
            "TO-01", node, filepath, source_lines,
            f"{display}() 未设置 timeout 参数",
            (f"{display}() 未设置 timeout,可能导致无限期阻塞."
             "默认行为是永远等待响应,无网络或服务端挂起时线程永久阻塞."),
            _to_suggestion(
                '代码缺少必要的元素, 导致功能不完整或存在风险',
                '添加 timeout=30 参数.对于关键路径建议 timeout=(3.05, 30).'),
        ))
    return issues
def check_TO02(tree: ast.AST | None, source_lines: Any,
               filepath: str) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node, display in _iter_missing_timeout_calls(
            tree, 'subprocess', _TO02_SUBPROCESS_VERBS):
        issues.append(_timeout_issue(
            "TO-02", node, filepath, source_lines,
            f"{display}() 未设置 timeout 参数",
            "子进程可能无限期运行,导致调用线程永久阻塞.",
            _to_suggestion(
                '代码缺少必要的元素, 导致功能不完整或存在风险',
                '添加 timeout=300 参数（5分钟）.'),
        ))
    return issues
def check_TO03(tree: ast.AST | None, source_lines: Any,
               filepath: str) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    for node, display in _iter_timeout_calls(tree, 'time', _TO03_SLEEP_VERBS):
        if not node.args:
            continue
        arg = node.args[0]
        if _is_numeric_const(arg) and arg.value > 60:
            issues.append(_timeout_issue(
                "TO-03", node, filepath, source_lines,
                f"{display}({arg.value}) 阻塞时间过长",
                (f"{display}({arg.value}) 将阻塞线程 {arg.value} 秒."
                 "长时间 sleep 通常说明缺少事件驱动或轮询机制."),
                _to_suggestion(
                    '代码使用了不规范或有风险的实现方式',
                    '使用 threading.Event.wait(timeout) 替代长时间 sleep,允许提前唤醒.'),
            ))
    return issues
def _timeout_kwarg_set(call: ast.Call, absent) -> bool:
    explicit = [kw for kw in call.keywords if kw.arg == 'timeout']
    if explicit:
        return any(not absent(kw.value) for kw in explicit)
    return any(kw.arg is None for kw in call.keywords)
def _explicit_timeout_is_absent(call: ast.Call, absent) -> bool:
    return any(kw.arg == 'timeout' and absent(kw.value)
               for kw in call.keywords)
def _has_timeout_kwarg(call: ast.Call) -> bool:
    return _timeout_kwarg_set(call, is_none_literal)
def _is_absent_timeout_const(node: Any) -> bool:
    if is_none_literal(node):
        return True
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return _is_numeric_const(node.operand) and node.operand.value > 0
    return _is_numeric_const(node) and node.value < 0
def _has_effective_timeout_kwarg(call: ast.Call) -> bool:
    return _timeout_kwarg_set(call, _is_absent_timeout_const)
_SYNC_PRIM_CTORS = frozenset((
    "Lock", "RLock", "Event", "Queue", "Semaphore",
    "BoundedSemaphore", "Condition", "Barrier"))
def _to04_ctor_bindings(
        facts: ImportFacts, modules: tuple[str, ...],
        ctors: frozenset = _SYNC_PRIM_CTORS) -> set[str]:
    names: set[str] = set()
    for local, targets in facts.members.items():
        for target in targets:
            module, member = _split_canonical(target)
            if module in modules and member in ctors:
                names.add(local)
    return names
def _to04_asyncio_bindings(
        facts: ImportFacts) -> tuple[set[str], set[str]]:
    aio_module_names = {local for local, paths in facts.modules.items()
                        if "asyncio" in paths}
    aio_module_names.add("asyncio")
    return (aio_module_names,
            _to04_ctor_bindings(facts, ("asyncio",)))
_TO04_SYNC_MODULES = frozenset({"threading", "queue", "multiprocessing"})
def _to04_sync_module_bindings(facts: ImportFacts) -> set[str]:
    names = {local for local, paths in facts.modules.items()
             if any(path.split(".", 1)[0] in _TO04_SYNC_MODULES
                    for path in paths)}
    names.update(_TO04_SYNC_MODULES)
    return names
def _assignment_call_pairs(
        node: ast.AST) -> list[tuple[ast.expr, ast.Call]] | None:
    if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
        return [(target, node.value) for target in node.targets]
    if isinstance(node, ast.AnnAssign) and isinstance(node.value, ast.Call):
        return [(node.target, node.value)]
    return None
def _with_call_pairs(
        node: ast.AST) -> list[tuple[ast.expr | None, ast.Call]]:
    if not isinstance(node, (ast.With, ast.AsyncWith)):
        return []
    return [
        (item.optional_vars, item.context_expr)
        for item in node.items
        if item.optional_vars is not None
        and isinstance(item.context_expr, ast.Call)]
def _to04_call_target_pairs(
        node: ast.AST) -> list[tuple[ast.expr | None, ast.Call]]:
    pairs = _assignment_call_pairs(node)
    return pairs if pairs is not None else _with_call_pairs(node)
def _to04_rebinding_targets(node: ast.AST) -> list[ast.expr]:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    return []
def _ctor_confirmed(fn: ast.AST, aio_module_names: set,
                    sync_module_names: set, aio_ctor_names: set,
                    sync_ctor_names: set) -> bool:
    if isinstance(fn, ast.Attribute) and fn.attr in _SYNC_PRIM_CTORS:
        return (_is_asyncio_ctor(fn, aio_module_names, aio_ctor_names)
                or (isinstance(fn.value, ast.Name)
                    and fn.value.id in sync_module_names))
    if isinstance(fn, ast.Name):
        return fn.id in aio_ctor_names or fn.id in sync_ctor_names
    return False
def _is_asyncio_ctor(fn: ast.AST, aio_module_names: set,
                     aio_ctor_names: set) -> bool:
    if (isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name)
            and fn.value.id in aio_module_names):
        return True
    return isinstance(fn, ast.Name) and fn.id in aio_ctor_names
_TO04_FUNCTION_SCOPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_TO04_BINDING_SCOPES = (*_TO04_FUNCTION_SCOPES, ast.ClassDef, ast.Module)
def _to04_definition_scope(node: ast.AST, parents: dict,
                           tree: ast.AST) -> ast.AST:
    cur = node
    while cur is not None:
        if isinstance(cur, _TO04_BINDING_SCOPES):
            return cur
        cur = parents.get(cur)
    return tree
_TO04_SELF_BASES = frozenset({"self", "cls"})
def _to04_enclosing_class(node: ast.AST, parents: dict) -> ast.ClassDef | None:
    cur = parents.get(node)
    while cur is not None:
        if isinstance(cur, ast.ClassDef):
            return cur
        cur = parents.get(cur)
    return None
def _to04_collect_prim_bindings(tree: ast.AST, aio_module_names: set,
                                sync_module_names: set,
                                aio_ctor_names: set,
                                sync_ctor_names: set,
                                parents: dict,
                                blocking: _BlockingFacts | None = None) -> tuple[
            set[str], set[str],
            dict[tuple[int, str], list[_ScopedValue]]]:
    sync_names: set[str] = set()
    async_prim_names: set[str] = set()
    kind_events: dict[tuple[int, str], list[_ScopedValue]] = {}
    for node in tree_nodes(tree):
        calls = {id(target): call
                 for target, call in _to04_call_target_pairs(node) or ()}
        for target in _to04_rebinding_targets(node):
            tn = dotted_name(target) or None
            if tn is None:
                continue
            call = calls.get(id(target))
            is_async = (call is not None and _is_asyncio_ctor(
                call.func, aio_module_names, aio_ctor_names))
            confirmed = (
                call is not None
                and _ctor_confirmed(
                    call.func, aio_module_names, sync_module_names,
                    aio_ctor_names, sync_ctor_names)
                and not (blocking is not None
                         and _call_root_is_shadowed(call, blocking)))
            if confirmed and blocking is not None:
                confirmed = _visible_import_matches(
                    call, blocking,
                    {"asyncio"} if is_async else _TO04_SYNC_MODULES)
            if confirmed:
                kind = "async" if is_async else "sync"
                names = async_prim_names if is_async else sync_names
                names.add(tn)
            else:
                if tn not in sync_names and tn not in async_prim_names:
                    continue
                kind = "opaque"
            scope = None
            if ("." in tn
                    and tn.partition(".")[0] in _TO04_SELF_BASES):
                scope = _to04_enclosing_class(node, parents)
            if scope is None:
                scope = _to04_definition_scope(node, parents, tree)
            branches = _source_branch_context(node, scope, parents)
            kind_events.setdefault((id(scope), tn), []).append(_ScopedValue(
                node.lineno, node.col_offset, branches, kind))
    return (sync_names, async_prim_names, kind_events)
_BLOCKING_CALL_ATTRS = frozenset(("acquire", "wait", "wait_for", "get"))
_SYNC_HINTS = frozenset((
    'lock', 'rlock', 'event', 'queue', 'sem', 'semaphore',
    'cond', 'condition', 'barrier', 'mutex'))
def _name_has_sync_hint(name: str) -> bool:
    return bool(set(split_identifier(name)) & _SYNC_HINTS)
def _to04_collect_awaited_calls(tree: ast.AST) -> set[ast.Call]:
    awaited_calls: set[ast.Call] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Await) or not isinstance(node.value, ast.Call):
            continue
        if _blocking_call_receiver(node.value) is not None:
            awaited_calls.add(node.value)
    return awaited_calls
def _to04_call_covered(call: ast.Call) -> bool:
    if _has_effective_timeout_kwarg(call):
        return True
    if _timeout_by_position(call):
        return True
    return _is_nonblocking_value(_blocking_argument(call))
def _timeout_by_position(call: ast.Call) -> bool:
    pos = call.args
    if not pos:
        return False
    if call.func.attr == 'wait':
        if isinstance(pos[0], ast.Starred):
            return True
        return not _is_absent_timeout_const(pos[0])
    fixed_timeout = (len(pos) >= 2 and not any(
        isinstance(arg, ast.Starred) for arg in pos[:2]))
    if fixed_timeout:
        return not _is_absent_timeout_const(pos[1])
    return any(isinstance(arg, ast.Starred) for arg in pos)
def _blocking_argument(call: ast.Call) -> ast.AST | None:
    if call.args:
        return call.args[0]
    return next((kw.value for kw in call.keywords
                 if kw.arg in ('blocking', 'block')), None)
def _is_nonblocking_value(value: ast.AST | None) -> bool:
    if not isinstance(value, ast.Constant):
        return False
    if value.value is False:
        return True
    return (isinstance(value.value, int)
            and not isinstance(value.value, bool)
            and value.value == 0)
class _TO04Bindings(NamedTuple):
    sync_names: set[str]
    async_prim_names: set[str]
    awaited_calls: set[ast.Call]
    aio_ctor_names: set[str]
    aio_module_names: set[str]
    sync_module_names: set[str]
    sync_ctor_names: set[str]
    kind_events: dict[tuple[int, str], list[_ScopedValue]]
    parents: dict
    tree: ast.AST
    lexical: Any = None
def _to04_collect_binding_context(tree: ast.Module) -> _TO04Bindings:
    blocking = _blocking_facts(tree)
    facts = blocking.facts
    aio_module_names, aio_ctor_names = _to04_asyncio_bindings(facts)
    sync_module_names = _to04_sync_module_bindings(facts)
    sync_ctor_names = _to04_ctor_bindings(
        facts, ("threading", "queue", "multiprocessing"))
    parents = _shared_parent_map(tree)
    (sync_names, async_prim_names, kind_events) = (
        _to04_collect_prim_bindings(
            tree, aio_module_names, sync_module_names, aio_ctor_names,
            sync_ctor_names, parents, blocking))
    awaited_calls = _to04_collect_awaited_calls(tree)
    return _TO04Bindings(
        sync_names=sync_names,
        async_prim_names=async_prim_names,
        awaited_calls=awaited_calls,
        aio_ctor_names=aio_ctor_names,
        aio_module_names=aio_module_names,
        sync_module_names=sync_module_names,
        sync_ctor_names=sync_ctor_names,
        kind_events=kind_events,
        parents=parents,
        tree=tree,
        lexical=blocking.lexical,
    )
def _to04_visible_scopes(node: ast.AST, bindings: _TO04Bindings):
    cur = node
    in_function = False
    while cur is not None:
        if isinstance(cur, _TO04_FUNCTION_SCOPES):
            in_function = True
            yield cur
        elif isinstance(cur, ast.ClassDef):
            if not in_function:
                yield cur
        elif isinstance(cur, ast.Module):
            yield cur
        cur = bindings.parents.get(cur)
def _to04_kind_at(events, node: ast.AST, *,
                  deferred: bool = False) -> str:
    if not events:
        return ""
    prior = (list(events) if deferred else [
        event for event in events
        if (event.lineno, event.col) <= (node.lineno, node.col_offset)])
    if not prior:
        return ""
    kinds = {event.value for event in _possible_latest_events(prior)}
    if "sync" in kinds:
        return "sync"
    if "async" in kinds:
        return "async"
    return "opaque" if "opaque" in kinds else ""
def _to04_deferred_outer_read(node: ast.AST, scope: ast.AST,
                              bindings: _TO04Bindings) -> bool:
    cur = bindings.parents.get(node)
    while cur is not None and cur is not scope:
        if isinstance(cur, _TO04_FUNCTION_SCOPES):
            return True
        cur = bindings.parents.get(cur)
    return False
def _to04_binding_kind(recv_text: str, node: ast.Call,
                       bindings: _TO04Bindings) -> str:
    is_attribute = "." in recv_text
    if is_attribute and recv_text.partition(".")[0] in _TO04_SELF_BASES:
        cls = _to04_enclosing_class(node, bindings.parents)
        if cls is not None:
            kind = _to04_kind_at(
                bindings.kind_events.get((id(cls), recv_text)), node)
            if kind:
                return kind
    for scope in _to04_visible_scopes(node, bindings):
        events = bindings.kind_events.get((id(scope), recv_text))
        if events is not None:
            kind = _to04_kind_at(
                events, node,
                deferred=_to04_deferred_outer_read(node, scope, bindings))
            if kind:
                return kind
        if (not is_attribute and bindings.lexical is not None
                and isinstance(scope, _TO04_FUNCTION_SCOPES)
                and recv_text in bindings.lexical.bound.get(scope, ())):
            return "opaque"
    if is_attribute:
        if recv_text in bindings.async_prim_names:
            return "async"
        return "sync" if recv_text in bindings.sync_names else ""
    return ""
def _to04_should_report_call(node: ast.Call, recv_text: str,
                            bindings: _TO04Bindings) -> bool:
    kind = _to04_binding_kind(recv_text, node, bindings)
    if kind in {"async", "opaque"} or recv_text in bindings.aio_ctor_names:
        return False
    if node in bindings.awaited_calls and kind != "sync":
        return False
    if node.func.attr == 'get':
        return kind == "sync"
    return kind == "sync" or _name_has_sync_hint(recv_text)
def check_TO04(tree: ast.AST | None, source_lines: Any,
               filepath: str) -> list[dict]:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    bindings = _to04_collect_binding_context(tree)
    for node in _to04_iter_blocking_calls(tree, bindings):
        if not _to04_call_covered(node):
            issues.append(_timeout_issue(
                "TO-04", node, filepath, source_lines,
                f".{node.func.attr}() 阻塞调用未设置 timeout",
                (f"调用 .{node.func.attr}() 未设置 timeout,可能永久阻塞."
                 "如果另一方未释放锁/设置事件/放入数据,调用线程将无限等待."),
                _to_suggestion(
                    '代码缺少必要的元素, 导致功能不完整或存在风险',
                    f'添加 timeout 参数: .{node.func.attr}(timeout=30).'),
            ))
    return issues
def _blocking_call_receiver(node: ast.AST) -> str | None:
    if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
        return None
    if node.func.attr not in _BLOCKING_CALL_ATTRS:
        return None
    return dotted_name(node.func.value) or None
_TO04_TEMPORARY_BLOCKING_OPS = frozenset({
    ("Event", "wait"), ("Queue", "get"),
})
def _to04_is_temporary_sync_blocking_call(
        node: ast.Call, bindings: _TO04Bindings) -> bool:
    if (not isinstance(node.func, ast.Attribute)
            or node.func.attr not in _BLOCKING_CALL_ATTRS
            or not isinstance(node.func.value, ast.Call)):
        return False
    ctor = node.func.value
    fn = ctor.func
    blocking = _blocking_facts(bindings.tree)
    if isinstance(fn, ast.Attribute):
        members = {fn.attr}
    elif isinstance(fn, ast.Name):
        members = {_split_canonical(target)[1]
                   for target in blocking.facts.members.get(fn.id, ())}
    else:
        return False
    if (len(members) != 1
            or (next(iter(members)), node.func.attr)
            not in _TO04_TEMPORARY_BLOCKING_OPS):
        return False
    if _call_root_is_shadowed(ctor, blocking):
        return False
    return (_ctor_confirmed(
                fn, bindings.aio_module_names, bindings.sync_module_names,
                bindings.aio_ctor_names, bindings.sync_ctor_names)
            and not _is_asyncio_ctor(
                fn, bindings.aio_module_names, bindings.aio_ctor_names)
            and _visible_import_matches(
                ctor, blocking, _TO04_SYNC_MODULES))
def _to04_iter_blocking_calls(tree: ast.AST, bindings: _TO04Bindings):
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        recv_text = _blocking_call_receiver(node)
        if recv_text is None:
            if _to04_is_temporary_sync_blocking_call(node, bindings):
                yield node
            continue
        if not _to04_should_report_call(node, recv_text, bindings):
            continue
        yield node
class _HTTPTimeoutRule(NamedTuple):
    rule_id: str
    severity: str
    desc_suffix: str
    fix_action: str
    timeout_default: str
    supports_session_timeout: bool
_IO01_RULE = _HTTPTimeoutRule(
    rule_id="IO-01", severity="P1", desc_suffix="(可能永久阻塞)",
    fix_action="添加timeout参数", timeout_default="30",
    supports_session_timeout=False,
)
_IO03_RULE = _HTTPTimeoutRule(
    rule_id="IO-03", severity="P2", desc_suffix="",
    fix_action="设置timeout", timeout_default="30.0",
    supports_session_timeout=True,
)
class _HttpClientConfig(NamedTuple):
    rule: _HTTPTimeoutRule
    targets: frozenset
    session_ctors: frozenset
    module_roots: frozenset[str]
def _http_client_config(tree: Any, libraries, rule: _HTTPTimeoutRule,
                        session_ctor_specs: tuple) -> _HttpClientConfig:
    libraries = tuple(libraries)
    targets: set = set()
    for lib in libraries:
        targets |= qualified_and_bare_call_targets(tree, lib, _HTTP_VERBS)
    session_ctors: set = set()
    for lib, members in session_ctor_specs:
        session_ctors |= qualified_and_bare_call_targets(tree, lib, members)
    return _HttpClientConfig(
        rule, frozenset(targets), frozenset(session_ctors),
        frozenset(lib.partition(".")[0] for lib in libraries))
class _HttpSessionContext(NamedTuple):
    parent_map: dict
    bindings: dict
    global_bindings: dict
    is_session_ctor: Any
    ctor_timeout_set: Any
    timeout_absent: Any = is_none_literal
    lexical: Any = None
    #: 作用域级导入/遮蔽事件来源；None 时退回仅按赋值/with 绑定判定。
    facts: Any = None
    #: 以 AST 对象为键的父节点表，用于计算调用点所在分支路径。
    node_parents: Any = None
def _session_ctor_last_names(ctor_targets) -> frozenset:
    return frozenset(name.rsplit(".", 1)[-1] for name in ctor_targets)
_CALL_LAST_NAMES_ATTR = "_jwsgj_call_last_names"
def _file_call_last_names(tree: Any) -> frozenset:
    cached = getattr(tree, _CALL_LAST_NAMES_ATTR, None)
    if cached is not None:
        return cached
    names = set()
    for node in iter_nodes(tree, None):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Attribute):
            names.add(func.attr)
        elif isinstance(func, ast.Name):
            names.add(func.id)
    cached = frozenset(names)
    try:
        setattr(tree, _CALL_LAST_NAMES_ATTR, cached)
    except AttributeError as e:
        _log.debug("_file_call_last_names 缓存挂载降级: %s", e)
    return cached
def _has_session_ctor_call(tree: Any, ctor_targets) -> bool:
    return bool(_session_ctor_last_names(ctor_targets)
                & _file_call_last_names(tree))
def _session_scan_context(tree: Any, is_session_ctor: Any,
                          ctor_timeout_set: Any,
                          nodes: Any = None,
                          facts: Any = None) -> tuple[dict, dict, dict, dict]:
    node_parent_map = (_shared_parent_map(tree)
                       if tree is not None else {})
    parent_map = {id(node): parent
                  for node, parent in node_parent_map.items()}
    candidates = iter_nodes(tree, None) if nodes is None else nodes
    binding_nodes = [n for n in candidates
                     if isinstance(n, _SESSION_BINDING_NODES)]
    bindings, global_bindings = _session_collect_bindings(
        binding_nodes, parent_map, is_session_ctor, ctor_timeout_set,
        node_parent_map, facts)
    return parent_map, bindings, global_bindings, node_parent_map
def _http_session_context(tree: Any,
                          config: _HttpClientConfig) -> _HttpSessionContext | None:
    if tree is None or not config.session_ctors:
        return None
    if not _has_session_ctor_call(tree, config.session_ctors):
        return None
    facts = _blocking_facts(tree)
    shadowed = facts.shadowed
    def _is_session_ctor(value: Any) -> bool:
        return (_is_library_ctor_call(
                    value, config.session_ctors, shadowed, facts)
                and _visible_import_matches(
                    value, facts, config.module_roots))
    def _ctor_timeout_set(value: Any) -> bool:
        return (config.rule.supports_session_timeout
                and _has_timeout_kwarg(value))
    parent_map, bindings, global_bindings, node_parents = _session_scan_context(
        tree, _is_session_ctor, _ctor_timeout_set, facts=facts)
    return _HttpSessionContext(parent_map, bindings, global_bindings,
                               _is_session_ctor, _ctor_timeout_set,
                               lexical=facts.lexical, facts=facts,
                               node_parents=node_parents)
def _http_session_callee(node: ast.Call, ctx: Any) -> str | None:
    if ctx is None:
        return None
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr in _HTTP_VERBS):
        return None
    receiver = func.value
    request_timeout_absent = _explicit_timeout_is_absent(
        node, ctx.timeout_absent)
    if ctx.is_session_ctor(receiver):
        if (ctx.ctor_timeout_set(receiver)
                and not request_timeout_absent):
            return None
        return f"{get_call_name(receiver)}.{func.attr}"
    chain = attr_chain_key(receiver)
    if chain is None:
        return None
    if not _session_without_timeout(
            node, chain, ctx.parent_map, ctx.bindings, ctx.global_bindings,
            request_timeout_absent=request_timeout_absent,
            lexical=ctx.lexical, facts=ctx.facts,
            node_parents=ctx.node_parents):
        return None
    return f"{chain}.{func.attr}"
def _is_shadowed_target(func_name: str, shadowed: set[str]) -> bool:
    return bool(func_name) and func_name.partition(".")[0] in shadowed
def _is_library_ctor_call(
        value: Any, ctor_targets: frozenset, shadowed: set[str],
        facts: _BlockingFacts | None = None) -> bool:
    if not isinstance(value, ast.Call):
        return False
    call_name = get_call_name(value)
    return (call_name in ctor_targets
            and not (facts is None
                     and _is_shadowed_target(call_name, shadowed))
            and not (facts is not None
                     and _call_root_is_shadowed(value, facts)))
def _find_http_timeout_issues(
    tree: Any,
    source_lines: Any,
    filepath: Any,
    config: _HttpClientConfig,
) -> list:
    issues = []
    ctx = _http_session_context(tree, config)
    facts = _blocking_facts(tree) if tree is not None else None
    shadowed = facts.shadowed if facts is not None else set()
    for node in iter_nodes(tree, None):
        if not isinstance(node, ast.Call):
            continue
        func_name = dotted_name(node.func)
        callee = func_name if func_name in config.targets else None
        if (callee is not None
                and ((facts is None and _is_shadowed_target(callee, shadowed))
                     or (facts is not None
                         and (_call_root_is_shadowed(node, facts)
                              or not _visible_import_matches(
                                  node, facts, config.module_roots))))):
            continue
        if callee is None:
            callee = _http_session_callee(node, ctx)
        if callee is None:
            continue
        if _has_timeout_kwarg(node):
            continue
        issues.append(DiagnoseFinding(
            id=config.rule.rule_id, severity=config.rule.severity,
            dimension="io_safety",
            file=filepath, line=node.lineno,
            description=f"{callee}()未设置timeout{config.rule.desc_suffix}",
            code_snippet=extract_code_lines(source_lines, node.lineno),
            suggestion=(f"根因: {callee}()未设置timeout{config.rule.desc_suffix}。该问题属于输入输出类别。\n"
                        f"修复策略: {config.rule.fix_action}: {callee}(url, timeout={config.rule.timeout_default})\n"
                        "参考标准: PEP 8 / PEP 597 / Bandit B501"),
            rule_ref="Bandit B310/B501",
        ))
    return issues
_IO01_SESSION_CTOR_SPECS = (
    ("requests", ("Session", "session")),
    ("requests.sessions", ("Session",)),
)
_IO03_SESSION_CTOR_SPECS = (("httpx", ("Client", "AsyncClient")),)
def check_IO01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    return _find_http_timeout_issues(
        tree, source_lines, filepath,
        _http_client_config(tree, _REQUESTS_API_MODULES, _IO01_RULE,
                            _IO01_SESSION_CTOR_SPECS))
def check_IO03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    return _find_http_timeout_issues(
        tree, source_lines, filepath,
        _http_client_config(tree, ("httpx", "aiohttp"), _IO03_RULE,
                            _IO03_SESSION_CTOR_SPECS))
def _net_finding(rule_id: str, severity: str, message: str,
                 suggestion: str, node: ast.AST, source_lines: Any,
                 filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id=rule_id, severity=severity, dimension='security', file=filepath,
        line=node.lineno, message=message, suggestion=suggestion,
        code_snippet=get_code_snippet(source_lines, node.lineno))
_HTTPX_METHODS = (*_HTTP_VERBS, 'stream')
def _nw03_finding(node: ast.Call, source_lines: Any,
                  filepath: Any) -> DiagnoseFinding:
    return _net_finding(
        'NW-03', 'P2',
        'httpx 请求未设置 timeout（或显式 None），可能被恶意服务端无限阻塞',
        ('根因: 无超时的网络请求可被恶意服务端无限阻塞，导致资源耗尽 DoS。该问题属于安全类别。\n'
         '修复策略: 添加 timeout 参数：httpx.get(url, timeout=30)；'
         '需长超时时显式 httpx.Timeout(connect=10, read=300)\n'
         '参考标准: CWE-400 / Bandit B113'),
        node, source_lines, filepath)
def check_NW03(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    httpx_funcs = qualified_and_bare_call_targets(
        tree, 'httpx', _HTTPX_METHODS)
    facts = _blocking_facts(tree) if tree is not None else None
    shadowed = facts.shadowed if facts is not None else set()
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        func_name = dotted_name(node.func)
        if func_name not in httpx_funcs:
            continue
        if ((facts is None and _is_shadowed_target(func_name, shadowed))
                or (facts is not None
                    and (_call_root_is_shadowed(node, facts)
                         or not _visible_import_matches(
                             node, facts, {"httpx"})))):
            continue
        if not _has_timeout_kwarg(node):
            issues.append(_nw03_finding(node, source_lines, filepath))
    return issues
_NW04_SESSION_METHODS = (*_HTTP_VERBS, 'ws_connect')
def _is_aiohttp_absent_timeout_literal(node: Any) -> bool:
    if is_none_literal(node):
        return True
    if isinstance(node, ast.Constant) and node.value is False:
        return True
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))
            and _is_numeric_const(node.operand)):
        value = (-node.operand.value if isinstance(node.op, ast.USub)
                 else node.operand.value)
        return value <= 0
    return _is_numeric_const(node) and node.value <= 0
def _aiohttp_timeout_object_absent(
        node: Any, ctor_targets) -> bool | None:
    if (not isinstance(node, ast.Call)
            or dotted_name(node.func) not in ctor_targets):
        return None
    total = None
    has_total = False
    if node.args:
        if isinstance(node.args[0], ast.Starred):
            return False
        total = node.args[0]
        has_total = True
    for kw in node.keywords:
        if kw.arg == "total":
            total = kw.value
            has_total = True
    if has_total:
        return _is_aiohttp_absent_timeout_literal(total)
    return not any(kw.arg is None for kw in node.keywords)
def _is_aiohttp_absent_timeout_const(
        node: Any, timeout_ctor_targets=_EMPTY_NAMES) -> bool:
    object_absent = _aiohttp_timeout_object_absent(
        node, timeout_ctor_targets)
    if object_absent is not None:
        return object_absent
    return _is_aiohttp_absent_timeout_literal(node)
def _nw04_has_effective_timeout(
        call: ast.Call, timeout_ctor_targets=_EMPTY_NAMES) -> bool:
    return _timeout_kwarg_set(
        call, lambda value: _is_aiohttp_absent_timeout_const(
            value, timeout_ctor_targets))
class _SessionBinding(NamedTuple):
    lineno: int
    col: int
    is_session: bool
    timeout_set: bool
    scope: Any = None
    branches: tuple[tuple[int, int], ...] = ()
_SESSION_TARGET_TYPES = (ast.Name, ast.Attribute)
_SESSION_BINDING_NODES = (ast.Assign, ast.AnnAssign, ast.With, ast.AsyncWith)
def _enclosing_class_name(node: Any, parent_map: dict) -> str:
    cur: Any = node
    while cur is not None:
        if isinstance(cur, ast.ClassDef):
            return cur.name
        cur = parent_map.get(id(cur))
    return ""
def _session_binding_key(node: Any, chain: str, parent_map: dict) -> str:
    if "." not in chain:
        return chain
    _cls = _enclosing_class_name(node, parent_map)
    return f"{_cls}.{chain}" if _cls else chain
def _session_assignment_constructs(n: Any) -> list[tuple[Any, list]]:
    if isinstance(n, ast.Assign):
        return [(n.value, [t for t in n.targets
                           if isinstance(t, _SESSION_TARGET_TYPES)])]
    if isinstance(n, ast.AnnAssign):
        if n.value is not None and isinstance(n.target, _SESSION_TARGET_TYPES):
            return [(n.value, [n.target])]
        return []
    if isinstance(n, (ast.With, ast.AsyncWith)):
        return [(item.context_expr, [item.optional_vars]) for item in n.items
                if isinstance(item.optional_vars, _SESSION_TARGET_TYPES)]
    return []
def _session_write_scope(scope: ast.AST, name: str, lexical: Any) -> ast.AST:
    """global/nonlocal 声明的名字写入外层作用域，其余名字写入本作用域。"""
    if lexical is None or name in lexical.shadow_bound.get(scope, set()):
        return scope
    target = lexical.parent.get(scope)
    while target is not None:
        if name in lexical.shadow_bound.get(target, set()):
            return target
        target = lexical.parent.get(target)
    return scope
def _session_collect_bindings(binding_nodes, parent_map, is_session_ctor,
                              ctor_timeout_set, node_parent_map,
                              facts: Any = None):
    bindings: dict[tuple[int, str], list[_SessionBinding]] = {}
    global_bindings: dict[str, list[_SessionBinding]] = {}
    #: 每个键已由赋值/with 登记过的语句位置，避免同一语句被重复并入。
    entry_positions: dict[tuple[int, str], set[tuple[int, int]]] = {}
    lexical = getattr(facts, "lexical", None)
    for n in binding_nodes:
        for value, targets in _session_assignment_constructs(n):
            is_session = is_session_ctor(value)
            scopes = scope_chain(n, parent_map)
            scope = scopes[0] if scopes else None
            entry = _SessionBinding(
                lineno=getattr(n, "lineno", 0) or 0,
                col=getattr(n, "col_offset", 0) or 0,
                is_session=is_session,
                timeout_set=ctor_timeout_set(value) if is_session else False,
                scope=scope,
                branches=(_source_branch_context(n, scope, node_parent_map)
                          if scope is not None else ()))
            for target in targets:
                chain = attr_chain_key(target)
                if chain is None:
                    continue
                if "." in chain:
                    _key = _session_binding_key(n, chain, parent_map)
                    global_bindings.setdefault(_key, []).append(entry)
                    continue
                if scope is None:
                    global_bindings.setdefault(chain, []).append(entry)
                    continue
                write_scope = _session_write_scope(scope, chain, lexical)
                key = (id(write_scope), chain)
                scoped_entry = entry
                if write_scope is not scope:
                    scoped_entry = entry._replace(
                        branches=_source_branch_context(
                            n, write_scope, node_parent_map))
                bindings.setdefault(key, []).append(scoped_entry)
                entry_positions.setdefault(key, set()).add(
                    (entry.lineno, entry.col))
                if write_scope is not scope:
                    # global/nonlocal 写入同时保留本函数视角：函数内紧随其后的
                    # 读取按位置判定，不受模块尾部重绑定的干扰。
                    local_key = (id(scope), chain)
                    bindings.setdefault(local_key, []).append(entry)
                    entry_positions.setdefault(local_key, set()).add(
                        (entry.lineno, entry.col))
    # 赋值/with 之外的重绑定（for 目标、元组解包、walrus、import、def/class、
    # match 捕获）同样会让名字不再是会话对象：把作用域级遮蔽/导入事件按位置
    # 并入同一键，交由 _possible_latest_events 裁决。
    if facts is not None:
        declared_only = {(n.lineno, n.col_offset) for n in binding_nodes
                         if isinstance(n, ast.AnnAssign) and n.value is None}
        for table in (facts.scoped_shadows, facts.scoped_imports):
            for key, events in table.items():
                covered = entry_positions.get(key, ())
                for event in events:
                    if ((event.lineno, event.col) in covered
                            or (event.lineno, event.col) in declared_only):
                        continue
                    bindings.setdefault(key, []).append(_SessionBinding(
                        event.lineno, event.col, False, False, None,
                        event.branches))
    return bindings, global_bindings
def _session_scope_candidates(entries: Any, lineno: int, col: int,
                             call_branches: Any
                             ) -> tuple[list[_SessionBinding], bool]:
    """同一作用域内调用时的可能绑定，及其是否已由路径上的绑定确定。

    调用点分支路径上的绑定必然先于调用执行（同块按位置、嵌套块按深度），
    最深且最靠后的那条就是调用时的绑定；位于其后方的旁支重绑定仍可能执行，
    一并列为可能值。路径上没有绑定时退回“可能最新”并集。
    """
    prior = [entry for entry in entries
             if (entry.lineno, entry.col) <= (lineno, col)]
    if call_branches is not None:
        on_path = [
            entry for entry in prior
            if entry.branches == call_branches[:len(entry.branches)]]
        if on_path:
            latest = max(on_path, key=lambda entry: (
                len(entry.branches), entry.lineno, entry.col))
            return ([latest, *[
                entry for entry in prior
                if (entry.lineno, entry.col) > (latest.lineno, latest.col)]],
                    True)
    return _possible_latest_events(prior), False
def _session_prior_binding(entries: Any, lineno: int,
                            col: int, *, deferred: bool = False
                            ) -> list[_SessionBinding]:
    if deferred:
        return _possible_latest_events(list(entries))
    return _session_scope_candidates(entries, lineno, col, None)[0]
def _session_call_branches(call: Any, scope: Any,
                           node_parents: Any) -> Any:
    if call is None or node_parents is None or scope is None:
        return None
    return _source_branch_context(call, scope, node_parents)
def _session_lookup(scopes: Any, var_name: str,
                    bindings, global_bindings,
                    lineno: int, col: int,
                    lexical: Any = None, *, call: Any = None,
                    facts: Any = None, node_parents: Any = None
                    ) -> list[_SessionBinding]:
    deferred_read = any(isinstance(scope, _TO04_FUNCTION_SCOPES)
                        for scope in scopes)
    if (facts is not None and "." not in var_name and scopes
            and _inner_scope_rebinds(
                call, var_name, facts.call_scopes, lexical)):
        return []
    if "." in var_name:
        entries = global_bindings.get(var_name, ())
        current_scope = scopes[0] if scopes else None
        current_entries = [entry for entry in entries
                           if entry.scope is current_scope]
        outer_entries = [entry for entry in entries
                         if entry.scope is not current_scope]
        # 调用就在当前作用域体内：本作用域写入按位置与分支路径精确判定；
        # 其它方法/模块级写入的执行序不可判定，只能整体列为可能值。
        found, definite = _session_scope_candidates(
            current_entries, lineno, col,
            _session_call_branches(call, current_scope, node_parents))
        if definite:
            return found
        return [*found, *_session_prior_binding(
            outer_entries, lineno, col, deferred=deferred_read)]
    deferred = False
    possible: list[_SessionBinding] = []
    for scope in scopes:
        if deferred:
            found, definite = _possible_latest_events(list(
                bindings.get((id(scope), var_name), ()))), False
        else:
            found, definite = _session_scope_candidates(
                bindings.get((id(scope), var_name), ()), lineno, col,
                _session_call_branches(call, scope, node_parents))
        possible.extend(found)
        is_function = isinstance(scope, _TO04_FUNCTION_SCOPES)
        if (definite or (lexical is not None and is_function
                         and var_name in lexical.bound.get(scope, ()))):
            return possible
        if is_function:
            deferred = True
    possible.extend(_session_prior_binding(
        global_bindings.get(var_name, ()), lineno, col, deferred=deferred))
    return possible
def _session_without_timeout(node: ast.Call, chain: str, parent_map: dict,
                             bindings: dict, global_bindings: dict,
                             request_timeout_absent: bool = False,
                             lexical: Any = None, facts: Any = None,
                             node_parents: Any = None) -> bool:
    key = _session_binding_key(node, chain, parent_map)
    found = _session_lookup(scope_chain(node, parent_map), key,
                            bindings, global_bindings,
                            node.lineno, node.col_offset, lexical=lexical,
                            call=node, facts=facts, node_parents=node_parents)
    return any(entry.is_session
               and (not entry.timeout_set or request_timeout_absent)
               for entry in found)
def _session_receiver_name(node: ast.Call, methods) -> str | None:
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr in methods):
        return None
    return attr_chain_key(func.value)
def _nw04_is_missing_timeout_call(node: ast.Call,
                                  ctx: _HttpSessionContext) -> bool:
    request_timeout_absent = _explicit_timeout_is_absent(
        node, ctx.timeout_absent)
    _var = _session_receiver_name(node, _NW04_SESSION_METHODS)
    if _var is not None:
        if not _session_without_timeout(
                node, _var, ctx.parent_map, ctx.bindings, ctx.global_bindings,
                request_timeout_absent=request_timeout_absent,
                lexical=ctx.lexical, facts=ctx.facts,
                node_parents=ctx.node_parents):
            return False
        return not ctx.ctor_timeout_set(node)
    func = node.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in _NW04_SESSION_METHODS):
        return False
    return (ctx.is_session_ctor(func.value)
            and (not ctx.ctor_timeout_set(func.value)
                 or request_timeout_absent)
            and not ctx.ctor_timeout_set(node))
def _nw04_build_context(tree: Any, idx: list | None) -> _HttpSessionContext:
    nodes = (idx or ()) if tree is None else None
    ctor_targets = (qualified_and_bare_call_targets(
        tree, 'aiohttp', ('ClientSession',))
        if tree is not None else frozenset())
    timeout_ctor_targets = (qualified_and_bare_call_targets(
        tree, 'aiohttp', ('ClientTimeout',))
        if tree is not None else frozenset())
    facts = _blocking_facts(tree) if tree is not None else None
    shadowed = facts.shadowed if facts is not None else set()
    def is_session_ctor(node):
        return (_is_library_ctor_call(node, ctor_targets, shadowed, facts)
                and _visible_import_matches(node, facts, {"aiohttp"}))
    def timeout_set(node):
        return _nw04_has_effective_timeout(node, timeout_ctor_targets)
    parent_map, bindings, global_bindings, node_parents = _session_scan_context(
        tree, is_session_ctor, timeout_set, nodes, facts=facts)
    return _HttpSessionContext(
        parent_map, bindings, global_bindings, is_session_ctor,
        timeout_set,
        lambda value: _is_aiohttp_absent_timeout_const(
            value, timeout_ctor_targets),
        lexical=facts.lexical if facts is not None else None,
        facts=facts, node_parents=node_parents)
def _nw04_issue(node: ast.Call, source_lines: Any, filepath: Any) -> DiagnoseFinding:
    return _net_finding(
        'NW-04', 'P2',
        'aiohttp 会话请求未设置 timeout，默认总超时 300s 偏长，可能拖垮调用方',
        ('根因: aiohttp 默认 ClientTimeout(total=300)，长阻塞会占用连接与协程资源。该问题属于安全类别。\n'
         '修复策略: session.get(url, timeout=aiohttp.ClientTimeout(total=30))；'
         '会话级统一配置 ClientSession(timeout=ClientTimeout(total=60))\n'
         '参考标准: CWE-400 / Bandit B113'),
        node, source_lines, filepath)
def check_NW04(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _idx = materialized_index(index)
    ctx = _nw04_build_context(tree, _idx)
    for node in iter_nodes(tree, _idx):
        if not isinstance(node, ast.Call):
            continue
        if not _nw04_is_missing_timeout_call(node, ctx):
            continue
        issues.append(_nw04_issue(node, source_lines, filepath))
    return issues
def _se27_urlopen_missing_timeout(node: ast.Call) -> bool:
    if len(node.args) >= 3:
        return _is_absent_timeout_const(node.args[2])
    return not _has_timeout_kwarg(node)
_SE27_FINDING_FORMS: dict[str, tuple[str, str]] = {
    'requests': ('网络请求未设置timeout参数,可能导致资源耗尽',
                 'requests.get(url, timeout=30)'),
    'urllib': ('urllib请求未设置timeout参数,可能导致资源耗尽',
               'urlopen(url, timeout=30)'),
}
def _se27_finding(node: ast.Call, source_lines: Any, filepath: Any,
                  flavor: str) -> DiagnoseFinding:
    _message, _fix_hint = _SE27_FINDING_FORMS[flavor]
    return _net_finding(
        'SE-27', 'P2', _message,
        ('根因: 未设置超时的网络请求可被恶意服务器无限阻塞,导致DoS。该问题属于安全类别。\n'
         '修复策略: 添加timeout参数: ' + _fix_hint + '\n'
         '参考标准: CWE-400 / Bandit B113'),
        node, source_lines, filepath)
def check_SE27(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    network_funcs = {
        target
        for module in _REQUESTS_API_MODULES
        for target in qualified_and_bare_call_targets(
            tree, module, _HTTP_VERBS)
    }
    urlopen_funcs = qualified_and_bare_call_targets(
        tree, 'urllib.request', ('urlopen',))
    facts = _blocking_facts(tree) if tree is not None else None
    shadowed = facts.shadowed if facts is not None else set()
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        func_name = dotted_name(node.func)
        if ((facts is None and _is_shadowed_target(func_name, shadowed))
                or (facts is not None and _call_root_is_shadowed(node, facts))):
            continue
        if func_name in network_funcs:
            if facts is not None and not _visible_import_matches(
                    node, facts, {"requests"}):
                continue
            if not _has_timeout_kwarg(node):
                issues.append(_se27_finding(
                    node, source_lines, filepath, 'requests'))
            continue
        if (func_name in urlopen_funcs
                and (facts is None or _visible_import_matches(
                    node, facts, {"urllib"}))
                and _se27_urlopen_missing_timeout(node)):
            issues.append(_se27_finding(
                node, source_lines, filepath, 'urllib'))
    return issues
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            'AY02': check_AY02,
            'IO01': check_IO01, 'IO03': check_IO03,
            'TO01': check_TO01, 'TO02': check_TO02,
            'TO03': check_TO03, 'TO04': check_TO04,
        },
        "traps_bindings": {
            'LK02': check_LK02, 'LK03': check_LK03, 'CN01': check_CN01,
            'TP27': check_TP27, 'AB01': check_AB01,
        },
        "aicoder_direct": {
            'LK-03': check_LK03, 'TP-27': check_TP27, 'AB-01': check_AB01,
        },
        "sec_registry_fns": {
            'NW03': check_NW03, 'NW04': check_NW04,
        },
        "se_checks": {'SE27': check_SE27},
    }}

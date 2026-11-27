from __future__ import annotations

import ast
import logging
from collections.abc import Iterator
from itertools import pairwise
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    TYPE_ALIAS_NODES,
    dotted_name,
    import_alias_bound_names,
    is_docstring_stmt,
    iter_arg_nodes,
    iter_unpack_target_names,
    latest_prior,
    resolve_import_binding,
)
from jwsgj.diag_shared_ast_views import (
    OPEN_FAMILY_MODULES,
    call_head_is_shadowed,
    call_scope_map,
    collect_lexical_scope_table,
    collect_module_bindings,
    definition_time_expressions,
    iter_nodes,
    non_builtin_open_call_ids,
    open_family_aliases,
    parent_map,
    qualified_and_bare_call_targets,
    same_scope_bfs_nodes,
    scope_import_tables,
    scope_shadows_import,
    scope_shadows_name,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    extract_code_lines,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    DiagnoseIssue,
    DiagnoseSeverity,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "GATE_DETECTORS",
    "check_DC01",
    "check_DC03",
    "check_IO04",
    "check_IO05",
    "detect_b02_resource_leak",
    "detect_b03_bare_except",
    "detect_b04_finally_control_flow",
    "detect_b13_swallowed_exception",
    "detect_b25_exception_chain_lost",
    "detect_b26_missing_encoding",
    "detect_b40_raise_non_exception",
    "detect_b46_except_invalid_handler_type",
    "detect_b58_bare_raise_outside_except",
]
logger = logging.getLogger(__name__)
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ''
def _issue(check_id: str, severity: DiagnoseSeverity, message: str,
           line: int, suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(check_id=check_id, severity=severity, message=message,
                         line=line, suggestion=suggestion, auto_fixable=False)
def _finish(label: str, issues: list[DiagnoseIssue],
            filepath: str) -> list[DiagnoseIssue]:
    if issues:
        logger.debug("[GateB] %s 命中: %s x%d", label,
                     filepath or "<inline>", len(issues))
    return issues
def check_IO05(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if tree is None:
        return []
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in _b26_open_calls_missing_encoding(tree):
        issues.append(DiagnoseFinding(
            id="IO-05", severity="P1", dimension="io_safety",
            file=filepath, line=node.lineno,
            description="open()未指定encoding参数, 跨平台编码不一致风险(Windows默认gbk/Linux默认utf-8)",
            code_snippet=extract_code_lines(source_lines, node.lineno),
            suggestion="根因: 文件/字符串编码未显式指定, 可能导致跨平台乱码。该问题属于输入输出类别。\n修复策略: 显式指定 encoding='utf-8' (PEP 597): open(path, 'r', encoding='utf-8')\n参考标准: PEP 8 / PEP 597 / Bandit B501",
            rule_ref="PEP 597 / Python文档 / Unicode最佳实践"))
    return issues
_FTPLIB_SSRF_CALLS = frozenset(("ftpcp",))
def _make_io04_issue(node: ast.Call, source_lines: Any, filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="IO-04", severity="P1", dimension="io_safety",
        file=filepath, line=node.lineno,
        description=(
            "ftplib.ftpcp() 直接信任 PASV 响应中的地址作为回连目标"
            "(CVE-2026-8328/CWE-918): 恶意 FTP 服务器可把数据连接指向"
            "任意内网地址/端口，构成 SSRF 跳板"),
        code_snippet=extract_code_lines(source_lines, node.lineno),
        suggestion=(
            '根因: ftpcp() 沿用未修复的 parse227() 原始地址，'
            '升级 makepasv() 不覆盖该路径。该问题属于输入输出类别。\n'
            '修复策略: 升级到含修复的版本(3.10.21/3.11.16/3.12.14/'
            '3.13.14/3.14.6+)，只对可信 FTP 服务器使用 ftpcp()，'
            '优先改用 HTTPS 传输\n'
            '参考标准: CWE-918 / PEP 8 / Bandit B501'),
        rule_ref="CVE-2026-8328")
def check_IO04(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if tree is None or finding_scan_exempt(filepath):
        return []
    issues = []
    targets = qualified_and_bare_call_targets(
        tree, "ftplib", _FTPLIB_SSRF_CALLS)
    if not targets:
        return issues
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    binding_cache: dict = {}
    for node in iter_nodes(tree, None):
        if not isinstance(node, ast.Call):
            continue
        if dotted_name(node.func) not in targets:
            continue
        func = node.func
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)):
            name = func.value.id
            expected = ('import', 'ftplib')
        elif isinstance(func, ast.Name):
            name = func.id
            expected = ('from', 'ftplib', 'ftpcp')
        else:
            continue
        ordered = _ordered_name_binding(
            node, name, scopes.get(id(node)), lexical, parents,
            binding_cache)
        if ordered is None:
            if call_head_is_shadowed(node, lexical, scopes):
                continue
            record = resolve_import_binding(imports, parents, node, name)
        else:
            state, record = ordered
            if state in {'custom', 'deleted'}:
                continue
        if record != expected:
            continue
        issues.append(_make_io04_issue(node, source_lines, filepath))
    return issues
def _dc01_first_unreachable(body: list, idx: int) -> ast.stmt | None:
    return body[idx + 1] if idx + 1 < len(body) else None
def _dc01_body_issues(body: list, source_lines: Any,
                      filepath: Any) -> list:
    issues = []
    for i, stmt in enumerate(body[:-1]):
        if not isinstance(stmt, (ast.Return, ast.Raise, ast.Break,
                                 ast.Continue)):
            continue
        unreachable = _dc01_first_unreachable(body, i)
        if unreachable is None:
            continue
        issues.append(DiagnoseFinding(
            id="DC-01", severity="P3", dimension="dead_code",
            file=filepath, line=unreachable.lineno,
            col_offset=unreachable.col_offset,
            title="unreachable code after flow terminator",
            description=(
                f"L{stmt.lineno} 的 {type(stmt).__name__.lower()} 使后续语句不可达."
            ),
            code_snippet=extract_code_lines(source_lines, unreachable.lineno),
            suggestion=f'根因: unreachable code after flow terminator。该问题属于死代码类别。\n修复策略: 删除 L{unreachable.lineno} 及之后的不可达语句,或将流程终止语句移到块末尾.\n参考标准: pylint W0101 (unreachable)',
            rule_ref="CS-97",
        ))
    return issues
def check_DC01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        for body in (getattr(node, 'body', None),
                     getattr(node, 'orelse', None),
                     getattr(node, 'finalbody', None)):
            if not body or not isinstance(body, list):
                continue
            issues.extend(_dc01_body_issues(body, source_lines, filepath))
    return issues
def _dc03_is_binding_takeover(node: ast.AST, name: str,
                               first_def: int, last_def: int) -> bool:
    return (isinstance(node, ast.Name) and node.id == name
            and isinstance(node.ctx, ast.Load)
            and first_def < node.lineno < last_def)
def _dc03_definition_time_nodes(root: ast.AST):
    stack: list[ast.AST] = [root]
    while stack:
        cur = stack.pop()
        yield cur
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend(cur.decorator_list)
            stack.append(cur.args)
            if cur.returns is not None:
                stack.append(cur.returns)
            continue
        if isinstance(cur, ast.Lambda):
            stack.append(cur.args)
            continue
        stack.extend(ast.iter_child_nodes(cur))
def _dc03_alias_captured_between(top_stmts: list, name: str,
                                 current_def: int, next_def: int) -> bool:
    if any(_dc03_is_binding_takeover(sub, name, current_def, next_def)
           for stmt in top_stmts
           for sub in _dc03_definition_time_nodes(stmt)):
        return True
    next_definition = next(
        (stmt for stmt in top_stmts
         if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef))
         and stmt.lineno == next_def), None)
    if next_definition is None:
        return False
    return any(
        isinstance(sub, ast.Name) and sub.id == name
        and isinstance(sub.ctx, ast.Load)
        for sub in _dc03_definition_time_nodes(next_definition))
def _dc03_alias_captured(top_stmts: list, name: str, lines: list) -> bool:
    # 每一次覆盖都会独立丢弃当时生效的定义；只保存其中任意一个旧定义，
    # 不能证明其余定义也仍然可达。
    return all(
        _dc03_alias_captured_between(top_stmts, name, current_def, next_def)
        for current_def, next_def in pairwise(lines))
_DC03_SCOPE_TYPES = (ast.Module, ast.ClassDef, ast.FunctionDef,
                     ast.AsyncFunctionDef)
def _dc03_iter_scope_bodies(tree: Any):
    for node in walk_nodes(tree):
        if isinstance(node, _DC03_SCOPE_TYPES):
            yield list(getattr(node, "body", ()))
def _dc03_collect_defs(stmts: list) -> dict[str, list[ast.AST]]:
    func_defs: dict[str, list[ast.AST]] = {}
    for node in stmts:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_defs.setdefault(node.name, []).append(node)
    return func_defs
_DC03_OVERLOAD_IMPORTS = frozenset({
    ('from', 'typing', 'overload'),
    ('from', 'typing_extensions', 'overload'),
})
_DC03_OVERLOAD_MODULE_IMPORTS = frozenset({
    ('import', 'typing'),
    ('import', 'typing_extensions'),
})
def _dc03_is_overload_decorator(
        dec: ast.AST, imports: dict, parents: dict, lexical: Any,
        binding_cache: dict) -> bool:
    if isinstance(dec, ast.Name):
        name = dec.id
        expected = _DC03_OVERLOAD_IMPORTS
    elif (isinstance(dec, ast.Attribute) and dec.attr == 'overload'
          and isinstance(dec.value, ast.Name)):
        name = dec.value.id
        expected = _DC03_OVERLOAD_MODULE_IMPORTS
    else:
        return False
    owner = parents.get(dec)
    if isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
        scope = lexical.parent.get(owner)
    else:
        scope = dec
        while scope is not None and scope not in lexical.bound:
            scope = parents.get(scope)
    ordered = (_ordered_name_binding(
        dec, name, scope, lexical, parents, binding_cache)
        if scope is not None else None)
    if ordered is not None:
        state, record = ordered
        if state == 'import':
            return record in expected
        if state in {'custom', 'deleted'}:
            return False
        return isinstance(dec, ast.Name) and dec.id == 'overload'
    if (scope is not None
            and scope_shadows_import(lexical, scope, name)):
        return False
    record = resolve_import_binding(imports, parents, dec, name)
    if record is not None:
        return record in expected
    return isinstance(dec, ast.Name) and dec.id == 'overload'
def _dc03_is_overload_chain(
        nodes: list[ast.AST], imports: dict, parents: dict,
        lexical: Any, binding_cache: dict) -> bool:
    return (len(nodes) > 1
            and all(any(_dc03_is_overload_decorator(
                dec, imports, parents, lexical, binding_cache)
                        for dec in node.decorator_list)
                    for node in nodes[:-1]))
def _dc03_finding(name: str, lines: list[int], source_lines: Any,
                  filepath: Any) -> dict:
    all_lines = ", ".join(f"L{n}" for n in lines)
    return {
        "rule_id": "DC-03", "severity": "P0", "dimension": "duplicate",
        "file": filepath, "line": lines[-1],
        "title": f"函数 '{name}' 被重复定义（{all_lines}）",
        "description": (
            f"函数 '{name}' 在第{lines[0]}行首次定义,共{len(lines)}处"
            f"重复（{all_lines}）,最终生效于第{lines[-1]}行."
            f"Python 不报错但前者被后者覆盖,可能导致部分功能丢失."
        ),
        "code_snippet": extract_code_lines(source_lines, lines[-1]),
        "suggestion": '根因: 代码实现中存在死代码方面的问题, 需要规范化处理。\n修复策略: 合并两个同名函数或重命名.若为有意重载,加注释说明.\n参考标准: pylint E0102 / flake8 F811',
        "rule_ref": "cs69_duplicate_func, rf395",
    }
def check_DC03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    lexical = collect_lexical_scope_table(tree)
    binding_cache: dict = {}
    for stmts in _dc03_iter_scope_bodies(tree):
        for name, nodes in _dc03_collect_defs(stmts).items():
            if len(nodes) <= 1:
                continue
            if name.startswith('__') and name.endswith('__'):
                continue
            if _dc03_is_overload_chain(
                    nodes, imports, parents, lexical, binding_cache):
                continue
            lines = [node.lineno for node in nodes]
            if _dc03_alias_captured(stmts, name, lines):
                continue
            issues.append(_dc03_finding(name, lines, source_lines, filepath))
    return issues
def _is_pairable_pair(target: ast.AST, value: ast.AST) -> bool:
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return False
    if len(target.elts) != len(value.elts):
        return False
    return not any(isinstance(t, ast.Starred) for t in target.elts) and not any(
        isinstance(e, ast.Starred) for e in value.elts)
def _pair_target_values(target: ast.AST, value: ast.AST) -> Iterator[tuple[ast.AST, ast.AST]]:
    if _is_pairable_pair(target, value):
        for t_el, v_el in zip(target.elts, value.elts, strict=True):
            yield from _pair_target_values(t_el, v_el)
    else:
        yield target, value
def _handle_scope_id(parent: dict, tree: ast.Module, n: ast.AST) -> int:
    cur = n
    while cur in parent:
        cur = parent[cur]
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Module)):
            return id(cur)
    return id(tree)
def _is_open_call(call_node: ast.Call) -> bool:
    func = call_node.func
    return ((isinstance(func, ast.Name) and func.id == 'open')
            or (isinstance(func, ast.Attribute) and func.attr == 'open'))
def _is_non_resource_import_record(record: Any) -> bool:
    if not isinstance(record, tuple):
        return False
    if len(record) == 2 and record[0] == 'import':
        module = record[1]
    elif len(record) == 3 and record[0] == 'from':
        module = record[1]
    else:
        return False
    if not isinstance(module, str) or not module:
        return False
    top_module = module.split('.', 1)[0]
    return top_module not in OPEN_FAMILY_MODULES | {'pathlib'}
def _collect_non_resource_open_ids(tree: ast.Module) -> set[int]:
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    binding_cache: dict = {}
    non_resource_ids: set[int] = set()
    for node, scope in lexical.calls:
        func = node.func
        if not (isinstance(func, ast.Attribute) and func.attr == 'open'):
            continue
        root = func.value
        while isinstance(root, ast.Attribute):
            root = root.value
        if not isinstance(root, ast.Name):
            continue
        if root is not func.value:
            # 属性链接收者（self.conn.open()）：根名是（外层）形参时，
            # 整条链都是业务对象而非模块，同样不得按资源泄漏告警。
            if _param_bound_in_scope_chain(lexical, scope, root.id):
                non_resource_ids.add(id(node))
            continue
        name = root.id
        ordered = _ordered_name_binding(
            node, name, scope, lexical, parents, binding_cache)
        if ordered is None:
            if call_head_is_shadowed(node, lexical, scopes):
                # 形参/self/cls 作接收者：形参不可能是模块，.open() 是
                # 业务方法而非文件打开，不得按资源泄漏告警。嵌套函数 /
                # lambda / 推导式里按 LEGB 落到外层形参（含外层方法的
                # self）的接收者同理，必须沿作用域链向上找，不能只看当前层。
                if _param_bound_in_scope_chain(lexical, scope, name):
                    non_resource_ids.add(id(node))
                continue
            record = resolve_import_binding(imports, parents, node, name)
        else:
            state, record = ordered
            if state != 'import':
                # 同上：形参/self 作接收者不是模块导入；局部变量
                # （如 p = Path(x); p.open()）仍保留为候选。
                if _scope_initial_name_binding(scope, name) is not None:
                    non_resource_ids.add(id(node))
                continue
        if _is_non_resource_import_record(record):
            non_resource_ids.add(id(node))
    return non_resource_ids
def _non_path_factory_open_ids(tree: ast.Module) -> set[int]:
    ctx = _b26_collect_context(tree)
    excluded: set[int] = set()
    for node, _scope in ctx.lexical.calls:
        func = node.func
        if not (isinstance(func, ast.Attribute) and func.attr == 'open'
                and isinstance(func.value, ast.Call)):
            continue
        if _b26_receiver_decidable(
                func, ctx.module_aliases, ctx.path_constructors):
            _module, resolved = _b26_resolve_receiver_module(node, ctx)
            if resolved:
                continue
        excluded.add(id(node))
    return excluded
def _closes_by_name(func: ast.expr) -> bool:
    """调用的函数名是否表达「关闭资源」（``fh.close()`` / ``_close_fd_quietly()``）。"""
    if isinstance(func, ast.Attribute):
        return 'close' in func.attr.lower()
    if isinstance(func, ast.Name):
        return 'close' in func.id.lower()
    return False


def _local_contextmanager_names(tree: ast.Module) -> frozenset[str]:
    """本模块内被 ``@contextmanager`` 装饰的函数名。

    ``with _quiet_close(open(...)) as h:`` 这类「本地上下文管理器包裹 open」
    的写法会把 fd 所有权交给 with 接管，但关闭型白名单只认
    ``contextlib.closing``，于是把安全写法误报为资源泄漏。
    """
    names: set[str] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        decorated = any(
            # 兼容 ``@contextmanager`` / ``@contextlib.contextmanager`` /
            # ``@contextlib.contextmanager()`` 三种写法。
            (isinstance(decorator, ast.Attribute)
             and decorator.attr == 'contextmanager')
            or (isinstance(decorator, ast.Name)
                and decorator.id == 'contextmanager')
            or (isinstance(decorator, ast.Call)
                and isinstance(decorator.func, ast.Attribute)
                and decorator.func.attr == 'contextmanager')
            for decorator in node.decorator_list)
        if not decorated:
            continue
        # 只有函数体真的关闭了资源才承认它接管所有权：
        # ``@contextmanager def tracked(fh): yield fh`` 并不关文件，
        # 放行会把真泄漏洗成误报的反面（漏报）。
        if any(isinstance(sub, ast.Call) and _closes_by_name(sub.func)
               for sub in walk_nodes(node)):
            names.add(node.name)
    return frozenset(names)


def _contextlib_closing_call_ids(tree: ast.Module) -> frozenset[int]:
    module_aliases, function_aliases = collect_module_bindings(
        tree, 'contextlib', ('closing',))
    local_managers = _local_contextmanager_names(tree)
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    closing_ids: set[int] = set()
    for node, _scope in lexical.calls:
        expected = None
        root = None
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr == 'closing'
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in module_aliases):
            root = node.func.value.id
            expected = ('import', 'contextlib')
        elif (isinstance(node.func, ast.Name)
              and node.func.id in function_aliases):
            root = node.func.id
            expected = ('from', 'contextlib', 'closing')
        elif (isinstance(node.func, ast.Name)
              and node.func.id in local_managers):
            # 本地上下文管理器：``with fn(...) as h`` 同样接管资源所有权。
            # 这里不做遮蔽校验——名字本来就是本模块内定义的，
            # ``call_head_is_shadowed`` 对本地 def 恒为 True。
            closing_ids.add(id(node))
            continue
        if root is None:
            continue
        record = resolve_import_binding(imports, parents, node, root)
        if (record == expected
                and not call_head_is_shadowed(node, lexical, scopes)):
            closing_ids.add(id(node))
    return frozenset(closing_ids)
def _closing_managed_value(node: ast.AST,
                           closing_ids: frozenset[int]) -> ast.AST | None:
    if not isinstance(node, ast.Call) or id(node) not in closing_ids:
        return None
    if len(node.args) == 1 and not node.keywords:
        return node.args[0]
    if (not node.args and len(node.keywords) == 1
            and node.keywords[0].arg == 'thing'):
        return node.keywords[0].value
    return None
_FD_CLOSEFD_ARG_INDEX = 6
def _fd_call_takes_ownership(node: ast.Call) -> bool:
    if (any(isinstance(arg, ast.Starred) for arg in node.args)
            or any(kw.arg is None for kw in node.keywords)):
        return False
    closefd_values = []
    if len(node.args) > _FD_CLOSEFD_ARG_INDEX:
        closefd_values.append(node.args[_FD_CLOSEFD_ARG_INDEX])
    closefd_values.extend(
        kw.value for kw in node.keywords if kw.arg == 'closefd')
    return all(isinstance(value, ast.Constant) and bool(value.value)
               for value in closefd_values)
def _fd_owning_call_ids(tree: ast.Module,
                        excluded_ids: frozenset[int]) -> frozenset[int]:
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    cache: dict = {}
    owner_ids: set[int] = set()
    for node, scope in lexical.calls:
        if (not node.args or id(node) in excluded_ids
                or not _fd_call_takes_ownership(node)):
            continue
        func = node.func
        canonical = False
        if isinstance(func, ast.Name):
            root = func.id
            allowed = {('from', 'builtins', 'open'), ('from', 'io', 'open'),
                       ('from', 'os', 'fdopen')}
            canonical = root == 'open'
        elif (isinstance(func, ast.Attribute)
              and isinstance(func.value, ast.Name)
              and func.attr in {'open', 'fdopen'}):
            root = func.value.id
            modules = {'builtins', 'io'} if func.attr == 'open' else {'os'}
            allowed = {('import', module) for module in modules}
            canonical = root in modules
        else:
            continue
        ordered = _ordered_name_binding(
            node, root, scope, lexical, parents, cache)
        if ordered is None:
            record = resolve_import_binding(imports, parents, node, root)
            if record is None:
                resolved = canonical and not call_head_is_shadowed(
                    node, lexical, scopes)
            else:
                resolved = record in allowed
        else:
            state, record = ordered
            resolved = record in allowed if state == 'import' else (
                state == 'none' and canonical)
        if not resolved:
            continue
        owner_ids.add(id(node))
    return frozenset(owner_ids)
def _with_item_open_ids(wnode: ast.With | ast.AsyncWith,
                        closing_ids: frozenset[int],
                        fd_owner_ids: frozenset[int],
                        os_aliases: frozenset[str],
                        os_open_aliases: frozenset[str],
                        excluded_ids: frozenset[int]) -> set[int]:
    ids: set[int] = set()
    for item in wnode.items:
        expr = item.context_expr
        candidates = [expr]
        if isinstance(expr, ast.NamedExpr):
            candidates.append(expr.value)
        candidates.extend(_closing_managed_value(candidate, closing_ids)
                          for candidate in tuple(candidates))
        for candidate in candidates:
            if (isinstance(candidate, ast.Call)
                    and (_is_open_call(candidate)
                         or _is_os_open_name_call(
                             candidate, os_open_aliases))):
                ids.add(id(candidate))
        if not isinstance(expr, ast.Call) or id(expr) not in fd_owner_ids:
            continue
        opened = expr.args[0]
        if (isinstance(opened, ast.Call) and id(opened) not in excluded_ids
                and (_is_os_open_call(opened, os_aliases)
                     or _is_os_open_name_call(opened, os_open_aliases))):
            ids.add(id(opened))
    return ids
def _collect_with_managed_open_ids(
        tree: ast.Module, os_aliases: frozenset[str],
        os_open_aliases: frozenset[str], excluded_ids: frozenset[int],
        fd_owner_ids: frozenset[int],
        closing_ids: frozenset[int]) -> set[int]:
    managed_ids: set[int] = set()
    for wnode in tree_nodes(tree):
        if isinstance(wnode, (ast.With, ast.AsyncWith)):
            managed_ids |= _with_item_open_ids(
                wnode, closing_ids, fd_owner_ids, os_aliases,
                os_open_aliases, excluded_ids)
    return managed_ids
def _fdopen_enclosing_statement(
        node: ast.AST, parent: dict) -> tuple[ast.AST, ast.AST | None]:
    """从 ``node`` 向上走到最近的语句 / 作用域边界，返回 (边界下直接子节点, 边界)。"""
    current = node
    while True:
        holder = parent.get(current)
        if (holder is None
                or isinstance(holder, (ast.stmt, ast.ExceptHandler, ast.Lambda,
                                       ast.ListComp, ast.SetComp, ast.DictComp,
                                       ast.GeneratorExp, ast.withitem))):
            return current, holder
        current = holder
def _fdopen_result_managed(
        node: ast.Call, parent: dict, tree: ast.Module,
        closing_ids: frozenset[int], with_uses: dict,
        attr_close_uses: dict, return_uses: dict,
        bind_positions: dict, branch_of_pos: dict) -> bool:
    """``os.fdopen(fd)`` 返回的文件对象是否被 with / return / close 接管。

    只有被接管的 fdopen 才真正承担了 ``fd`` 的 closefd 责任；返回值被
    丢弃、或绑定后从未使用的 fdopen 自身就是泄漏，不能反过来给
    ``os.open()`` 销项。
    """
    expr, holder = _fdopen_enclosing_statement(node, parent)
    # with os.fdopen(fd) as h / with closing(os.fdopen(fd)) as h
    if isinstance(holder, ast.withitem):
        return holder.context_expr is expr
    # return os.fdopen(fd) / yield os.fdopen(fd)
    if isinstance(holder, ast.Return) and holder.value is expr:
        return True
    if (isinstance(holder, ast.Expr) and holder.value is expr
            and isinstance(expr, (ast.Yield, ast.YieldFrom))):
        return True
    # os.fdopen(fd).close()
    if (isinstance(expr, ast.Call) and isinstance(expr.func, ast.Attribute)
            and expr.func.attr == 'close' and expr.func.value is node
            and not expr.args and not expr.keywords):
        return True
    # h = os.fdopen(fd) 之后由 h 接管：with h / h.close() / return h
    if isinstance(holder, ast.Assign):
        targets, value = holder.targets, holder.value
    elif isinstance(holder, ast.AnnAssign):
        targets, value = [holder.target], holder.value
    elif isinstance(expr, ast.NamedExpr) and expr.value is node:
        targets, value = [expr.target], expr.value
    else:
        return False
    scope = _handle_scope_id(parent, tree, node)
    pos = (node.lineno, node.col_offset)
    for target in targets:
        for t_el, v_el in _pair_target_values(target, value):
            if v_el is not node:
                v_el = _closing_managed_value(v_el, closing_ids)
                if v_el is not node:
                    continue
            if any(isinstance(sub, ast.Attribute) for sub in walk_nodes(t_el)):
                # self.h = os.fdopen(fd)：所有权转交实例属性，与
                # ``self.f = open(p)`` 同样不在本函数内判定泄漏。
                return True
            if not isinstance(t_el, ast.Name):
                continue
            meta = {id(node): [(scope, t_el.id, pos)]}
            for uses in (with_uses, attr_close_uses, return_uses):
                if _b02_managed_by(id(node), uses, meta,
                                   bind_positions, branch_of_pos):
                    return True
    return False
def _collect_fd_transfer_uses(
        tree: ast.Module, parent: dict, os_aliases: frozenset[str],
        os_fdopen_aliases: frozenset[str],
        fd_owner_ids: frozenset[int], closing_ids: frozenset[int],
        with_uses: dict, attr_close_uses: dict, return_uses: dict,
        bind_positions: dict, branch_of_pos: dict) -> dict:
    """收集经绑定解析且实际接管 closefd 的 ``os.fdopen(fd)`` 使用点。

    历史缺陷：只要出现 ``os.fdopen(fd)`` 就无条件视为 fd 已转移，于是
    ``fd = os.open(p); h = os.fdopen(fd)`` 之后 ``h`` 从未关闭的真实泄漏
    被整体销项；而内联写法 ``os.fdopen(os.open(p))`` 却会报泄漏，两种
    等价写法结论相反。转移成立的前提是 fdopen 的返回文件对象本身被
    with / return / close 接管。
    """
    uses: dict[tuple[int, str], list[tuple[int, int]]] = {}
    if not os_fdopen_aliases and not os_aliases:
        return uses
    for node in tree_nodes(tree):
        if (not isinstance(node, ast.Call) or not node.args
                or id(node) not in fd_owner_ids):
            continue
        func = node.func
        is_fdopen = (
            (isinstance(func, ast.Attribute) and func.attr == 'fdopen'
             and isinstance(func.value, ast.Name)
             and func.value.id in os_aliases)
            or (isinstance(func, ast.Name) and func.id in os_fdopen_aliases))
        if not is_fdopen or not isinstance(node.args[0], ast.Name):
            continue
        if not _fdopen_result_managed(
                node, parent, tree, closing_ids, with_uses,
                attr_close_uses, return_uses, bind_positions,
                branch_of_pos):
            continue
        key = (_handle_scope_id(parent, tree, node), node.args[0].id)
        uses.setdefault(key, []).append((node.lineno, node.col_offset))
    return uses
def _collect_open_assigns(tree: ast.Module, parent: dict,
                          os_open_aliases: frozenset[str],
                          ) -> tuple[dict, dict]:
    open_meta: dict[int, list[tuple[int, str, tuple[int, int]]]] = {}
    bind_positions: dict[tuple[int, str], list[tuple[int, int]]] = {}
    for node in tree_nodes(tree):
        _register_bind_positions(node, parent, tree, bind_positions)
        _register_open_handle(node, parent, tree, open_meta,
                              os_open_aliases)
    return open_meta, bind_positions
def _expr_pos(node: ast.AST, fallback: ast.AST) -> tuple[int, int]:
    return (getattr(node, 'lineno', fallback.lineno),
            getattr(node, 'col_offset', fallback.col_offset))
def _binding_entries(node: ast.AST) -> list[tuple[str, tuple[int, int]]]:
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                         ast.NamedExpr)):
        return _binding_entries_value(node)
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        pos = _expr_pos(node, node)
        return [(name, pos) for name in import_alias_bound_names(node)]
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return [(node.name, _expr_pos(node, node))]
    if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
        return ([(node.name.id, _expr_pos(node.name, node))]
                if isinstance(node.name, ast.Name) else [])
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        return [(node.name, _expr_pos(node, node))] if node.name else []
    if isinstance(node, ast.MatchMapping):
        return [(node.rest, _expr_pos(node, node))] if node.rest else []
    if isinstance(node, ast.ExceptHandler):
        if not node.name:
            return []
        return [(node.name, (node.lineno, node.col_offset))]
    if isinstance(node, (ast.For, ast.AsyncFor, ast.Delete,
                         ast.With, ast.AsyncWith)):
        return _binding_entries_iterable(node)
    return []
def _binding_entries_iterable(node: ast.AST) -> list[tuple[str, tuple[int, int]]]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _binding_entries_targets(node.target, node)
    if isinstance(node, ast.Delete):
        return _binding_entries_deleted(node)
    return _binding_entries_with(node)
def _binding_entries_deleted(node: ast.Delete) -> list[tuple[str, tuple[int, int]]]:
    return [entry for target in node.targets
            for entry in _binding_entries_targets(target, node)]
def _binding_entries_with(
        node: ast.With | ast.AsyncWith) -> list[tuple[str, tuple[int, int]]]:
    return [entry for item in node.items if item.optional_vars is not None
            for entry in _binding_entries_targets(item.optional_vars, node)]
def _binding_entries_value(node: ast.AST) -> list[tuple[str, tuple[int, int]]]:
    if isinstance(node, ast.Assign):
        return [(name, _expr_pos(v_el, node))
                for target in node.targets
                for t_el, v_el in _pair_target_values(target, node.value)
                for name in iter_unpack_target_names(t_el)]
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return []
    pos = _expr_pos(node.value, node)
    return [(name, pos) for name in iter_unpack_target_names(node.target)]
def _binding_entries_targets(target: ast.AST,
                             node: ast.AST) -> list[tuple[str, tuple[int, int]]]:
    pos = _expr_pos(target, node)
    return [(name, pos) for name in iter_unpack_target_names(target)]
def _register_bind_positions(node, parent: dict, tree: ast.Module,
                             bind_positions: dict) -> None:
    entries = _binding_entries(node)
    if not entries:
        return
    _scope = _handle_scope_id(parent, tree, node)
    for name, pos in entries:
        bind_positions.setdefault((_scope, name), []).append(pos)
def _direct_import_record(node: ast.AST, name: str) -> tuple | None:
    if isinstance(node, ast.Import):
        for alias in node.names:
            bound = alias.asname or alias.name.split('.', 1)[0]
            if bound == name:
                module = alias.name if alias.asname else bound
                return ('import', module)
    elif isinstance(node, ast.ImportFrom):
        for alias in node.names:
            if alias.name != '*' and (alias.asname or alias.name) == name:
                source = '' if node.level else (node.module or '')
                return ('from', source, alias.name)
    return None
_STMT_BINDING_INDEX_KEY: str = '__stmt_binding_index__'


def _statement_binding_index(node: ast.AST) -> tuple:
    """单次子树遍历预计算语句绑定名与星号导入（等价加速）。

    原实现对每条语句按名称重复 ast.walk 全子树，复杂度呈
    O(名称数 × 语句数 × 子树大小)，大文件单检测器可达数秒；
    这里把「本语句绑定名 / 本语句是否星号导入 / 子树绑定名 /
    子树是否星号导入」一次算清并缓存，使每次查询退化为集合成员判定。
    """
    node_bound = {bound for bound, _pos in _binding_entries(node)}
    node_star = (isinstance(node, ast.ImportFrom)
                 and any(alias.name == '*' for alias in node.names))
    child_bound: set[str] = set()
    child_star = False
    stack = list(ast.iter_child_nodes(node))
    while stack:
        child = stack.pop()
        if child_star is False and isinstance(child, ast.ImportFrom) and any(
                alias.name == '*' for alias in child.names):
            child_star = True
        for bound, _pos in _binding_entries(child):
            child_bound.add(bound)
        stack.extend(ast.iter_child_nodes(child))
    return node_bound, node_star, child_bound, child_star


def _statement_name_binding(node: ast.AST, name: str,
                            cache: dict | None = None) -> tuple:
    direct = _direct_import_record(node, name)
    state = ('import', direct) if direct is not None else None
    if cache is None:
        index = _statement_binding_index(node)
    else:
        index_map = cache.get(_STMT_BINDING_INDEX_KEY)
        if not isinstance(index_map, dict):
            index_map = {}
            cache[_STMT_BINDING_INDEX_KEY] = index_map
        index = index_map.get(id(node))
        if index is None:
            index = _statement_binding_index(node)
            index_map[id(node)] = index
    node_bound, node_star, child_bound, child_star = index
    if state is None and isinstance(node, ast.Delete) and name in node_bound:
        state = ('deleted', None)
    elif state is None and name in node_bound:
        state = ('custom', None)
    ambiguous = node_star or child_star or name in child_bound
    return state, ambiguous
def _scope_initial_name_binding(scope: ast.AST,
                                name: str) -> tuple[str, Any] | None:
    args = getattr(scope, 'args', None)
    if (isinstance(args, ast.arguments)
            and any(param.arg == name for param in iter_arg_nodes(args))):
        return ('custom', None)
    if isinstance(scope, ast.ExceptHandler) and scope.name == name:
        return ('custom', None)
    if any(getattr(param, 'name', None) == name
           for param in getattr(scope, 'type_params', ()) or ()):
        return ('custom', None)
    return None
def _param_bound_in_scope_chain(lexical: Any, scope: ast.AST,
                                name: str) -> bool:
    """``name`` 是否是当前或任一外层作用域的入口绑定（形参等）。

    ``_scope_initial_name_binding`` 只看单个作用域；嵌套函数、lambda、
    推导式引用外层方法的 ``self`` 或外层形参时，名字按 LEGB 规则落到
    外层形参上，与当前层形参一样不可能是模块导入。
    """
    current = scope
    while current is not None:
        if _scope_initial_name_binding(current, name) is not None:
            return True
        current = lexical.parent.get(current)
    return False
def _name_query_precedes_statement_binding(
        node: ast.AST, statement: ast.AST, parents: dict) -> bool:
    if isinstance(statement, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                              ast.NamedExpr)):
        roots = [statement.value]
    elif isinstance(statement, (ast.For, ast.AsyncFor)):
        roots = [statement.iter]
    elif isinstance(statement, (ast.With, ast.AsyncWith)):
        roots = [item.context_expr for item in statement.items]
    elif isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)):
        roots = definition_time_expressions(statement)
    else:
        return False
    current = node
    while current is not None:
        if any(current is root for root in roots):
            return True
        current = parents.get(current)
    return False
def _ordered_name_binding(node: ast.AST, name: str, scope: ast.AST,
                          lexical: Any, parents: dict, cache: dict,
                          at_statement_start: bool = False,
                          ) -> tuple[str, Any] | None:
    if isinstance(scope, ast.ExceptHandler):
        current = node
        while current in parents and parents[current] is not scope:
            current = parents[current]
        if current is scope.type:
            outer = lexical.parent.get(scope)
            if outer is not None:
                return _ordered_name_binding(
                    node, name, outer, lexical, parents, cache)
        return None
    initial = _scope_initial_name_binding(scope, name)
    if isinstance(scope, ast.Lambda):
        return initial
    if not isinstance(scope, (ast.Module, ast.ClassDef, ast.FunctionDef,
                              ast.AsyncFunctionDef, ast.ExceptHandler)):
        return None
    body = getattr(scope, 'body', None)
    if not isinstance(body, list):
        return None
    current = node
    if current is not scope:
        while True:
            parent = parents.get(current)
            if parent is scope:
                break
            if parent is None:
                return None
            current = parent
    key = (scope, name)
    prefixes = cache.get(key)
    if prefixes is None:
        prefixes = [(stmt, *_statement_name_binding(stmt, name, cache))
                    for stmt in body]
        cache[key] = prefixes
    state = initial
    for stmt, direct, ambiguous in prefixes:
        if stmt is current:
            before_binding = _name_query_precedes_statement_binding(
                node, stmt, parents)
            if not at_statement_start and (
                    ambiguous or (direct is not None and not before_binding)):
                return None
            break
        if ambiguous:
            return None
        if direct is not None:
            state = direct
    else:
        return None
    local_frame = isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                                     ast.ExceptHandler))
    if local_frame and state is not None and state[0] == 'deleted':
        return ('custom', None)
    if state is not None and not (
            state[0] == 'deleted' and isinstance(scope, ast.ClassDef)):
        return state
    if isinstance(scope, ast.ClassDef):
        outer = lexical.parent.get(scope)
        if outer is not None:
            return _ordered_name_binding(
                scope, name, outer, lexical, parents, cache,
                at_statement_start=True)
    if state is not None:
        return state
    if local_frame and name in lexical.bound.get(scope, set()):
        return ('custom', None)
    return None if local_frame else ('none', None)
def _has_prior_direct_delete(node: ast.AST, name: str, scope: ast.AST,
                             parents: dict) -> bool:
    if not isinstance(scope, (ast.Module, ast.ClassDef)):
        return False
    current = node
    while current is not scope:
        parent = parents.get(current)
        if parent is scope:
            break
        if parent is None:
            return False
        current = parent
    for stmt in scope.body:
        if stmt is current:
            return False
        if (isinstance(stmt, ast.Delete) and any(
                bound == name for bound, _pos in _binding_entries(stmt))):
            return True
    return False
def _deleted_open_family_call_ids(tree: ast.Module) -> frozenset[int]:
    lexical = collect_lexical_scope_table(tree)
    parents = parent_map(tree)
    cache: dict = {}
    restored: set[int] = set()
    for node, scope in lexical.open_calls:
        if not _has_prior_direct_delete(node, 'open', scope, parents):
            continue
        ordered = _ordered_name_binding(
            node, 'open', scope, lexical, parents, cache)
        if ordered is None:
            continue
        state, record = ordered
        if state in {'none', 'deleted'} or (
                state == 'import' and isinstance(record, tuple)
                and len(record) == 3 and record[0] == 'from'
                and record[1] in OPEN_FAMILY_MODULES and record[2] == 'open'):
            restored.add(id(node))
    return frozenset(restored)
def _register_with_open_handle(
        node: ast.With | ast.AsyncWith, parent: dict, tree: ast.Module,
        open_meta: dict, os_open_aliases: frozenset[str]) -> None:
    for item in node.items:
        if not isinstance(item.optional_vars, ast.Name):
            continue
        opened = [
            sub for sub in walk_nodes(item.context_expr)
            if isinstance(sub, ast.Call)
            and (_is_open_call(sub)
                 or _is_os_open_name_call(sub, os_open_aliases))
        ]
        if len(opened) != 1:
            continue
        call = opened[0]
        scope = _handle_scope_id(parent, tree, node)
        handle_pos = _expr_pos(item.optional_vars, node)
        open_meta.setdefault(id(call), []).append(
            (scope, item.optional_vars.id, handle_pos))
def _register_open_handle(node, parent: dict, tree: ast.Module,
                          open_meta: dict,
                          os_open_aliases: frozenset[str],
                          ) -> None:
    if isinstance(node, (ast.With, ast.AsyncWith)):
        _register_with_open_handle(
            node, parent, tree, open_meta, os_open_aliases)
        return
    if isinstance(node, ast.Assign):
        targets = node.targets
        value = node.value
    elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        targets = [node.target]
        value = node.value
    else:
        return
    for t in targets:
        for t_el, v_el in _pair_target_values(t, value):
            if (isinstance(t_el, ast.Name) and isinstance(v_el, ast.Call)
                    and (_is_open_call(v_el)
                         or _is_os_open_name_call(v_el, os_open_aliases))):
                _key = (_handle_scope_id(parent, tree, node), t_el.id)
                _pos = (v_el.lineno, v_el.col_offset)
                open_meta.setdefault(id(v_el), []).append(
                    (_key[0], _key[1], _pos))
def _os_module_aliases(tree: ast.Module) -> frozenset[str]:
    aliases, _bare = collect_module_bindings(tree, 'os', ('open', 'close'))
    return frozenset(aliases)
def _is_os_open_name_call(node: ast.Call,
                          aliases: frozenset[str]) -> bool:
    return isinstance(node.func, ast.Name) and node.func.id in aliases
def _os_function_aliases(tree: ast.Module, member: str) -> frozenset[str]:
    _aliases, imported = collect_module_bindings(tree, 'os', (member,))
    return frozenset(imported)
def _collect_attr_handle_open_ids(
        tree: ast.Module,
        os_open_aliases: frozenset[str]) -> set[int]:
    attr_open_ids: set[int] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            for target_el, value_el in _pair_target_values(target, node.value):
                if not (isinstance(value_el, ast.Call)
                        and (_is_open_call(value_el)
                             or _is_os_open_name_call(
                                 value_el, os_open_aliases))):
                    continue
                if any(isinstance(sub, ast.Attribute)
                       for sub in walk_nodes(target_el)):
                    attr_open_ids.add(id(value_el))
    return attr_open_ids
def _with_item_managed_name(
        expr: ast.expr, fd_owner_ids: frozenset[int],
        closing_ids: frozenset[int]) -> str | None:
    if isinstance(expr, ast.Name):
        return expr.id
    managed = _closing_managed_value(expr, closing_ids)
    if isinstance(managed, ast.Name):
        return managed.id
    return _fd_owner_source_name(expr, fd_owner_ids)
def _fd_owner_source_name(
        expr: ast.AST, fd_owner_ids: frozenset[int]) -> str | None:
    if (not (isinstance(expr, ast.Call) and expr.args)
            or id(expr) not in fd_owner_ids):
        return None
    first = expr.args[0]
    return first.id if isinstance(first, ast.Name) else None
def _with_item_transferred_name(
        item: ast.withitem, scope: int, open_meta: dict) -> str | None:
    """``with wrapper(open(...)) as h``：由 ``open_meta`` 确认句柄被接管。

    ``_with_item_managed_name`` 只能看到 ``as`` 名与直接调用形态；本地
    上下文管理器包裹 ``open()`` 时句柄名在 ``optional_vars`` 上，需回查
    该 open 调用已登记到同名变量才算「被 with 接管」。
    """
    if not isinstance(item.optional_vars, ast.Name):
        return None
    name = item.optional_vars.id
    for sub in walk_nodes(item.context_expr):
        for _scope, _var, _pos in open_meta.get(id(sub), ()):
            if _scope == scope and _var == name:
                return name
    return None


def _collect_with_uses(tree: ast.Module, parent: dict,
                        fd_owner_ids: frozenset[int],
                        closing_ids: frozenset[int],
                        open_meta: dict | None = None) -> dict:
    with_uses: dict[tuple[int, str], list[tuple[int, int]]] = {}
    for wnode in tree_nodes(tree):
        if not isinstance(wnode, (ast.With, ast.AsyncWith)):
            continue
        _scope = _handle_scope_id(parent, tree, wnode)
        for item in wnode.items:
            _name = _with_item_managed_name(
                item.context_expr, fd_owner_ids, closing_ids)
            if _name is None and open_meta:
                _name = _with_item_transferred_name(item, _scope, open_meta)
            if _name is None and open_meta and isinstance(
                    item.context_expr, ast.Name):
                # ``fh = open(...)`` 后 ``with fh:`` 同样是标准接管写法。
                _candidate = item.context_expr.id
                if any(_scope == _scope_id and _var == _candidate
                       for _handles in open_meta.values()
                       for _scope_id, _var, _pos in _handles):
                    _name = _candidate
            if _name is not None:
                with_uses.setdefault((_scope, _name), []).append(
                    (wnode.lineno, wnode.col_offset))
    return with_uses
def _collect_close_uses(tree: ast.Module, parent: dict,
                        os_aliases: frozenset[str],
                        close_aliases: frozenset[str],
                        excluded_ids: frozenset[int]) -> tuple[dict, dict]:
    attr_close_uses: dict[tuple[int, str], list[tuple[int, int]]] = {}
    os_close_uses: dict[tuple[int, str], list[tuple[int, int]]] = {}
    for node in tree_nodes(tree):
        if id(node) in excluded_ids:
            continue
        is_os_close = _is_os_close_call(node, os_aliases, close_aliases)
        _name = _close_use_handle_name(node, os_aliases, close_aliases)
        if _name is None:
            continue
        key = (_handle_scope_id(parent, tree, node), _name)
        pos = (node.lineno, node.col_offset)
        if is_os_close:
            os_close_uses.setdefault(key, []).append(pos)
        else:
            attr_close_uses.setdefault(key, []).append(pos)
    return attr_close_uses, os_close_uses
def _handle_names_in_return_value(
        value: ast.AST | None, closing_ids: frozenset[int]) -> tuple[str, ...]:
    if isinstance(value, ast.Name):
        return (value.id,)
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        return tuple(name for item in value.elts
                     for name in _handle_names_in_return_value(item, closing_ids))
    if isinstance(value, ast.Dict):
        items = [*value.keys, *value.values]
        return tuple(name for item in items if item is not None
                     for name in _handle_names_in_return_value(item, closing_ids))
    if isinstance(value, ast.IfExp):
        return (_handle_names_in_return_value(value.body, closing_ids)
                + _handle_names_in_return_value(value.orelse, closing_ids))
    if isinstance(value, ast.Starred):
        return _handle_names_in_return_value(value.value, closing_ids)
    if isinstance(value, ast.Call):
        managed = _closing_managed_value(value, closing_ids)
        if managed is not None:
            return _handle_names_in_return_value(managed, closing_ids)
    return ()
def _collect_return_uses(
        tree: ast.Module, parent: dict, closing_ids: frozenset[int]) -> dict:
    return_uses: dict[tuple[int, str], list[tuple[int, int]]] = {}
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.Return, ast.Yield, ast.YieldFrom)):
            continue
        _names = _handle_names_in_return_value(node.value, closing_ids)
        if not _names:
            continue
        _scope = _handle_scope_id(parent, tree, node)
        for _name in _names:
            return_uses.setdefault((_scope, _name), []).append(
                (node.lineno, node.col_offset))
    return return_uses
def _is_os_close_call(node: ast.AST,
                      os_aliases: frozenset[str],
                      close_aliases: frozenset[str]) -> bool:
    if (not isinstance(node, ast.Call) or len(node.args) != 1
            or node.keywords):
        return False
    if isinstance(node.func, ast.Name):
        return node.func.id in close_aliases
    return (isinstance(node.func, ast.Attribute)
            and node.func.attr == 'close'
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in os_aliases)
def _collect_inline_closed_open_ids(
        tree: ast.Module, os_aliases: frozenset[str],
        open_function_aliases: frozenset[str],
        close_function_aliases: frozenset[str],
        open_call_modules: dict[int, str],
        excluded_ids: frozenset[int]) -> set[int]:
    closed: set[int] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call) or id(node) in excluded_ids:
            continue
        if (not node.args and not node.keywords
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == 'close'
                and isinstance(node.func.value, ast.Call)):
            opened = node.func.value
            if ((_is_open_call(opened)
                 or _is_os_open_name_call(
                     opened, open_function_aliases))
                    and id(opened) not in excluded_ids):
                module = open_call_modules.get(id(opened))
                is_fd = module == 'os' or (
                    module is None and _is_os_open_call(opened, os_aliases))
                if not is_fd:
                    closed.add(id(opened))
            continue
        if not (node.args and _is_os_close_call(
                node, os_aliases, close_function_aliases)):
            continue
        opened = node.args[0]
        if not isinstance(opened, ast.Call) or id(opened) in excluded_ids:
            continue
        module = open_call_modules.get(id(opened))
        if module == 'os' or (
                module is None and _is_os_open_call(opened, os_aliases)):
            closed.add(id(opened))
    return closed
def _close_use_handle_name(node: ast.AST,
                           os_aliases: frozenset[str],
                           close_aliases: frozenset[str]) -> str | None:
    if _is_os_close_call(node, os_aliases, close_aliases):
        if node.args and isinstance(node.args[0], ast.Name):
            return node.args[0].id
        return None
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'close'
            and isinstance(node.func.value, ast.Name)):
        return None
    if node.args or node.keywords:
        return None
    return node.func.value.id
def _b02_branch_ranges(tree: ast.Module) -> list[tuple[int, str, int, int]]:
    """收集 ``if`` 的两条互斥分支行区间 ``(if_id, 'body'|'orelse', start, end)``。

    用行区间而不是位点，是因为同一个 ``if`` 分支里「赋值语句」与「赋值的
    调用表达式」列偏移不同，按 ``(lineno, col)`` 精确匹配会漏。
    """
    ranges: list[tuple[int, str, int, int]] = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        for label, block in (('body', node.body), ('orelse', node.orelse)):
            if not block:
                continue
            start = getattr(block[0], 'lineno', None)
            end = getattr(block[-1], 'end_lineno', None) or start
            if start is None:
                continue
            ranges.append((id(node), label, start, end))
    return ranges


def _b02_branch_of(pos, ranges) -> tuple:
    if not pos:
        return ()
    line = pos[0]
    return tuple((if_id, label) for if_id, label, start, end in ranges
                 if start <= line <= end)


def _b02_branches_disjoint(left: tuple, right: tuple) -> bool:
    """两条路径是否分处同一 ``if`` 的互斥分支。"""
    for left_id, left_label in left:
        for right_id, right_label in right:
            if left_id == right_id and left_label != right_label:
                return True
    return False


def _b02_managed_by(node_id: int, uses: dict, open_meta: dict,
                    bind_positions: dict,
                    branch_of_pos: dict | None = None) -> bool:
    for _scope, _var, _pos in open_meta.get(node_id, []):
        _rebinds = bind_positions.get((_scope, _var), ())
        for _use_pos in uses.get((_scope, _var), []):
            if _use_pos < _pos:
                continue
            _latest = latest_prior(_rebinds, _use_pos)
            if _latest is None or _latest <= _pos:
                return True
            # 历史缺陷：``if exclusive: fh = open(...)`` /
            # ``else: fh = os.fdopen(...)`` 两条互斥分支各自绑定同名变量时，
            # 后一条绑定位点会被 ``latest_prior`` 当成「覆盖」，于是
            # ``with fh:`` 只归属后一条绑定，前一条的 ``open()`` 被判资源
            # 泄漏（实测 diag_guard_io.py:508 为 P1 误报）。互斥分支互不
            # 覆盖，视为同一绑定位点。
            if (branch_of_pos is not None
                    and _b02_branches_disjoint(
                        _b02_branch_of(_pos, branch_of_pos),
                        _b02_branch_of(_latest, branch_of_pos))):
                return True
    return False
def _propagate_fd_owner_uses(
        tree: ast.Module, parent: dict, fd_owner_ids: frozenset[int],
        open_meta: dict, os_aliases: frozenset[str],
        os_open_aliases: frozenset[str], bind_positions: dict,
        with_uses: dict, attr_close_uses: dict,
        os_close_uses: dict, return_uses: dict) -> None:
    for node in tree_nodes(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == 'close'
                and not node.args and not node.keywords):
            fd_name = _fd_owner_source_name(node.func.value, fd_owner_ids)
            if fd_name is not None:
                scope = _handle_scope_id(parent, tree, node)
                os_close_uses.setdefault((scope, fd_name), []).append(
                    (node.lineno, node.col_offset))
        if isinstance(node, (ast.Return, ast.Yield, ast.YieldFrom)):
            if node.value is None:
                continue
            scope = _handle_scope_id(parent, tree, node)
            pos = (node.lineno, node.col_offset)
            for sub in walk_nodes(node.value):
                if not (isinstance(sub, ast.Call) and id(sub) in fd_owner_ids
                        and sub.args and isinstance(sub.args[0], ast.Name)):
                    continue
                if isinstance(parent.get(sub), ast.Attribute):
                    continue
                return_uses.setdefault(
                    (scope, sub.args[0].id), []).append(pos)
            continue
        targets = value = None
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
            targets, value = [node.target], node.value
        if targets is None or value is None:
            continue
        scope = _handle_scope_id(parent, tree, node)
        for t in targets:
            for t_el, v_el in _pair_target_values(t, value):
                if not (isinstance(t_el, ast.Name)
                        and isinstance(v_el, ast.Call)
                        and id(v_el) in fd_owner_ids and v_el.args):
                    continue
                source = v_el.args[0]
                owner_key = (scope, t_el.id)
                owner_pos = (v_el.lineno, v_el.col_offset)
                if isinstance(source, ast.Name):
                    fd_key = (scope, source.id)
                    if len(bind_positions.get(fd_key, ())) != 1:
                        continue
                elif (isinstance(source, ast.Call)
                      and (_is_os_open_call(source, os_aliases)
                           or _is_os_open_name_call(
                               source, os_open_aliases))):
                    # fd = os.fdopen(os.open(...))：内联 fd 也必须继承
                    # 目标句柄的 with/return/close 使用，不能只识别命名 fd。
                    fd_key = owner_key
                    open_meta.setdefault(id(source), []).append(
                        (scope, t_el.id, _expr_pos(source, v_el)))
                else:
                    continue
                owner_rebinds = bind_positions.get(owner_key, ())
                for uses in (with_uses, attr_close_uses, return_uses):
                    # fd = os.fdopen(fd) 时源键与目标键相同；快照遍历
                    # 防止向正在迭代的列表追加同一使用点而永不终止。
                    for use_pos in tuple(uses.get(owner_key, ())):
                        if use_pos < owner_pos:
                            continue
                        latest = latest_prior(owner_rebinds, use_pos)
                        if latest is None or latest <= owner_pos:
                            if uses is attr_close_uses:
                                os_close_uses.setdefault(
                                    fd_key, []).append(use_pos)
                            else:
                                uses.setdefault(fd_key, []).append(use_pos)
def _open_family_name_call_modules(
        tree: ast.Module, aliases: dict[str, str]) -> dict[int, str]:
    alias_names = frozenset(aliases) | {'open'}
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    binding_cache: dict = {}
    modules: dict[int, str] = {}
    for node, scope in lexical.calls:
        if not isinstance(node.func, ast.Name):
            continue
        name = node.func.id
        if name not in alias_names:
            continue
        ordered = _ordered_name_binding(
            node, name, scope, lexical, parents, binding_cache)
        if ordered is None:
            if call_head_is_shadowed(node, lexical, scopes):
                continue
            record = resolve_import_binding(imports, parents, node, name)
            if name == 'open' and record is None:
                modules[id(node)] = 'builtins'
                continue
        else:
            state, record = ordered
            if state == 'custom':
                continue
            if state == 'deleted':
                if name == 'open':
                    modules[id(node)] = 'builtins'
                continue
            if state == 'none' and name == 'open' and record is None:
                modules[id(node)] = 'builtins'
                continue
        if not (isinstance(record, tuple) and len(record) == 3
                and record[0] == 'from' and record[2] == 'open'
                and record[1] in OPEN_FAMILY_MODULES):
            continue
        modules[id(node)] = record[1]
    return modules
class _B02Context(NamedTuple):
    managed_ids: set[int]
    escaped_ids: set[int]
    non_resource_open_ids: set[int]
    attr_handle_open_ids: set[int]
    inline_closed_ids: set[int]
    non_stdlib_os_call_ids: frozenset[int]
    open_call_modules: dict[int, str]
    os_aliases: frozenset[str]
    os_open_function_aliases: frozenset[str]
    os_close_function_aliases: frozenset[str]
    open_meta: dict
    bind_positions: dict
    fd_transfer_uses: dict
    with_uses: dict
    attr_close_uses: dict
    os_close_uses: dict
    return_uses: dict
    branch_of_pos: dict
def _b02_collect_context(tree: ast.Module) -> _B02Context:
    parents = parent_map(tree)
    os_aliases = _os_module_aliases(tree)
    os_open_aliases = _os_function_aliases(tree, 'open')
    open_name_aliases = open_family_aliases(tree)
    open_aliases = frozenset(open_name_aliases)
    open_call_modules = _open_family_name_call_modules(
        tree, open_name_aliases)
    os_close_aliases = _os_function_aliases(tree, 'close')
    os_fdopen_aliases = _os_function_aliases(tree, 'fdopen')
    alias_members = {
        name: member
        for member, aliases in (('open', os_open_aliases),
                                ('close', os_close_aliases),
                                ('fdopen', os_fdopen_aliases))
        for name in aliases
    }
    excluded_ids = _non_stdlib_os_call_ids(
        tree, os_aliases, alias_members)
    fd_owner_ids = _fd_owning_call_ids(tree, excluded_ids)
    open_meta, bind_positions = _collect_open_assigns(
        tree, parents, open_aliases)
    closing_ids = _contextlib_closing_call_ids(tree)
    with_uses = _collect_with_uses(
        tree, parents, fd_owner_ids, closing_ids, open_meta)
    attr_close_uses, os_close_uses = _collect_close_uses(
        tree, parents, os_aliases, os_close_aliases, excluded_ids)
    return_uses = _collect_return_uses(tree, parents, closing_ids)
    branch_of_pos = _b02_branch_ranges(tree)
    # fd 转移是否成立取决于 fdopen 返回对象的接管情况，必须在
    # with/close/return 使用点收集完成之后再判定。
    fd_transfer_uses = _collect_fd_transfer_uses(
        tree, parents, os_aliases, os_fdopen_aliases, fd_owner_ids,
        closing_ids, with_uses, attr_close_uses, return_uses,
        bind_positions, branch_of_pos)
    _propagate_fd_owner_uses(
        tree, parents, fd_owner_ids, open_meta, os_aliases,
        os_open_aliases, bind_positions,
        with_uses, attr_close_uses, os_close_uses, return_uses)
    return _B02Context(
        managed_ids=_collect_with_managed_open_ids(
            tree, os_aliases, open_aliases, excluded_ids, fd_owner_ids,
            closing_ids),
        escaped_ids=_collect_escaped_open_ids(
            tree, open_aliases, closing_ids, fd_owner_ids),
        non_resource_open_ids=(
            _collect_non_resource_open_ids(tree)
            | _non_path_factory_open_ids(tree)),
        attr_handle_open_ids=_collect_attr_handle_open_ids(
            tree, open_aliases),
        inline_closed_ids=_collect_inline_closed_open_ids(
            tree, os_aliases, open_aliases, os_close_aliases,
            open_call_modules, excluded_ids),
        non_stdlib_os_call_ids=excluded_ids,
        open_call_modules=open_call_modules,
        os_aliases=os_aliases,
        os_open_function_aliases=os_open_aliases,
        os_close_function_aliases=os_close_aliases,
        open_meta=open_meta,
        bind_positions=bind_positions,
        fd_transfer_uses=fd_transfer_uses,
        with_uses=with_uses,
        attr_close_uses=attr_close_uses,
        os_close_uses=os_close_uses,
        return_uses=return_uses,
        branch_of_pos=branch_of_pos,
    )
def _inline_escaped_open_id(
        node: ast.AST, os_open_aliases: frozenset[str]) -> int | None:
    if (isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension))
            and isinstance(node.iter, ast.Call)
            and (_is_open_call(node.iter)
                 or _is_os_open_name_call(node.iter, os_open_aliases))):
        return id(node.iter)
    return None
def _returned_value_open_ids(
        value: ast.AST, os_open_aliases: frozenset[str],
        closing_ids: frozenset[int], fd_owner_ids: frozenset[int]) -> set[int]:
    if isinstance(value, ast.Call):
        if (_is_open_call(value)
                or _is_os_open_name_call(value, os_open_aliases)):
            return {id(value)}
        managed = _closing_managed_value(value, closing_ids)
        if managed is not None:
            return _returned_value_open_ids(
                managed, os_open_aliases, closing_ids, fd_owner_ids)
        if id(value) in fd_owner_ids and value.args:
            return _returned_value_open_ids(
                value.args[0], os_open_aliases, closing_ids, fd_owner_ids)
        return set()
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        children = value.elts
    elif isinstance(value, ast.Dict):
        children = [*value.keys, *value.values]
    elif isinstance(value, ast.IfExp):
        children = (value.body, value.orelse)
    elif isinstance(value, ast.BoolOp):
        children = value.values
    elif isinstance(value, (ast.NamedExpr, ast.Starred)):
        children = (value.value,)
    elif isinstance(value, ast.Lambda):
        children = (value.body,)
    else:
        return set()
    return {
        open_id
        for child in children if child is not None
        for open_id in _returned_value_open_ids(
            child, os_open_aliases, closing_ids, fd_owner_ids)
    }
def _returned_escaped_open_ids(
        node: ast.AST, os_open_aliases: frozenset[str],
        closing_ids: frozenset[int], fd_owner_ids: frozenset[int]) -> set[int]:
    if not (isinstance(node, (ast.Return, ast.Yield, ast.YieldFrom))
            and node.value is not None):
        return set()
    return _returned_value_open_ids(
        node.value, os_open_aliases, closing_ids, fd_owner_ids)
def _collect_escaped_open_ids(
        tree: ast.Module, os_open_aliases: frozenset[str],
        closing_ids: frozenset[int], fd_owner_ids: frozenset[int]) -> set[int]:
    escaped: set[int] = set()
    for node in tree_nodes(tree):
        inline_id = _inline_escaped_open_id(node, os_open_aliases)
        if inline_id is not None:
            escaped.add(inline_id)
        escaped.update(_returned_escaped_open_ids(
            node, os_open_aliases, closing_ids, fd_owner_ids))
    return escaped
def _is_os_open_call(node: ast.Call,
                     os_aliases: frozenset[str]) -> bool:
    return (isinstance(node.func, ast.Attribute)
            and node.func.attr == 'open'
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in os_aliases)
def _b02_is_os_open(node: ast.Call, ctx: _B02Context) -> bool:
    alias_module = ctx.open_call_modules.get(id(node))
    if alias_module is not None:
        return alias_module == 'os'
    return (_is_os_open_call(node, ctx.os_aliases)
            or _is_os_open_name_call(node, ctx.os_open_function_aliases))
def _b02_classify_open(node: ast.Call, ctx: _B02Context) -> DiagnoseIssue | None:
    node_id = id(node)
    if (node_id in ctx.managed_ids or node_id in ctx.escaped_ids
            or node_id in ctx.non_resource_open_ids
            or node_id in ctx.inline_closed_ids):
        return None
    if _b02_managed_by(node_id, ctx.with_uses, ctx.open_meta,
                       ctx.bind_positions, ctx.branch_of_pos):
        return None
    if node_id in ctx.attr_handle_open_ids:
        return None
    if _b02_managed_by(node_id, ctx.return_uses, ctx.open_meta,
                       ctx.bind_positions, ctx.branch_of_pos):
        return None
    is_os_open = _b02_is_os_open(node, ctx)
    if is_os_open and _b02_managed_by(
            node_id, ctx.fd_transfer_uses, ctx.open_meta,
            ctx.bind_positions, ctx.branch_of_pos):
        return None
    close_uses = ctx.os_close_uses if is_os_open else ctx.attr_close_uses
    manually_closed = _b02_managed_by(
        node_id, close_uses, ctx.open_meta, ctx.bind_positions,
        ctx.branch_of_pos)
    if manually_closed:
        if is_os_open:
            return _issue(
                'B02', DiagnoseSeverity.WARN,
                'os.open() 已手动 os.close()，但未使用 finally 保护异常路径',
                node.lineno, '在 finally 中调用 os.close(fd)，避免异常路径泄漏')
        return _issue(
            'B02', DiagnoseSeverity.WARN,
            'open() 已手动 close，但建议改用 with 上下文管理以避免异常路径泄漏',
            node.lineno, '改用 with open(...) as f: 更安全')
    if is_os_open:
        return _issue(
            'B02', DiagnoseSeverity.ERROR,
            '资源泄漏: os.open() 返回的文件描述符未关闭',
            node.lineno,
            '在 finally 中调用 os.close(fd)；os.open 的 fd 不支持 with 协议')
    return _issue(
        'B02', DiagnoseSeverity.ERROR,
        '资源泄漏: open() 未使用 with 上下文管理，文件可能未关闭',
        node.lineno, '使用 with open(...) as f: 确保资源释放')
def _non_stdlib_os_call_ids(
        tree: ast.Module, os_aliases: frozenset[str],
        alias_members: dict[str, str]) -> frozenset[int]:
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    excluded: set[int] = set()
    binding_cache: dict = {}
    for node, _scope in lexical.calls:
        expected = None
        root = None
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in {'open', 'close', 'fdopen'}
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in os_aliases):
            root = node.func.value.id
            expected = ('import', 'os')
        elif isinstance(node.func, ast.Name) and node.func.id in alias_members:
            root = node.func.id
            expected = ('from', 'os', alias_members[root])
        if root is None:
            continue
        ordered = _ordered_name_binding(
            node, root, _scope, lexical, parents, binding_cache)
        if ordered is None:
            rec = resolve_import_binding(imports, parents, node, root)
            shadowed = call_head_is_shadowed(node, lexical, scopes)
        else:
            state, rec = ordered
            shadowed = state in {'custom', 'deleted'}
        if shadowed or (rec is not None and rec != expected):
            excluded.add(id(node))
    return frozenset(excluded)
def detect_b02_resource_leak(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    if tree is None:
        return []
    issues = []
    ctx = _b02_collect_context(tree)
    verified_alias_ids = set(ctx.open_call_modules)
    shadowed_ids = ((non_builtin_open_call_ids(tree)
                     - _deleted_open_family_call_ids(tree))
                    | (ctx.non_stdlib_os_call_ids - verified_alias_ids))
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if not (_is_open_call(node) or id(node) in verified_alias_ids):
            continue
        if id(node) in shadowed_ids:
            continue
        issue = _b02_classify_open(node, ctx)
        if issue is not None:
            issues.append(issue)
    return _finish('B02 资源泄漏', issues, filepath)
_NO_ENCODING_TEXT_MODULES = frozenset({'gzip', 'bz2', 'lzma'})
_MEMBER_ENCODING_OPEN_MODULES = frozenset({'tarfile'})
_AUTO_ENCODING_OPEN_MODULES = frozenset({'tokenize'})
_NO_ENCODING_PARAM_OPEN_MODULES = frozenset({'zipfile'})
_ENCODING_ARG_INDEX_DEFAULT = 3
_ENCODING_ARG_INDEX_BY_MODULE: dict[str, int] = {'codecs': 2}
_PATH_OPEN_ENCODING_ARG_INDEX = 2
_MODE_ARG_INDEX_DEFAULT = 1
_PATH_OPEN_MODE_ARG_INDEX = 0
_B26_RECEIVER_MODULES = OPEN_FAMILY_MODULES | frozenset({'pathlib'})
def _b26_open_module_aliases(tree: ast.Module) -> dict[str, str]:
    aliases: dict[str, str] = {}
    for module in sorted(_B26_RECEIVER_MODULES):
        names, _bare = collect_module_bindings(tree, module, ())
        for name in names:
            aliases[name] = module
    return aliases
def _b26_receiver_module(
        func: ast.expr, module_aliases: dict[str, str],
        function_aliases: dict[str, str]) -> str | None:
    if isinstance(func, ast.Name):
        return function_aliases.get(func.id)
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return module_aliases.get(func.value.id)
    return None
def _b26_is_open_call(call: ast.Call,
                      function_aliases: dict[str, str]) -> bool:
    return ((isinstance(call.func, ast.Name)
             and call.func.id in function_aliases)
            or _is_open_call(call))
def _mode_arg_index(call_node: ast.Call) -> int:
    func = call_node.func
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Call):
        return _PATH_OPEN_MODE_ARG_INDEX
    return _MODE_ARG_INDEX_DEFAULT
def _encoding_arg_index(call_node: ast.Call,
                        receiver_module: str | None = None) -> int:
    func = call_node.func
    if isinstance(func, ast.Name):
        return _ENCODING_ARG_INDEX_BY_MODULE.get(
            receiver_module, _ENCODING_ARG_INDEX_DEFAULT)
    if isinstance(func, ast.Attribute):
        if isinstance(func.value, ast.Name):
            module = receiver_module or func.value.id
            return _ENCODING_ARG_INDEX_BY_MODULE.get(
                module, _ENCODING_ARG_INDEX_DEFAULT)
        if isinstance(func.value, ast.Call):
            return _PATH_OPEN_ENCODING_ARG_INDEX
    return _ENCODING_ARG_INDEX_DEFAULT
def _b26_path_constructor_names(tree: ast.Module) -> frozenset[str]:
    _aliases, imported = collect_module_bindings(tree, 'pathlib', ('Path',))
    return frozenset(imported)
def _is_decidable_text_open_receiver(
        recv: ast.AST, module_aliases: dict[str, str],
        path_constructors: frozenset[str]) -> bool:
    if isinstance(recv, ast.Name):
        return module_aliases.get(recv.id) in _B26_RECEIVER_MODULES
    if isinstance(recv, ast.Call):
        ctor = recv.func
        if isinstance(ctor, ast.Name):
            return ctor.id in path_constructors
        return (isinstance(ctor, ast.Attribute)
                and isinstance(ctor.value, ast.Name)
                and module_aliases.get(ctor.value.id) == 'pathlib'
                and ctor.attr == 'Path')
    return False
def _open_call_mode(call_node: ast.Call) -> str | None:
    mode = None
    _idx = _mode_arg_index(call_node)
    if (len(call_node.args) > _idx
            and isinstance(call_node.args[_idx], ast.Constant)
            and isinstance(call_node.args[_idx].value, str)):
        mode = call_node.args[_idx].value
    for kw in call_node.keywords:
        if kw.arg == 'mode' and isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
            mode = kw.value.value
    return mode
def _open_family_encoding_exempt(
        receiver_module: str | None, mode: str | None) -> bool:
    _recv_mod = receiver_module
    if _recv_mod in _MEMBER_ENCODING_OPEN_MODULES:
        return True
    if _recv_mod in _AUTO_ENCODING_OPEN_MODULES:
        return True
    if _recv_mod in _NO_ENCODING_PARAM_OPEN_MODULES:
        return True
    return (_recv_mod in _NO_ENCODING_TEXT_MODULES
            and (mode is None or 't' not in mode))
def _b26_receiver_decidable(
        func: ast.expr, module_aliases: dict[str, str],
        path_constructors: frozenset[str]) -> bool:
    return (isinstance(func, ast.Name)
            or _is_decidable_text_open_receiver(
                func.value, module_aliases, path_constructors))
def _b26_encoding_unspecified(value: ast.AST | None) -> bool:
    return value is None or (isinstance(value, ast.Constant)
                             and value.value is None)
def _b26_declares_encoding(node: ast.Call) -> bool:
    for kw in node.keywords:
        if kw.arg == 'encoding':
            return not _b26_encoding_unspecified(kw.value)
    return False
def _b26_has_positional_encoding(
        node: ast.Call, receiver_module: str | None) -> bool:
    idx = _encoding_arg_index(node, receiver_module)
    if len(node.args) <= idx:
        return False
    return not _b26_encoding_unspecified(node.args[idx])
class _B26Context(NamedTuple):
    shadowed_ids: frozenset[int]
    os_aliases: frozenset[str]
    module_aliases: dict[str, str]
    function_aliases: dict[str, str]
    path_constructors: frozenset[str]
    lexical: Any
    scopes: dict[int, ast.AST]
    imports: dict
    parents: dict
    binding_cache: dict
def _b26_collect_context(tree: ast.Module) -> _B26Context:
    lexical = collect_lexical_scope_table(tree)
    return _B26Context(
        shadowed_ids=(non_builtin_open_call_ids(tree)
                      - _deleted_open_family_call_ids(tree)),
        os_aliases=_os_module_aliases(tree),
        module_aliases=_b26_open_module_aliases(tree),
        function_aliases=open_family_aliases(tree),
        path_constructors=_b26_path_constructor_names(tree),
        lexical=lexical,
        scopes=call_scope_map(lexical),
        imports=scope_import_tables(tree),
        parents=parent_map(tree),
        binding_cache={},
    )
def _b26_receiver_binding(
        call: ast.Call, module_aliases: dict[str, str],
        function_aliases: dict[str, str],
        path_constructors: frozenset[str],
) -> tuple[ast.AST, str, tuple] | None:
    func = call.func
    if isinstance(func, ast.Name):
        module = function_aliases.get(func.id)
        if module is None:
            return None
        return call, func.id, ('from', module, 'open')
    recv = func.value
    if isinstance(recv, ast.Name):
        module = module_aliases.get(recv.id)
        return (call, recv.id, ('import', module)) if module else None
    if isinstance(recv, ast.Call):
        ctor = recv.func
        if isinstance(ctor, ast.Name) and ctor.id in path_constructors:
            return recv, ctor.id, ('from', 'pathlib', 'Path')
        if (isinstance(ctor, ast.Attribute) and ctor.attr == 'Path'
                and isinstance(ctor.value, ast.Name)
                and module_aliases.get(ctor.value.id) == 'pathlib'):
            return recv, ctor.value.id, ('import', 'pathlib')
    return None
def _b26_open_module_from_record(record: tuple, expected: tuple) -> str | None:
    if (len(expected) == 2 and expected[0] == 'import'
            and len(record) == 2 and record[0] == 'import'
            and record[1] in _B26_RECEIVER_MODULES):
        return record[1]
    if (len(expected) == 3 and expected[0] == 'from'
            and expected[2] == 'open' and len(record) == 3
            and record[0] == 'from' and record[2] == 'open'
            and record[1] in _B26_RECEIVER_MODULES):
        return record[1]
    return None
def _b26_resolve_receiver_module(
        call: ast.Call, ctx: _B26Context) -> tuple[str | None, bool]:
    fallback = _b26_receiver_module(
        call.func, ctx.module_aliases, ctx.function_aliases)
    binding = _b26_receiver_binding(
        call, ctx.module_aliases, ctx.function_aliases,
        ctx.path_constructors)
    if binding is None:
        return fallback, True
    query, name, expected = binding
    ordered = _ordered_name_binding(
        query, name, ctx.scopes.get(id(query)), ctx.lexical, ctx.parents,
        ctx.binding_cache)
    if ordered is None:
        if call_head_is_shadowed(query, ctx.lexical, ctx.scopes):
            return fallback, False
        record = resolve_import_binding(ctx.imports, ctx.parents, query, name)
    else:
        state, record = ordered
        if state == 'custom' or (
                state == 'deleted'
                and not (isinstance(call.func, ast.Name)
                         and call.func.id == 'open')):
            return fallback, False
    if record == expected:
        return fallback, True
    if record is not None:
        resolved = _b26_open_module_from_record(record, expected)
        return (resolved, True) if resolved is not None else (fallback, False)
    func = call.func
    if isinstance(func, ast.Name):
        return (None, True) if func.id == 'open' else (fallback, False)
    recv = func.value
    if isinstance(recv, ast.Name):
        return (fallback, recv.id == fallback)
    if isinstance(recv, ast.Call):
        ctor = recv.func
        if isinstance(ctor, ast.Name):
            return fallback, ctor.id == 'Path'
        if (isinstance(ctor, ast.Attribute)
                and isinstance(ctor.value, ast.Name)):
            return fallback, ctor.value.id == 'pathlib'
    return fallback, False
def _b26_should_report(node: ast.Call, ctx: _B26Context) -> bool:
    if not _b26_is_open_call(node, ctx.function_aliases):
        return False
    if id(node) in ctx.shadowed_ids:
        return False
    if (any(isinstance(arg, ast.Starred) for arg in node.args)
            or any(kw.arg is None for kw in node.keywords)):
        return False
    if not _b26_receiver_decidable(
            node.func, ctx.module_aliases, ctx.path_constructors):
        return False
    receiver_module, receiver_resolved = _b26_resolve_receiver_module(node, ctx)
    if not receiver_resolved:
        return False
    if receiver_module == 'os' or _is_os_open_call(node, ctx.os_aliases):
        return False
    if _b26_declares_encoding(node):
        return False
    if _b26_has_positional_encoding(node, receiver_module):
        return False
    mode = _open_call_mode(node)
    if mode and 'b' in mode:
        return False
    return not _open_family_encoding_exempt(receiver_module, mode)
def _b26_open_calls_missing_encoding(tree: ast.Module) -> list[ast.Call]:
    ctx = _b26_collect_context(tree)
    return [
        node for node in tree_nodes(tree)
        if isinstance(node, ast.Call) and _b26_should_report(node, ctx)]
def detect_b26_missing_encoding(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    if tree is None:
        return []
    issues = []
    for node in _b26_open_calls_missing_encoding(tree):
        issues.append(_issue(
            'B26', DiagnoseSeverity.WARN,
            '文件打开未指定 encoding，跨平台默认编码不一致'
            '（Windows GBK / Linux UTF-8）可能导致乱码',
            node.lineno, '显式指定 encoding="utf-8"（或文件实际编码）'))
    return _finish('B26 未指定 encoding', issues, filepath)
def detect_b03_bare_except(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for node in tree_nodes(tree):
        if isinstance(node, ast.ExceptHandler) and node.type is None:
            issues.append(_issue(
                'B03', DiagnoseSeverity.WARN,
                '裸 except: 未指定异常类型，会捕获 KeyboardInterrupt/SystemExit 等所有异常',
                node.lineno,
                '明确捕获具体异常类型（如 except (ValueError, KeyError)）'))
    return _finish('B03 裸 except', issues, filepath)
def _iter_finally_flow_nodes(stmt: ast.stmt) -> Iterator[ast.AST]:
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return
    for inner in (stmt, *same_scope_bfs_nodes(stmt)):
        if isinstance(inner, (ast.Return, ast.Break, ast.Continue)):
            yield inner
def _b04_crosses_try_boundary(inner: ast.AST, try_node: ast.AST, parents: dict) -> bool:
    cur = inner
    while cur is not try_node and cur is not None:
        cur = parents.get(cur)
        if isinstance(cur, (ast.For, ast.AsyncFor, ast.While)):
            return False
    return True
def _scan_finally_control_flow(try_node: ast.AST, parents: dict, seen: set[int]) -> list[DiagnoseIssue]:
    found: list[DiagnoseIssue] = []
    for stmt in try_node.finalbody:
        for inner in _iter_finally_flow_nodes(stmt):
            if id(inner) in seen:
                continue
            if (isinstance(inner, (ast.Break, ast.Continue))
                    and not _b04_crosses_try_boundary(inner, try_node, parents)):
                continue
            seen.add(id(inner))
            found.append(_issue(
                'B04', DiagnoseSeverity.ERROR,
                f'finally 块中的 {type(inner).__name__.lower()}: 会吞掉异常或改变控制流',
                inner.lineno, '避免在 finally 中使用 return/break/continue'))
    return found
def detect_b04_finally_control_flow(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    _parents = parent_map(tree)
    seen: set[int] = set()
    for node in tree_nodes(tree):
        if isinstance(node, (ast.Try, TRY_STAR)):
            issues.extend(_scan_finally_control_flow(node, _parents, seen))
    return _finish('B04 finally 控制流', issues, filepath)
def _b13_is_placeholder_stmt(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, (ast.Pass, ast.Continue))
            or (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and stmt.value.value is ...))
def _b13_silent_state(handler: ast.ExceptHandler) -> str | None:
    body = [s for s in handler.body if not is_docstring_stmt(s)]
    if not body:
        return 'empty'
    if all(_b13_is_placeholder_stmt(s) for s in body):
        return 'placeholder'
    return None
_B13_SILENT_FORMS: dict[str, tuple[str, str]] = {
    'empty': ('异常被静默吞掉: except 块为空，掩盖真实错误',
              '至少记录日志或重新抛出（raise），避免无声失败'),
    'placeholder': ('异常被静默吞掉: except 块仅含 pass/continue/... 占位，掩盖真实错误',
                    '记录日志或重新抛出，避免无声失败'),
}
def detect_b13_swallowed_exception(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.ExceptHandler):
            continue
        state = _b13_silent_state(node)
        if state is None:
            continue
        message, suggestion = _B13_SILENT_FORMS[state]
        issues.append(_issue('B13', DiagnoseSeverity.WARN, message,
                             node.lineno, suggestion))
    return _finish('B13 静默吞异常', issues, filepath)
def _b25_loses_chain(raise_node: ast.Raise,
                     active_exception_names: frozenset[str]) -> bool:
    if raise_node.cause is not None or raise_node.exc is None:
        return False
    if isinstance(raise_node.exc, ast.Name):
        return raise_node.exc.id not in active_exception_names
    if isinstance(raise_node.exc, ast.Call):
        func = raise_node.exc.func
        return not (isinstance(func, ast.Attribute)
                    and func.attr == 'with_traceback'
                    and isinstance(func.value, ast.Name)
                    and func.value.id in active_exception_names)
    return False
def _b25_active_handler_names(node: ast.AST,
                              parents: dict) -> frozenset[str] | None:
    names: set[str] = set()
    inside_handler = False
    cur: ast.AST | None = node
    while cur is not None:
        cur = parents.get(cur)
        if isinstance(cur, ast.ExceptHandler):
            inside_handler = True
            if cur.name:
                names.add(cur.name)
        elif isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            break
    return frozenset(names) if inside_handler else None
def detect_b25_exception_chain_lost(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    if tree is None:
        return []
    issues = []
    parents = parent_map(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Raise):
            continue
        active_names = _b25_active_handler_names(node, parents)
        if active_names is None:
            continue
        if not _b25_loses_chain(node, active_names):
            continue
        issues.append(_issue(
            'B25', DiagnoseSeverity.WARN,
            '异常链丢失: except 块内 raise 新异常未使用 from 保留原始异常上下文',
            node.lineno,
            '使用 raise NewError(...) from e 保留原始异常链，便于追溯根因'))
    return _finish('B25 异常链丢失', issues, filepath)
def _not_implemented_scope(node: ast.AST, lexical: Any,
                           parents: dict) -> ast.AST | None:
    scope = node
    while scope is not None and scope not in lexical.bound:
        scope = parents.get(scope)
    return scope
def _builtin_not_implemented_ids(
        tree: ast.Module, lexical: Any, parents: dict) -> frozenset[int]:
    imports = scope_import_tables(tree)
    ids: set[int] = set()
    binding_cache: dict = {}
    for node in tree_nodes(tree):
        if isinstance(node, ast.Name):
            name = node.id
            scope = _not_implemented_scope(node, lexical, parents)
            ordered = (_ordered_name_binding(
                node, name, scope, lexical, parents, binding_cache)
                if scope is not None else None)
            if ordered is None:
                record = resolve_import_binding(imports, parents, node, name)
            else:
                state, record = ordered
                if state == 'custom':
                    continue
            if name == 'NotImplemented' and record is None:
                if ordered is not None or (
                        scope is not None and not scope_shadows_name(
                            lexical, scope, name)):
                    ids.add(id(node))
                continue
            expected = ('from', 'builtins', 'NotImplemented')
        elif (isinstance(node, ast.Attribute)
              and node.attr == 'NotImplemented'
              and isinstance(node.value, ast.Name)):
            name = node.value.id
            scope = _not_implemented_scope(node, lexical, parents)
            ordered = (_ordered_name_binding(
                node, name, scope, lexical, parents, binding_cache)
                if scope is not None else None)
            if ordered is None:
                record = resolve_import_binding(imports, parents, node, name)
            else:
                state, record = ordered
                if state == 'custom':
                    continue
            expected = ('import', 'builtins')
        else:
            continue
        if record != expected:
            continue
        if ordered is not None:
            ids.add(id(node))
            continue
        scope = _not_implemented_scope(node, lexical, parents)
        if (scope is not None and not scope_shadows_import(
                lexical, scope, name)):
            ids.add(id(node))
    return frozenset(ids)
def detect_b40_raise_non_exception(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    if tree is None:
        return []
    lexical = collect_lexical_scope_table(tree)
    parents = parent_map(tree)
    builtin_ni_ids = _builtin_not_implemented_ids(tree, lexical, parents)
    issues = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Raise) or node.exc is None:
            continue
        exc = node.exc
        hit = _b40_non_exception_hit(exc, builtin_ni_ids)
        if hit is not None:
            issues.append(_issue(
                'B40', DiagnoseSeverity.ERROR,
                f'raise {hit}——exceptions must derive from BaseException，'
                f'一执行即 TypeError',
                exc.lineno,
                'raise 具体异常实例（如 raise ValueError("...")）；'
                '意图标记未实现应为 raise NotImplementedError'))
    return _finish('B40 raise 非异常对象', issues, filepath)
def _is_literal_expr(node: ast.AST) -> bool:
    if isinstance(node, (ast.Constant, ast.JoinedStr, ast.List,
                         ast.Set, ast.Dict, ast.Tuple)):
        return True
    if isinstance(node, ast.UnaryOp):
        return _is_literal_expr(node.operand)
    if isinstance(node, ast.BinOp):
        return _is_literal_expr(node.left) and _is_literal_expr(node.right)
    return False
def _non_exception_literal_kind(
        node: ast.AST, builtin_ni_ids: frozenset[int]) -> str | None:
    if isinstance(node, ast.Call) and id(node.func) in builtin_ni_ids:
        return 'not_implemented_call'
    if id(node) in builtin_ni_ids:
        return 'not_implemented_name'
    if isinstance(node, ast.Constant):
        return 'constant'
    if isinstance(node, ast.JoinedStr):
        return 'fstring'
    if isinstance(node, ast.Tuple):
        return 'tuple'
    if isinstance(node, ast.List):
        return 'list'
    if isinstance(node, ast.Set):
        return 'set'
    if isinstance(node, ast.Dict):
        return 'dict'
    if isinstance(node, ast.UnaryOp) and _is_literal_expr(node.operand):
        return 'unary'
    if isinstance(node, ast.BinOp) and _is_literal_expr(node):
        return 'binary'
    return None
def _b40_non_exception_hit(
        exc: ast.expr, builtin_ni_ids: frozenset[int]) -> str | None:
    kind = _non_exception_literal_kind(exc, builtin_ni_ids)
    if kind is None:
        return None
    if kind == 'constant':
        return f'{exc.value!r}（{type(exc.value).__name__} 字面量）'
    if kind == 'fstring':
        return 'f-string 字面量（str）'
    if kind == 'not_implemented_call':
        return 'NotImplemented()（内建单例不可调用，非异常对象）'
    if kind == 'not_implemented_name':
        return 'NotImplemented（内建单例，非异常类）'
    if kind == 'unary':
        return '一元运算字面量（非异常对象）'
    if kind == 'binary':
        return '二元运算字面量（非异常对象）'
    return f'{kind} 字面量'
def _b46_bad_type_element(
        el: ast.AST, builtin_ni_ids: frozenset[int]) -> str | None:
    kind = _non_exception_literal_kind(el, builtin_ni_ids)
    if kind is None:
        return None
    if kind == 'constant':
        return f'{el.value!r}（字面量）'
    if kind == 'fstring':
        return 'f-string 字面量'
    if kind == 'tuple':
        return '嵌套元组（捕获元组不支持嵌套）'
    if kind == 'not_implemented_name':
        return 'NotImplemented（非异常类）'
    if kind == 'not_implemented_call':
        return 'NotImplemented()（不可调用，非异常类）'
    if kind == 'unary':
        return '一元运算字面量（非异常类）'
    if kind == 'binary':
        return '二元运算字面量（非异常类）'
    return f'{kind} 字面量'
def detect_b46_except_invalid_handler_type(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    if tree is None:
        return []
    lexical = collect_lexical_scope_table(tree)
    parents = parent_map(tree)
    builtin_ni_ids = _builtin_not_implemented_ids(tree, lexical, parents)
    issues = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.ExceptHandler) or node.type is None:
            continue
        for bad, line, in_tuple in _b46_iter_bad_elements(
                node.type, builtin_ni_ids):
            message = (f'except 元组元素为 {bad}——捕获非异常类一执行即 TypeError'
                       if in_tuple else
                       f'except 类型为 {bad}——catching classes that do not '
                       f'inherit from BaseException，一执行即 TypeError')
            suggestion = ('except 子句只放异常类（派生自 BaseException）'
                          if in_tuple else 'except 子句只放异常类或异常类元组')
            issues.append(_issue('B46', DiagnoseSeverity.ERROR, message,
                                 line, suggestion))
    return _finish('B46 except 非法类型', issues, filepath)
def _b46_iter_bad_elements(handler_type: ast.expr,
                           builtin_ni_ids: frozenset[int]):
    if isinstance(handler_type, ast.Tuple):
        for el in handler_type.elts:
            bad = _b46_bad_type_element(el, builtin_ni_ids)
            if bad is not None:
                yield bad, el.lineno, True
        return
    bad = _b46_bad_type_element(handler_type, builtin_ni_ids)
    if bad is not None:
        yield bad, handler_type.lineno, False
def _b58_try_body_guarantees_exception(
        try_node: ast.Try, parents: dict) -> bool:
    # try 正常路径与每个 handler 都以 raise 结束时，finally 始终有活动异常；
    # 未匹配的 handler 则让原异常直接传播到 finally。
    bodies = [try_node.body, *(handler.body for handler in try_node.handlers)]
    for raw_body in bodies:
        body = [stmt for stmt in raw_body if not is_docstring_stmt(stmt)]
        if not body or not isinstance(body[-1], ast.Raise):
            return False
        for stmt in body[:-1]:
            for inner in _iter_finally_flow_nodes(stmt):
                if isinstance(inner, ast.Return):
                    return False
                if (isinstance(inner, (ast.Break, ast.Continue))
                        and _b04_crosses_try_boundary(inner, try_node, parents)):
                    return False
    return True
def detect_b58_bare_raise_outside_except(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    _pm = parent_map(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Raise) or node.exc is not None:
            continue
        cur = node
        protected = False
        while cur in _pm:
            child = cur
            cur = _pm[cur]
            if isinstance(cur, ast.ExceptHandler):
                protected = True
                break
            if (isinstance(cur, (ast.Try, TRY_STAR))
                    and child in cur.finalbody
                    and _b58_try_body_guarantees_exception(cur, _pm)):
                protected = True
                break
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
                break
        if protected:
            continue
        issues.append(_issue(
            'B58', DiagnoseSeverity.ERROR,
            '裸 raise 在 except 上下文外：执行即 RuntimeError: '
            'No active exception to re-raise',
            node.lineno,
            '裸 raise 只放 except 子句内（原样再抛出）；'
            '上下文外请 raise 具体异常实例'))
    return _finish('B58 裸 raise 上下文外', issues, filepath)
GATE_DETECTORS: dict[str, Any] = {
    "B02": detect_b02_resource_leak,
    "B03": detect_b03_bare_except,
    "B04": detect_b04_finally_control_flow,
    "B13": detect_b13_swallowed_exception,
    "B25": detect_b25_exception_chain_lost,
    "B26": detect_b26_missing_encoding,
    "B40": detect_b40_raise_non_exception,
    "B46": detect_b46_except_invalid_handler_type,
    "B58": detect_b58_bare_raise_outside_except,
}
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            "DC01": check_DC01, "DC03": check_DC03,
            "IO04": check_IO04, "IO05": check_IO05,
        },
        "diag4_direct": {"DC-03": check_DC03},
        "gate_adapter_bindings": {
            "RB03": (detect_b02_resource_leak, "RB-03"),
            "RB04": (detect_b03_bare_except, "RB-04"),
            "RB11": (detect_b02_resource_leak, "RB-11"),
        },
    }}

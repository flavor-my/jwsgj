from __future__ import annotations  # noqa: I001
import ast
import logging
import re
import string
from typing import Any, NamedTuple
from jwsgj.diag_shared_ast_nodes import (
    argument_param_names,
    as_format_call,
    assign_targets_value,
    build_parent_map,
    collect_param_names,
    dotted_name,
    get_call_name,
    iter_target_bindings,
    pattern_capture_name,
    str_constant_value,
)
from jwsgj.diag_shared_ast_views import (
    collect_module_bindings,
    collect_module_bindings_detailed,
    iter_nodes,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    extract_code_lines,
    join_source_lines,
)
from jwsgj.diag_shared_source_scan import (
    get_code_snippet,
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    SUBPROCESS_CHECK_CALL,
    SUBPROCESS_CHECK_OUTPUT,
)
from jwsgj.fix_guide_rule_identity import get_fix_guidance
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    "check_PT01",
    "check_SE02",
    "check_SE05",
    "check_SE06",
    "check_SE08",
    "check_SE20",
    "check_SE30b",
    "check_SE35",
    "check_SE37",
    "wiring_declarations",
]
_log = logging.getLogger(__name__)
_log.info("diag_se_injection 已加载: %d 项导出", len(__all__))
_SUBPROCESS_SHELL_FUNCS_QUALIFIED = frozenset({
    'subprocess.run', 'subprocess.Popen', 'subprocess.call',
    SUBPROCESS_CHECK_OUTPUT, SUBPROCESS_CHECK_CALL,
})
_SUBPROCESS_SHELL_FUNCS_BARE = frozenset(
    name.rsplit('.', 1)[-1] for name in _SUBPROCESS_SHELL_FUNCS_QUALIFIED)
_OS_SHELL_MEMBERS = frozenset({"system", "popen"})
def _se02_finding(node: ast.Call, member: str, source: Any,
                  filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id='SE-02', severity='P0', dimension='security', file=filepath,
        line=node.lineno,
        message='os.' + member + '() 命令恒经 shell 解释,存在命令注入风险',
        suggestion=('根因: 代码使用了不安全的函数或API, 存在安全风险。该问题属于安全类别。\n'
                    '修复策略: Use safe alternative\n'
                    + _OWASP_REF_LINE),
        code_snippet=get_code_snippet(source, node.lineno))
def _se02_shell_value(func: ast.AST, os_names: set, from_origins: dict,
                      bindings: dict | None = None,
                      scope_chains: dict | None = None) -> str | None:
    if isinstance(func, ast.Attribute):
        if (isinstance(func.value, ast.Name) and func.value.id in os_names
                and func.attr in _OS_SHELL_MEMBERS):
            return func.attr
        return None
    if not isinstance(func, ast.Name) or func.id in from_origins:
        return None
    if bindings is None or scope_chains is None:
        return None
    entry = _scoped_entry(
        bindings, func.id, scope_chains.get(id(func), ()),
        getattr(func, "lineno", 0) or 0,
        getattr(func, "col_offset", 0) or 0,
        enclosing_runtime=True)
    return entry[2] if entry is not None else None
def check_SE02(tree: Any, source: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _scope_chains = _build_scope_chains(tree) if tree is not None else {}
    _os_names, _os_origins = collect_module_bindings_detailed(
        tree, 'os', _OS_SHELL_MEMBERS)
    _os_bindings, _scope_chains = _assignment_member_bindings(
        tree, _os_names, _os_origins, _OS_SHELL_MEMBERS,
        scope_chains=_scope_chains, module='os')
    _os_lookup = _MemberLookup(
        _os_names, _os_origins, _OS_SHELL_MEMBERS,
        _os_bindings, _scope_chains)
    _shadowed = _shadowed_call_ids(
        tree, index,
        assignment_is_dangerous=lambda value: _rhs_member_origin(
            value, _os_lookup) is not None,
        import_is_dangerous=lambda node, alias: _import_matches(
            node, alias, 'os', _OS_SHELL_MEMBERS),
        scope_chains=_scope_chains)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call) or id(node) in _shadowed:
            continue
        member = _se02_shell_value(
            node.func, _os_names, _os_origins, _os_bindings, _scope_chains)
        if member is None:
            continue
        issues.append(_se02_finding(node, member, source, filepath))
    return issues
_OWASP_REF_LINE = '参考标准: OWASP Top 10 / CWE / Bandit'
_SE20_BUILTIN_MEMBERS = ('eval', 'exec')
_SE20_USER_INPUT_PATTERNS = frozenset(
    {"input", "request", "args", "argv", "getenv",
     "GET", "POST", "cookies", "headers", "data"})
_SE20_USER_INPUT_TOKENS = _SE20_USER_INPUT_PATTERNS - {"GET", "POST"}
_SE20_NAME_SPLIT = re.compile(r"[^A-Za-z0-9]+|(?<=[a-z0-9])(?=[A-Z])")
def _se20_name_is_user_input(name: str) -> bool:
    if name in _SE20_USER_INPUT_PATTERNS:
        return True
    return any(token.lower() in _SE20_USER_INPUT_TOKENS
               for token in _SE20_NAME_SPLIT.split(name) if token)
def _se20_suppress_map(source_lines: list | str) -> dict:
    if isinstance(source_lines, list):
        code_str = "\n".join(source_lines)
    elif isinstance(source_lines, str):
        code_str = source_lines
    else:
        code_str = ""
    try:
        return parse_suppressions(code_str)
    except (SyntaxError, ValueError):
        _log.debug("check_SE20: parse_suppressions failed", exc_info=True)
    except Exception:  # noqa: BLE001
        _log.warning("check_SE20: suppress map build failed", exc_info=True)
    return {}
def _se20_eval_exec_func(func: ast.AST, builtin_names: frozenset | set,
                         ) -> str | None:
    if not (isinstance(func, ast.Attribute)
            and func.attr in _SE20_BUILTIN_MEMBERS):
        return None
    if isinstance(func.value, ast.Name) and func.value.id in builtin_names:
        return func.attr
    return None
def _se20_eval_exec_name(node: ast.Call, lookup: _MemberLookup,
                         ) -> str | None:
    if isinstance(node.func, ast.Name):
        origin = _rhs_member_origin(node.func, lookup)
        return origin if origin in lookup.member_set else None
    return _se20_eval_exec_func(node.func, lookup.aliases)
def _se20_is_suppressed(suppress_map: dict, lineno: int) -> bool:
    if not suppress_map:
        return False
    try:
        return is_suppressed(suppress_map, lineno, "SE-20")
    except (KeyError, TypeError, AttributeError):
        _log.warning("check_SE20: is_suppressed lookup failed, "
                     "treat as not suppressed", exc_info=True)
        return False
def _se20_expr_is_user_input(value: ast.AST) -> bool:
    if isinstance(value, ast.Name):
        return _se20_name_is_user_input(value.id)
    if isinstance(value, ast.Call):
        cname = get_call_name(value)
        if cname and (
                _se20_name_is_user_input(cname)
                or _se20_name_is_user_input(cname.rsplit('.', 1)[-1])):
            return True
        return (any(_se20_expr_is_user_input(arg) for arg in value.args)
                or any(_se20_expr_is_user_input(kw.value)
                       for kw in value.keywords))
    if isinstance(value, ast.Attribute):
        return (_se20_name_is_user_input(value.attr)
                or _se20_expr_is_user_input(value.value))
    if isinstance(value, ast.Subscript):
        return (_se20_expr_is_user_input(value.value)
                or _se20_expr_is_user_input(value.slice))
    if isinstance(value, ast.JoinedStr):
        return any(isinstance(part, ast.FormattedValue)
                   and _se20_expr_is_user_input(part.value)
                   for part in value.values)
    if isinstance(value, ast.BinOp):
        return (_se20_expr_is_user_input(value.left)
                or _se20_expr_is_user_input(value.right))
    if isinstance(value, ast.BoolOp):
        return any(_se20_expr_is_user_input(item) for item in value.values)
    if isinstance(value, ast.IfExp):
        return (_se20_expr_is_user_input(value.body)
                or _se20_expr_is_user_input(value.orelse))
    if isinstance(value, ast.Starred):
        return _se20_expr_is_user_input(value.value)
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return any(_se20_expr_is_user_input(item) for item in value.elts)
    if isinstance(value, ast.Dict):
        return (any(key is not None and _se20_expr_is_user_input(key)
                    for key in value.keys)
                or any(_se20_expr_is_user_input(item) for item in value.values))
    if isinstance(value, ast.NamedExpr):
        return _se20_expr_is_user_input(value.value)
    if isinstance(value, ast.Await):
        return _se20_expr_is_user_input(value.value)
    return False
def _se20_user_input_arg(node: ast.Call) -> bool:
    return bool(node.args) and _se20_expr_is_user_input(node.args[0])
_SE20_ISSUE_TEMPLATES: dict[str, tuple[str, str]] = {
    "P0": (
        "%(name)s() 执行可能来自用户输入的代码, 存在 RCE 风险",
        "禁止对用户输入使用 %(name)s(); 使用 ast.literal_eval() 或白名单验证",
    ),
    "P2": (
        "%(name)s() 执行动态代码, 若输入不可信则存在 RCE 风险",
        "使用 ast.literal_eval() 替代; 或对输入进行严格白名单验证",
    ),
}
def _se20_issue(node: ast.Call, func_name: str, severity: str) -> dict:
    message, strategy = _SE20_ISSUE_TEMPLATES[severity]
    _render = {"name": func_name}
    return {
        "rule_id": "SE-20",
        "line": node.lineno,
        "severity": severity,
        "message": message % _render,
        "suggestion": (
            "根因: 代码使用了不规范或有风险的实现方式。该问题属于安全类别。\n"
            f"修复策略: {strategy % _render}\n"
            + _OWASP_REF_LINE
        ),
        "rule_ref": "OWASP Code Injection Prevention",
    }
def _se20_issue_for(node: ast.Call, suppress_map: dict,
                    lookup: _MemberLookup) -> dict | None:
    func_name = _se20_eval_exec_name(node, lookup)
    if func_name is None:
        return None
    if not node.args:
        return None
    if _se20_is_suppressed(suppress_map, node.lineno):
        return None
    if _se20_user_input_arg(node):
        return _se20_issue(node, func_name, "P0")
    if isinstance(node.args[0], ast.Constant):
        return None
    return _se20_issue(node, func_name, "P2")
def check_SE20(tree: ast.AST, source_lines: list, filepath: str, index: list | None=None) -> list:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _suppress_map = _se20_suppress_map(source_lines)
    _scope_chains = _build_scope_chains(tree) if tree is not None else {}
    _builtin_names, _builtin_origins = collect_module_bindings_detailed(
        tree, 'builtins', _SE20_BUILTIN_MEMBERS)
    _builtin_names = set(_builtin_names) | {"__builtins__"}
    _eval_bindings, _scope_chains = _assignment_member_bindings(
        tree, _builtin_names, _builtin_origins, _SE20_BUILTIN_MEMBERS,
        scope_chains=_scope_chains, builtin_direct=True, module='builtins')
    _builtin_lookup = _MemberLookup(
        _builtin_names, _builtin_origins, _SE20_BUILTIN_MEMBERS,
        _eval_bindings, _scope_chains, True)
    _shadowed = _shadowed_call_ids(
        tree, index,
        lambda value: _rhs_member_origin(value, _builtin_lookup) is not None,
        lambda node, alias: _import_matches(
            node, alias, 'builtins', _SE20_BUILTIN_MEMBERS),
        scope_chains=_scope_chains,
        deleted_bare_builtins=_SE20_BUILTIN_MEMBERS)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call) or id(node) in _shadowed:
            continue
        issue = _se20_issue_for(node, _suppress_map, _builtin_lookup)
        if issue is not None:
            issues.append(issue)
    return issues
def _import_matches(node: ast.AST, alias: ast.alias,
                    module: str, members: Any) -> bool:
    if isinstance(node, ast.ImportFrom):
        return (node.level == 0 and node.module == module
                and alias.name in members)
    if isinstance(node, ast.Import):
        return (alias.name == module
                or (alias.asname is None
                    and alias.name.startswith(module + '.')))
    return False
class _NameBinding(NamedTuple):
    lineno: int
    col: int
    name: str
    bare_ok: bool
    attr_ok: bool
    deleted: bool = False
def _call_root_name(func: ast.AST) -> str | None:
    while isinstance(func, ast.Attribute):
        func = func.value
    return func.id if isinstance(func, ast.Name) else None
def _import_binds_module(node: ast.AST, alias: ast.alias, name: str) -> bool:
    if not isinstance(node, ast.Import):
        return False
    return (alias.asname or alias.name.split('.')[0]) == name
def _unpack_target_values(target: ast.AST, value: ast.AST | None) -> Any:
    if isinstance(target, ast.Starred):
        yield target.value, None
        return
    if not isinstance(target, (ast.Tuple, ast.List)):
        yield target, value
        return
    targets = target.elts
    values = value.elts if isinstance(value, (ast.Tuple, ast.List)) else []
    starred = [i for i, item in enumerate(targets)
               if isinstance(item, ast.Starred)]
    if isinstance(value, (ast.Tuple, ast.List)) and len(starred) <= 1:
        fixed_count = len(targets) - len(starred)
        if (not starred and len(values) == len(targets)) or (
                starred and len(values) >= fixed_count):
            split = starred[0] if starred else len(targets)
            for item, item_value in zip(targets[:split], values[:split]):
                yield from _unpack_target_values(item, item_value)
            if starred:
                yield targets[split].value, None
                tail_count = len(targets) - split - 1
                tail_values = values[len(values) - tail_count:]
                for item, item_value in zip(targets[split + 1:], tail_values):
                    yield from _unpack_target_values(item, item_value)
            return
    for item in targets:
        yield from _unpack_target_values(item, None)
def _assignment_target_values(node: ast.AST) -> list:
    pair = assign_targets_value(node)
    if pair is None:
        if isinstance(node, ast.NamedExpr):
            return [(node.target, node.value)]
        return []
    targets, value = pair
    return [(target, item_value) for root in targets
            for target, item_value in _unpack_target_values(root, value)]
def _function_scope_semantics(tree: ast.AST, scope_chains: dict) -> tuple:
    function_scopes: set[tuple] = set()
    global_decls: dict[tuple, set[str]] = {}
    nonlocal_decls: dict[tuple, set[str]] = {}
    for node in iter_nodes(tree, None):
        scope = scope_chains.get(id(node), ())
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            body_start = (node.body if isinstance(node, ast.Lambda)
                          else node.body[0])
            function_scopes.add(scope_chains.get(id(body_start), scope))
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            declarations = (global_decls if isinstance(node, ast.Global)
                            else nonlocal_decls)
            declarations.setdefault(scope, set()).update(node.names)
    return function_scopes, global_decls, nonlocal_decls
def _local_binding_names(tree: ast.AST, scope_chains: dict,
                         global_decls: dict, nonlocal_decls: dict) -> dict:
    local_names: dict[tuple, set[str]] = {}
    def _note(scope: tuple, name: str) -> None:
        if (name in global_decls.get(scope, ())
                or name in nonlocal_decls.get(scope, ())):
            return
        local_names.setdefault(scope, set()).add(name)
    for node in iter_nodes(tree, None):
        scope = scope_chains.get(id(node), ())
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            if not isinstance(node, ast.Lambda):
                _note(scope, node.name)
            body_start = (node.body if isinstance(node, ast.Lambda)
                          else node.body[0])
            param_scope = scope_chains.get(id(body_start), scope)
            for name in collect_param_names(node):
                _note(param_scope, name)
            continue
        if isinstance(node, ast.ClassDef):
            _note(scope, node.name)
            continue
        if isinstance(node, (ast.For, ast.AsyncFor)):
            targets = [node.target]
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            targets = [item.optional_vars for item in node.items
                       if item.optional_vars is not None]
        elif isinstance(node, (ast.MatchAs, ast.MatchStar, ast.MatchMapping)):
            capture = pattern_capture_name(node)
            if capture:
                _note(scope, capture)
            continue
        elif isinstance(node, ast.ExceptHandler):
            if node.name:
                _note(scope, node.name)
            continue
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                if alias.name == '*':
                    continue
                name = (alias.asname or alias.name.split('.')[0]
                        if isinstance(node, ast.Import)
                        else alias.asname or alias.name)
                _note(scope, name)
            continue
        elif isinstance(node, ast.AnnAssign) and node.value is None:
            targets = [node.target]
        elif isinstance(node, ast.Delete):
            targets = list(node.targets)
        elif isinstance(node, ast.AugAssign):
            targets = [node.target]
        else:
            targets = [target for target, _value
                       in _assignment_target_values(node)]
        for target in targets:
            for name, _lineno, _col in iter_target_bindings(target):
                _note(scope, name)
    return local_names
def _global_binding_scope(scope: tuple, name: str,
                          global_decls: dict) -> tuple:
    return () if name in global_decls.get(scope, ()) else scope

def _declared_binding_scope(scope: tuple, name: str,
                            global_decls: dict | None,
                            nonlocal_decls: dict | None,
                            local_names: dict | None = None) -> tuple:
    if name in (global_decls or {}).get(scope, ()):
        return ()
    if name not in (nonlocal_decls or {}).get(scope, ()):
        return scope
    chain = scope[:-1]
    fallback: tuple | None = None
    while chain:
        if getattr(chain[-1], "kind", None) == "function":
            if fallback is None:
                fallback = chain
            if (local_names is None
                    or name in local_names.get(chain, ())):
                return chain
        chain = chain[:-1]
    return fallback if fallback is not None else ()
def _shadowed_call_ids(
    tree: Any, index: list | None,
    assignment_is_dangerous: Any = None,
    import_is_dangerous: Any = None,
    scope_chains: dict | None = None,
    *,
    from_import_attr_ok: bool = False,
    reference_attributes: bool = False,
    reference_names: bool = False,
    deleted_bare_builtins: frozenset | set = frozenset(),
) -> set[int]:
    if tree is None:
        return set()
    if scope_chains is None:
        scope_chains = _build_scope_chains(tree)
    (function_scopes, global_decls,
     nonlocal_decls) = _function_scope_semantics(tree, scope_chains)
    local_names = _local_binding_names(
        tree, scope_chains, global_decls, nonlocal_decls)
    events: dict[tuple, list[_NameBinding]] = {}
    def _bind(scope: tuple, binding: _NameBinding) -> None:
        scope = _declared_binding_scope(
            scope, binding.name, global_decls, nonlocal_decls, local_names)
        events.setdefault(scope, []).append(binding)
    for node in iter_nodes(tree, None):
        scope = scope_chains.get(id(node), ())
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            _bind(scope, _NameBinding(node.lineno, node.col_offset,
                                      node.name, False, False))
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            body_start = (node.body if isinstance(node, ast.Lambda)
                          else node.body[0])
            param_scope = scope_chains.get(id(body_start), scope)
            position = (body_start.lineno, body_start.col_offset)
            for name in collect_param_names(node):
                _bind(param_scope, _NameBinding(*position, name, False, False))
            continue
        if isinstance(node, ast.ClassDef):
            continue
        if isinstance(node, (ast.For, ast.AsyncFor)):
            for name, lineno, col in iter_target_bindings(node.target):
                _bind(scope, _NameBinding(lineno, col, name, False, False))
            continue
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is None:
                    continue
                for name, lineno, col in iter_target_bindings(item.optional_vars):
                    _bind(scope, _NameBinding(lineno, col, name, False, False))
            continue
        if isinstance(node, (ast.MatchAs, ast.MatchStar, ast.MatchMapping)):
            capture = pattern_capture_name(node)
            if capture:
                _bind(scope, _NameBinding(
                    node.lineno, node.col_offset, capture, False, False))
            continue
        if isinstance(node, ast.ExceptHandler):
            if node.name:
                _bind(scope, _NameBinding(
                    node.lineno, node.col_offset, node.name, False, False))
                _bind(scope, _NameBinding(
                    getattr(node, "end_lineno", node.lineno) or node.lineno,
                    getattr(node, "end_col_offset", node.col_offset) or 0,
                    node.name, False, False, True))
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if import_is_dangerous is None:
                continue
            for alias in node.names:
                name = (alias.asname or alias.name.split('.')[0]
                        if isinstance(node, ast.Import)
                        else alias.asname or alias.name)
                if name == '*':
                    continue
                dangerous = bool(import_is_dangerous(node, alias))
                attr_ok = dangerous and (
                    (from_import_attr_ok and isinstance(node, ast.ImportFrom))
                    or _import_binds_module(node, alias, name))
                _bind(scope, _NameBinding(
                    node.lineno, node.col_offset, name,
                    dangerous and isinstance(node, ast.ImportFrom), attr_ok))
            continue
        if isinstance(node, ast.Delete):
            for target in node.targets:
                for name, lineno, col in iter_target_bindings(target):
                    _bind(scope, _NameBinding(
                        lineno, col, name, False, False, True))
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            if scope in function_scopes:
                for name, lineno, col in iter_target_bindings(node.target):
                    _bind(scope, _NameBinding(
                        lineno, col, name, False, False))
            continue
        if assignment_is_dangerous is None:
            continue
        for target, value in _assignment_target_values(node):
            dangerous = (value is not None
                         and bool(assignment_is_dangerous(value)))
            for name, lineno, col in iter_target_bindings(target):
                _bind(scope, _NameBinding(lineno, col, name, dangerous, False))
    shadowed: set[int] = set()
    for node in iter_nodes(tree, index):
        attribute_reference = (reference_attributes
                               and isinstance(node, ast.Attribute))
        name_reference = (reference_names and isinstance(node, ast.Name)
                          and isinstance(node.ctx, ast.Load))
        if (not isinstance(node, ast.Call) and not attribute_reference
                and not name_reference):
            continue
        func = node if attribute_reference or name_reference else node.func
        name = _call_root_name(func)
        if name is None:
            continue
        bare = isinstance(func, ast.Name)
        lexical_scope = scope_chains.get(id(node), ())
        scope = _global_binding_scope(lexical_scope, name, global_decls)
        initial_scope = scope
        defer_enclosing = bool(
            lexical_scope
            and getattr(lexical_scope[-1], "kind", None) == "function")
        call_position = (node.lineno, node.col_offset)
        while True:
            entries = [binding for binding in events.get(scope, ())
                       if binding.name == name]
            if defer_enclosing and scope != initial_scope:
                candidates = entries
            else:
                candidates = [binding for binding in entries
                              if (binding.lineno, binding.col) <= call_position]
            if candidates:
                latest = max(candidates, key=lambda binding: (binding.lineno,
                                                             binding.col))
                if latest.deleted:
                    builtin_restored = (
                        bare and name in deleted_bare_builtins
                        and (not scope
                             or getattr(scope[-1], "kind", None) == "class"))
                    if not builtin_restored:
                        shadowed.add(id(node))
                elif not (latest.bare_ok if bare else latest.attr_ok):
                    shadowed.add(id(node))
                break
            if (entries and scope in function_scopes
                    and name not in nonlocal_decls.get(scope, ())):
                shadowed.add(id(node))
                break
            if not scope:
                break
            scope = scope[:-1]
    return shadowed
_DELETED_MEMBER_ORIGIN = object()
class _MemberLookup(NamedTuple):
    aliases: set
    origins: dict
    member_set: frozenset | set
    bindings: dict
    scope_chains: dict
    builtin_direct: bool = False
    shadowed_references: frozenset = frozenset()
def _assignment_member_origin(value: ast.AST, lookup: _MemberLookup,
                              lineno: int, col: int) -> str | None:
    if id(value) in lookup.shadowed_references:
        return None
    if isinstance(value, ast.Attribute):
        if (isinstance(value.value, ast.Name)
                and value.value.id in lookup.aliases
                and value.attr in lookup.member_set):
            return value.attr
        return None
    if not isinstance(value, ast.Name):
        return None
    scope = lookup.scope_chains.get(id(value), ())
    entry = _scoped_entry(
        lookup.bindings, value.id, scope, lineno, col,
        enclosing_runtime=True)
    if entry is not None:
        if entry[2] is _DELETED_MEMBER_ORIGIN:
            if lookup.builtin_direct and value.id in lookup.member_set:
                return value.id
            return None
        return entry[2]
    imported = lookup.origins.get(value.id)
    if imported in lookup.member_set:
        return imported
    if lookup.builtin_direct and value.id in lookup.member_set:
        return value.id
    return None
def _rhs_member_origin(value: ast.AST,
                       lookup: _MemberLookup) -> str | None:
    return _assignment_member_origin(
        value, lookup,
        getattr(value, "lineno", 0) or 0,
        getattr(value, "col_offset", 0) or 0)
def _assignment_member_bindings(tree: Any, aliases: set,
                                origins: dict,
                                member_set: frozenset | set,
                                scope_chains: dict | None = None,
                                *,
                                builtin_direct: bool = False,
                                module: str | None = None,
                                ) -> tuple[dict, dict]:
    if scope_chains is None:
        scope_chains = _build_scope_chains(tree) if tree is not None else {}
    if tree is not None:
        _, global_decls, nonlocal_decls = _function_scope_semantics(
            tree, scope_chains)
        local_names = _local_binding_names(
            tree, scope_chains, global_decls, nonlocal_decls)
    else:
        global_decls, nonlocal_decls, local_names = {}, {}, {}
    shadowed_references = (_shadowed_call_ids(
        tree, None, lambda _value: False,
        lambda node, alias: _import_matches(node, alias, module, member_set),
        scope_chains=scope_chains, reference_attributes=True,
        reference_names=True,
        deleted_bare_builtins=member_set if builtin_direct else frozenset())
        if tree is not None and module is not None else set())
    bindings: dict = {}
    lookup = _MemberLookup(aliases, origins, member_set, bindings,
                           scope_chains, builtin_direct,
                           frozenset(shadowed_references))
    for node in iter_nodes(tree, None):
        if isinstance(node, ast.Delete):
            lineno = getattr(node, "lineno", 0) or 0
            col = getattr(node, "col_offset", 0) or 0
            scope = scope_chains.get(id(node), ())
            for target in node.targets:
                for name, _line, _col in iter_target_bindings(target):
                    binding_scope = _declared_binding_scope(
                        scope, name, global_decls, nonlocal_decls, local_names)
                    bindings.setdefault((binding_scope, name), []).append(
                        (lineno, col, _DELETED_MEMBER_ORIGIN))
            continue
        if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            continue
        value = getattr(node, "value", None)
        if value is None:
            continue
        assignments = _assignment_target_values(node)
        if not assignments:
            continue
        lineno = getattr(node, "lineno", 0) or 0
        col = getattr(node, "col_offset", 0) or 0
        scope = scope_chains.get(id(node), ())
        for target, item_value in assignments:
            origin = (_assignment_member_origin(
                item_value, lookup, lineno, col)
                if item_value is not None else None)
            for name, _line, _col in iter_target_bindings(target):
                binding_scope = _declared_binding_scope(
                    scope, name, global_decls, nonlocal_decls, local_names)
                bindings.setdefault((binding_scope, name), []).append(
                    (lineno, col, origin))
    return bindings, scope_chains
def _se08_is_subprocess_call(node: ast.Call, aliases: set, origins: dict,
                             shadowed: set[int], bindings: dict,
                             scope_chains: dict) -> str | None:
    if id(node) in shadowed:
        return None
    func = node.func
    if isinstance(func, ast.Name):
        scope = scope_chains.get(id(node), ())
        entry = _scoped_entry(
            bindings, func.id, scope, getattr(node, "lineno", 0) or 0,
            getattr(node, "col_offset", 0) or 0, enclosing_runtime=True)
        origin = entry[2] if entry is not None else origins.get(func.id)
        return func.id if origin in _SUBPROCESS_SHELL_FUNCS_BARE else None
    func_name = dotted_name(func) or ''
    receiver, _, member = func_name.rpartition('.')
    if not receiver or member not in _SUBPROCESS_SHELL_FUNCS_BARE:
        return None
    if receiver not in aliases:
        return None
    return func_name
def _se08_has_shell_true(node: ast.Call) -> bool:
    positional_shell = (
        len(node.args) >= 9
        and not any(isinstance(arg, ast.Starred) for arg in node.args[:9])
        and isinstance(node.args[8], ast.Constant)
        and bool(node.args[8].value)
    )
    return positional_shell or any(
        kw.arg == 'shell' and isinstance(kw.value, ast.Constant)
        and bool(kw.value.value) for kw in node.keywords)
def check_SE08(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _aliases, _origins = collect_module_bindings_detailed(
        tree, 'subprocess', _SUBPROCESS_SHELL_FUNCS_BARE)
    _scope_chains = _build_scope_chains(tree) if tree is not None else {}
    _bindings, _scope_chains = _assignment_member_bindings(
        tree, _aliases, _origins, _SUBPROCESS_SHELL_FUNCS_BARE,
        scope_chains=_scope_chains, module='subprocess')
    _subprocess_lookup = _MemberLookup(
        _aliases, _origins, _SUBPROCESS_SHELL_FUNCS_BARE,
        _bindings, _scope_chains)
    _shadowed = _shadowed_call_ids(
        tree, index,
        assignment_is_dangerous=lambda value: _rhs_member_origin(
            value, _subprocess_lookup) is not None,
        import_is_dangerous=lambda node, alias: _import_matches(
            node, alias, 'subprocess', _SUBPROCESS_SHELL_FUNCS_BARE),
        scope_chains=_scope_chains)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        func_name = _se08_is_subprocess_call(
            node, _aliases, _origins, _shadowed, _bindings, _scope_chains)
        if func_name is None:
            continue
        if not _se08_has_shell_true(node):
            continue
        issues.append({
            "rule_id": "SE-08",
            "severity": "P0",
            "dimension": "security",
            "file": filepath,
            "line": node.lineno,
            "message": func_name + '() 使用 shell=True, 存在shell注入风险',
            "code_snippet": get_code_snippet(source_lines, node.lineno),
        })
    return issues
def _se30b_bare_member(node: ast.Call, from_origins: dict) -> str | None:
    if not isinstance(node.func, ast.Name):
        return None
    return from_origins.get(node.func.id)
def _se30b_finding(node: ast.Call, member: str, source_lines: Any,
                   filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id='SE-30b', severity='P1', dimension='security', file=filepath,
        line=node.lineno,
        message=f'裸 {member}()（from os import {member}）执行动态构造命令，命令经 shell 解释存在注入风险',
        suggestion=('根因: 动态命令经 shell 解释，外部输入可注入任意命令（分号/管道/反引号）。该问题属于安全类别。\n'
                    '修复策略: 改用 subprocess.run(shlex.split(cmd), shell=False, check=True)；必须拼接时对每个外部输入 shlex.quote\n'
                    '参考标准: CWE-78 / Bandit B605'),
        code_snippet=get_code_snippet(source_lines, node.lineno))
def _se30b_is_constant_command(arg: ast.AST) -> bool:
    if isinstance(arg, ast.Constant):
        return True
    return isinstance(arg, ast.JoinedStr) and not _has_placeholder(arg)
def check_SE30b(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _os_names, _from_origins = collect_module_bindings_detailed(
        tree, 'os', _OS_SHELL_MEMBERS)
    _scope_chains = _build_scope_chains(tree) if tree is not None else {}
    _os_bindings, _scope_chains = _assignment_member_bindings(
        tree, _os_names, _from_origins, _OS_SHELL_MEMBERS,
        scope_chains=_scope_chains, module='os')
    _os_lookup = _MemberLookup(
        _os_names, _from_origins, _OS_SHELL_MEMBERS,
        _os_bindings, _scope_chains)
    _shadowed = _shadowed_call_ids(
        tree, index,
        assignment_is_dangerous=lambda value: _rhs_member_origin(
            value, _os_lookup) is not None,
        import_is_dangerous=lambda node, alias: _import_matches(
            node, alias, 'os', _OS_SHELL_MEMBERS),
        scope_chains=_scope_chains)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call) or id(node) in _shadowed:
            continue
        _member = _se30b_bare_member(node, _from_origins)
        if _member is None:
            continue
        if not node.args:
            continue
        if _se30b_is_constant_command(node.args[0]):
            continue
        issues.append(_se30b_finding(node, _member, source_lines, filepath))
    return issues
def _se35_extract_arg_names(node: Any) -> Any:
    arg_names = set()
    values = list(node.args) + [kw.value for kw in node.keywords]
    for value in values:
        arg_names.update(
            sub.id for sub in walk_nodes(value) if isinstance(sub, ast.Name))
    return arg_names
_SE35_STRONG_KEYWORDS = frozenset({
    "input", "request", "param", "query", "user", "data", "body", "form",
    "args", "kwargs", "payload", "sql", "command", "cmd", "file", "path",
})
_SE35_GENERIC_KEYWORDS = frozenset({
    "name", "id", "key", "value", "text", "content", "msg", "message",
})
def _se35_split_tokens(name: Any) -> set[str]:
    raw = str(name)
    tokens = re.split(r"[_\-\s]+|(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])", raw)
    lowered = raw.lower()
    return {t.lower() for t in tokens if t} | {lowered}
def _se35_match_risky_keywords(arg_names: Any) -> Any:
    matched = set()
    for an in arg_names:
        tokens = _se35_split_tokens(an)
        if any(token == kw or token.startswith(kw)
               for token in tokens for kw in _SE35_STRONG_KEYWORDS):
            matched.add(an)
            continue
        if any(kw in tokens or (kw + "s") in tokens
               for kw in _SE35_GENERIC_KEYWORDS):
            matched.add(an)
    return matched
def _se35_build_issue(node: Any, filepath: Any, matched: Any,
                      source: Any) -> Any:
    return {
        "rule_id": "SE-35",
        "severity": "P1",
        "line": node.lineno,
        "file": filepath,
        "message": "[SE-35] str.format() variable injection risk: " + ", ".join(sorted(matched)),
        "suggestion": '根因: 代码实现中存在安全方面的问题, 需要规范化处理。\n修复策略: Use f-strings or explicit sanitization for format() arguments\n' + _OWASP_REF_LINE,
        "code_snippet": get_code_snippet(source, node.lineno),
    }
def _se35_all_constant_literals(node: ast.AST) -> bool:
    _items: list = []
    if isinstance(node, ast.Dict):
        _items = list(node.keys) + list(node.values)
    elif isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        _items = list(node.elts)
    for _it in _items:
        if _it is None:
            continue
        if isinstance(_it, ast.Constant) and isinstance(_it.value, str):
            continue
        if isinstance(_it, (ast.Dict, ast.List, ast.Tuple, ast.Set)) \
                and _se35_all_constant_literals(_it):
            continue
        return False
    return True
def _se35_value_kind(value, table: _Se35BindingTable, scope: tuple,
                     lineno: int, col: int | None) -> str | None:
    if isinstance(value, ast.Constant) and isinstance(value.value, str):
        return "str"
    if isinstance(value, ast.JoinedStr):
        return "dyn" if _has_placeholder(value) else "str"
    if isinstance(value, ast.Name):
        return table.lookup(value.id, scope, lineno, col)
    if isinstance(value, ast.Call):
        return "dyn"
    if (isinstance(value, ast.BinOp)
            and isinstance(value.op, (ast.Add, ast.Mod))):
        return "dyn" if _se37_dynamic_interpolation(value) else "str"
    if isinstance(value, ast.Subscript):
        if (isinstance(value.value, ast.Name)
                and table.lookup(value.value.id, scope, lineno, col)
                == "container"):
            return "str"
        return "dyn"
    if isinstance(value, (ast.Dict, ast.List, ast.Tuple, ast.Set)) \
            and _se35_all_constant_literals(value):
        return "container"
    return None
class _Se35BindingTable:
    __slots__ = ("entries", "records")
    def __init__(self) -> None:
        self.entries: dict = {}
        self.records: list = []
    def add(self, scope: tuple, name: str, lineno: int, col: int,
            value: ast.AST | None,
            iter_expr: ast.AST | None = None,
            augmented_op: ast.operator | None = None,
            binding_scope: tuple | None = None) -> None:
        previous = (_scoped_entry(self.entries, name, scope, lineno, col)
                    if augmented_op is not None else None)
        entry = [lineno, col, None]
        target_scope = scope if binding_scope is None else binding_scope
        self.entries.setdefault((target_scope, name), []).append(entry)
        self.records.append(
            (scope, entry, value, iter_expr, augmented_op, previous))
    def add_param(self, scope: tuple, name: str, lineno: int) -> None:
        self.entries.setdefault((scope, name), []).append(
            [lineno, 0, "dyn"])
    def lookup(self, name: str, scope: tuple,
               lineno: int, col: int | None) -> str | None:
        entry = _scoped_entry(
            self.entries, name, scope, lineno, col,
            enclosing_runtime=True)
        return entry[2] if entry is not None else None
def _se35_collect_assign_bindings(nodes: list, scope_chains: dict,
                                  table: _Se35BindingTable,
                                  global_decls: dict | None = None,
                                  nonlocal_decls: dict | None = None,
                                  local_names: dict | None = None) -> None:
    for node in nodes:
        if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr,
                                 ast.AugAssign)):
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        augmented_op = (node.op if isinstance(node, ast.AugAssign)
                        and isinstance(node.op, (ast.Add, ast.Mod)) else None)
        if isinstance(node, ast.AugAssign):
            if augmented_op is None:
                continue
            assignments = [(node.target, node.value)]
        else:
            assignments = _assignment_target_values(node)
        if not assignments:
            continue
        scope = scope_chains.get(id(node), ())
        lineno = getattr(node, "lineno", 0) or 0
        col = getattr(node, "col_offset", 0) or 0
        for target, value in assignments:
            for name, _line, _col in iter_target_bindings(target):
                table.add(scope, name, lineno, col, value,
                          augmented_op=augmented_op,
                          binding_scope=_declared_binding_scope(
                              scope, name, global_decls, nonlocal_decls,
                              local_names))
def _se35_collect_loop_bindings(nodes: list, scope_chains: dict,
                                table: _Se35BindingTable,
                                global_decls: dict | None = None,
                                nonlocal_decls: dict | None = None,
                                local_names: dict | None = None) -> None:
    for node in nodes:
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            continue
        scope = scope_chains.get(id(node), ())
        lineno = getattr(node, "lineno", 0) or 0
        col = getattr(node, "col_offset", 0) or 0
        for target in walk_nodes(node.target):
            if isinstance(target, ast.Name):
                table.add(scope, target.id, lineno, col, None, node.iter,
                          binding_scope=_declared_binding_scope(
                              scope, target.id, global_decls, nonlocal_decls,
                              local_names))
def _se35_iter_kind(iter_expr: ast.AST, table: _Se35BindingTable,
                    scope: tuple, lineno: int,
                    col: int | None) -> str | None:
    if isinstance(iter_expr, ast.Name):
        return ("elem"
                if table.lookup(iter_expr.id, scope, lineno, col)
                == "container" else None)
    if isinstance(iter_expr, (ast.Call, ast.Attribute, ast.Subscript)):
        return "dyn"
    if (isinstance(iter_expr, (ast.List, ast.Tuple, ast.Set))
            and _se35_all_constant_literals(iter_expr)):
        return "str"
    return None
def _se35_resolve_kinds(table: _Se35BindingTable) -> None:
    for _ in range(len(table.records) + 2):
        changed = False
        for (scope, entry, value, iter_expr,
             augmented_op, previous) in table.records:
            if augmented_op is not None:
                previous_kind = previous[2] if previous is not None else None
                value_kind = _se35_value_kind(
                    value, table, scope, entry[0], entry[1])
                literal_rhs = ({"str", "elem", "container"}
                               if isinstance(augmented_op, ast.Mod)
                               else {"str", "elem"})
                kind = ("str" if previous_kind in {"str", "elem"}
                        and value_kind in literal_rhs else "dyn")
            elif iter_expr is not None:
                kind = _se35_iter_kind(
                    iter_expr, table, scope, entry[0], entry[1])
            else:
                kind = _se35_value_kind(
                    value, table, scope, entry[0], entry[1])
            if entry[2] != kind:
                entry[2] = kind
                changed = True
        if not changed:
            break
def _se35_collect_param_bindings(nodes: list, scope_chains: dict,
                                 table: _Se35BindingTable) -> None:
    for node in nodes:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
            continue
        body_start = (node.body if isinstance(node, ast.Lambda)
                      else node.body[0])
        scope = scope_chains.get(id(body_start), ())
        lineno = getattr(node, "lineno", 0) or 0
        for name in collect_param_names(node):
            table.add_param(scope, name, lineno)
def _se35_scope_bindings(tree: ast.AST, scope_chains: dict,
                         global_decls: dict | None = None,
                         nonlocal_decls: dict | None = None,
                         local_names: dict | None = None
                         ) -> _Se35BindingTable:
    nodes = list(iter_nodes(tree, None))
    table = _Se35BindingTable()
    _se35_collect_assign_bindings(
        nodes, scope_chains, table, global_decls, nonlocal_decls, local_names)
    _se35_collect_loop_bindings(
        nodes, scope_chains, table, global_decls, nonlocal_decls, local_names)
    _se35_collect_param_bindings(nodes, scope_chains, table)
    _se35_resolve_kinds(table)
    return table
_SE35_TEMPLATE_CONSTANT = "constant"
_SE35_TEMPLATE_DYNAMIC = "dynamic"
_SE35_TEMPLATE_UNKNOWN = "unknown"
def _se35_template_kind(fmt_obj: ast.AST, table: _Se35BindingTable,
                        scope: tuple, lineno: int,
                        col: int | None) -> str:
    if isinstance(fmt_obj, ast.Constant):
        return (_SE35_TEMPLATE_CONSTANT
                if isinstance(fmt_obj.value, str)
                else _SE35_TEMPLATE_UNKNOWN)
    if isinstance(fmt_obj, ast.JoinedStr):
        return (_SE35_TEMPLATE_DYNAMIC if _has_placeholder(fmt_obj)
                else _SE35_TEMPLATE_CONSTANT)
    if isinstance(fmt_obj, ast.Name):
        kind = table.lookup(fmt_obj.id, scope, lineno, col)
        if kind in ("str", "elem"):
            return _SE35_TEMPLATE_CONSTANT
        return (_SE35_TEMPLATE_DYNAMIC if kind == "dyn"
                else _SE35_TEMPLATE_UNKNOWN)
    if isinstance(fmt_obj, ast.Subscript):
        if (isinstance(fmt_obj.value, ast.Name)
                and table.lookup(fmt_obj.value.id, scope, lineno, col)
                in ("str", "elem", "container")):
            return _SE35_TEMPLATE_CONSTANT
        return _SE35_TEMPLATE_DYNAMIC
    if isinstance(fmt_obj, ast.Attribute):
        return (_SE35_TEMPLATE_CONSTANT
                if isinstance(fmt_obj.value, ast.Name)
                and table.lookup(fmt_obj.value.id, scope, lineno, col)
                == "elem"
                else _SE35_TEMPLATE_UNKNOWN)
    if isinstance(fmt_obj, ast.Call):
        return _SE35_TEMPLATE_DYNAMIC
    return _SE35_TEMPLATE_UNKNOWN
def _se35_issue_for(node: ast.AST, filepath: Any, table: _Se35BindingTable,
                    scope_chains: dict, source: Any) -> dict | None:
    if as_format_call(node) is None:
        return None
    scope = scope_chains.get(id(node), ())
    lineno = getattr(node, "lineno", 0) or 0
    col = getattr(node, "col_offset", 0) or 0
    if _se35_template_kind(
            node.func.value, table, scope, lineno, col) \
            != _SE35_TEMPLATE_DYNAMIC:
        return None
    matched = _se35_match_risky_keywords(_se35_extract_arg_names(node))
    if not matched:
        return None
    return _se35_build_issue(node, filepath, matched, source)
def check_SE35(tree: Any, source: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    scope_chains = _build_scope_chains(tree)
    _, global_decls, nonlocal_decls = _function_scope_semantics(
        tree, scope_chains)
    local_names = _local_binding_names(
        tree, scope_chains, global_decls, nonlocal_decls)
    table = _se35_scope_bindings(
        tree, scope_chains, global_decls, nonlocal_decls, local_names)
    for node in iter_nodes(tree, index):
        issue = _se35_issue_for(
            node, filepath, table, scope_chains, source)
        if issue is not None:
            issues.append(issue)
    return issues
_SQL_EXEC_METHODS_SE = ('execute', 'executemany', 'raw', 'text',
                        'executescript', 'read_sql', 'read_sql_query')
_SQL_KEYWORDS_SE = ("SELECT", "INSERT", "UPDATE", "DELETE", "CREATE", "DROP", "ALTER")
_SCOPE_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.ClassDef, ast.Lambda)
class _ScopeMarker(NamedTuple):
    position: tuple[int, int]
    kind: str
def _build_scope_chains(tree: ast.AST) -> dict:
    chains: dict = {}
    work: list = [(tree, (), ())]
    while work:
        node, scope, closure = work.pop()
        chains[id(node)] = scope
        if isinstance(node, _SCOPE_NODE_TYPES):
            marker = (_ScopeMarker(
                (getattr(node, "lineno", 0),
                 getattr(node, "col_offset", 0)),
                "class" if isinstance(node, ast.ClassDef) else "function"),)
            if isinstance(node, ast.ClassDef):
                child_scope, child_closure = scope + marker, closure
            else:
                child_scope = closure + marker
                child_closure = child_scope
        else:
            child_scope, child_closure = scope, closure
        body_children = (
            {id(node.body)} if isinstance(node, ast.Lambda)
            else {id(child) for child in getattr(node, "body", ())}
        ) if isinstance(node, _SCOPE_NODE_TYPES) else set()
        for child in ast.iter_child_nodes(node):
            if id(child) in body_children:
                work.append((child, child_scope, child_closure))
            else:
                work.append((child, scope, closure))
    return chains
def _scoped_entry(bindings: dict, name: str, scope: tuple,
                  upto_line: int, upto_col: int | None, *,
                  enclosing_runtime: bool = False):
    initial_scope = tuple(scope)
    defer_enclosing = bool(
        enclosing_runtime and initial_scope
        and getattr(initial_scope[-1], "kind", None) == "function")
    chain = initial_scope
    while True:
        entries = bindings.get((chain, name))
        if entries:
            if defer_enclosing and chain != initial_scope:
                return max(entries, key=lambda entry: (entry[0], entry[1]))
            if upto_col is None:
                prior = [entry for entry in entries if entry[0] <= upto_line]
            else:
                prior = [entry for entry in entries
                         if (entry[0], entry[1]) <= (upto_line, upto_col)]
            if prior:
                return max(prior, key=lambda entry: (entry[0], entry[1]))
            if chain and getattr(chain[-1], "kind", None) != "class":
                return None
        if not chain:
            return None
        chain = chain[:-1]
def _has_placeholder(joined: ast.JoinedStr) -> bool:
    return any(isinstance(part, ast.FormattedValue) for part in joined.values)
def _is_constant_fstring(node: ast.AST) -> bool:
    return isinstance(node, ast.JoinedStr) and not _has_placeholder(node)
_SQL_KEYWORD_BOUNDARY = r"(?<![A-Za-z0-9_.])"
_SQL_KEYWORD_RE = re.compile(
    _SQL_KEYWORD_BOUNDARY + r"(?:" + "|".join(_SQL_KEYWORDS_SE)
    + r")(?![A-Za-z0-9_])", re.IGNORECASE)
def _sql_keyword_hit(text: str) -> bool:
    return bool(text) and bool(_SQL_KEYWORD_RE.search(text))
def _fstring_literal_text(node: ast.JoinedStr) -> str:
    return "".join(
        part.value for part in node.values
        if isinstance(part, ast.Constant) and isinstance(part.value, str))
def _se05_record_binding(node: ast.AST, scope: tuple, bindings: dict,
                         col: int, alias_records: list,
                         global_decls: dict | None = None,
                         nonlocal_decls: dict | None = None,
                         local_names: dict | None = None) -> bool:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return False
    assignments = _assignment_target_values(node)
    if not assignments:
        return False
    lineno = getattr(node, "lineno", 0) or 0
    recorded = False
    for target, value in assignments:
        dynamic = (isinstance(value, ast.JoinedStr)
                   and _sql_keyword_hit(_fstring_literal_text(value)))
        for name, _line, _col in iter_target_bindings(target):
            entry = ([lineno, col, 0, "derive"]
                     if isinstance(value, ast.Name)
                     else [lineno, col, id(value) if dynamic else 0,
                           "dynamic" if dynamic else "safe"])
            binding_scope = _declared_binding_scope(
                scope, name, global_decls, nonlocal_decls, local_names)
            bindings.setdefault((binding_scope, name), []).append(entry)
            if isinstance(value, ast.Name):
                alias_records.append((value.id, scope, entry))
            recorded = True
    return recorded
def _se05_resolve_alias_bindings(alias_records: list, bindings: dict) -> None:
    for _ in range(len(alias_records) + 1):
        changed = False
        for source_name, scope, entry in alias_records:
            if entry[3] != "derive":
                continue
            source = _scoped_entry(
                bindings, source_name, scope, entry[0], entry[1])
            if source is None or source is entry or source[3] == "derive":
                continue
            if source[3] == "dynamic" and source[2]:
                entry[2], entry[3] = source[2], "dynamic"
                changed = True
            elif source[3] == "safe":
                entry[3] = "safe"
                changed = True
        if not changed:
            break
def _se05_collect_scan(nodes, scope_chains: dict,
                       global_decls: dict | None = None,
                       nonlocal_decls: dict | None = None,
                       local_names: dict | None = None) -> tuple:
    _bindings: dict = {}
    _sql_exec_calls: list = []
    _joinedstr_nodes = []
    _alias_records: list = []
    for node in nodes:
        _scope = scope_chains.get(id(node), ())
        if _se05_record_binding(
                node, _scope, _bindings, getattr(node, "col_offset", 0) or 0,
                _alias_records, global_decls, nonlocal_decls, local_names):
            continue
        if _is_sql_exec_call(node):
            _sql_exec_calls.append((node, _scope))
        elif _is_interpolated_fstring(node):
            _joinedstr_nodes.append(node)
    _se05_resolve_alias_bindings(_alias_records, _bindings)
    return _bindings, _sql_exec_calls, _joinedstr_nodes
def _arg_fstr_ids(arg: ast.AST) -> set:
    return {id(sub) for sub in walk_nodes(arg) if isinstance(sub, ast.JoinedStr)}
def _se05_sql_ctx_fstr_ids(sql_exec_calls: list) -> set:
    _sql_ctx_fstr_ids: set = set()
    for call, _scope in sql_exec_calls:
        sql_arg = _call_sql_slot(call)
        if sql_arg is not None:
            _sql_ctx_fstr_ids |= _arg_fstr_ids(sql_arg)
    return _sql_ctx_fstr_ids
def _se05_in_sql_context(node: ast.AST, bindings: dict,
                         sql_exec_calls: list, sql_ctx_fstr_ids: set) -> bool:
    if id(node) in sql_ctx_fstr_ids:
        return True
    _node_id = id(node)
    for call, call_scope in sql_exec_calls:
        _call_line = getattr(call, "lineno", 0) or 0
        _call_col = getattr(call, "col_offset", 0) or 0
        arg = _call_sql_slot(call)
        if not isinstance(arg, ast.Name):
            continue
        entry = _scoped_entry(
            bindings, arg.id, call_scope, _call_line, _call_col,
            enclosing_runtime=True)
        if entry is not None and entry[2] == _node_id \
                and entry[3] == "dynamic":
            return True
    return False
def _detect_fstring_sql_injection(tree: Any, index=None) -> list:
    nodes = list(iter_nodes(tree, index))
    _scope_chains = _build_scope_chains(tree) if tree is not None else {}
    _, global_decls, nonlocal_decls = _function_scope_semantics(
        tree, _scope_chains)
    local_names = _local_binding_names(
        tree, _scope_chains, global_decls, nonlocal_decls)
    (_bindings, _sql_exec_calls,
     _joinedstr_nodes) = _se05_collect_scan(
        nodes, _scope_chains, global_decls, nonlocal_decls, local_names)
    _sql_ctx_fstr_ids = _se05_sql_ctx_fstr_ids(_sql_exec_calls)
    issues = []
    for node in _joinedstr_nodes:
        if not _sql_keyword_hit(_fstring_literal_text(node)):
            continue
        if not _se05_in_sql_context(node, _bindings,
                                    _sql_exec_calls, _sql_ctx_fstr_ids):
            continue
        issues.append({
            "rule_id": "SE-05",
            "line": getattr(node, "lineno", 0),
            "severity": "P0",
            "message": "f-string SQL injection risk",
        })
    return issues
def check_SE05(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = _detect_fstring_sql_injection(tree, index)
    source = join_source_lines(source_lines)
    for issue in issues:
        issue["code_snippet"] = get_code_snippet(source, issue["line"])
    return issues
_SE37_DYNAMIC_ID = re.compile(r'(?:SELECT|INSERT|UPDATE|DELETE|CREATE|DROP|ALTER|TRUNCATE)\s+[^\n]*?(?:FROM|INTO|TABLE|JOIN)\s+\{', re.IGNORECASE)
_SE37_ORM_BYPASS = [
    (re.compile(r'(\.extra\s*\()(.*?)(?:select|where|tables)\s*=', re.IGNORECASE | re.DOTALL), "P0", "Django .extra() bypass ORM parametrization"),
    (re.compile(r'(RawSQL\s*\()(.*?)\{', re.IGNORECASE | re.DOTALL), "P0", "Django RawSQL() expression injection"),
    (re.compile(r'(literal_column\s*\()(.*?)\{', re.IGNORECASE | re.DOTALL), "P1", "SQLAlchemy literal_column() bypass"),
]
_SE37_LIKE_INJECTION = re.compile(
    '(?:' + '|'.join(re.escape('.' + _m) for _m in
                     sorted(_SQL_EXEC_METHODS_SE, key=len, reverse=True))
    + ')\\s*\\(\\s*.*?LIKE\\s+', re.IGNORECASE)
_SE37_LIKE_WORD = re.compile(r'(?<![A-Za-z0-9_])like(?![A-Za-z0-9_])',
                             re.IGNORECASE)
_SE37_LIKE_FSTR_EVIDENCE = re.compile(r'f["\'][^"\n]*\{')
_SE37_LIKE_PCT_EVIDENCE = re.compile(r'[\'"\)\]]\s*%\s*\(')
_SE37_LIKE_CONCAT_EVIDENCE = re.compile(r'[\'"]\s*\+|\+\s*[\'"]')
_SE37_ASYNC_SQL = re.compile(
    r'await\s+[^\n]*?\.execute\s*\(\s*f["\']', re.IGNORECASE)
_SE37_READ_SQL = re.compile(
    '(?<![A-Za-z0-9_])read_sql(?:_query)?\\s*\\(\\s*f["\']', re.IGNORECASE)
_SE37_FORMAT_SQL = re.compile(
    '["\'][^"\']*(?:SELECT|INSERT|UPDATE|DELETE|DROP|ALTER|TRUNCATE)'
    '[^"\']*(?:FROM|INTO|TABLE|JOIN|SET|VALUES|WHERE)[^"\']*\\{\\}["\']'
    '\\s*\\.\\s*format\\s*\\(', re.IGNORECASE)
_SE37_COMMENT = re.compile(r'(?:SELECT|INSERT|UPDATE|DELETE|WHERE|FROM)\s.*?(--|/\*)', re.IGNORECASE)
def _line_no_at(code: str, offset: int) -> int:
    return code[:offset].count("\n") + 1
_SQL_FIX_REF = '\n参考标准: OWASP Top 10 / CWE / Bandit'
_SQL_FIX_ROOT_PARAM = (
    '根因: SQL查询未使用参数化查询, 用户输入直接嵌入SQL语句。该问题属于安全类别。')
_SQL_FIX_ROOT_IDENT = (
    '根因: SQL查询使用动态拼接的标识符, 未使用白名单校验, 存在SQL注入风险。该问题属于安全类别。')
def _sql_fix_suggestion(strategy: str, root: str = _SQL_FIX_ROOT_PARAM) -> str:
    return f"{root}\n修复策略: {strategy}{_SQL_FIX_REF}"
def _se37_finding(severity: str, line_no: int, message: str,
                  suggestion: str) -> dict:
    return {
        "rule_id": "SE-37",
        "severity": severity,
        "line": line_no,
        "message": f"[SE-37] {message}",
        "suggestion": suggestion,
    }
def _se37_comment_start(raw_line: str) -> int:
    i, n = 0, len(raw_line)
    while i < n:
        char = raw_line[i]
        if char in ("'", '"'):
            i = _se37_skip_string_literal(raw_line, i)
            continue
        if char == "#":
            return i
        i += 1
    return -1
def _se37_match_in_comment(code: str, match, raw_line: str) -> bool:
    comment_at = _se37_comment_start(raw_line)
    if comment_at < 0:
        return False
    column = match.start() - (code.rfind("\n", 0, match.start()) + 1)
    return column >= comment_at
_SE37_QUERY_PREFIXES = ("#", "_SE37")
_SE37_TEXT_SKIP_PREFIXES = _SE37_QUERY_PREFIXES + ("from ", "import ")
def _se37_iter_hits(pattern, code: str, lines_local: list,
                    skip_spans, prefixes=_SE37_TEXT_SKIP_PREFIXES):
    for match in pattern.finditer(code):
        line_no = _line_no_at(code, match.start())
        raw_line = (lines_local[line_no - 1]
                    if 1 <= line_no <= len(lines_local) else "")
        line = raw_line.strip()
        if 're.compile' in line or line.startswith(prefixes):
            continue
        if skip_spans and _se37_match_in_string(match, skip_spans):
            continue
        if _se37_match_in_comment(code, match, raw_line):
            continue
        yield match, line_no, line
class _VectorCopy(NamedTuple):
    severity: str
    message: str
    suggestion: str
_SE37_FORMAT_COPY = _VectorCopy(
    "P0", "str.format SQL template injection: ",
    _sql_fix_suggestion(
        'Use parameterized queries: cursor.execute(sql, (param,))，'
        '勿用 str.format 拼接 SQL'))
_SE37_CONCAT_COPY = _VectorCopy(
    "P0", "Dynamic SQL concatenation: ",
    _sql_fix_suggestion(
        'Use parameterized queries: cursor.execute(sql, (param,))，'
        '勿用 % 或 + 拼接 SQL'))
_SE37_DYNAMIC_ID_COPY = _VectorCopy(
    "P0", "Dynamic table/column name in f-string: ",
    _sql_fix_suggestion(
        'Use whitelist mapping for identifiers: '
        'ALLOWED_TABLES = {"users": "users"}',
        root=_SQL_FIX_ROOT_IDENT))
_SE37_COMMENT_COPY = _VectorCopy(
    "P2", "SQL comment truncation possible: ",
    '根因: 用户输入中可能包含SQL注释字符, 可绕过查询逻辑。该问题属于安全类别。\n'
    '修复策略: Filter SQL comment characters from user input: -- # /* */\n'
    + _OWASP_REF_LINE)
def _emit_text_vector(pattern, copy: _VectorCopy, code: Any, lines_local: Any,
                      issues: Any, skip_spans: Any) -> set[int]:
    lines: set[int] = set()
    for _match, line_no, line in _se37_iter_hits(
            pattern, code, lines_local, skip_spans):
        issues.append(_se37_finding(
            copy.severity, line_no, f"{copy.message}{line}", copy.suggestion))
        lines.add(line_no)
    return lines
def _check_orm_bypass(code: Any, lines_local: Any, issues: Any, skip_spans: Any = None) -> None:
    for pattern, severity, description in _SE37_ORM_BYPASS:
        for match, line_no, _line in _se37_iter_hits(
                pattern, code, lines_local, skip_spans,
                prefixes=_SE37_QUERY_PREFIXES):
            if pattern.groups >= 2 and (
                    _se37_pos_in_string_span(match.start(), skip_spans or [])
                    or not _se37_anchor_in_call(
                        code, match.end(1), match.end(2))):
                continue
            issues.append(_se37_finding(
                severity, line_no, description,
                _sql_fix_suggestion(
                    'Use ORM parametrized API: .filter() / .where() '
                    'instead of raw SQL')))
def _is_interpolated_fstring(node: ast.AST) -> bool:
    return isinstance(node, ast.JoinedStr) and _has_placeholder(node)
def _is_mod_format(node: ast.AST) -> bool:
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod)
            and not (isinstance(node.right, ast.Constant)
                     and isinstance(node.right.value, (int, float))))
def _is_dynamic_concat(node: ast.AST) -> bool:
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and not (isinstance(node.left, ast.Constant)
                     and isinstance(node.right, ast.Constant)))
def _arg_has_dynamic_pattern(arg: ast.AST) -> bool:
    return any(_is_interpolated_fstring(sub) or _is_mod_format(sub)
               or _is_dynamic_concat(sub)
               for sub in walk_nodes(arg))
_SQL_QUERY_KWARGS_SE = frozenset({"sql", "query", "operation", "statement"})
def _call_sql_slot(call: ast.Call) -> ast.AST | None:
    if call.args:
        return call.args[0]
    for keyword in call.keywords:
        if keyword.arg in _SQL_QUERY_KWARGS_SE:
            return keyword.value
    return None
def _call_has_dynamic_pattern(call: ast.Call) -> bool:
    sql_arg = _call_sql_slot(call)
    return sql_arg is not None and _arg_has_dynamic_pattern(sql_arg)
def _like_text_hit(text: str) -> bool:
    return bool(text) and bool(_SE37_LIKE_WORD.search(text))
def _subtree_carries_like(arg: ast.AST, name_const_map: dict,
                          call_scope: tuple, call_line: int,
                          call_col: int | None) -> bool:
    for sub in walk_nodes(arg):
        if (isinstance(sub, ast.Constant) and isinstance(sub.value, str)
                and _like_text_hit(sub.value)):
            return True
        if isinstance(sub, ast.Name):
            entry = _scoped_entry(
                name_const_map, sub.id, call_scope, call_line, call_col)
            value = entry[2] if entry is not None else None
            if isinstance(value, str) and _like_text_hit(value):
                return True
    return False
def _call_carries_like(call: ast.Call, name_const_map: dict,
                       call_scope: tuple = ()) -> bool:
    sql_arg = _call_sql_slot(call)
    if sql_arg is None:
        return False
    call_line = getattr(call, "lineno", 0) or 0
    call_col = getattr(call, "col_offset", 0) or 0
    return _subtree_carries_like(
        sql_arg, name_const_map, call_scope, call_line, call_col)
def _like_replacement_neutralizes(replacement: str, wildcard: str) -> bool:
    start = 0
    while True:
        index = replacement.find(wildcard, start)
        if index < 0:
            return True
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and replacement[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return False
        start = index + len(wildcard)
def _like_escaped_wildcard(node: ast.AST) -> str | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
        return None
    if node.func.attr != "replace" or len(node.args) < 2:
        return None
    wildcard, replacement = node.args[:2]
    if not (isinstance(wildcard, ast.Constant) and wildcard.value in ("%", "_")
            and isinstance(replacement, ast.Constant)
            and isinstance(replacement.value, str)):
        return None
    return (wildcard.value if _like_replacement_neutralizes(
        replacement.value, wildcard.value) else None)
def _arg_has_escape_hatch(arg: ast.AST) -> bool:
    escaped = {wildcard for sub in walk_nodes(arg)
               if (wildcard := _like_escaped_wildcard(sub)) is not None}
    return escaped == {"%", "_"}
def _call_has_escape_hatch(call: ast.Call) -> bool:
    sql_arg = _call_sql_slot(call)
    return sql_arg is not None and _arg_has_escape_hatch(sql_arg)
def _check_like_injection(code: Any, lines_local: Any, issues: Any, skip_spans: Any = None, *,
                          sql_calls: list | None = None,
                          name_const_map: dict[tuple, list] | None = None) -> None:
    if sql_calls is not None:
        _like_injection_ast_channel(sql_calls, lines_local, issues, name_const_map)
        return
    _like_injection_text_channel(code, lines_local, issues, skip_spans)
def _like_finding(ln: int, line: str) -> dict:
    return _se37_finding(
        "P1", ln, f"LIKE wildcard not escaped: {line}",
        _sql_fix_suggestion(
            "Escape LIKE params: val.replace('%', '\\\\%')"
            ".replace('_', '\\\\_')",
            root="根因: 代码实现中存在安全方面的问题, 需要规范化处理。"))
def _like_call_is_vulnerable(call: ast.Call, call_scope: Any,
                             name_const_map: dict | None) -> bool:
    return (_call_carries_like(call, name_const_map or {}, call_scope)
            and _call_has_dynamic_pattern(call)
            and not _call_has_escape_hatch(call))
def _like_injection_ast_channel(sql_calls: list, lines_local: list,
                                issues: list,
                                name_const_map: dict | None) -> None:
    _seen_lines: set[int] = set()
    for call, _call_scope in sql_calls:
        if not _like_call_is_vulnerable(call, _call_scope, name_const_map):
            continue
        ln = getattr(call, "lineno", 0)
        if not ln or ln in _seen_lines:
            continue
        _seen_lines.add(ln)
        line = (lines_local[ln - 1].strip()
                if 1 <= ln <= len(lines_local) else "")
        issues.append(_like_finding(ln, line))
def _like_injection_text_channel(code: str, lines_local: list,
                                 issues: list, skip_spans) -> None:
    for _match, line_no, line in _se37_iter_hits(
            _SE37_LIKE_INJECTION, code, lines_local, skip_spans,
            prefixes=_SE37_QUERY_PREFIXES):
        if ".replace(" in line or "escape(" in line:
            continue
        if not (_SE37_LIKE_FSTR_EVIDENCE.search(line)
                or _SE37_LIKE_PCT_EVIDENCE.search(line)
                or _SE37_LIKE_CONCAT_EVIDENCE.search(line)):
            continue
        issues.append(_like_finding(line_no, line))
def _check_async_sql(code: Any, lines_local: Any, issues: Any, skip_spans: Any = None,
                     fstr_interp_lines: Any = None,
                     skip_lines: set[int] | None = None) -> None:
    for match, line_no, _line in _se37_iter_hits(
            _SE37_ASYNC_SQL, code, lines_local, skip_spans):
        if skip_lines and line_no in skip_lines:
            continue
        if (fstr_interp_lines is not None
                and match.group().endswith(('f"', "f'"))
                and _line_no_at(code, match.end())
                not in fstr_interp_lines):
            continue
        issues.append(_se37_finding(
            "P0", line_no, "async SQL f-string concatenation",
            _sql_fix_suggestion(
                'Async SQL also needs parametrization: '
                'await conn.execute(sql, *params)')))
def _check_pandas_sql(code: Any, lines_local: Any, issues: Any, skip_spans: Any = None,
                      fstr_interp_lines: Any = None,
                      skip_lines: set[int] | None = None) -> None:
    for match, line_no, line in _se37_iter_hits(
            _SE37_READ_SQL, code, lines_local, skip_spans):
        if skip_lines and line_no in skip_lines:
            continue
        if (fstr_interp_lines is not None
                and _line_no_at(code, match.end())
                not in fstr_interp_lines):
            continue
        issues.append(_se37_finding(
            "P0", line_no,
            f"read_sql() with f-string: {line}",
            _sql_fix_suggestion(
                'read_sql() supports params: '
                'pd.read_sql(sql, conn, params=(val,))')))
def _check_dynamic_sql_slot(sql_exec_calls: list, lines_local: list,
                            issues: list, bindings: dict | None = None) -> None:
    _seen_lines: set[int] = set()
    for call, _call_scope in sql_exec_calls:
        sql_arg = _call_sql_slot(call)
        if not (_is_mod_format(sql_arg) or _is_dynamic_concat(sql_arg)):
            continue
        ln = getattr(call, "lineno", 0) or 0
        call_col = getattr(call, "col_offset", 0) or 0
        if (bindings is not None and _se37_literal_expression(
                sql_arg, bindings, _call_scope, ln, call_col)):
            continue
        if not ln or ln in _seen_lines:
            continue
        _seen_lines.add(ln)
        line = (lines_local[ln - 1].strip()
                if 1 <= ln <= len(lines_local) else "")
        issues.append(_se37_finding(
            _SE37_CONCAT_COPY.severity, ln,
            f"{_SE37_CONCAT_COPY.message}{line}",
            _SE37_CONCAT_COPY.suggestion))
def _check_format_sql(code: Any, lines_local: Any, issues: Any,
                      skip_spans: Any = None,
                      format_calls: list | None = None) -> None:
    if format_calls is not None:
        _seen_lines: set[int] = set()
        for call in format_calls:
            ln = getattr(call, "lineno", 0)
            if not ln or ln in _seen_lines:
                continue
            line = (lines_local[ln - 1].strip()
                    if 1 <= ln <= len(lines_local) else "")
            if "re.compile" in line:
                continue
            _seen_lines.add(ln)
            issues.append(_se37_finding(
                _SE37_FORMAT_COPY.severity, ln,
                f"{_SE37_FORMAT_COPY.message}{line}",
                _SE37_FORMAT_COPY.suggestion))
        return
    _emit_text_vector(
        _SE37_FORMAT_SQL, _SE37_FORMAT_COPY,
        code, lines_local, issues, skip_spans)
def _se37_byte_col_to_char(line_bytes: bytes, byte_col: int) -> int:
    if byte_col <= 0:
        return 0
    return len(line_bytes[:byte_col].decode("utf-8", errors="ignore"))
def _se37_match_in_string(m: re.Match, const_spans: list[tuple[int, int]]) -> bool:
    if not const_spans:
        return False
    start, end = m.start(), m.end()
    return any(start >= cs and end <= ce for cs, ce in const_spans)
def _se37_pos_in_string_span(pos: int, const_spans: list[tuple[int, int]]) -> bool:
    return any(cs <= pos < ce for cs, ce in const_spans)
def _se37_skip_string_literal(code: str, start: int) -> int:
    quote = code[start]
    triple = quote * 3
    n = len(code)
    if code.startswith(triple, start):
        end = code.find(triple, start + 3)
        return n if end == -1 else end + 3
    i = start + 1
    while i < n:
        if code[i] == "\\":
            i += 2
            continue
        if code[i] == quote:
            return i + 1
        i += 1
    return n
def _se37_anchor_in_call(code: str, call_open_end: int, anchor: int) -> bool:
    depth = 1
    i = call_open_end
    n = len(code)
    while i < anchor and i < n:
        ch = code[i]
        if ch in ("'", '"'):
            i = _se37_skip_string_literal(code, i)
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return False
        i += 1
    return depth >= 1
def _se37_record_name_const(node: ast.AST, name_const_map: dict,
                            scope_chains: dict, col: int,
                            global_decls: dict | None = None,
                            nonlocal_decls: dict | None = None,
                            local_names: dict | None = None) -> bool:
    if not isinstance(node, (ast.Assign, ast.AnnAssign)):
        return False
    scope = scope_chains.get(id(node), ())
    lineno = getattr(node, "lineno", 0) or 0
    for target, value in _assignment_target_values(node):
        constant = str_constant_value(value)
        for name, _line, _col in iter_target_bindings(target):
            binding_scope = _declared_binding_scope(
                scope, name, global_decls, nonlocal_decls, local_names)
            name_const_map.setdefault((binding_scope, name), []).append(
                (lineno, col, constant))
    return True
def _is_sql_exec_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if isinstance(node.func, ast.Attribute):
        return node.func.attr in _SQL_EXEC_METHODS_SE
    return (isinstance(node.func, ast.Name)
            and node.func.id in _SQL_EXEC_METHODS_SE)
_SE37_FORMAT_ROOT_KEYWORDS = _SQL_KEYWORDS_SE + ("TRUNCATE",)
_SE37_FORMAT_ROOT_RE = re.compile(
    _SQL_KEYWORD_BOUNDARY + r"(?:" + "|".join(_SE37_FORMAT_ROOT_KEYWORDS)
    + r")(?![A-Za-z0-9_])", re.IGNORECASE)
_SE37_FORMAT_STRUCTURE_KEYWORDS = ("FROM", "INTO", "TABLE", "JOIN",
                                   "SET", "VALUES", "WHERE")
_SE37_FORMAT_STRUCTURE_RE = re.compile(
    _SQL_KEYWORD_BOUNDARY + r"(?:" + "|".join(_SE37_FORMAT_STRUCTURE_KEYWORDS)
    + r")(?![A-Za-z0-9_])", re.IGNORECASE)
_SE37_FRAGMENT_KEYWORD_RE = re.compile(
    _SQL_KEYWORD_BOUNDARY + r"(?:FROM|TRUNCATE)(?![A-Za-z0-9_])",
    re.IGNORECASE)
def _se37_format_template_is_sql(template: str) -> bool:
    if not template:
        return False
    if not _SE37_FORMAT_ROOT_RE.search(template):
        return False
    if not _SE37_FORMAT_STRUCTURE_RE.search(template):
        return False
    try:
        return any(field is not None
                   for _, field, _, _ in string.Formatter().parse(template))
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_se37_format_template_is_sql:ValueError')
        return False
def _se37_literal_arg(node: ast.AST) -> bool:
    try:
        ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):  # jwsgj:silent-ok
        return False
    return True
def _se37_format_args_dynamic(node: ast.Call) -> bool:
    return (any(not _se37_literal_arg(arg) for arg in node.args)
            or any(not _se37_literal_arg(kw.value)
                   for kw in node.keywords))
def _se37_format_template(node: ast.Call, name_const_map: dict | None,
                          scope_chains: dict | None) -> str | None:
    template = str_constant_value(node.func.value)
    if template is not None:
        return template
    if not name_const_map or not isinstance(node.func.value, ast.Name):
        return None
    entry = _scoped_entry(
        name_const_map, node.func.value.id, (scope_chains or {}).get(id(node), ()),
        getattr(node, "lineno", 0) or 0, getattr(node, "col_offset", 0) or 0)
    return entry[2] if entry is not None else None
def _se37_record_format_call(node: ast.AST, format_sql_calls: list,
                             name_const_map: dict | None = None,
                             scope_chains: dict | None = None) -> bool:
    if as_format_call(node) is None:
        return False
    if not _se37_format_args_dynamic(node):
        return False
    template = _se37_format_template(node, name_const_map, scope_chains)
    if template is None or not _se37_format_template_is_sql(template):
        return False
    format_sql_calls.append(node)
    return True
def _se37_collect_ast_evidence(tree: Any, index: list | None,
                               lines_local: list) -> dict:
    _line_offsets, _line_bytes = _se37_line_layouts(lines_local)
    _const_spans: list[tuple[int, int]] = []
    _fstr_interp_lines: set[int] = set()
    _sql_exec_calls: list = []
    _name_const_map: dict = {}
    _format_sql_calls: list = []
    _scope_chains = (_build_scope_chains(tree)
                     if tree is not None else {})
    if tree is not None:
        _, global_decls, nonlocal_decls = _function_scope_semantics(
            tree, _scope_chains)
        local_names = _local_binding_names(
            tree, _scope_chains, global_decls, nonlocal_decls)
    else:
        global_decls, nonlocal_decls, local_names = {}, {}, {}
    if tree is not None:
        for node in iter_nodes(tree, index):
            span = _se37_const_span(
                node, lines_local, _line_offsets, _line_bytes)
            if span is not None:
                _const_spans.append(span)
                continue
            if _is_interpolated_fstring(node):
                _fstr_interp_lines.add(getattr(node, "lineno", 0))
                continue
            if _se37_record_name_const(
                    node, _name_const_map, _scope_chains,
                    getattr(node, "col_offset", 0) or 0,
                    global_decls, nonlocal_decls, local_names):
                continue
            if _se37_record_format_call(node, _format_sql_calls):
                continue
            if _is_sql_exec_call(node):
                _sql_exec_calls.append(
                    (node, _scope_chains.get(id(node), ())))
        for node in iter_nodes(tree, index):
            if (as_format_call(node) is not None
                    and isinstance(node.func.value, ast.Name)):
                _se37_record_format_call(
                    node, _format_sql_calls, _name_const_map, _scope_chains)
    return {
        "const_spans": _const_spans,
        "fstr_interp_lines": _fstr_interp_lines,
        "sql_exec_calls": _sql_exec_calls,
        "name_const_map": _name_const_map,
        "format_sql_calls": _format_sql_calls,
        "scope_chains": _scope_chains,
    }
def _se37_line_layouts(lines_local: list) -> tuple:
    _line_offsets = [0]
    for _l in lines_local:
        _line_offsets.append(_line_offsets[-1] + len(_l) + 1)
    _line_bytes = [_l.encode("utf-8") for _l in lines_local]
    return _line_offsets, _line_bytes
def _se37_const_span(node: ast.AST, lines_local: list,
                     _line_offsets: list, _line_bytes: list) -> tuple | None:
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return None
    _ln = getattr(node, "lineno", 0)
    _eln = getattr(node, "end_lineno", _ln) or _ln
    if not (1 <= _ln <= len(lines_local) and 1 <= _eln <= len(lines_local)):
        return None
    return (
        _line_offsets[_ln - 1] + _se37_byte_col_to_char(
            _line_bytes[_ln - 1], getattr(node, "col_offset", 0) or 0),
        _line_offsets[_eln - 1] + _se37_byte_col_to_char(
            _line_bytes[_eln - 1], getattr(node, "end_col_offset", 0) or 0),
    )
def _se37_indirect_sql_phase(tree: Any, index: list | None,
                             issues: list, scope_chains: dict) -> dict:
    nodes = list(iter_nodes(tree, index))
    _, global_decls, nonlocal_decls = _function_scope_semantics(
        tree, scope_chains)
    local_names = _local_binding_names(
        tree, scope_chains, global_decls, nonlocal_decls)
    _bindings = _se37_collect_indirect_sql_bindings(
        nodes, scope_chains, global_decls, nonlocal_decls, local_names)
    if _bindings:
        _se37_emit_indirect_findings(nodes, _bindings, scope_chains, issues)
    return _bindings
def _se37_fstr_from_truncate_gate(joined_str: ast.JoinedStr) -> bool:
    literal = _fstring_literal_text(joined_str)
    return bool(_SE37_FRAGMENT_KEYWORD_RE.search(literal)
                and not _sql_keyword_hit(literal))
def _se37_dynamic_interpolation(value: ast.AST) -> bool:
    return _is_mod_format(value) or _is_dynamic_concat(value)
def _se37_binding_kind(value: ast.AST) -> str:
    if _is_interpolated_fstring(value) and _se37_fstr_from_truncate_gate(value):
        return "dynamic"
    if str_constant_value(value) is not None or _is_constant_fstring(value):
        return "literal"
    if _se37_dynamic_interpolation(value):
        return "dynamic"
    return "derive"
def _se37_literal_expression(value: ast.AST, bindings: dict, scope: tuple,
                             lineno: int, col: int) -> bool:
    if isinstance(value, ast.Constant) or _is_constant_fstring(value):
        return True
    if isinstance(value, ast.Name):
        entry = _scoped_entry(bindings, value.id, scope, lineno, col)
        return entry is not None and entry[2] == "literal"
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        return all(_se37_literal_expression(
            item, bindings, scope, lineno, col) for item in value.elts)
    if isinstance(value, ast.Dict):
        return all(
            key is not None and _se37_literal_expression(
                key, bindings, scope, lineno, col)
            for key in value.keys) and all(
                _se37_literal_expression(item, bindings, scope, lineno, col)
                for item in value.values)
    if isinstance(value, ast.BinOp) and isinstance(value.op, (ast.Add, ast.Mod)):
        return (_se37_literal_expression(
            value.left, bindings, scope, lineno, col)
            and _se37_literal_expression(
                value.right, bindings, scope, lineno, col))
    return False
def _se37_collect_indirect_sql_bindings(nodes, scope_chains: dict,
                                        global_decls: dict | None = None,
                                        nonlocal_decls: dict | None = None,
                                        local_names: dict | None = None
                                        ) -> dict:
    _records: list = []
    for assign in nodes:
        if (isinstance(assign, ast.AugAssign)
                and isinstance(assign.op, (ast.Add, ast.Mod))):
            assignments = [(assign.target, assign.value)]
        else:
            assignments = _assignment_target_values(assign)
        if not assignments:
            continue
        _lineno = getattr(assign, "lineno", 0) or 0
        _col = getattr(assign, "col_offset", 0) or 0
        _scope = scope_chains.get(id(assign), ())
        for target, value in assignments:
            if not isinstance(target, ast.Name):
                continue
            _value_kind = _se37_binding_kind(value)
            if isinstance(assign, ast.AugAssign):
                _kind = "derive" if _value_kind == "literal" else "dynamic"
                _literal_kind = "derive"
            else:
                _kind = _value_kind
                _literal_kind = "literal"
            entry = [_lineno, _col, _kind]
            source_name = (
                value.id if not isinstance(assign, ast.AugAssign)
                and isinstance(value, ast.Name) else None)
            binding_scope = _declared_binding_scope(
                _scope, target.id, global_decls, nonlocal_decls, local_names)
            _records.append((
                _lineno, _col, _scope, binding_scope, target.id,
                source_name, value, _literal_kind, entry))
    bindings: dict = {}
    ordered = sorted(_records, key=lambda item: (item[0], item[1]))
    for (_lineno, _col, _scope, binding_scope, _name, _source_name, value,
         _literal_kind, entry) in ordered:
        if (entry[2] == "dynamic" and _se37_literal_expression(
                value, bindings, _scope, _lineno, _col)):
            entry[2] = _literal_kind
        if entry[2] == "derive":
            source = None
            if _source_name is not None:
                source = _scoped_entry(
                    bindings, _source_name, _scope, _lineno, _col)
            if source is None:
                source = _scoped_entry(
                    bindings, _name, _scope, _lineno, _col)
            entry[2] = source[2] if source is not None else "unknown"
        bindings.setdefault((binding_scope, _name), []).append(entry)
    return bindings
def _se37_indirect_finding(call: ast.Call, arg_name: str) -> dict:
    member = (call.func.attr if isinstance(call.func, ast.Attribute)
              else call.func.id)
    return _se37_finding(
        "P0", call.lineno,
        f"Indirect SQL injection: dynamic SQL built into '{arg_name}' "
        f"then passed to {member}()",
        _sql_fix_suggestion(
            'Use parameterized queries: cursor.execute(sql, (param,))'))
def _se37_indirect_sql_arg(call: ast.Call, bindings: dict,
                           call_scope: tuple) -> str | None:
    arg = _call_sql_slot(call)
    if not isinstance(arg, ast.Name):
        return None
    call_line = getattr(call, "lineno", 0) or 0
    call_col = getattr(call, "col_offset", 0) or 0
    entry = _scoped_entry(
        bindings, arg.id, call_scope, call_line, call_col,
        enclosing_runtime=True)
    return arg.id if entry is not None and entry[2] == "dynamic" else None
def _se37_emit_indirect_findings(nodes, bindings: dict,
                                 scope_chains: dict, issues: list) -> None:
    for call in nodes:
        if not _is_sql_exec_call(call):
            continue
        arg_name = _se37_indirect_sql_arg(
            call, bindings, scope_chains.get(id(call), ()))
        if arg_name is not None:
            issues.append(_se37_indirect_finding(call, arg_name))
def check_SE37(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    if not isinstance(source_lines, (list, str)):
        return []
    raw_code = ("\n".join(source_lines) if isinstance(source_lines, list)
                else source_lines)
    code = "\n".join(ast_split_lines(raw_code))
    lines_local = code.split("\n")
    issues = []
    _idx = list(index) if index is not None else None
    _ev = _se37_collect_ast_evidence(tree, _idx, lines_local)
    _const_spans = _ev["const_spans"]
    _fstr_filter = _ev["fstr_interp_lines"] if tree is not None else None
    _like_calls_filter = _ev["sql_exec_calls"] if tree is not None else None
    _like_map_filter = _ev["name_const_map"] if tree is not None else None
    _format_calls_filter = _ev["format_sql_calls"] if tree is not None else None
    _dynamic_lines = _emit_text_vector(
        _SE37_DYNAMIC_ID, _SE37_DYNAMIC_ID_COPY,
        code, lines_local, issues, _const_spans)
    _indirect_bindings = {}
    if tree is not None:
        _indirect_bindings = _se37_indirect_sql_phase(
            tree, _idx, issues, _ev["scope_chains"])
    _check_orm_bypass(code, lines_local, issues, _const_spans)
    _check_like_injection(code, lines_local, issues, _const_spans,
                          sql_calls=_like_calls_filter,
                          name_const_map=_like_map_filter)
    _emit_text_vector(
        _SE37_COMMENT, _SE37_COMMENT_COPY,
        code, lines_local, issues, _const_spans)
    _check_async_sql(code, lines_local, issues, _const_spans, _fstr_filter,
                     _dynamic_lines)
    _check_pandas_sql(code, lines_local, issues, _const_spans, _fstr_filter,
                      _dynamic_lines)
    _check_format_sql(code, lines_local, issues, _const_spans,
                      _format_calls_filter)
    if _like_calls_filter is not None:
        _check_dynamic_sql_slot(
            _like_calls_filter, lines_local, issues, _indirect_bindings)
    return issues
_SE06_EXTERNAL_HINTS = ('request', 'input', 'params', 'query', 'form',
                        'cookie', 'header', 'upload', 'user', 'getenv',
                        'environ', 'argv', 'user_input', 'userfile',
                        'userpath')
_SE06_TOKEN_SPLIT = re.compile(r'[^A-Za-z0-9]+')
_SE06_CAMEL_SPLIT = re.compile(r'(?<=[a-z0-9])(?=[A-Z])')
_SE06_EXTERNAL_TOKEN_SET = frozenset(
    hint for hint in _SE06_EXTERNAL_HINTS if '_' not in hint
    and hint not in ('userfile', 'userpath'))
_SE06_EXTERNAL_COMPOUNDS = ('userinput', 'userfile', 'userpath')
def _se06_name_tokens(name: str) -> tuple[str, ...]:
    tokens: list[str] = []
    for seg in _SE06_TOKEN_SPLIT.split(str(name)):
        if seg:
            tokens.extend(_SE06_CAMEL_SPLIT.sub(' ', seg).lower().split())
    return tuple(tokens)
def _se06_attr_chain(node: ast.AST) -> str:
    chain = []
    n = node
    while isinstance(n, (ast.Attribute, ast.Subscript)):
        if isinstance(n, ast.Attribute):
            chain.append(n.attr)
        n = n.value
    if isinstance(n, ast.Name):
        chain.append(n.id)
    return '.'.join(reversed(chain)).lower()
_SE06_ATTR_EXTERNAL_PREFIXES = ('request.', 'form.', 'query.', 'cookies.', 'headers.')
def _se06_token_is_external(token: str) -> bool:
    if token in _SE06_EXTERNAL_TOKEN_SET:
        return True
    return any(len(hint) >= 5 and token == hint + 's'
               for hint in _SE06_EXTERNAL_TOKEN_SET)
def _se06_name_is_external(name: str) -> bool:
    tokens = _se06_name_tokens(name)
    if not tokens:
        return False
    if any(_se06_token_is_external(token) for token in tokens):
        return True
    joined = ''.join(tokens)
    return any(compound in joined for compound in _SE06_EXTERNAL_COMPOUNDS)
def _se06_attr_chain_is_external(full: str) -> bool:
    return (full.startswith(_SE06_ATTR_EXTERNAL_PREFIXES)
            or _se06_name_is_external(full))
_BUILTIN_INPUT_CALLS = frozenset({'input', 'raw_input'})
_BUILTIN_INPUT_SCOPES = frozenset({'builtins', '__builtins__'})
def _se06_call_is_external(call: ast.Call) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        return func.id in _BUILTIN_INPUT_CALLS
    if isinstance(func, ast.Attribute):
        return _se06_attr_chain_is_external(_se06_attr_chain(func))
    return False
def _se06_arg_is_external(arg: ast.AST) -> bool:
    if isinstance(arg, ast.Name):
        return _se06_name_is_external(arg.id)
    if isinstance(arg, ast.Subscript):
        return _se06_arg_is_external(arg.value)
    if isinstance(arg, ast.Attribute):
        return _se06_attr_chain_is_external(_se06_attr_chain(arg))
    if isinstance(arg, ast.Call):
        if _se06_call_is_external(arg):
            return True
        return (any(_se06_arg_is_external(value) for value in arg.args)
                or any(_se06_arg_is_external(kw.value)
                       for kw in arg.keywords))
    if isinstance(arg, ast.BinOp):
        return (_se06_arg_is_external(arg.left)
                or _se06_arg_is_external(arg.right))
    if isinstance(arg, ast.JoinedStr):
        return any(isinstance(value, ast.FormattedValue)
                   and _se06_arg_is_external(value.value)
                   for value in arg.values)
    if isinstance(arg, ast.Starred):
        return _se06_arg_is_external(arg.value)
    if isinstance(arg, (ast.List, ast.Tuple, ast.Set)):
        return any(_se06_arg_is_external(elt) for elt in arg.elts)
    if isinstance(arg, ast.Dict):
        return any(_se06_arg_is_external(item)
                   for item in arg.values if item is not None)
    if isinstance(arg, ast.IfExp):
        return (_se06_arg_is_external(arg.body)
                or _se06_arg_is_external(arg.orelse))
    if isinstance(arg, ast.BoolOp):
        return any(_se06_arg_is_external(value) for value in arg.values)
    if isinstance(arg, ast.NamedExpr):
        return _se06_arg_is_external(arg.value)
    if isinstance(arg, ast.Await):
        return _se06_arg_is_external(arg.value)
    return False
class _Se06Targets(NamedTuple):
    join_calls: frozenset
    path_calls: frozenset
def _se06_collect_targets(tree: Any) -> _Se06Targets:
    os_names, path_mod_names = collect_module_bindings(tree, 'os', ('path',))
    osp_names, join_bare = collect_module_bindings(tree, 'os.path', ('join',))
    pl_names, path_bare = collect_module_bindings(tree, 'pathlib', ('Path',))
    join_calls = {'os.path.join'}
    join_calls |= {f'{a}.path.join' for a in os_names}
    join_calls |= {f'{a}.join' for a in (osp_names | path_mod_names)}
    join_calls |= set(join_bare)
    path_calls = {'pathlib.Path'}
    path_calls |= {f'{a}.Path' for a in pl_names}
    path_calls |= set(path_bare)
    return _Se06Targets(frozenset(join_calls), frozenset(path_calls))
def _se06_has_external_arg(node: ast.Call) -> bool:
    if all(isinstance(a, ast.Constant) for a in node.args):
        return False
    return any(_se06_arg_is_external(a) for a in node.args)
def _se06_finding(node: ast.AST, func_name: str, filepath: Any,
                  source_lines: Any, *, path_chain: bool = False) -> dict:
    return {
        "rule_id": "SE-06",
        "severity": "P0",
        "dimension": "security",
        "file": filepath,
        "line": node.lineno,
        "title": (f"{func_name} 路径拼接外部输入" if path_chain
                  else f"{func_name} 拼接外部输入"),
        "message": (f"{func_name} 拼接外部输入, 存在路径遍历风险"
                    if path_chain
                    else f"{func_name}() 拼接外部输入, 存在路径遍历风险"),
        "suggestion": get_fix_guidance("SE-06"),
        "rule_ref": "OWASP A01 / CWE-22",
        "code_snippet": get_code_snippet(source_lines, node.lineno),
    }
def _se06_is_path_anchor(node: ast.AST, path_calls: frozenset,
                         shadowed: set[int] | None = None) -> bool:
    if isinstance(node, ast.Call):
        if shadowed is not None and id(node) in shadowed:
            return False
        func_name = get_call_name(node)
        if func_name in path_calls:
            return True
        return (isinstance(node.func, ast.Attribute)
                and node.func.attr == "joinpath"
                and _se06_is_path_anchor(
                    node.func.value, path_calls, shadowed))
    if isinstance(node, ast.Attribute):
        return _se06_is_path_anchor(node.value, path_calls, shadowed)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return _se06_is_path_anchor(node.left, path_calls, shadowed)
    return False
def _se06_is_path_chain(node: ast.AST, path_calls: frozenset,
                        shadowed: set[int] | None = None) -> bool:
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)
            and _se06_is_path_anchor(node.left, path_calls, shadowed))
_SE06_IMPORT_SOURCES = (
    ("os", ("path",)),
    ("os.path", ("join",)),
    ("pathlib", ("Path",)),
)
def check_SE06(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _targets = _se06_collect_targets(tree)
    _call_targets = _targets.join_calls | _targets.path_calls
    _shadowed = _shadowed_call_ids(
        tree, index, lambda _value: False,
        lambda node, alias: any(
            _import_matches(node, alias, module, members)
            for module, members in _SE06_IMPORT_SOURCES),
        from_import_attr_ok=True)
    for node in iter_nodes(tree, index):
        if id(node) in _shadowed:
            continue
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "joinpath"
                and _se06_is_path_anchor(node.func.value,
                                         _targets.path_calls, _shadowed)):
            if any(_se06_arg_is_external(arg) for arg in node.args):
                issues.append(_se06_finding(
                    node, "pathlib.Path", filepath, source_lines,
                    path_chain=True))
            continue
        if isinstance(node, ast.Call):
            _func_name = get_call_name(node)
            if _func_name not in _call_targets:
                continue
            if not _se06_has_external_arg(node):
                continue
            issues.append(_se06_finding(
                node, _func_name, filepath, source_lines))
            continue
        if (_se06_is_path_chain(node, _targets.path_calls, _shadowed)
                and _se06_arg_is_external(node.right)):
            issues.append(_se06_finding(
                node, "pathlib.Path", filepath, source_lines,
                path_chain=True))
    return issues
def _pt01_member_aliases(namespace: list, members) -> set:
    return {alias.asname or alias.name
            for alias in namespace
            if alias.name != "*" and alias.name in members}
_UNTRUSTED_SOURCE_HINTS = ("request", "socket", "urlopen", "urllib",
                           "environ", "getenv", "argv")
_UNTRUSTED_HINT_RE = re.compile(
    r"(?<![A-Za-z0-9_])("
    + "|".join(map(re.escape, _UNTRUSTED_SOURCE_HINTS))
    + r")(?![A-Za-z0-9_])")
def _has_untrusted_hint(text: str) -> bool:
    return bool(_UNTRUSTED_HINT_RE.search(text))
def _is_untrusted_source_call(func_name: str) -> bool:
    scope, _, leaf = func_name.rpartition(".")
    if (leaf in _BUILTIN_INPUT_CALLS
            and (not scope or scope in _BUILTIN_INPUT_SCOPES)):
        return True
    return _has_untrusted_hint(func_name)
def _unparsed_text(node: ast.AST) -> str:
    try:
        return ast.unparse(node)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_unparsed_text:{type(_e).__name__}')
        return ""
def _is_untrusted_source_expr(value: ast.AST) -> bool:
    if isinstance(value, ast.Call):
        return _is_untrusted_source_call(_unparsed_text(value.func))
    if isinstance(value, (ast.Subscript, ast.Attribute)):
        return _has_untrusted_hint(_unparsed_text(value))
    return False
_OS_MODULE_FAMILY = frozenset({"os"})
_JOIN_MODULE_FAMILY = frozenset({"ntpath", "posixpath"})
class _PT01Context(NamedTuple):
    os_path_bindings: frozenset
    join_bare_names: frozenset
    os_module_aliases: frozenset
    bindings: dict
    parent_map: dict
def _pt01_collect_import(node: ast.Import, os_path_bindings: set,
                          os_module_aliases: set) -> None:
    for alias in node.names:
        if alias.name == "os":
            os_module_aliases.add(alias.asname or "os")
        elif alias.name in _JOIN_MODULE_FAMILY:
            os_path_bindings.add(alias.asname or alias.name)
        elif alias.name == "os.path" and alias.asname:
            os_path_bindings.add(alias.asname)
def _pt01_collect_import_from(node: ast.ImportFrom, os_path_bindings: set,
                              join_bare_names: set) -> None:
    if node.level:
        return
    if node.module == "os":
        os_path_bindings.update(
            _pt01_member_aliases(node.names, ("path",)))
    elif node.module in ("os.path", "ntpath", "posixpath"):
        join_bare_names.update(
            _pt01_member_aliases(node.names, ("join",)))
_PT01_KIND_UNTRUSTED = "untrusted"
_PT01_KIND_OTHER = "other"
_PT01_SCOPE_STOPS = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.ClassDef, ast.Lambda)
_PT01_FUNCTION_SCOPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _pt01_nearest_scope(node: ast.AST | None,
                        parent_map: dict) -> ast.AST | None:
    while node is not None and not isinstance(node, _PT01_SCOPE_STOPS):
        node = parent_map.get(id(node))
    return node
def _pt01_parent_scope(scope: ast.AST, parent_map: dict) -> ast.AST | None:
    parent = _pt01_nearest_scope(parent_map.get(id(scope)), parent_map)
    if isinstance(scope, _PT01_FUNCTION_SCOPES):
        while isinstance(parent, ast.ClassDef):
            parent = _pt01_nearest_scope(parent_map.get(id(parent)), parent_map)
    return parent
def _pt01_lookup_kind(bindings: dict, name: str, scope: Any,
                      lineno: int, col: int, parent_map: dict) -> str | None:
    initial_scope = scope
    chain = scope
    while chain is not None:
        entries = bindings.get((id(chain), name))
        if entries:
            if (chain is not initial_scope
                    and isinstance(initial_scope, _PT01_FUNCTION_SCOPES)):
                return max(entries, key=lambda entry: (entry[0], entry[1]))[2]
            prior = [entry for entry in entries
                     if (entry[0], entry[1]) <= (lineno, col)]
            if not prior:
                if isinstance(chain, ast.ClassDef):
                    chain = _pt01_parent_scope(chain, parent_map)
                    continue
                return None
            return max(prior, key=lambda entry: (entry[0], entry[1]))[2]
        chain = _pt01_parent_scope(chain, parent_map)
    return None
def _pt01_is_literal(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            or _is_constant_fstring(node)
            or _pt01_is_literal_sequence(node)
            or _pt01_is_literal_mapping(node))
def _pt01_is_literal_sequence(node: ast.AST) -> bool:
    return isinstance(node, (ast.Tuple, ast.List, ast.Set)) and all(
        _pt01_is_literal(e) for e in node.elts)
def _pt01_is_literal_mapping(node: ast.AST) -> bool:
    return isinstance(node, ast.Dict) and (
        all(k is None or _pt01_is_literal(k) for k in node.keys)
        and all(_pt01_is_literal(v) for v in node.values))
def _pt01_iter_untrusted(iter_obj: ast.AST, scope: Any, bindings: dict,
                         parent_map: dict, lineno: int, col: int) -> bool:
    if _is_untrusted_source_expr(iter_obj):
        return True
    if isinstance(iter_obj, ast.Call):
        return (any(_pt01_iter_untrusted(
                        arg, scope, bindings, parent_map, lineno, col)
                    for arg in iter_obj.args)
                or any(_pt01_iter_untrusted(
                        kw.value, scope, bindings, parent_map, lineno, col)
                       for kw in iter_obj.keywords))
    if not isinstance(iter_obj, ast.Name):
        return False
    return (_pt01_lookup_kind(bindings, iter_obj.id, scope, lineno, col,
                              parent_map) == _PT01_KIND_UNTRUSTED)
def _pt01_loop_events(node: ast.For | ast.AsyncFor, scope: Any,
                      bindings: dict, parent_map: dict) -> list:
    target_bindings = list(iter_target_bindings(node.target))
    if not target_bindings:
        return []
    kind = (_PT01_KIND_UNTRUSTED
            if _pt01_iter_untrusted(node.iter, scope, bindings, parent_map,
                                    node.lineno, node.col_offset)
            else _PT01_KIND_OTHER)
    return [(name, lineno, col, kind)
            for name, lineno, col in target_bindings]
def _pt01_comprehension_events(node: ast.comprehension, scope: Any,
                               bindings: dict, parent_map: dict) -> list:
    target_bindings = list(iter_target_bindings(node.target))
    if not target_bindings:
        return []
    parent = parent_map.get(id(node))
    line = getattr(parent, "lineno", 0) or 0
    col = getattr(parent, "col_offset", 0) or 0
    kind = (_PT01_KIND_UNTRUSTED
            if _pt01_iter_untrusted(node.iter, scope, bindings, parent_map,
                                    line, col)
            else _PT01_KIND_OTHER)
    return [(name, line, col, kind)
            for name, _lineno, _col in target_bindings]
def _pt01_assignment_source(node: ast.AST) -> list[tuple] | None:
    if isinstance(node, ast.AugAssign):
        return [(node.target, ast.BinOp(
            left=node.target, op=node.op, right=node.value))]
    pair = assign_targets_value(node)
    if pair is not None:
        _targets, value = pair
        return [(target, value if item_value is None else item_value)
                for target, item_value in _assignment_target_values(node)]
    if isinstance(node, ast.NamedExpr):
        return [(node.target, node.value)]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [(item.optional_vars, item.context_expr)
                for item in node.items if item.optional_vars is not None]
    return None
_PT01_EXPR_SCOPE_STOPS = (ast.Lambda, ast.FunctionDef,
                          ast.AsyncFunctionDef, ast.ClassDef)
def _pt01_expr_nodes(node: ast.AST) -> list[ast.AST]:
    nodes: list[ast.AST] = []
    stack = [node]
    while stack:
        current = stack.pop()
        if isinstance(current, _PT01_EXPR_SCOPE_STOPS):
            continue
        nodes.append(current)
        stack.extend(ast.iter_child_nodes(current))
    return nodes
def _pt01_inherited_kind(source_value: ast.AST | None, scope: Any,
                          bindings: dict, parent_map: dict,
                          lineno: int, col: int) -> str:
    if source_value is None:
        return _PT01_KIND_OTHER
    nodes = _pt01_expr_nodes(source_value)
    if any(_is_untrusted_source_expr(sub) for sub in nodes):
        return _PT01_KIND_UNTRUSTED
    kinds = {_pt01_lookup_kind(bindings, name.id, scope, lineno, col,
                              parent_map)
             for name in nodes if isinstance(name, ast.Name)}
    if _PT01_KIND_UNTRUSTED in kinds:
        return _PT01_KIND_UNTRUSTED
    return _PT01_KIND_OTHER
def _pt01_assignment_events(node: ast.AST, scope: Any, bindings: dict,
                            parent_map: dict) -> list:
    assignments = _pt01_assignment_source(node)
    if assignments is None:
        return []
    events = []
    for target, source_value in assignments:
        for name, lineno, col in iter_target_bindings(target):
            kind = (_PT01_KIND_OTHER
                    if source_value is None or _pt01_is_literal(source_value)
                    else _pt01_inherited_kind(
                        source_value, scope, bindings, parent_map, lineno, col))
            events.append((name, lineno, col, kind))
    return events
def _pt01_node_events(node: ast.AST, scope: Any, bindings: dict,
                      parent_map: dict) -> list:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _pt01_loop_events(node, scope, bindings, parent_map)
    if isinstance(node, ast.comprehension):
        return _pt01_comprehension_events(
            node, scope, bindings, parent_map)
    if isinstance(node, ast.ExceptHandler):
        if not node.name:
            return []
        return [(node.name, node.lineno, node.col_offset,
                 _PT01_KIND_OTHER)]
    return _pt01_assignment_events(node, scope, bindings, parent_map)
def _pt01_build_bindings(binding_nodes: list, param_nodes: list,
                         parent_map: dict,
                         declaration_nodes: list | None = None) -> dict:
    bindings: dict = {}
    global_decls: dict[int, set[str]] = {}
    nonlocal_decls: dict[int, set[str]] = {}
    for node in declaration_nodes or ():
        scope = _pt01_nearest_scope(node, parent_map)
        declarations = (global_decls if isinstance(node, ast.Global)
                        else nonlocal_decls)
        declarations.setdefault(
            id(scope) if scope is not None else 0, set()).update(node.names)
    root = next(
        (node for node in parent_map.values() if isinstance(node, ast.Module)),
        None)
    lexical_nodes = (list(walk_nodes(root)) if root is not None else
                     list(binding_nodes) + list(param_nodes))
    local_names: dict[int, set[str]] = {}
    def _note_local(scope_node, name: str) -> None:
        scope_key = id(scope_node) if scope_node is not None else 0
        if (name in global_decls.get(scope_key, ())
                or name in nonlocal_decls.get(scope_key, ())):
            return
        local_names.setdefault(scope_key, set()).add(name)
    for node in lexical_nodes:
        scope = _pt01_nearest_scope(node, parent_map)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            if not isinstance(node, ast.Lambda):
                _note_local(_pt01_parent_scope(node, parent_map), node.name)
            for name in argument_param_names(node.args):
                _note_local(node, name)
            continue
        if isinstance(node, ast.ClassDef):
            _note_local(_pt01_parent_scope(node, parent_map), node.name)
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                if alias.name == "*":
                    continue
                name = (alias.asname or alias.name.split('.')[0]
                        if isinstance(node, ast.Import)
                        else alias.asname or alias.name)
                _note_local(scope, name)
            continue
        if isinstance(node, (ast.For, ast.AsyncFor)):
            targets = [node.target]
        elif isinstance(node, ast.ExceptHandler):
            if node.name:
                _note_local(scope, node.name)
            continue
        else:
            targets = [target for target, _source in
                       _pt01_assignment_source(node) or ()]
        for target in targets:
            for name, _lineno, _col in iter_target_bindings(target):
                _note_local(scope, name)
    def _record(scope_node, name, lineno, col, kind) -> None:
        scope_key = id(scope_node) if scope_node is not None else 0
        if name in global_decls.get(scope_key, ()):
            while (scope_node is not None
                   and not isinstance(scope_node, ast.Module)):
                scope_node = _pt01_parent_scope(scope_node, parent_map)
        elif name in nonlocal_decls.get(scope_key, ()):
            scope_node = _pt01_parent_scope(scope_node, parent_map)
            while (scope_node is not None
                   and not isinstance(scope_node, ast.Module)
                   and name not in local_names.get(id(scope_node), ())):
                scope_node = _pt01_parent_scope(scope_node, parent_map)
        key = (id(scope_node) if scope_node is not None else 0, name)
        bindings.setdefault(key, []).append((lineno, col, kind))
    for fn in param_nodes:
        _lineno = getattr(fn, "lineno", 0) or 0
        for name in argument_param_names(fn.args):
            _record(fn, name, _lineno, 0, _PT01_KIND_OTHER)
    for node in sorted(binding_nodes,
                       key=lambda n: (getattr(n, "lineno", 0),
                                      getattr(n, "col_offset", 0))):
        scope = _pt01_nearest_scope(node, parent_map)
        for name, lineno, col, kind in _pt01_node_events(
                node, scope, bindings, parent_map):
            _record(scope, name, lineno, col, kind)
    return bindings
class _PT01Collector:
    __slots__ = ("binding_nodes", "declaration_nodes", "join_bare_names",
                 "os_module_aliases", "os_path_bindings", "param_nodes")
    def __init__(self) -> None:
        self.os_path_bindings: set = set()
        self.join_bare_names: set = set()
        self.os_module_aliases: set = set()
        self.binding_nodes: list = []
        self.param_nodes: list = []
        self.declaration_nodes: list = []
    def feed(self, node: ast.AST) -> None:
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            self.declaration_nodes.append(node)
        if isinstance(node, ast.Import):
            _pt01_collect_import(
                node, self.os_path_bindings, self.os_module_aliases)
        elif isinstance(node, ast.ImportFrom):
            _pt01_collect_import_from(
                node, self.os_path_bindings, self.join_bare_names)
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension,
                               ast.Assign, ast.AnnAssign, ast.AugAssign,
                               ast.NamedExpr, ast.With, ast.AsyncWith,
                               ast.ExceptHandler)):
            self.binding_nodes.append(node)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            self.param_nodes.append(node)
    def freeze(self, parent_map: dict) -> _PT01Context:
        return _PT01Context(
            os_path_bindings=frozenset(self.os_path_bindings),
            join_bare_names=frozenset(self.join_bare_names),
            os_module_aliases=frozenset(self.os_module_aliases),
            bindings=_pt01_build_bindings(
                self.binding_nodes, self.param_nodes, parent_map,
                self.declaration_nodes),
            parent_map=parent_map,
        )
def _collect_pt01_context(tree: Any) -> _PT01Context:
    collector = _PT01Collector()
    for node in iter_nodes(tree, None):
        collector.feed(node)
    return collector.freeze(build_parent_map(tree) if tree is not None else {})
def _is_two_level_path_join(func: ast.AST, os_module_bindings: set) -> bool:
    return (isinstance(func, ast.Attribute) and func.attr == "join"
            and isinstance(func.value, ast.Attribute)
            and func.value.attr == "path"
            and isinstance(func.value.value, ast.Name)
            and func.value.value.id in os_module_bindings)
def _is_os_path_join_call(node: ast.Call, join_mod_bindings: set,
                          join_bare_names: set,
                          os_module_bindings: set) -> bool:
    if _is_two_level_path_join(node.func, os_module_bindings):
        return True
    func_name = dotted_name(node.func)
    if func_name in join_bare_names:
        return True
    return any(func_name == f"{mod}.join" for mod in join_mod_bindings)
def _first_untrusted_join_arg(node: ast.Call, ctx: _PT01Context) -> Any:
    scope = _pt01_nearest_scope(node, ctx.parent_map)
    lineno = getattr(node, "lineno", 0) or 0
    col = getattr(node, "col_offset", 0) or 0
    for arg in node.args:
        if isinstance(arg, ast.Name):
            if _pt01_lookup_kind(
                    ctx.bindings, arg.id, scope, lineno, col,
                    ctx.parent_map) == _PT01_KIND_UNTRUSTED:
                return arg.id
            continue
        if (_is_untrusted_source_expr(arg)
                or _pt01_inherited_kind(
                    arg, scope, ctx.bindings, ctx.parent_map,
                    lineno, col) == _PT01_KIND_UNTRUSTED):
            return _unparsed_text(arg)
    return None
def _make_pt01_issue(node: ast.Call, name: str, source: Any,
                     filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="PT-01", severity="P1", dimension="path_security",
        file=filepath, line=node.lineno, col_offset=node.col_offset,
        title="os.path.join() 路径穿越风险",
        description=(f"os.path.join() 接收变量 '{name}' 且未做路径校验 "
                     "(OWASP A01:2021)."),
        suggestion='根因: 路径拼接使用了未经校验的不可信来源输入。'
                   '该问题属于路径安全类别。\n'
                   '修复策略: 用 os.path.realpath() + os.path.commonpath() '
                   '对白名单做路径校验。\n'
                   '参考标准: OWASP A01:2021 / PEP 8 / pylint',
        rule_ref="OWASP A01:2021",
        code_snippet=extract_code_lines(source, node.lineno))
_PT01_IMPORT_SOURCES = (
    ("os", ("path",)),
    ("os.path", ("join",)),
    ("ntpath", ("join",)),
    ("posixpath", ("join",)),
)
def check_PT01(tree: Any, source_lines: Any, filepath: Any, index: Any = None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    source = join_source_lines(source_lines)
    ctx = _collect_pt01_context(tree)
    os_module_bindings = _OS_MODULE_FAMILY | ctx.os_module_aliases
    join_mod_bindings = _JOIN_MODULE_FAMILY | ctx.os_path_bindings
    _shadowed = _shadowed_call_ids(
        tree, index, lambda _value: False,
        lambda node, alias: any(
            _import_matches(node, alias, module, members)
            for module, members in _PT01_IMPORT_SOURCES),
        from_import_attr_ok=True)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call) or id(node) in _shadowed:
            continue
        if not _is_os_path_join_call(node, join_mod_bindings,
                                     ctx.join_bare_names,
                                     os_module_bindings):
            continue
        name = _first_untrusted_join_arg(node, ctx)
        if name is None:
            continue
        issues.append(_make_pt01_issue(node, name, source, filepath))
    return issues
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "sec_registry_fns": {
                'SE05': check_SE05, 'SE06': check_SE06, 'SE08': check_SE08,
                'SE20': check_SE20, 'SE30B': check_SE30b,
                'SE35': check_SE35, 'SE37': check_SE37,
            },
            "se_checks": {
                'SE02': check_SE02, 'SE05': check_SE05, 'SE06': check_SE06,
                'SE08': check_SE08, 'SE20': check_SE20,
                'SE35': check_SE35, 'SE37': check_SE37,
            },
            "rule_bindings": {'PT01': check_PT01},
        },
    }

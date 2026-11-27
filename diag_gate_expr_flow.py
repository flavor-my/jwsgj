from __future__ import annotations

import ast
import logging
import operator
from typing import Any, NamedTuple

from jwsgj.diag_gate_expr import (
    _COMPREHENSION_SCOPES,
    _DEFAULT_FILEPATH,
    _DEFAULT_SOURCE_LINES,
    _MUTATORS_RETURN_NONE,
    _NESTED_BLOCK_STMTS,
    _NOT_NUMBER,
    _SCOPE_BOUNDARY_NODES,
    _TRY_NODES,
    _b44_static_positional_prefix,
    _collect_issues,
    _collect_scope_bodies,
    _comprehension_shadowed,
    _from_binding,
    _import_binding_at,
    _is_empty_literal,
    _is_unshadowed_builtin,
    _is_zero_numeric_const,
    _issue,
    _iter_arg_defaults,
    _iter_expr_nodes_shallow,
    _iter_nested_statement_bodies,
    _literal_number_value,
    _LiteralBinding,
    _log_hits,
    _module_binding_name,
    _nullable_regex_call,
    _pop_names_touched,
    _scan_binding_domain,
    _scan_use_sites,
    _scope_context,
    _scope_header_nodes,
    _update_literal_bindings,
)
from jwsgj.diag_shared_ast_nodes import (
    attr_chain_key,
    is_match_method,
    iter_pattern_capture_names,
)
from jwsgj.diag_types_defs import (
    DiagnoseIssue,
)
from jwsgj.diag_types_vocab import (
    DiagnoseSeverity,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    'GATE_DETECTORS',
    'detect_b22_ignored_string_method',
    'detect_b23_unchecked_get_deref',
    'detect_b30_dynamic_call_default',
    'detect_b34_regex_result_deref',
    'detect_b38_dict_view_subscript',
    'detect_b52_inplace_module_func_result',
    'detect_b64_regex_assigned_unchecked_deref',
    'detect_b65_callable_ref_truthy',
    'detect_b69_literal_index_missing',
    'detect_b70_immutable_item_assign',
    'detect_b71_immutable_forbidden_method',
    'detect_b72_debugger_residue',
]
_log.info("diag_gate_expr_flow B 族表达式面规则域已加载: %d 项导出", len(__all__))
def _attr_chain_root(value: ast.AST) -> ast.AST:
    root = value
    while isinstance(root, ast.Attribute):
        root = root.value
    return root
def _receiver_is_module(recv: ast.AST, node: ast.AST, pm: dict,
                        scope_imports: dict) -> bool:
    if not isinstance(recv, ast.Name):
        return False
    return _module_binding_name(
        _import_binding_at(scope_imports, pm, node, recv.id)) is not None
_STR_METHODS = frozenset({
    'capitalize', 'casefold', 'center', 'encode', 'expandtabs',
    'format', 'format_map', 'ljust', 'lower', 'lstrip',
    'partition', 'removeprefix', 'removesuffix', 'replace', 'rjust',
    'rpartition', 'rsplit', 'rstrip', 'split', 'splitlines', 'strip',
    'swapcase', 'title', 'translate', 'upper', 'zfill',
    'decode',
})
_DYNAMIC_DEFAULT_MODULE_FUNCS = frozenset({
    ('time', 'time'), ('time', 'time_ns'), ('time', 'monotonic'),
    ('time', 'perf_counter'), ('time', 'thread_time'),
    ('random', 'random'), ('random', 'randint'), ('random', 'randrange'),
    ('random', 'choice'), ('random', 'uniform'), ('random', 'sample'),
    ('random', 'choices'), ('random', 'gauss'), ('random', 'expovariate'),
    ('uuid', 'uuid4'), ('uuid', 'uuid1'),
})
_DYNAMIC_DEFAULT_CLASS_METHODS = frozenset({
    ('datetime', 'now'), ('datetime', 'today'), ('datetime', 'utcnow'),
    ('date', 'today'),
})
_DYNAMIC_DEFAULT_FUNCS = (
    _DYNAMIC_DEFAULT_MODULE_FUNCS | _DYNAMIC_DEFAULT_CLASS_METHODS)
def _b22_is_exception_probe(node: ast.Expr, pm: dict) -> bool:
    cur = node
    while cur in pm:
        parent = pm[cur]
        if isinstance(parent, _TRY_NODES) and cur in parent.body:
            return True
        if isinstance(parent, _SCOPE_BOUNDARY_NODES + (ast.Module,)):
            return False
        cur = parent
    return False
def _b22_match(node: ast.AST, pm: dict, scope_imports: dict) -> DiagnoseIssue | None:
    if not isinstance(node, ast.Expr):
        return None
    val = node.value
    if not isinstance(val, ast.Call):
        return None
    func = val.func
    if not isinstance(func, ast.Attribute) or func.attr not in _STR_METHODS:
        return None
    if _receiver_is_module(func.value, node, pm, scope_imports):
        return None
    if _b22_is_exception_probe(node, pm):
        return None
    return _issue(
        'B22',
        f"str/bytes 方法 '{func.attr}()' 返回值被忽略，源对象不可变导致调用无效",
        node.lineno,
        f"将结果赋回变量：s = s.{func.attr}(...)",
        DiagnoseSeverity.WARN)
def detect_b22_ignored_string_method(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _scan_use_sites(
        tree, _b22_match, 'B22', 'ignored_string_method', filepath)
def _b23_is_get_call(node: ast.AST) -> bool:
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == 'get'
    )
def _b23_has_safe_default(call: ast.Call) -> bool:
    positional, dynamic_prefix = _b44_static_positional_prefix(call.args)
    if len(positional) >= 3:
        return True
    second = positional[1] if len(positional) >= 2 else None
    if second is None:
        if dynamic_prefix:
            return False
        for kw in call.keywords:
            if kw.arg == 'default':
                second = kw.value
                break
    if second is None:
        return False
    if isinstance(second, ast.Constant):
        return second.value is not None
    return True
def _b23_deref_kind(node: ast.AST, pm: dict,
                     scope_imports: dict) -> str | None:
    if not isinstance(node, (ast.Attribute, ast.Subscript)):
        return None
    if not _b23_is_get_call(node.value):
        return None
    get_call = node.value
    if _b23_has_safe_default(get_call):
        return None
    if _receiver_is_module(get_call.func.value, get_call, pm,
                           scope_imports):
        return None
    return 'attr' if isinstance(node, ast.Attribute) else 'subscript'
def _b23_match(node: ast.AST, pm: dict, scope_imports: dict) -> DiagnoseIssue | None:
    kind = _b23_deref_kind(node, pm, scope_imports)
    if kind == 'attr':
        return _issue(
            'B23',
            'dict.get() 结果未判空直接解引用（访问属性/方法），'
            'key 不存在时返回 None 会抛 AttributeError',
            node.lineno,
            '先判空（if v is not None）或用 d.get(key, 默认值) 提供非 None 默认值',
            DiagnoseSeverity.WARN)
    if kind == 'subscript':
        return _issue(
            'B23',
            'dict.get() 结果未判空直接下标访问，key 不存在时返回 None 会抛 TypeError',
            node.lineno,
            '先判空或用 d.get(key, [])[idx] 提供默认容器',
            DiagnoseSeverity.WARN)
    return None
def detect_b23_unchecked_get_deref(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _scan_use_sites(
        tree, _b23_match, 'B23', 'unchecked_get_deref', filepath)
def _b30_name_form_hit(fn: ast.Name, query_node: ast.AST, pm: dict,
                       scope_imports: dict) -> bool:
    binding = _from_binding(
        _import_binding_at(scope_imports, pm, query_node, fn.id))
    return binding is not None and binding in _DYNAMIC_DEFAULT_FUNCS
def _b30_attr_form_hit(fn: ast.Attribute, query_node: ast.AST, pm: dict,
                       scope_imports: dict) -> bool:
    root = _attr_chain_root(fn)
    dotted = attr_chain_key(fn)
    if not isinstance(root, ast.Name) or dotted is None:
        return False
    parts = dotted.split('.')
    rec = _import_binding_at(scope_imports, pm, query_node, root.id)
    module_name = _module_binding_name(rec)
    if module_name is not None:
        if len(parts) == 2:
            return (module_name, parts[1]) in _DYNAMIC_DEFAULT_MODULE_FUNCS
        return (module_name == 'datetime' and len(parts) == 3
                and (parts[1], parts[2]) in _DYNAMIC_DEFAULT_CLASS_METHODS)
    imported = _from_binding(rec)
    return (imported is not None and imported[0] == 'datetime'
            and len(parts) == 2
            and (imported[1], parts[1]) in _DYNAMIC_DEFAULT_CLASS_METHODS)
def _b30_hit_issue(call: ast.Call, query_node: ast.AST, pm: dict,
                   scope_imports: dict, owner: str) -> DiagnoseIssue | None:
    fn = call.func
    if isinstance(fn, ast.Name):
        if not _b30_name_form_hit(fn, query_node, pm, scope_imports):
            return None
        target = fn.id
    elif isinstance(fn, ast.Attribute):
        if not _b30_attr_form_hit(fn, query_node, pm, scope_imports):
            return None
        target = attr_chain_key(fn) or fn.attr
    else:
        return None
    return _issue(
        'B30',
        f"动态调用默认参数: {owner} 用 {target}() 作为默认值，"
        f"仅在定义时求值一次，跨调用共享同一值",
        call.lineno,
        f"改用 None 作为默认值，函数体内再调用 {target}()",
        DiagnoseSeverity.ERROR)
def _b30_node_issues(node: ast.AST, pm: dict,
                    scope_imports: dict) -> list[DiagnoseIssue]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        owner = f"函数 '{node.name}'"
    else:
        owner = 'lambda 表达式'
    found: list[DiagnoseIssue] = []
    for default in _iter_arg_defaults(node.args):
        for call in _b30_default_calls(default):
            issue = _b30_hit_issue(call, node, pm, scope_imports, owner)
            if issue is not None:
                found.append(issue)
    return found
def _b30_default_calls(default: ast.AST) -> list[ast.Call]:
    """默认值表达式在定义时整体求值一次，其中任意位置（容器字面量/条件表达式/
    布尔短路/推导式内嵌）的调用结果同样被冻结，均属 B30；lambda 整体跳过：其体内
    调用不在定义时执行，其自身默认值由 _collect_issues 单独访问 Lambda 节点时判定。"""
    calls: list[ast.Call] = []
    stack: list[ast.AST] = [default]
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Lambda):
            continue
        if isinstance(current, ast.Call):
            calls.append(current)
        stack.extend(ast.iter_child_nodes(current))
    return calls
def detect_b30_dynamic_call_default(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, scope_imports = _scope_context(tree)
    issues = _collect_issues(
        tree, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda),
        _b30_node_issues, pm, scope_imports, multi=True)
    _log_hits('B30', 'dynamic_call_default', issues, filepath)
    return issues
def _b34_attribute_issue(node: ast.Attribute, pm: dict,
                         scope_imports: dict) -> DiagnoseIssue | None:
    if (not is_match_method(node.attr)
            or not _nullable_regex_call(node.value, pm, scope_imports)):
        return None
    _fn = node.value.func
    _fn_name = getattr(_fn, 'attr', None) or getattr(_fn, 'id', '?')
    return _issue(
        'B34',
        f"正则匹配结果未判空直接解引用: re.{_fn_name}(...) 无匹配返回 None，"
        f"直接 .{node.attr}() 会抛 AttributeError",
        node.lineno,
        '先判空再取组: m = re.search(p, s); if m: v = m.group(1)，'
        '或用 (m.group(1) if m else 默认值)',
        DiagnoseSeverity.WARN)
def _b34_subscript_issue(node: ast.Subscript, pm: dict,
                         scope_imports: dict) -> DiagnoseIssue | None:
    if not _nullable_regex_call(node.value, pm, scope_imports):
        return None
    return _issue(
        'B34',
        '正则匹配结果未判空直接下标访问: 无匹配返回 None，下标访问会抛 TypeError',
        node.lineno,
        '先判空再取组: m = re.search(p, s); if m: v = m[0]',
        DiagnoseSeverity.WARN)
def _b34_match(node: ast.AST, pm: dict, scope_imports: dict) -> DiagnoseIssue | None:
    if isinstance(node, ast.Attribute):
        return _b34_attribute_issue(node, pm, scope_imports)
    if isinstance(node, ast.Subscript):
        return _b34_subscript_issue(node, pm, scope_imports)
    return None
def detect_b34_regex_result_deref(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _scan_use_sites(
        tree, _b34_match, 'B34', 'regex_result_deref', filepath)
def _b38_view_method(node: ast.Subscript) -> str | None:
    v = node.value
    if not (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute)):
        return None
    if v.func.attr not in ('keys', 'values', 'items') or v.args or v.keywords:
        return None
    return v.func.attr
def _b38_hit_issue(node: ast.Subscript, pm: dict,
                   scope_imports: dict) -> DiagnoseIssue | None:
    attr = _b38_view_method(node)
    if attr is None:
        return None
    v = node.value
    recv = v.func.value
    if _receiver_is_module(recv, v, pm, scope_imports):
        return None
    if isinstance(recv, ast.Dict):
        return _issue(
            'B38',
            f'dict 字面量 .{attr}() 返回视图对象，直接下标一执行即 '
            f'TypeError: not subscriptable',
            node.lineno,
            f'先物化：list(d.{attr}())[i]，或改 next(iter(...))',
            DiagnoseSeverity.ERROR)
    if isinstance(recv, (ast.Name, ast.Attribute)):
        return _issue(
            'B38',
            f'.{attr}() 若为 dict 视图（py3），直接下标即 '
            f'TypeError: not subscriptable——py2 返回 list 的迁移直觉笔误',
            node.lineno,
            f'确认接收者为 dict 时先物化：list(d.{attr}())[i]',
            DiagnoseSeverity.ERROR)
    return None
def _b38_match(node: ast.AST, pm: dict, scope_imports: dict) -> DiagnoseIssue | None:
    if not isinstance(node, ast.Subscript):
        return None
    return _b38_hit_issue(node, pm, scope_imports)
def detect_b38_dict_view_subscript(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _scan_use_sites(
        tree, _b38_match, 'B38', 'dict_view_subscript', filepath)
_INPLACE_MODULE_FUNCS = frozenset({
    ('random', 'shuffle'), ('random', 'seed'),
})
def _b52_inplace_func_name(call: ast.Call, pm: dict,
                           scope_imports: dict) -> str | None:
    func = call.func
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        _rec = _import_binding_at(scope_imports, pm, call, func.value.id)
        return func.attr if _b52_import_hit(_rec, func.attr) else None
    if isinstance(func, ast.Name):
        _rec = _import_binding_at(scope_imports, pm, call, func.id)
        return func.id if _b52_from_hit(_rec) else None
    return None
def _b52_import_hit(rec, attr: str) -> bool:
    module = _module_binding_name(rec)
    return module is not None and (module, attr) in _INPLACE_MODULE_FUNCS
def _b52_from_hit(rec) -> bool:
    binding = _from_binding(rec)
    return binding is not None and binding in _INPLACE_MODULE_FUNCS
def _b52_match(node: ast.AST, pm: dict, scope_imports: dict) -> DiagnoseIssue | None:
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        value, form = node.value, 'assign'
    elif isinstance(node, ast.Return):
        value, form = node.value, 'return'
    else:
        return None
    if not isinstance(value, ast.Call):
        return None
    hit = _b52_inplace_func_name(value, pm, scope_imports)
    if not hit:
        return None
    if form == 'assign':
        message = (f'{hit}() 是就地变更函数（返回 None），赋值所得恒为 '
                   f'None，后续消费即 TypeError')
        suggestion = f'先独立调用 {hit}(...) 再使用原对象，或改用返回新值的 API'
    else:
        message = f'return {hit}() 就地函数结果，调用方收到的恒为 None'
        suggestion = f'先调用 {hit}(...) 再 return 原对象本身'
    return _issue('B52', message, node.lineno, suggestion, DiagnoseSeverity.ERROR)
def detect_b52_inplace_module_func_result(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _scan_use_sites(
        tree, _b52_match, 'B52', 'inplace_module_func_result', filepath)
class _B65Context(NamedTuple):
    pm: dict
    scope_imports: dict
    called: set[str]
_B65_BUILTIN_CALLABLES = frozenset({
    'len', 'abs', 'max', 'min', 'sum', 'sorted', 'reversed', 'print', 'input',
    'open', 'str', 'int', 'float', 'complex', 'bool', 'list', 'dict', 'set',
    'tuple', 'frozenset', 'bytes', 'bytearray', 'repr', 'ascii', 'hash', 'id',
    'type', 'isinstance', 'issubclass', 'getattr', 'setattr', 'hasattr',
    'delattr', 'iter', 'next', 'enumerate', 'zip', 'map', 'filter', 'range',
    'super', 'object', 'callable', 'ord', 'chr', 'hex', 'oct', 'bin', 'pow',
    'round', 'divmod', 'all', 'any', 'vars', 'dir', 'help', 'eval', 'exec',
    'compile', 'format', 'slice', 'memoryview', 'breakpoint',
})
def _b65_name_issue(ref: ast.AST,
                    ctx: _B65Context) -> DiagnoseIssue | None:
    if not (isinstance(ref, ast.Name) and ref.id in _B65_BUILTIN_CALLABLES
            and _is_unshadowed_builtin(ref, ref.id, ctx.pm)):
        return None
    return _issue(
        'B65',
        f"内置函数 '{ref.id}' 引用未调用作条件：函数对象恒真，"
        f"else 分支成死代码（漏写调用括号？）",
        ref.lineno,
        f'应为 {ref.id}(...) 调用结果判定，如 if {ref.id}(x):',
        DiagnoseSeverity.WARN)
def _is_upper_snake_name(name: str) -> bool:
    return (any(ch.isalpha() for ch in name)
            and all(ch.isupper() or ch.isdigit() or ch == '_' for ch in name))
def _called_attr_names(tree: ast.Module) -> set[str]:
    return {name for node in walk_nodes(tree)
            if isinstance(node, ast.Call)
            for name in (attr_chain_key(node.func),) if name is not None}
def _b65_attr_issue(ref: ast.AST,
                    ctx: _B65Context) -> DiagnoseIssue | None:
    if not isinstance(ref, ast.Attribute):
        return None
    root = _attr_chain_root(ref)
    if not isinstance(root, ast.Name):
        return None
    if _is_upper_snake_name(ref.attr):
        return None
    dotted = attr_chain_key(ref)
    if dotted is None or dotted not in ctx.called:
        return None
    _rec = _import_binding_at(ctx.scope_imports, ctx.pm, ref, root.id)
    if _module_binding_name(_rec) is None:
        return None
    return _issue(
        'B65',
        f"模块 '{root.id}' 的属性引用未调用作条件：{dotted} 在本文件另有"
        f"调用点，函数对象恒真，else 分支成死代码（此处漏写调用括号？）",
        ref.lineno,
        f'应为 {dotted}(...) 调用结果判定',
        DiagnoseSeverity.WARN)
def _b65_context(tree: ast.Module) -> _B65Context:
    _pm, _scope_imports = _scope_context(tree)
    return _B65Context(pm=_pm, scope_imports=_scope_imports,
                       called=_called_attr_names(tree))
def _b65_node_issues(node: ast.AST, ctx: _B65Context) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    _b65_scan_test(node.test, ctx, issues)
    return issues
def detect_b65_callable_ref_truthy(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    ctx = _b65_context(tree)
    issues = _collect_issues(
        tree, (ast.If, ast.While), _b65_node_issues, ctx, multi=True)
    _log_hits('B65', 'callable_ref_truthy', issues, filepath)
    return issues
def _b65_scan_test(test: ast.AST, ctx: _B65Context,
                   issues: list[DiagnoseIssue]) -> None:
    if isinstance(test, ast.BoolOp):
        for v in test.values:
            _b65_scan_test(v, ctx, issues)
        return
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        _b65_scan_test(test.operand, ctx, issues)
        return
    issue = _b65_name_issue(test, ctx) or _b65_attr_issue(test, ctx)
    if issue is not None:
        issues.append(issue)
def _scan_scope_bodies(check_id: str, detector: str, tree: ast.Module,
                       scan_body, filepath: str) -> list[DiagnoseIssue]:
    issues = [issue for body in _collect_scope_bodies(tree)
              for issue in scan_body(body)]
    _log_hits(check_id, detector, issues, filepath)
    return issues
_IMMUTABLE_TYPE_TAGS = frozenset({'str', 'bytes', 'int', 'float', 'complex', 'bool', 'tuple', 'frozenset', 'range', 'NoneType'})
def _referenced_names(test: ast.AST) -> set[str]:
    return {n.id for n in walk_nodes(test) if isinstance(n, ast.Name)}
def _drop_names_guarded_by_test(bindings: dict, stmt: ast.stmt) -> None:
    if not isinstance(stmt, ast.Assert):
        return
    for name in _referenced_names(stmt.test):
        if _guard_truth_relation(stmt.test, name) is True:
            bindings.pop(name, None)
def _none_test_name(test: ast.AST) -> tuple[str, bool] | None:
    if not isinstance(test, ast.Compare) or len(test.ops) != 1:
        return None
    subject = test.left
    right = test.comparators[0]
    if isinstance(subject, ast.Constant) and subject.value is None:
        subject, right = right, subject
    if isinstance(subject, ast.NamedExpr) and isinstance(subject.target, ast.Name):
        subject = subject.target
    if not isinstance(subject, ast.Name):
        return None
    if not (isinstance(right, ast.Constant) and right.value is None):
        return None
    op = test.ops[0]
    if isinstance(op, ast.Is):
        return subject.id, True
    if isinstance(op, ast.IsNot):
        return subject.id, False
    return None
def _guard_boolop_relation(test: ast.AST, name: str) -> bool | None:
    if not isinstance(test, ast.BoolOp):
        return None
    if (isinstance(test.op, ast.And)
            and any(_guard_truth_relation(value, name) is True
                    for value in test.values)):
        return True
    if (isinstance(test.op, ast.Or)
            and any(_guard_truth_relation(value, name) is False
                    for value in test.values)):
        return False
    return None
def _guard_truth_relation(test: ast.AST, name: str) -> bool | None:
    if isinstance(test, ast.Name):
        return True if test.id == name else None
    if (isinstance(test, ast.NamedExpr)
            and isinstance(test.target, ast.Name) and test.target.id == name):
        return True
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        inner = _guard_truth_relation(test.operand, name)
        return None if inner is None else not inner
    none_test = _none_test_name(test)
    if none_test is not None and none_test[0] == name:
        return not none_test[1]
    return _guard_boolop_relation(test, name)
def _short_circuit_guards(parent: ast.BoolOp, child: ast.AST,
                          name: str) -> bool:
    want_true = isinstance(parent.op, ast.And)
    for value in parent.values:
        if value is child:
            return False
        if _guard_truth_relation(value, name) is want_true:
            return True
    return False
def _b64_comprehension_region(comp: ast.AST, child: ast.AST,
                               node: ast.AST, pm: dict) -> int | None:
    for index, generator in enumerate(comp.generators):
        part = (_b64_direct_child(node, generator, pm)
                if child is generator else child)
        if part is generator.iter:
            return 3 * index
        if part is generator.target:
            return 3 * index + 1
        if part in generator.ifs:
            return 3 * index + 2
    result_region = 3 * len(comp.generators)
    if isinstance(comp, ast.DictComp):
        return result_region if child in (comp.key, comp.value) else None
    return result_region if child is comp.elt else None
def _b64_comprehension_guarded(comp: ast.AST, child: ast.AST,
                               name: str, node: ast.AST, pm: dict) -> bool:
    child_region = _b64_comprehension_region(comp, child, node, pm)
    if child_region is None:
        return False
    child_pos = (getattr(node, 'lineno', -1),
                 getattr(node, 'col_offset', -1))
    for index, generator in enumerate(comp.generators):
        test_region = 3 * index + 2
        for test in generator.ifs:
            if test_region > child_region:
                continue
            test_pos = (test.lineno, test.col_offset)
            if test_region == child_region and test_pos >= child_pos:
                continue
            if _guard_truth_relation(test, name) is True:
                return True
    return False
def _deref_guarded_by_context(pm: dict, sub: ast.AST, name: str) -> bool:
    cur = sub
    while cur in pm:
        parent = pm[cur]
        if isinstance(parent, ast.IfExp):
            relation = _guard_truth_relation(parent.test, name)
            if ((cur is parent.body and relation is True)
                    or (cur is parent.orelse and relation is False)):
                return True
        elif ((isinstance(parent, ast.BoolOp)
               and _short_circuit_guards(parent, cur, name))
              or (isinstance(parent, _COMPREHENSION_SCOPES)
                  and _b64_comprehension_guarded(
                      parent, cur, name, sub, pm))):
            return True
        if isinstance(parent, _SCOPE_BOUNDARY_NODES + (ast.Module,)):
            return False
        cur = parent
    return False
_FACTORY_TAGS = frozenset({'frozenset', 'tuple', 'list', 'set', 'dict', 'str', 'bytes', 'int', 'float', 'complex', 'bool', 'range'})
_SEQ_TYPE_TAGS = ((ast.Tuple, 'tuple'), (ast.List, 'list'),
                  (ast.Set, 'set'), (ast.Dict, 'dict'))
_MUTABLE_RECV_TAGS = frozenset({'list', 'dict', 'set'})
def _literal_tag_of(value: ast.AST, pm: dict) -> str | None:
    if isinstance(value, ast.Constant):
        return type(value.value).__name__
    for node_type, tag in _SEQ_TYPE_TAGS:
        if isinstance(value, node_type):
            return tag
    if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id in _FACTORY_TAGS
            and _is_unshadowed_builtin(value, value.func.id, pm)):
        return value.func.id
    return None
def _literal_binding_of(value: ast.AST,
                        pm: dict) -> _LiteralBinding | None:
    tag = _literal_tag_of(value, pm)
    return None if tag is None else _LiteralBinding(value, tag)
def _immutable_recv_tag(recv: ast.AST,
                        bindings: dict[str, _LiteralBinding],
                        pm: dict) -> str | None:
    if isinstance(recv, ast.Name):
        binding = bindings.get(recv.id)
        return binding.tag if binding is not None else None
    tag = _literal_tag_of(recv, pm)
    if tag in _MUTABLE_RECV_TAGS:
        return None
    return tag
class _B69Binding:
    def __init__(self, node: ast.AST, tag: str) -> None:
        self.node = node
        self.tag = tag
        self.stale = False
        self.order_known = True
        self.elements: list[object] | None = (
            [el.value for el in node.elts]
            if tag == 'list' and all(isinstance(el, ast.Constant)
                                     for el in node.elts)
            else None)
def _b69_binding_value(v: ast.AST) -> _B69Binding | None:
    for node_type, tag in _SEQ_TYPE_TAGS:
        if isinstance(v, node_type):
            return _B69Binding(v, tag)
    if isinstance(v, ast.Constant) and isinstance(v.value, (str, bytes)):
        return _B69Binding(v, type(v.value).__name__)
    return None
def _b64_receiver_name(value: ast.AST) -> str | None:
    if isinstance(value, ast.Name):
        return value.id
    if isinstance(value, ast.NamedExpr) and isinstance(value.target, ast.Name):
        return value.target.id
    return None
def _b64_named_receiver(sub: ast.AST) -> ast.NamedExpr | None:
    if not isinstance(sub, (ast.Attribute, ast.Subscript)):
        return None
    value = sub.value
    if isinstance(value, ast.NamedExpr) and isinstance(value.target, ast.Name):
        return value
    return None
def _b64_deref_name(sub: ast.AST, nullable: dict[str, int]) -> str | None:
    if not isinstance(sub, (ast.Attribute, ast.Subscript)):
        return None
    name = _b64_receiver_name(sub.value)
    if name is None or name not in nullable:
        return None
    if isinstance(sub, ast.Attribute) and not is_match_method(sub.attr):
        return None
    return name
class _B64WalrusSite(NamedTuple):
    node: ast.NamedExpr
    name: str
    mark: int | None
def _b64_compare_segment(left: ast.AST, op: ast.cmpop,
                         right: ast.AST) -> ast.Compare:
    return ast.Compare(left=left, ops=[op], comparators=[right])
def _b64_compare_tail_unreachable(node: ast.AST, pm: dict) -> bool:
    cur = node
    while cur in pm:
        parent = pm[cur]
        if isinstance(parent, ast.Compare) and cur in parent.comparators:
            left = parent.left
            for op, right in zip(parent.ops, parent.comparators, strict=True):
                if right is cur:
                    break
                segment = _b64_compare_segment(left, op, right)
                if _b64_const_truth(segment) is False:
                    return True
                left = right
        cur = parent
    return False
def _b64_comprehension_child_unreachable(
        comp: ast.AST, child: ast.AST, node: ast.AST, pm: dict) -> bool:
    child_region = _b64_comprehension_region(comp, child, node, pm)
    if child_region is None or child_region == 0:
        return False
    child_pos = (getattr(node, 'lineno', -1),
                 getattr(node, 'col_offset', -1))
    current_generator = child_region // 3
    for index, generator in enumerate(comp.generators):
        if index > current_generator:
            break
        if ((index < current_generator or child_region % 3 != 0)
                and _b64_empty_iteration(generator.iter, pm)):
            return True
        test_region = 3 * index + 2
        for test in generator.ifs:
            if test_region > child_region:
                continue
            test_pos = (test.lineno, test.col_offset)
            if (test_region == child_region and test_pos >= child_pos):
                continue
            if _b64_const_truth(test) is False:
                return True
    return False

def _b64_comprehension_tail_unreachable(node: ast.AST, pm: dict) -> bool:
    cur = node
    while cur in pm:
        parent = pm[cur]
        if (isinstance(parent, _COMPREHENSION_SCOPES)
                and _b64_comprehension_child_unreachable(
                    parent, cur, node, pm)):
            return True
        if isinstance(parent, _SCOPE_BOUNDARY_NODES + (ast.Module,)):
            return False
        cur = parent
    return False

def _b64_walrus_sites(node: ast.AST, pm: dict,
                      scope_imports: dict) -> list[_B64WalrusSite]:
    sites: list[_B64WalrusSite] = []
    for sub in _iter_expr_nodes_shallow(node):
        if (_b64_compare_tail_unreachable(sub, pm)
                or _b64_comprehension_tail_unreachable(sub, pm)):
            continue
        if (not isinstance(sub, ast.NamedExpr)
                or not isinstance(sub.target, ast.Name)):
            continue
        mark = (sub.lineno
                if _nullable_regex_call(sub.value, pm, scope_imports) else None)
        sites.append(_B64WalrusSite(sub, sub.target.id, mark))
    sites.sort(key=lambda site: (site.node.lineno, site.node.col_offset))
    return sites
def _b64_set_mark(state: dict[str, int], name: str,
                  mark: int | None) -> None:
    if mark is None:
        state.pop(name, None)
    else:
        state[name] = mark
def _b64_direct_child(node: ast.AST, ancestor: ast.AST,
                      pm: dict) -> ast.AST | None:
    if node is ancestor:
        return None
    child = node
    parent = pm.get(child)
    while parent is not None and parent is not ancestor:
        child = parent
        parent = pm.get(child)
    return child if parent is ancestor else None
def _b64_source_precedes(site: ast.AST, node: ast.AST) -> bool:
    site_pos = (getattr(site, 'lineno', None), getattr(site, 'col_offset', None))
    node_pos = (getattr(node, 'lineno', None), getattr(node, 'col_offset', None))
    return None not in site_pos and None not in node_pos and site_pos < node_pos
def _b64_site_precedes(site: ast.NamedExpr, node: ast.AST,
                       pm: dict) -> bool:
    cur = node
    while cur is not None:
        if cur is site:
            return False
        cur = pm.get(cur)
    node_ancestors: set[ast.AST] = set()
    cur = node
    while cur is not None:
        node_ancestors.add(cur)
        cur = pm.get(cur)
    ancestor = site
    while ancestor is not None and ancestor not in node_ancestors:
        ancestor = pm.get(ancestor)
    if ancestor is None:
        return _b64_source_precedes(site, node)
    site_child = _b64_direct_child(site, ancestor, pm)
    node_child = _b64_direct_child(node, ancestor, pm)
    if site_child is None or node_child is None:
        return _b64_source_precedes(site, node)
    if isinstance(ancestor, ast.IfExp):
        if site_child is ancestor.test and node_child is not ancestor.test:
            return True
        if site_child is not node_child:
            return False
    elif isinstance(ancestor, _COMPREHENSION_SCOPES):
        site_region = _b64_comprehension_region(
            ancestor, site_child, site, pm)
        node_region = _b64_comprehension_region(
            ancestor, node_child, node, pm)
        if (site_region is not None and node_region is not None
                and site_region != node_region):
            return site_region < node_region
    elif isinstance(ancestor, (ast.Assign, ast.AnnAssign)):
        targets = (ancestor.targets if isinstance(ancestor, ast.Assign)
                   else [ancestor.target])
        if site_child is ancestor.value and node_child in targets:
            return True
        if node_child is ancestor.value and site_child in targets:
            return False
    return _b64_source_precedes(site, node)
def _b64_state_at(state: dict[str, int], sites: list[_B64WalrusSite],
                  node: ast.AST | None = None,
                  pm: dict | None = None) -> dict[str, int]:
    visible: dict[str, int] | None = None
    for site in sites:
        if (node is not None
                and (pm is None or not _b64_site_precedes(site.node, node, pm))):
            continue
        if visible is None:
            visible = dict(state)
        _b64_set_mark(visible, site.name, site.mark)
    return state if visible is None else visible
def _b64_apply_walrus(node: ast.AST, state: dict[str, int], pm: dict,
                      scope_imports: dict) -> None:
    then_state, else_state = _b64_test_branch_states(
        state, node, pm, scope_imports)
    _b64_replace_state(
        state, _b64_merge_states([then_state, else_state]))
def _b64_static_format_text(node: ast.AST) -> str | bytes | None:
    if (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes))):
        return node.value
    if not isinstance(node, ast.JoinedStr):
        return None
    parts: list[str] = []
    for part in node.values:
        if not (isinstance(part, ast.Constant)
                and isinstance(part.value, str)):
            return None
        parts.append(part.value)
    return ''.join(parts)
def _b64_definitely_raises(node: ast.AST) -> bool:
    if isinstance(node, ast.Starred):
        return _b64_definitely_raises(node.value)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return any(_b64_definitely_raises(element) for element in node.elts)
    if isinstance(node, ast.Dict):
        return any(_b64_definitely_raises(child)
                   for pair in zip(node.keys, node.values, strict=True)
                   for child in pair if child is not None)
    if not (isinstance(node, ast.BinOp)
            and isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod))
            and _is_zero_numeric_const(node.right)):
        return False
    if (not isinstance(node.left, (ast.Constant, ast.List, ast.Tuple,
                                   ast.Set, ast.Dict))
            and _literal_number_value(node.left) is _NOT_NUMBER):
        return False
    if isinstance(node.op, ast.Mod):
        format_text = _b64_static_format_text(node.left)
        if format_text is not None:
            try:
                format_text % _literal_number_value(node.right)
            except (TypeError, ValueError, KeyError, OverflowError) as e:
                log_swallowed(
                    __name__, e, context='_b64_definitely_raises:format')
                return True
            return False
    return True
def _b64_after_raising_call_arg(parent: ast.AST, child: ast.AST) -> bool:
    if not isinstance(parent, ast.Call):
        return False
    current = child.value if isinstance(child, ast.keyword) else child
    ordered = [parent.func, *parent.args,
               *(keyword.value for keyword in parent.keywords)]
    for index, candidate in enumerate(ordered):
        if candidate is current:
            return any(_b64_definitely_raises(previous)
                       for previous in ordered[:index])
    return False
def _b64_apply_exception_walrus(stmt: ast.stmt, state: dict[str, int],
                                pm: dict, scope_imports: dict) -> None:
    linear_stmts = (ast.Expr, ast.Assign, ast.AnnAssign, ast.AugAssign,
                    ast.Return, ast.Raise, ast.Assert)
    if not isinstance(stmt, linear_stmts):
        return
    for site in _b64_walrus_sites(stmt, pm, scope_imports):
        cur: ast.AST = site.node
        unconditional = True
        while cur is not stmt:
            parent = pm.get(cur)
            if parent is None:
                unconditional = False
                break
            if (_b64_after_raising_call_arg(parent, cur)
                    or (isinstance(parent, ast.BoolOp)
                 and cur is not parent.values[0])
                    or (isinstance(parent, ast.IfExp)
                        and cur is not parent.test)
                    or (isinstance(parent, ast.Compare)
                        and cur in parent.comparators[1:])
                    or (isinstance(parent, ast.comprehension)
                        and cur is not parent.iter)
                    or (isinstance(parent, _COMPREHENSION_SCOPES)
                        and cur is not parent.generators[0])):
                unconditional = False
                break
            cur = parent
        if unconditional:
            _b64_set_mark(state, site.name, site.mark)
def _b64_apply_walrus_branch(then_state: dict[str, int],
                             else_state: dict[str, int], test: ast.AST,
                             pm: dict, scope_imports: dict) -> None:
    for site in _b64_walrus_sites(test, pm, scope_imports):
        relation = _guard_truth_relation(test, site.name)
        if relation is True:
            then_state.pop(site.name, None)
        if relation is False:
            else_state.pop(site.name, None)
def _b64_scan_uses(stmt: ast.AST, nullable: dict[str, int], pm: dict,
                   scope_imports: dict,
                   sites: list[_B64WalrusSite] | None = None
                   ) -> list[DiagnoseIssue]:
    if sites is None:
        sites = _b64_walrus_sites(stmt, pm, scope_imports)
    found: list[DiagnoseIssue] = []
    for sub in _iter_expr_nodes_shallow(stmt):
        if (_b64_compare_tail_unreachable(sub, pm)
                or _b64_comprehension_tail_unreachable(sub, pm)):
            continue
        visible = _b64_state_at(nullable, sites, sub, pm) if sites else nullable
        named = _b64_named_receiver(sub)
        if named is not None:
            visible = dict(visible)
            if _nullable_regex_call(named.value, pm, scope_imports):
                visible[named.target.id] = named.lineno
            else:
                visible.pop(named.target.id, None)
        hit_name = _b64_deref_name(sub, visible)
        if hit_name is None:
            continue
        if _comprehension_shadowed(pm, sub, hit_name):
            continue
        if _deref_guarded_by_context(pm, sub, hit_name):
            continue
        error_name = 'TypeError' if isinstance(sub, ast.Subscript) else 'AttributeError'
        found.append(_issue(
            'B64',
            f"正则匹配结果 '{hit_name}' 未判空直接解引用（第 {visible[hit_name]} 行赋值）：无匹配返回 None 时必 {error_name}",
            sub.lineno,
            '先判空再取组: if m: v = m.group(1)，或用 (m.group(1) if m else 默认值)',
            DiagnoseSeverity.WARN))
    return found
def _b64_unwrap_walrus(value: ast.AST) -> ast.AST:
    while isinstance(value, ast.NamedExpr):
        value = value.value
    return value
def _b64_assignment_values(
        stmt: ast.Assign | ast.AnnAssign) -> list[tuple[str, ast.AST]] | None:
    if isinstance(stmt, ast.AnnAssign):
        if stmt.value is None or not isinstance(stmt.target, ast.Name):
            return None
        return [(stmt.target.id, stmt.value)]
    if all(isinstance(target, ast.Name) for target in stmt.targets):
        return [(target.id, stmt.value) for target in stmt.targets]
    if len(stmt.targets) != 1:
        return None
    target, value = stmt.targets[0], stmt.value
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and all(isinstance(item, ast.Name) for item in target.elts)):
        return None
    return [(item.id, item_value)
            for item, item_value in zip(target.elts, value.elts, strict=True)]
def _b64_assign_nullable(stmt: ast.Assign | ast.AnnAssign,
                         nullable: dict[str, int], pm: dict,
                         scope_imports: dict) -> None:
    if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
        return
    assignments = _b64_assignment_values(stmt)
    if assignments is None:
        _pop_names_touched(stmt, nullable)
        return
    for target, value in assignments:
        nullable_hit = _nullable_regex_call(
            _b64_unwrap_walrus(value), pm, scope_imports)
        if nullable_hit:
            nullable[target] = stmt.lineno
        else:
            nullable.pop(target, None)
def _b64_pop_target(target: ast.AST, nullable: dict[str, int]) -> None:
    for sub in walk_nodes(target):
        if (isinstance(sub, ast.Name)
                and isinstance(sub.ctx, (ast.Store, ast.Del))):
            nullable.pop(sub.id, None)
def _b64_branch_state(nullable: dict[str, int], test: ast.AST,
                      truth: bool) -> dict[str, int]:
    state = dict(nullable)
    for name in list(state):
        if _guard_truth_relation(test, name) is truth:
            state.pop(name)
    return state
def _b64_merge_states(states: list[dict[str, int]]) -> dict[str, int]:
    merged: dict[str, int] = {}
    for state in states:
        for name, line in state.items():
            merged.setdefault(name, line)
    return merged
def _b64_range_nonempty(node: ast.AST, pm: dict) -> bool | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'range' and not node.keywords
            and 1 <= len(node.args) <= 3
            and _is_unshadowed_builtin(node, 'range', pm)):
        return None
    values: list[int] = []
    for arg in node.args:
        value = _literal_number_value(arg)
        if (value is _NOT_NUMBER or not isinstance(value, int)
                or isinstance(value, bool)):
            return None
        values.append(value)
    if len(values) == 1:
        start, stop, step = 0, values[0], 1
    elif len(values) == 2:
        start, stop, step = values[0], values[1], 1
    else:
        start, stop, step = values
    if step == 0:
        return None
    return start < stop if step > 0 else start > stop
def _b64_empty_iteration(node: ast.AST, pm: dict) -> bool:
    nonempty = _b64_nonempty_literal(node, pm)
    if nonempty is not None:
        return not nonempty
    return _is_empty_literal(node, pm)
def _b64_nonempty_literal(node: ast.AST, pm: dict) -> bool | None:
    range_nonempty = _b64_range_nonempty(node, pm)
    if range_nonempty is not None:
        return range_nonempty
    parts: list[bool | None]
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if any(not isinstance(el, ast.Starred) for el in node.elts):
            return True
        parts = [_b64_nonempty_literal(el.value, pm)
                 for el in node.elts if isinstance(el, ast.Starred)]
    elif isinstance(node, ast.Dict):
        if any(key is not None for key in node.keys):
            return True
        parts = [_b64_nonempty_literal(value, pm)
                 for key, value in zip(node.keys, node.values, strict=True)
                 if key is None]
    elif isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
        return bool(node.value)
    else:
        return None
    if not parts or all(part is False for part in parts):
        return False
    if any(part is True for part in parts):
        return True
    return None
def _b64_comprehension_branch_states(
        nullable: dict[str, int], comp: ast.AST, pm: dict, scope_imports: dict
        ) -> tuple[dict[str, int], dict[str, int]]:
    entered = dict(nullable)
    outer_iter = comp.generators[0].iter
    _b64_apply_walrus(outer_iter, entered, pm, scope_imports)
    if isinstance(comp, ast.GeneratorExp) or _b64_empty_iteration(outer_iter, pm):
        return dict(entered), dict(entered)
    exits = ([] if _b64_nonempty_literal(outer_iter, pm) else [dict(entered)])
    paths = [entered]
    for index, generator in enumerate(comp.generators):
        if index:
            next_paths: list[dict[str, int]] = []
            for state in paths:
                evaluated = _b64_expression_walrus_state(
                    state, generator.iter, pm, scope_imports)
                if not _b64_nonempty_literal(generator.iter, pm):
                    exits.append(evaluated)
                if not _b64_empty_iteration(generator.iter, pm):
                    next_paths.append(evaluated)
            paths = ([_b64_merge_states(next_paths)]
                     if next_paths else [])
        for test in generator.ifs if paths else ():
            next_paths = []
            for state in paths:
                then_state, else_state = _b64_test_branch_states(
                    state, test, pm, scope_imports)
                constant = _b64_const_truth(test)
                if constant is not True:
                    exits.append(else_state)
                if constant is not False:
                    next_paths.append(then_state)
            paths = ([_b64_merge_states(next_paths)]
                     if next_paths else [])
            if not paths:
                break
        if not paths:
            break
    for state in paths:
        if isinstance(comp, ast.DictComp):
            state = _b64_expression_walrus_state(
                state, comp.key, pm, scope_imports)
            state = _b64_expression_walrus_state(
                state, comp.value, pm, scope_imports)
        else:
            state = _b64_expression_walrus_state(
                state, comp.elt, pm, scope_imports)
        exits.append(state)
    after = _b64_merge_states(exits)
    return dict(after), dict(after)
def _b64_expression_walrus_state(
        nullable: dict[str, int], test: ast.AST, pm: dict,
        scope_imports: dict) -> dict[str, int]:
    if isinstance(test, (ast.BoolOp, ast.IfExp, ast.Compare)
                       + _COMPREHENSION_SCOPES):
        then_state, else_state = _b64_test_branch_states(
            nullable, test, pm, scope_imports)
        return _b64_merge_states([then_state, else_state])
    if isinstance(test, ast.NamedExpr):
        children = (test.value,)
    elif isinstance(test, _SCOPE_BOUNDARY_NODES):
        children = tuple(_scope_header_nodes(test))
    elif isinstance(test, ast.Dict):
        children = tuple(
            child for pair in zip(test.keys, test.values, strict=True)
            for child in pair if child is not None)
    else:
        children = tuple(
            child.value if isinstance(child, ast.keyword) else child
            for child in ast.iter_child_nodes(test)
            if isinstance(child, (ast.expr, ast.keyword)))
    state = dict(nullable)
    for child in children:
        state = _b64_expression_walrus_state(
            state, child, pm, scope_imports)
    if isinstance(test, ast.NamedExpr) and isinstance(test.target, ast.Name):
        mark = (test.lineno
                if _nullable_regex_call(test.value, pm, scope_imports) else None)
        _b64_set_mark(state, test.target.id, mark)
    return state
def _b64_test_branch_states(nullable: dict[str, int], test: ast.AST,
                            pm: dict, scope_imports: dict
                            ) -> tuple[dict[str, int], dict[str, int]]:
    if isinstance(test, ast.IfExp):
        condition_then, condition_else = _b64_test_branch_states(
            nullable, test.test, pm, scope_imports)
        constant = _b64_const_truth(test.test)
        if constant is True:
            return _b64_test_branch_states(
                condition_then, test.body, pm, scope_imports)
        if constant is False:
            return _b64_test_branch_states(
                condition_else, test.orelse, pm, scope_imports)
        body_then, body_else = _b64_test_branch_states(
            condition_then, test.body, pm, scope_imports)
        orelse_then, orelse_else = _b64_test_branch_states(
            condition_else, test.orelse, pm, scope_imports)
        return (_b64_merge_states([body_then, orelse_then]),
                _b64_merge_states([body_else, orelse_else]))
    if isinstance(test, _COMPREHENSION_SCOPES):
        return _b64_comprehension_branch_states(
            nullable, test, pm, scope_imports)
    if isinstance(test, ast.Compare):
        continuing = [dict(nullable)]
        true_paths: list[dict[str, int]] = []
        false_paths: list[dict[str, int]] = []
        left = test.left
        last_index = len(test.ops) - 1
        for index, (op, right) in enumerate(
                zip(test.ops, test.comparators, strict=True)):
            next_continuing: list[dict[str, int]] = []
            for state in continuing:
                if index == 0:
                    state = _b64_expression_walrus_state(
                        state, left, pm, scope_imports)
                state = _b64_expression_walrus_state(
                    state, right, pm, scope_imports)
                segment = _b64_compare_segment(left, op, right)
                then_state = _b64_branch_state(state, segment, True)
                else_state = _b64_branch_state(state, segment, False)
                _b64_apply_walrus_branch(
                    then_state, else_state, segment, pm, scope_imports)
                constant = _b64_const_truth(segment)
                if constant is not True:
                    false_paths.append(else_state)
                target = true_paths if index == last_index else next_continuing
                if constant is not False:
                    target.append(then_state)
            continuing = ([_b64_merge_states(next_continuing)]
                          if next_continuing else [])
            if not continuing:
                break
            left = right
        return _b64_merge_states(true_paths), _b64_merge_states(false_paths)
    if not isinstance(test, ast.BoolOp):
        evaluated = _b64_expression_walrus_state(
            nullable, test, pm, scope_imports)
        then_state = _b64_branch_state(evaluated, test, True)
        else_state = _b64_branch_state(evaluated, test, False)
        _b64_apply_walrus_branch(
            then_state, else_state, test, pm, scope_imports)
        return then_state, else_state
    is_and = isinstance(test.op, ast.And)
    continuing = [dict(nullable)]
    true_paths: list[dict[str, int]] = []
    false_paths: list[dict[str, int]] = []
    last_index = len(test.values) - 1
    for index, value in enumerate(test.values):
        next_continuing: list[dict[str, int]] = []
        for state in continuing:
            then_state, else_state = _b64_test_branch_states(
                state, value, pm, scope_imports)
            constant = _b64_const_truth(value)
            if is_and:
                if constant is not True:
                    false_paths.append(else_state)
                target = true_paths if index == last_index else next_continuing
                if constant is not False:
                    target.append(then_state)
            else:
                if constant is not False:
                    true_paths.append(then_state)
                target = false_paths if index == last_index else next_continuing
                if constant is not True:
                    target.append(else_state)
        continuing = ([_b64_merge_states(next_continuing)]
                      if next_continuing else [])
    return _b64_merge_states(true_paths), _b64_merge_states(false_paths)
def _b64_block_exits(body: list[ast.stmt]) -> bool:
    if not body:
        return False
    last = body[-1]
    if isinstance(last, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
        return True
    return (isinstance(last, ast.If) and bool(last.orelse)
            and _b64_block_exits(last.body)
            and _b64_block_exits(last.orelse))
def _b64_loop_terminal(body: list[ast.stmt]) -> str | None:
    if not body:
        return None
    if isinstance(body[-1], ast.Break):
        return 'break'
    if isinstance(body[-1], (ast.Return, ast.Raise)):
        return 'exit'
    return None
def _b64_replace_state(nullable: dict[str, int], state: dict[str, int]) -> None:
    nullable.clear()
    nullable.update(state)
_B64_COMPARE_OPERATORS = {
    ast.Eq: operator.eq,
    ast.NotEq: operator.ne,
    ast.Lt: operator.lt,
    ast.LtE: operator.le,
    ast.Gt: operator.gt,
    ast.GtE: operator.ge,
    ast.Is: operator.is_,
    ast.IsNot: operator.is_not,
    ast.In: lambda left, right: left in right,
    ast.NotIn: lambda left, right: left not in right,
}
def _b64_const_truth(test: ast.AST) -> bool | None:
    if isinstance(test, ast.Constant):
        return bool(test.value)
    if not isinstance(test, ast.Compare):
        return None
    try:
        values = [ast.literal_eval(test.left),
                  *(ast.literal_eval(node) for node in test.comparators)]
    except (SyntaxError, TypeError, ValueError):
        return None
    for left, op, right in zip(
            values[:-1], test.ops, values[1:], strict=True):
        compare = _B64_COMPARE_OPERATORS.get(type(op))
        if compare is None:
            return None
        try:
            if not compare(left, right):
                return False
        except (TypeError, ValueError):
            return None
    return True
def _b64_scan_guard_uses(test: ast.AST, nullable: dict[str, int], pm: dict,
                         scope_imports: dict) -> list[DiagnoseIssue]:
    if not isinstance(test, ast.BoolOp):
        return _b64_scan_uses(test, nullable, pm, scope_imports)
    state = dict(nullable)
    found: list[DiagnoseIssue] = []
    is_and = isinstance(test.op, ast.And)
    for value in test.values:
        found.extend(_b64_scan_guard_uses(value, state, pm, scope_imports))
        then_state, else_state = _b64_test_branch_states(
            state, value, pm, scope_imports)
        constant = _b64_const_truth(value)
        if (is_and and constant is False) or (not is_and and constant is True):
            break
        state = then_state if is_and else else_state
    return found
def _b64_scan_if(stmt: ast.If, nullable: dict[str, int], pm: dict,
                 scope_imports: dict) -> list[DiagnoseIssue]:
    found = _b64_scan_guard_uses(stmt.test, nullable, pm, scope_imports)
    constant = _b64_const_truth(stmt.test)
    if constant is not None:
        taken = stmt.body if constant else stmt.orelse
        taken_state = _b64_branch_state(nullable, stmt.test, constant)
        found.extend(_b64_scan_body(taken, pm, scope_imports, taken_state))
        _b64_replace_state(nullable, taken_state)
        return found
    then_state, else_state = _b64_test_branch_states(
        nullable, stmt.test, pm, scope_imports)
    found.extend(_b64_scan_body(stmt.body, pm, scope_imports, then_state))
    found.extend(_b64_scan_body(stmt.orelse, pm, scope_imports, else_state))
    then_exits = _b64_block_exits(stmt.body)
    else_exits = _b64_block_exits(stmt.orelse)
    if then_exits and not else_exits:
        merged = else_state
    elif else_exits and not then_exits:
        merged = then_state
    else:
        merged = _b64_merge_states([then_state, else_state])
    _b64_replace_state(nullable, merged)
    return found
def _b64_extend_unique(found: list[DiagnoseIssue],
                       new_issues: list[DiagnoseIssue]) -> None:
    seen = {(issue.check_id, issue.line) for issue in found}
    for issue in new_issues:
        key = (issue.check_id, issue.line)
        if key not in seen:
            found.append(issue)
            seen.add(key)
def _b64_scan_loop(stmt, nullable: dict[str, int], pm: dict,
                   scope_imports: dict) -> list[DiagnoseIssue]:
    found = _b64_scan_uses(stmt.iter, nullable, pm, scope_imports)
    _b64_apply_walrus(stmt.iter, nullable, pm, scope_imports)
    if _b64_empty_iteration(stmt.iter, pm):
        else_state = dict(nullable)
        found.extend(_b64_scan_body(stmt.orelse, pm, scope_imports, else_state))
        _b64_replace_state(nullable, else_state)
        return found
    found.extend(_b64_scan_uses(stmt.target, nullable, pm, scope_imports))
    entry_state = dict(nullable)
    _b64_pop_target(stmt.target, entry_state)
    exit_states: list[dict[str, int]] = []
    while True:
        body_state = dict(entry_state)
        _b64_extend_unique(found, _b64_scan_body(
            stmt.body, pm, scope_imports, body_state))
        exit_states.append(body_state)
        terminal = _b64_loop_terminal(stmt.body)
        if terminal in {'break', 'exit'}:
            break
        next_entry = _b64_merge_states([entry_state, body_state])
        _b64_pop_target(stmt.target, next_entry)
        if next_entry == entry_state:
            break
        entry_state = next_entry
    zero_states = [] if _b64_nonempty_literal(stmt.iter, pm) else [nullable]
    normal_states = [] if terminal in {'break', 'exit'} else exit_states
    else_states = [*zero_states, *normal_states]
    else_state = _b64_merge_states(else_states)
    continuing_states = []
    if else_states:
        found.extend(_b64_scan_body(
            stmt.orelse, pm, scope_imports, else_state))
        continuing_states.append(else_state)
    if terminal == 'break':
        continuing_states.extend(exit_states)
    _b64_replace_state(nullable, _b64_merge_states(continuing_states))
    return found
def _b64_scan_while(stmt: ast.While, nullable: dict[str, int], pm: dict,
                    scope_imports: dict) -> list[DiagnoseIssue]:
    constant = _b64_const_truth(stmt.test)
    if constant is False:
        found = _b64_scan_guard_uses(stmt.test, nullable, pm, scope_imports)
        else_state = dict(nullable)
        found.extend(_b64_scan_body(stmt.orelse, pm, scope_imports, else_state))
        _b64_replace_state(nullable, else_state)
        return found
    found: list[DiagnoseIssue] = []
    test_state = dict(nullable)
    else_states: list[dict[str, int]] = []
    break_states: list[dict[str, int]] = []
    while True:
        _b64_extend_unique(found, _b64_scan_guard_uses(
            stmt.test, test_state, pm, scope_imports))
        body_state, test_else_state = _b64_test_branch_states(
            test_state, stmt.test, pm, scope_imports)
        if constant is not True:
            else_states.append(test_else_state)
        _b64_extend_unique(found, _b64_scan_body(
            stmt.body, pm, scope_imports, body_state))
        terminal = _b64_loop_terminal(stmt.body)
        if terminal == 'break':
            break_states.append(body_state)
        if terminal in {'break', 'exit'}:
            break
        next_test_state = _b64_merge_states([test_state, body_state])
        if next_test_state == test_state:
            break
        test_state = next_test_state
    else_state = _b64_merge_states(else_states)
    continuing_states = []
    if else_states:
        found.extend(_b64_scan_body(
            stmt.orelse, pm, scope_imports, else_state))
        continuing_states.append(else_state)
    continuing_states.extend(break_states)
    _b64_replace_state(nullable, _b64_merge_states(continuing_states))
    return found
def _b64_definitely_nonraising(stmt: ast.stmt) -> bool:
    if isinstance(stmt, ast.Pass):
        return True
    if not isinstance(stmt, (ast.Assign, ast.AnnAssign)):
        return False
    if not isinstance(stmt.value, ast.Constant):
        return False
    targets = stmt.targets if isinstance(stmt, ast.Assign) else [stmt.target]
    return bool(targets) and all(isinstance(target, ast.Name) for target in targets)
def _b64_scan_try(stmt, nullable: dict[str, int], pm: dict,
                  scope_imports: dict) -> list[DiagnoseIssue]:
    body_state = dict(nullable)
    exception_state = dict(nullable)
    found: list[DiagnoseIssue] = []
    for body_stmt in stmt.body:
        nonraising = _b64_definitely_nonraising(body_stmt)
        entry_state = dict(body_state)
        if not nonraising:
            exception_state = _b64_merge_states([exception_state, body_state])
        found.extend(_b64_scan_stmt(body_stmt, body_state, pm, scope_imports))
        if not nonraising:
            statement_exception_state = dict(entry_state)
            _b64_apply_exception_walrus(
                body_stmt, statement_exception_state, pm, scope_imports)
            exception_state = _b64_merge_states(
                [exception_state, statement_exception_state])
    orelse_state = dict(body_state)
    body_exits = _b64_block_exits(stmt.body)
    if not body_exits:
        found.extend(_b64_scan_body(
            stmt.orelse, pm, scope_imports, orelse_state))
    normal_exits = body_exits or _b64_block_exits(stmt.orelse)
    states = [orelse_state]
    continuing_states = [] if normal_exits else [orelse_state]
    for handler in stmt.handlers:
        handler_state = dict(exception_state)
        if handler.name:
            handler_state.pop(handler.name, None)
        if handler.type is not None:
            found.extend(_b64_scan_uses(
                handler.type, exception_state, pm, scope_imports))
        found.extend(_b64_scan_body(handler.body, pm, scope_imports, handler_state))
        states.append(handler_state)
        if not _b64_block_exits(handler.body):
            continuing_states.append(handler_state)
    merged = _b64_merge_states(states)
    found.extend(_b64_scan_body(stmt.finalbody, pm, scope_imports, merged))
    continuing = _b64_merge_states(continuing_states)
    if stmt.finalbody:
        _b64_scan_body(stmt.finalbody, pm, scope_imports, continuing)
    _b64_replace_state(nullable, continuing)
    return found
def _b64_scan_with(stmt, nullable: dict[str, int], pm: dict,
                   scope_imports: dict) -> list[DiagnoseIssue]:
    found: list[DiagnoseIssue] = []
    for item in stmt.items:
        found.extend(_b64_scan_uses(
            item.context_expr, nullable, pm, scope_imports))
        _b64_apply_walrus(
            item.context_expr, nullable, pm, scope_imports)
        if item.optional_vars is not None:
            found.extend(_b64_scan_uses(
                item.optional_vars, nullable, pm, scope_imports))
            _b64_pop_target(item.optional_vars, nullable)
    found.extend(_b64_scan_body(stmt.body, pm, scope_imports, nullable))
    return found
def _b64_pattern_irrefutable(pattern: ast.AST) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return (pattern.pattern is None
                or _b64_pattern_irrefutable(pattern.pattern))
    if isinstance(pattern, ast.MatchOr):
        return any(_b64_pattern_irrefutable(item)
                   for item in pattern.patterns)
    return False
def _b64_pattern_may_match_none(pattern: ast.AST) -> bool:
    if isinstance(pattern, ast.MatchSingleton):
        return pattern.value is None
    if isinstance(pattern, ast.MatchValue):
        return False
    if isinstance(pattern, ast.MatchAs):
        return (pattern.pattern is None
                or _b64_pattern_may_match_none(pattern.pattern))
    if isinstance(pattern, ast.MatchOr):
        return any(_b64_pattern_may_match_none(item)
                   for item in pattern.patterns)
    if isinstance(pattern, ast.MatchClass):
        return isinstance(pattern.cls, ast.Name) and pattern.cls.id == 'object'
    return False
def _b64_scan_match(stmt: ast.Match, nullable: dict[str, int], pm: dict,
                    scope_imports: dict) -> list[DiagnoseIssue]:
    found = _b64_scan_uses(stmt.subject, nullable, pm, scope_imports)
    remaining = dict(nullable)
    _b64_apply_walrus(stmt.subject, remaining, pm, scope_imports)
    subject_name = _b64_receiver_name(stmt.subject)
    continuing_states: list[dict[str, int]] = []
    exhaustive = False
    for case in stmt.cases:
        found.extend(_b64_scan_uses(case.pattern, remaining, pm, scope_imports))
        body_state = dict(remaining)
        for captured_name in iter_pattern_capture_names(case.pattern):
            body_state.pop(captured_name, None)
        if (isinstance(case.pattern, ast.MatchAs)
                and case.pattern.pattern is None
                and case.pattern.name is not None
                and subject_name in remaining):
            body_state[case.pattern.name] = remaining[subject_name]
        may_match_none = _b64_pattern_may_match_none(case.pattern)
        if subject_name is not None and not may_match_none:
            body_state.pop(subject_name, None)
        fallthrough = dict(remaining)
        if case.guard is not None:
            found.extend(_b64_scan_guard_uses(
                case.guard, body_state, pm, scope_imports))
            body_state, guard_fallthrough = _b64_test_branch_states(
                body_state, case.guard, pm, scope_imports)
            fallthrough = _b64_merge_states([fallthrough, guard_fallthrough])
        found.extend(_b64_scan_body(
            case.body, pm, scope_imports, body_state))
        if not _b64_block_exits(case.body):
            continuing_states.append(body_state)
        if case.guard is None and _b64_pattern_irrefutable(case.pattern):
            exhaustive = True
            break
        remaining = fallthrough
        if (subject_name is not None and may_match_none
                and case.guard is None):
            remaining.pop(subject_name, None)
    if not exhaustive:
        continuing_states.append(remaining)
    _b64_replace_state(nullable, _b64_merge_states(continuing_states))
    return found
def _b64_scan_stmt(stmt: ast.stmt, nullable: dict[str, int], pm: dict,
                   scope_imports: dict) -> list[DiagnoseIssue]:
    if isinstance(stmt, ast.If):
        return _b64_scan_if(stmt, nullable, pm, scope_imports)
    if isinstance(stmt, ast.Match):
        return _b64_scan_match(stmt, nullable, pm, scope_imports)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return _b64_scan_loop(stmt, nullable, pm, scope_imports)
    if isinstance(stmt, ast.While):
        return _b64_scan_while(stmt, nullable, pm, scope_imports)
    if isinstance(stmt, _TRY_NODES):
        return _b64_scan_try(stmt, nullable, pm, scope_imports)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _b64_scan_with(stmt, nullable, pm, scope_imports)
    found = _b64_scan_uses(stmt, nullable, pm, scope_imports)
    if isinstance(stmt, ast.Expr):
        then_state, else_state = _b64_test_branch_states(
            nullable, stmt.value, pm, scope_imports)
        _b64_replace_state(
            nullable, _b64_merge_states([then_state, else_state]))
    else:
        if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
            _b64_assign_nullable(stmt, nullable, pm, scope_imports)
            if stmt.value is not None:
                _b64_apply_walrus(stmt.value, nullable, pm, scope_imports)
            targets = (stmt.targets if isinstance(stmt, ast.Assign)
                       else [stmt.target])
            for target in targets:
                _b64_apply_walrus(target, nullable, pm, scope_imports)
        else:
            _pop_names_touched(stmt, nullable)
            _b64_apply_walrus(stmt, nullable, pm, scope_imports)
    _drop_names_guarded_by_test(nullable, stmt)
    return found
def _b64_scan_body(body: list[ast.stmt], pm: dict, scope_imports: dict,
                   nullable: dict[str, int] | None = None
                   ) -> list[DiagnoseIssue]:
    state: dict[str, int] = {} if nullable is None else nullable
    found: list[DiagnoseIssue] = []
    for stmt in body:
        found.extend(_b64_scan_stmt(stmt, state, pm, scope_imports))
    return found
def detect_b64_regex_assigned_unchecked_deref(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    _pm, _scope_imports = _scope_context(tree)
    return _scan_scope_bodies(
        'B64', 'regex_assigned_unchecked_deref', tree,
        lambda body: _b64_scan_body(body, _pm, _scope_imports), filepath)
def _b69_seq_missing(recv: ast.List | ast.Tuple, needle: object) -> str | None:
    if not all(isinstance(el, ast.Constant) for el in recv.elts):
        return None
    if needle in [el.value for el in recv.elts]:
        return None
    return 'list' if isinstance(recv, ast.List) else 'tuple'
def _b69_text_missing(recv: ast.AST, needle: object) -> str | None:
    if not (isinstance(recv, ast.Constant)
            and isinstance(recv.value, (str, bytes))):
        return None
    if (isinstance(recv.value, bytes)
            and isinstance(needle, int) and not isinstance(needle, bool)):
        if not 0 <= needle <= 255:
            return 'bytes'
        return None if needle in recv.value else 'bytes'
    if not (isinstance(needle, type(recv.value)) and needle not in recv.value):
        return None
    return type(recv.value).__name__
def _b69_missing_kind(recv: ast.AST, needle: object) -> str | None:
    if isinstance(recv, (ast.List, ast.Tuple)):
        return _b69_seq_missing(recv, needle)
    return _b69_text_missing(recv, needle)
def _b69_issue(node: ast.Call, needle: object,
               missing: str | None) -> DiagnoseIssue | None:
    if missing is None:
        return None
    return _issue(
        'B69',
        f'{missing} 字面量 .index({needle!r}) 试算必失败：值不在容器中，必 ValueError',
        node.lineno,
        '确认查找值存在，或改用 in 判存/try 捕获 ValueError',
        DiagnoseSeverity.ERROR)
def _b69_check_call(node: ast.Call, recv: ast.AST) -> DiagnoseIssue | None:
    needle = _b69_index_value(node.args[0])
    return _b69_issue(node, needle, _b69_missing_kind(recv, needle))
def _b69_check_bound_call(
        node: ast.Call, bound: _B69Binding) -> DiagnoseIssue | None:
    if bound.stale:
        return None
    needle = _b69_index_value(node.args[0])
    if bound.tag == 'list':
        if bound.elements is None or needle in bound.elements:
            return None
        return _b69_issue(node, needle, 'list')
    return _b69_issue(node, needle, _b69_missing_kind(bound.node, needle))
_B69_UNPARSED = object()
_B69_DELETE = object()
_B69_LIST_MUTATORS = frozenset({
    'append', 'extend', 'insert', 'remove', 'clear', 'sort', 'reverse', 'pop',
})
def _b69_index_value(arg: ast.AST):
    if isinstance(arg, ast.Constant):
        return arg.value
    value = _literal_number_value(arg)
    return value if value is not _NOT_NUMBER else _B69_UNPARSED
def _b69_is_index_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'index' and len(node.args) == 1
            and not node.keywords
            and _b69_index_value(node.args[0]) is not _B69_UNPARSED)
def _b69_bound_list(call: ast.Call,
                    bindings: dict[str, _B69Binding]) -> _B69Binding | None:
    func = call.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in _B69_LIST_MUTATORS
            and isinstance(func.value, ast.Name)):
        return None
    bound = bindings.get(func.value.id)
    if bound is None or bound.tag != 'list' or bound.stale:
        return None
    return bound
def _b69_constant_sequence(node: ast.AST) -> list[object] | None:
    if (not isinstance(node, (ast.List, ast.Tuple, ast.Set))
            or any(isinstance(el, ast.Starred) for el in node.elts)
            or not all(isinstance(el, ast.Constant) for el in node.elts)):
        return None
    return [el.value for el in node.elts]
def _b69_stale_list_binding(
        name: str, bindings: dict[str, _B69Binding]) -> None:
    bound = bindings.get(name)
    if bound is not None and bound.tag == 'list':
        bound.stale = True

def _b69_invalidate_alias_assignment(
        value: ast.AST, bindings: dict[str, _B69Binding]) -> None:
    if isinstance(value, ast.Name):
        _b69_stale_list_binding(value.id, bindings)

def _b69_supported_list_call(
        call: ast.Call, bindings: dict[str, _B69Binding]) -> bool:
    func = call.func
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)):
        return False
    bound = bindings.get(func.value.id)
    return (bound is not None and bound.tag == 'list'
            and func.attr in (_B69_LIST_MUTATORS | {'copy', 'count', 'index'}))

def _b69_invalidate_unmodeled_call(
        call: ast.Call, bindings: dict[str, _B69Binding]) -> None:
    if _b69_supported_list_call(call, bindings):
        return
    if (isinstance(call.func, ast.Attribute)
            and isinstance(call.func.value, ast.Name)):
        _b69_stale_list_binding(call.func.value.id, bindings)
    for arg in call.args:
        if isinstance(arg, ast.Name):
            _b69_stale_list_binding(arg.id, bindings)
    for keyword in call.keywords:
        if isinstance(keyword.value, ast.Name):
            _b69_stale_list_binding(keyword.value.id, bindings)

def _b69_apply_call_mutation(
        call: ast.AST, bindings: dict[str, _B69Binding]) -> None:
    if not isinstance(call, ast.Call):
        return
    bound = _b69_bound_list(call, bindings)
    if bound is None:
        return
    method = call.func.attr
    if bound.elements is None or call.keywords:
        bound.stale = True
        return
    if method == 'sort' and not call.args:
        bound.order_known = False
        return
    if method == 'reverse' and not call.args:
        if bound.order_known:
            bound.elements.reverse()
        return
    if method == 'clear' and not call.args:
        bound.elements.clear()
        bound.order_known = True
        return
    if (method == 'append' and len(call.args) == 1
            and isinstance(call.args[0], ast.Constant)):
        bound.elements.append(call.args[0].value)
        return
    if method == 'extend' and len(call.args) == 1:
        values = _b69_constant_sequence(call.args[0])
        if values is not None:
            if isinstance(call.args[0], ast.Set):
                bound.order_known = False
            bound.elements.extend(values)
            return
    if (method == 'insert' and len(call.args) == 2
            and isinstance(call.args[1], ast.Constant)
            and bound.order_known):
        index = _b69_index_value(call.args[0])
        if isinstance(index, int) and not isinstance(index, bool):
            position = index + len(bound.elements) if index < 0 else index
            position = max(0, min(position, len(bound.elements)))
            bound.elements.insert(position, call.args[1].value)
            return
    if (method == 'pop' and len(call.args) <= 1
            and bound.order_known):
        index = -1 if not call.args else _b69_index_value(call.args[0])
        if isinstance(index, int) and not isinstance(index, bool):
            normalized = index + len(bound.elements) if index < 0 else index
            if 0 <= normalized < len(bound.elements):
                bound.elements.pop(normalized)
                return
        bound.stale = True
        return
    if (method == 'remove' and len(call.args) == 1
            and isinstance(call.args[0], ast.Constant)):
        needle = call.args[0].value
        if needle in bound.elements:
            bound.elements.remove(needle)
            return
    bound.stale = True
def _b69_apply_item_mutation(
        target: ast.AST, value: object,
        bindings: dict[str, _B69Binding]) -> None:
    if not (isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Name)):
        return
    bound = bindings.get(target.value.id)
    if bound is None or bound.tag != 'list' or bound.stale:
        return
    index = _b69_index_value(target.slice)
    if (bound.elements is None or not bound.order_known
            or not isinstance(index, int) or isinstance(index, bool)):
        bound.stale = True
        return
    normalized = index + len(bound.elements) if index < 0 else index
    if not 0 <= normalized < len(bound.elements):
        bound.stale = True
        return
    if value is _B69_DELETE:
        bound.elements.pop(normalized)
    elif isinstance(value, ast.Constant):
        bound.elements[normalized] = value.value
    else:
        bound.stale = True
def _b69_clone_bindings(
        bindings: dict[str, _B69Binding]) -> dict[str, _B69Binding]:
    cloned: dict[str, _B69Binding] = {}
    for name, bound in bindings.items():
        duplicate = _B69Binding(bound.node, bound.tag)
        duplicate.stale = bound.stale
        duplicate.order_known = bound.order_known
        duplicate.elements = (None if bound.elements is None
                              else list(bound.elements))
        cloned[name] = duplicate
    return cloned


def _b69_merge_binding_paths(
        bindings: dict[str, _B69Binding],
        paths: list[dict[str, _B69Binding]]) -> None:
    if not paths:
        for bound in bindings.values():
            bound.stale = True
        return
    for name, bound in bindings.items():
        options = [path.get(name) for path in paths]
        if any(option is None or option.tag != bound.tag or option.stale
               for option in options):
            bound.stale = True
            continue
        if bound.tag != 'list':
            continue
        if any(option.elements is None for option in options):
            bound.elements = None
            bound.order_known = False
            continue
        sequences = [list(option.elements) for option in options]
        elements: list[object] = []
        for sequence in sequences:
            for value in sequence:
                if value not in elements:
                    elements.append(value)
        bound.elements = elements
        bound.order_known = (
            all(option.order_known for option in options)
            and all(sequence == sequences[0] for sequence in sequences[1:]))


def _b69_visible_bindings(
        node: ast.AST, bindings: dict[str, _B69Binding],
        pm: dict) -> dict[str, _B69Binding]:
    return {name: bound for name, bound in bindings.items()
            if not _comprehension_shadowed(pm, node, name)}

def _b69_index_issue(
        node: ast.AST, bindings: dict[str, _B69Binding]) -> DiagnoseIssue | None:
    if not _b69_is_index_call(node):
        return None
    recv = node.func.value
    if isinstance(recv, ast.Name):
        bound = bindings.get(recv.id)
        return None if bound is None else _b69_check_bound_call(node, bound)
    return _b69_check_call(node, recv)

def _b69_scan_node(node: ast.AST, bindings: dict[str, _B69Binding],
                   pm: dict, found: list[DiagnoseIssue], *,
                   include_nested_statements: bool = True) -> None:
    if isinstance(node, _SCOPE_BOUNDARY_NODES):
        for child in _scope_header_nodes(node):
            _b69_scan_node(child, bindings, pm, found)
        return
    if isinstance(node, ast.Match):
        _b69_scan_node(node.subject, bindings, pm, found)
        return
    if isinstance(node, ast.Assign):
        _b69_scan_node(node.value, bindings, pm, found)
        _b69_invalidate_alias_assignment(node.value, bindings)
        for target in node.targets:
            _b69_scan_node(target, bindings, pm, found)
            visible = _b69_visible_bindings(target, bindings, pm)
            _b69_apply_item_mutation(target, node.value, visible)
        return
    if isinstance(node, ast.AnnAssign):
        if node.value is not None:
            _b69_scan_node(node.value, bindings, pm, found)
            _b69_invalidate_alias_assignment(node.value, bindings)
        _b69_scan_node(node.target, bindings, pm, found)
        _b69_scan_node(node.annotation, bindings, pm, found)
        if node.value is not None:
            visible = _b69_visible_bindings(node.target, bindings, pm)
            _b69_apply_item_mutation(node.target, node.value, visible)
        return
    if isinstance(node, ast.AugAssign):
        _b69_scan_node(node.target, bindings, pm, found)
        _b69_scan_node(node.value, bindings, pm, found)
        visible = _b69_visible_bindings(node.target, bindings, pm)
        _b69_apply_item_mutation(node.target, None, visible)
        return
    if isinstance(node, ast.Delete):
        for target in node.targets:
            _b69_scan_node(target, bindings, pm, found)
            visible = _b69_visible_bindings(target, bindings, pm)
            _b69_apply_item_mutation(target, _B69_DELETE, visible)
        return
    if isinstance(node, ast.BoolOp):
        continuing = [_b69_clone_bindings(bindings)]
        exits: list[dict[str, _B69Binding]] = []
        last_index = len(node.values) - 1
        is_and = isinstance(node.op, ast.And)
        for index, value in enumerate(node.values):
            next_continuing: list[dict[str, _B69Binding]] = []
            for state in continuing:
                _b69_scan_node(value, state, pm, found)
                constant = _b64_const_truth(value)
                if index != last_index and constant is not is_and:
                    exits.append(_b69_clone_bindings(state))
                if constant is not (not is_and):
                    next_continuing.append(state)
            continuing = next_continuing
            if not continuing:
                break
        exits.extend(continuing)
        _b69_merge_binding_paths(bindings, exits)
        return
    if isinstance(node, ast.IfExp):
        _b69_scan_node(node.test, bindings, pm, found)
        constant = _b64_const_truth(node.test)
        branches = ((node.body,) if constant is True
                    else (node.orelse,) if constant is False
                    else (node.body, node.orelse))
        paths: list[dict[str, _B69Binding]] = []
        for branch in branches:
            state = _b69_clone_bindings(bindings)
            _b69_scan_node(branch, state, pm, found)
            paths.append(state)
        _b69_merge_binding_paths(bindings, paths)
        return
    if isinstance(node, ast.Call):
        _b69_scan_node(node.func, bindings, pm, found)
        for arg in node.args:
            _b69_scan_node(arg, bindings, pm, found)
        for keyword in node.keywords:
            _b69_scan_node(keyword.value, bindings, pm, found)
        visible = _b69_visible_bindings(node, bindings, pm)
        _b69_apply_call_mutation(node, visible)
        _b69_invalidate_unmodeled_call(node, visible)
        issue = _b69_index_issue(node, visible)
        if issue is not None:
            found.append(issue)
        return
    if isinstance(node, ast.Dict):
        for key, value in zip(node.keys, node.values, strict=True):
            if key is not None:
                _b69_scan_node(key, bindings, pm, found)
            _b69_scan_node(value, bindings, pm, found)
        return
    if isinstance(node, _COMPREHENSION_SCOPES):
        outer_iter = node.generators[0].iter
        _b69_scan_node(outer_iter, bindings, pm, found)
        zero_path = _b69_clone_bindings(bindings)
        if _b64_empty_iteration(outer_iter, pm):
            _b69_merge_binding_paths(bindings, [zero_path])
            return
        executed_path = _b69_clone_bindings(bindings)
        skipped_paths = ([] if _b64_nonempty_literal(outer_iter, pm)
                         else [_b69_clone_bindings(zero_path)])
        for index, generator in enumerate(node.generators):
            if index:
                _b69_scan_node(generator.iter, executed_path, pm, found)
                if _b64_empty_iteration(generator.iter, pm):
                    skipped_paths.append(executed_path)
                    _b69_merge_binding_paths(bindings, skipped_paths)
                    return
                if not _b64_nonempty_literal(generator.iter, pm):
                    skipped_paths.append(_b69_clone_bindings(executed_path))
            _b69_scan_node(generator.target, executed_path, pm, found)
            for test in generator.ifs:
                _b69_scan_node(test, executed_path, pm, found)
                constant = _b64_const_truth(test)
                if constant is False:
                    skipped_paths.append(executed_path)
                    _b69_merge_binding_paths(bindings, skipped_paths)
                    return
                if constant is not True:
                    skipped_paths.append(_b69_clone_bindings(executed_path))
        if isinstance(node, ast.DictComp):
            _b69_scan_node(node.key, executed_path, pm, found)
            _b69_scan_node(node.value, executed_path, pm, found)
        else:
            _b69_scan_node(node.elt, executed_path, pm, found)
        if isinstance(node, ast.GeneratorExp) and not skipped_paths:
            skipped_paths.append(zero_path)
        _b69_merge_binding_paths(bindings, [executed_path, *skipped_paths])
        return
    for child in ast.iter_child_nodes(node):
        if not include_nested_statements and isinstance(child, ast.stmt):
            continue
        _b69_scan_node(
            child, bindings, pm, found,
            include_nested_statements=include_nested_statements)

def _b69_scan_domain(tree: ast.Module, filepath: str) -> list[DiagnoseIssue]:
    pm = _scope_context(tree)[0]
    found: list[DiagnoseIssue] = []

    def scan_body(body: list[ast.stmt], bindings: dict[str, _B69Binding]) -> None:
        for stmt in body:
            nested = isinstance(stmt, _NESTED_BLOCK_STMTS + (ast.Match,))
            if nested:
                _pop_names_touched(stmt, bindings)
            _b69_scan_node(
                stmt, bindings, pm, found,
                include_nested_statements=not nested)
            if isinstance(stmt, ast.Match):
                paths: list[dict[str, _B69Binding]] = []
                remaining = _b69_clone_bindings(bindings)
                exhaustive = False
                for case in stmt.cases:
                    case_state = _b69_clone_bindings(remaining)
                    for captured_name in iter_pattern_capture_names(case.pattern):
                        case_state.pop(captured_name, None)
                    if case.guard is not None:
                        _b69_scan_node(case.guard, case_state, pm, found)
                    body_state = _b69_clone_bindings(case_state)
                    scan_body(case.body, body_state)
                    paths.append(body_state)
                    if (case.guard is None
                            and _b64_pattern_irrefutable(case.pattern)):
                        exhaustive = True
                        break
                    if case.guard is not None:
                        remaining = case_state
                if not exhaustive:
                    paths.append(remaining)
                _b69_merge_binding_paths(bindings, paths)
            elif nested:
                paths = [] if isinstance(stmt, ast.If) else [
                    _b69_clone_bindings(bindings)]
                for nested_body in _iter_nested_statement_bodies(stmt):
                    branch = _b69_clone_bindings(bindings)
                    scan_body(nested_body, branch)
                    paths.append(branch)
                _b69_merge_binding_paths(bindings, paths)
            _update_literal_bindings(stmt, bindings, _b69_binding_value)

    for body in _collect_scope_bodies(tree):
        scan_body(body, {})
    _log_hits('B69', 'literal_index_missing', found, filepath)
    return found

def detect_b69_literal_index_missing(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _b69_scan_domain(tree, filepath)
def _b70_item_assign_issue(sub: ast.AST,
                           bindings: dict[str, _LiteralBinding],
                           pm: dict) -> DiagnoseIssue | None:
    if not (isinstance(sub, ast.Subscript)
            and isinstance(sub.ctx, (ast.Store, ast.Del))):
        return None
    tag = _immutable_recv_tag(sub.value, bindings, pm)
    if tag not in _IMMUTABLE_TYPE_TAGS:
        return None
    return _issue(
        'B70',
        f"不可变对象（{tag}）元素赋值：必 TypeError（object does not support item assignment）",
        sub.lineno,
        'str/tuple 不可变：构造新对象（s[:i] + ch + s[i+1:] / 元素重建元组）',
        DiagnoseSeverity.ERROR)
def detect_b70_immutable_item_assign(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm = _scope_context(tree)[0]
    return _scan_binding_domain(
        'B70', 'immutable_item_assign', tree,
        lambda sub, bindings: _b70_item_assign_issue(sub, bindings, pm),
        lambda value: _literal_binding_of(value, pm),
        filepath)
_B71_FORBIDDEN_METHODS = _MUTATORS_RETURN_NONE | {'pop'}
def _b71_forbidden_method_issue(sub: ast.AST,
                                bindings: dict[str, _LiteralBinding],
                                pm: dict) -> DiagnoseIssue | None:
    if not (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
            and sub.func.attr in _B71_FORBIDDEN_METHODS):
        return None
    tag = _immutable_recv_tag(sub.func.value, bindings, pm)
    if tag not in _IMMUTABLE_TYPE_TAGS:
        return None
    return _issue(
        'B71',
        f"不可变类型（{tag}）调用修改方法 .{sub.func.attr}()：必 AttributeError（无此方法）",
        sub.lineno,
        f'{tag} 不可变：改用构造新对象（拼接/转换 list 处理后重建）',
        DiagnoseSeverity.ERROR)
def detect_b71_immutable_forbidden_method(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm = _scope_context(tree)[0]
    return _scan_binding_domain(
        'B71', 'immutable_forbidden_method', tree,
        lambda sub, bindings: _b71_forbidden_method_issue(sub, bindings, pm),
        lambda value: _literal_binding_of(value, pm),
        filepath)
_B72_DEBUGGER_MODULES = frozenset({'pdb', 'ipdb', 'pudb', 'bpdb'})
def _b72_set_trace_source(func: ast.AST, call: ast.Call, pm: dict,
                          scope_imports: dict) -> str | None:
    if isinstance(func, ast.Attribute):
        if func.attr != 'set_trace' or not isinstance(func.value, ast.Name):
            return None
        module = _module_binding_name(
            _import_binding_at(scope_imports, pm, call, func.value.id))
    elif isinstance(func, ast.Name):
        binding = _from_binding(
            _import_binding_at(scope_imports, pm, call, func.id))
        if binding is None or binding[1] != 'set_trace':
            return None
        module = binding[0]
    else:
        return None
    return module if module in _B72_DEBUGGER_MODULES else None
def _b72_breakpoint_issue(call: ast.Call, pm: dict,
                          scope_imports: dict) -> DiagnoseIssue | None:
    func = call.func
    if (isinstance(func, ast.Name) and func.id == 'breakpoint'
            and _is_unshadowed_builtin(call, 'breakpoint', pm)):
        return _issue(
            'B72',
            'breakpoint() 调试断点残留：执行到此进入交互式调试器挂起',
            call.lineno,
            '发布前移除断点调用（或改用 logging 输出诊断信息）',
            DiagnoseSeverity.WARN)
    module = _b72_set_trace_source(func, call, pm, scope_imports)
    if module is None:
        return None
    return _issue(
        'B72',
        f'{module}.set_trace() 调试断点残留：执行到此进入交互式调试器挂起',
        call.lineno,
        f'发布前移除 {module} 断点调用',
        DiagnoseSeverity.WARN)
def _b72_scan_body(body: list[ast.stmt], pm: dict,
                   scope_imports: dict) -> list[DiagnoseIssue]:
    found: list[DiagnoseIssue] = []
    for stmt in body:
        for sub in _iter_expr_nodes_shallow(stmt):
            if not isinstance(sub, ast.Call):
                continue
            issue = _b72_breakpoint_issue(sub, pm, scope_imports)
            if issue is not None:
                found.append(issue)
    return found
def detect_b72_debugger_residue(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, scope_imports = _scope_context(tree)
    return _scan_scope_bodies(
        'B72', 'debugger_residue', tree,
        lambda body: _b72_scan_body(body, pm, scope_imports), filepath)
GATE_DETECTORS: dict[str, Any] = {
    "B22": detect_b22_ignored_string_method,
    "B23": detect_b23_unchecked_get_deref,
    "B30": detect_b30_dynamic_call_default,
    "B34": detect_b34_regex_result_deref,
    "B38": detect_b38_dict_view_subscript,
    "B52": detect_b52_inplace_module_func_result,
    "B64": detect_b64_regex_assigned_unchecked_deref,
    "B65": detect_b65_callable_ref_truthy,
    "B69": detect_b69_literal_index_missing,
    "B70": detect_b70_immutable_item_assign,
    "B71": detect_b71_immutable_forbidden_method,
    "B72": detect_b72_debugger_residue,
}

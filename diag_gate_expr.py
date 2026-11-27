from __future__ import annotations

import ast
import logging
import re as _re
import weakref
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    _evaluation_scope_chain,
    collect_param_names,
    is_none_literal,
    resolve_import_binding,
)
from jwsgj.diag_shared_ast_views import (
    parent_map,
    same_scope_bfs_nodes,
    scope_import_tables,
    scope_node_bound_names,
    tree_nodes,
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
    'detect_b05_none_comparison',
    'detect_b08_is_literal_comparison',
    'detect_b14_type_equality',
    'detect_b15_division_by_zero',
    'detect_b16_float_equality',
    'detect_b20_bool_redundancy',
    'detect_b21_mutator_return_used',
    'detect_b31_assert_validation',
    'detect_b33_len_zero_check',
    'detect_b36_unpack_literal_mismatch',
    'detect_b42_invalid_regex_literal',
    'detect_b43_duplicate_keyword_arg',
    'detect_b44_literal_number_parse_invalid',
    'detect_b45_literal_subscript_out_of_range',
    'detect_b50_duplicate_case_pattern',
    'detect_b51_index_of_len_oob',
    'detect_b56_nan_equality',
    'detect_b57_walrus_literal_condition',
    'detect_b61_isinstance_invalid_type_arg',
    'detect_b63_min_max_empty_literal',
    'detect_b67_input_arithmetic',
]
_log.info("diag_gate_expr B 族表达式面规则域已加载: %d 项导出", len(__all__))
try:
    from re import _constants as _re_constants
    from re import _parser as _re_parser
except ImportError:
    import sre_constants as _re_constants
    import sre_parse as _re_parser
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ''
_NOT_NUMBER = object()
def _literal_number_value(node: ast.AST):
    if (isinstance(node, ast.Constant)
            and isinstance(node.value, (int, float, complex))
            and not isinstance(node.value, bool)):
        return node.value
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))):
        inner = _literal_number_value(node.operand)
        if inner is _NOT_NUMBER:
            return _NOT_NUMBER
        return -inner if isinstance(node.op, ast.USub) else +inner
    return _NOT_NUMBER
def _issue(check_id: str, message: str, line: int, suggestion: str,
           severity: DiagnoseSeverity = DiagnoseSeverity.WARN) -> DiagnoseIssue:
    return DiagnoseIssue(check_id=check_id, severity=severity, message=message,
                         line=line, suggestion=suggestion, auto_fixable=False)
def _log_hits(check_id: str, detector: str, issues: list, filepath: str) -> None:
    if issues:
        _log.debug("[%s] %s 命中 %d 处: %s", check_id, detector, len(issues), filepath)
def _collect_issues(tree: ast.Module, node_types, probe, *args,
                    multi: bool = False) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for node in tree_nodes(tree):
        if not isinstance(node, node_types):
            continue
        found = probe(node, *args)
        if multi:
            issues.extend(found)
        elif found is not None:
            issues.append(found)
    return issues
def _emit(tree: ast.Module, node_types, probe, filepath: str,
          check_id: str, detector: str, *, multi: bool = False,
          args: tuple = ()) -> list[DiagnoseIssue]:
    issues = _collect_issues(tree, node_types, probe, *args, multi=multi)
    _log_hits(check_id, detector, issues, filepath)
    return issues
def _scan_use_sites(tree: ast.Module, match_node, check_id: str,
                    detector: str, filepath: str) -> list[DiagnoseIssue]:
    pm, scope_imports = _scope_context(tree)
    issues = _collect_issues(
        tree, ast.AST, lambda node: match_node(node, pm, scope_imports))
    _log_hits(check_id, detector, issues, filepath)
    return issues
def _scope_context(tree: ast.Module) -> tuple[dict, dict]:
    return parent_map(tree), scope_import_tables(tree)
def _module_binding_name(rec) -> str | None:
    return rec[1] if rec is not None and rec[0] == 'import' else None
def _from_binding(rec) -> tuple[str, str] | None:
    if rec is not None and rec[0] == 'from':
        return rec[1], rec[2]
    return None
_SHADOW_NAMES_CACHE: weakref.WeakKeyDictionary[ast.AST, frozenset[str]] = (
    weakref.WeakKeyDictionary())
def _scope_shadow_names(scope: ast.AST) -> frozenset[str]:
    cached = _SHADOW_NAMES_CACHE.get(scope)
    if cached is not None:
        return cached
    names: set[str] = set()
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        names |= collect_param_names(scope)
    for sub in same_scope_bfs_nodes(scope):
        if isinstance(sub, (ast.Import, ast.ImportFrom)):
            continue
        names |= scope_node_bound_names(sub)
    names.discard('')
    result = frozenset(names)
    _SHADOW_NAMES_CACHE[scope] = result
    return result
def _shadowed_by_local_binding(node: ast.AST, name: str, pm: dict) -> bool:
    cur = pm.get(node)
    crossed_function = False
    while cur is not None:
        if (isinstance(cur, _SCOPE_BOUNDARY_NODES + (ast.Module,))
                and not (isinstance(cur, ast.ClassDef) and crossed_function)):
            if name in _scope_shadow_names(cur):
                return True
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
                crossed_function = True
        cur = pm.get(cur)
    return False
def _scope_has_unknown_star_import(scope: ast.AST) -> bool:
    return any(
        isinstance(sub, ast.ImportFrom) and (sub.level or sub.module != 'builtins')
        and any(alias.name == '*' for alias in sub.names)
        for sub in same_scope_bfs_nodes(scope))
def _is_unshadowed_builtin(node: ast.AST, name: str, pm: dict) -> bool:
    if _shadowed_by_local_binding(node, name, pm):
        return False
    root = node
    while root in pm:
        root = pm[root]
    if not isinstance(root, ast.Module):
        return False
    imports = scope_import_tables(root)
    for scope in _evaluation_scope_chain(node, pm.get):
        rec = imports.get(scope, {}).get(name)
        if rec is not None:
            return (rec[0] == 'from' and rec[1] == 'builtins'
                    and rec[2] == name)
        if _scope_has_unknown_star_import(scope):
            return False
    return True
def _import_binding_at(scope_imports: dict, pm: dict, node: ast.AST,
                       name: str):
    if _shadowed_by_local_binding(node, name, pm):
        return None
    return resolve_import_binding(scope_imports, pm, node, name)
_MUTATORS_RETURN_NONE = frozenset({
    'append', 'extend', 'insert', 'remove', 'clear', 'sort', 'reverse',
    'update', 'add', 'discard',
    'intersection_update', 'difference_update', 'symmetric_difference_update',
})
_TRY_NODES = (ast.Try,) + (
    (ast.TryStar,) if hasattr(ast, "TryStar") else ())
def _returns_value_or_generator(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    stack: list[ast.AST] = list(fn.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        if ((isinstance(node, ast.Return) and node.value is not None
                and not (isinstance(node.value, ast.Constant)
                         and node.value.value is None))
                or isinstance(node, (ast.Yield, ast.YieldFrom))):
            return True
        stack.extend(ast.iter_child_nodes(node))
    return False
def _collect_class_method_returns(tree: ast.Module) -> dict[ast.ClassDef, dict[str, bool]]:
    return {
        cls: {
            fn.name: _returns_value_or_generator(fn)
            for fn in cls.body
            if isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        for cls in tree_nodes(tree) if isinstance(cls, ast.ClassDef)
    }
def _b21_class_at(node: ast.AST, name: str, pm: dict) -> ast.ClassDef | None:
    for scope in _evaluation_scope_chain(node, pm.get):
        classes = [
            sub for sub in same_scope_bfs_nodes(scope)
            if isinstance(sub, ast.ClassDef) and sub.name == name
        ]
        if classes:
            return classes[-1]
    return None
def _b21_explicit_method_return(
        cls: ast.ClassDef, method_name: str,
        class_returns: dict[ast.ClassDef, dict[str, bool]],
        pm: dict) -> bool | None:
    seen: set[ast.ClassDef] = set()
    while cls not in seen:
        seen.add(cls)
        methods = class_returns[cls]
        if method_name in methods:
            return methods[method_name]
        if len(cls.bases) != 1 or not isinstance(cls.bases[0], ast.Name):
            return None
        cls = _b21_class_at(cls, cls.bases[0].id, pm)
        if cls is None:
            return None
    return None
def _b21_method_returns_value(
        func: ast.Attribute, class_returns: dict[ast.ClassDef, dict[str, bool]],
        pm: dict, bindings: dict[str, _LiteralBinding]) -> bool:
    if (_b21_definite_builtin_mutator(func)
            or _b21_bound_builtin_mutator(func, bindings)):
        return False
    recv = func.value
    if isinstance(recv, ast.Call) and isinstance(recv.func, ast.Name):
        cls = _b21_class_at(func, recv.func.id, pm)
        if cls is not None:
            known_return = _b21_explicit_method_return(
                cls, func.attr, class_returns, pm)
            if known_return is not None:
                return known_return
    candidate_returns = [
        methods[func.attr]
        for methods in class_returns.values()
        if func.attr in methods
    ]
    return bool(candidate_returns) and all(candidate_returns)
_B21_LITERAL_MUTATORS = (
    (ast.List, frozenset({
        'append', 'extend', 'insert', 'remove', 'clear', 'sort', 'reverse',
    })),
    (ast.Set, frozenset({
        'add', 'discard', 'remove', 'clear', 'update', 'intersection_update',
        'difference_update', 'symmetric_difference_update',
    })),
    (ast.Dict, frozenset({'clear', 'update'})),
)
def _b21_definite_builtin_mutator(func: ast.Attribute) -> bool:
    return any(isinstance(func.value, node_type) and func.attr in methods
               for node_type, methods in _B21_LITERAL_MUTATORS)
def _b21_literal_binding(value: ast.AST,
                         pm: dict) -> _LiteralBinding | None:
    if isinstance(value, (ast.List, ast.Set, ast.Dict)):
        return _LiteralBinding(value, type(value).__name__.lower())
    if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id in {'list', 'set', 'dict'}
            and not value.args and not value.keywords
            and _is_unshadowed_builtin(value, value.func.id, pm)):
        return _LiteralBinding(value, value.func.id)
    return None
def _b21_bound_builtin_mutator(
        func: ast.Attribute, bindings: dict[str, _LiteralBinding]) -> bool:
    if not isinstance(func.value, ast.Name):
        return False
    binding = bindings.get(func.value.id)
    if binding is None:
        return False
    return any(binding.tag == node_type.__name__.lower()
               and func.attr in methods
               for node_type, methods in _B21_LITERAL_MUTATORS)
def _b21_node_issue(
        node: ast.AST, bindings: dict[str, _LiteralBinding],
        class_returns: dict[ast.ClassDef, dict[str, bool]],
        pm: dict) -> DiagnoseIssue | None:
    if not isinstance(node, (ast.Return, ast.Yield, ast.YieldFrom)):
        return None
    val = node.value
    if not isinstance(val, ast.Call):
        return None
    func = val.func
    if (not isinstance(func, ast.Attribute)
            or func.attr not in _MUTATORS_RETURN_NONE):
        return None
    if _b21_method_returns_value(func, class_returns, pm, bindings):
        return None
    return _issue(
        'B21',
        f"原地修改方法 '{func.attr}()' 返回 None，"
        f"return/yield/yield from 其调用结果将得到 None",
        node.lineno,
        f"先调用 {func.attr}() 再 return 对象本身，或返回期望的值（如 sorted()/副本）",
        DiagnoseSeverity.ERROR)
def detect_b21_mutator_return_used(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    class_returns = _collect_class_method_returns(tree)
    pm = parent_map(tree)
    return _scan_binding_domain(
        'B21', 'mutator_return_used', tree,
        lambda node, bindings: _b21_node_issue(
            node, bindings, class_returns, pm),
        lambda value: _b21_literal_binding(value, pm), filepath)
_NULLABLE_REGEX_CALLS = ('search', 'match', 'fullmatch')
def _binding_is_re_module(rec) -> bool:
    return rec is not None and rec[0] == 'import' and rec[1] == 're'
def _binding_is_re_call(rec) -> bool:
    return (rec is not None and rec[0] == 'from' and rec[1] == 're'
            and rec[2] in _NULLABLE_REGEX_CALLS)
def _regex_api_name(func: ast.expr, node: ast.AST, pm: dict,
                    scope_imports: dict) -> str | None:
    if isinstance(func, ast.Attribute):
        if func.attr not in _NULLABLE_REGEX_CALLS:
            return None
        if not isinstance(func.value, ast.Name):
            return None
        rec = _import_binding_at(scope_imports, pm, node, func.value.id)
        return func.attr if _binding_is_re_module(rec) else None
    if isinstance(func, ast.Name):
        rec = _import_binding_at(scope_imports, pm, node, func.id)
        if _binding_is_re_call(rec):
            return rec[2]
    return None
def _literal_str_pattern(call: ast.Call) -> str | None:
    if not call.args:
        return None
    arg0 = call.args[0]
    if not isinstance(arg0, ast.Constant) or not isinstance(arg0.value, str):
        return None
    return arg0.value
def _regex_subpattern_always_matches_at_end(subpattern) -> bool:
    return all(_regex_op_always_matches_at_end(op, arg)
               for op, arg in subpattern)
def _regex_op_always_matches_at_end(op, arg) -> bool:
    constants = _re_constants
    repeat_ops = [constants.MAX_REPEAT, constants.MIN_REPEAT]
    possessive_repeat = getattr(constants, 'POSSESSIVE_REPEAT', None)
    if possessive_repeat is not None:
        repeat_ops.append(possessive_repeat)
    if op in repeat_ops:
        return arg[0] == 0
    if op is constants.AT:
        return arg in (constants.AT_END, constants.AT_END_STRING)
    if op is constants.SUBPATTERN:
        return _regex_subpattern_always_matches_at_end(arg[-1])
    if op is constants.BRANCH:
        return any(_regex_subpattern_always_matches_at_end(branch)
                   for branch in arg[1])
    if op is constants.ASSERT:
        direction, subpattern = arg
        return (direction > 0
                and _regex_subpattern_always_matches_at_end(subpattern))
    return op is constants.SUCCESS
def _regex_search_always_matches(pattern: str) -> bool:
    try:
        parsed = _re_parser.parse(pattern, 0)
    except (_re.error, OverflowError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_regex_search_always_matches:Exc')
        return False
    return (_regex_subpattern_always_matches_at_start(parsed)
            or _regex_subpattern_always_matches_at_end(parsed))
def _regex_subpattern_always_matches_at_start(subpattern) -> bool:
    return all(_regex_op_always_matches_at_start(op, arg)
               for op, arg in subpattern)
def _regex_op_always_matches_at_start(op, arg) -> bool:
    constants = _re_constants
    repeat_ops = [constants.MAX_REPEAT, constants.MIN_REPEAT]
    possessive_repeat = getattr(constants, 'POSSESSIVE_REPEAT', None)
    if possessive_repeat is not None:
        repeat_ops.append(possessive_repeat)
    if op in repeat_ops:
        return arg[0] == 0
    if op is constants.AT:
        return arg in (constants.AT_BEGINNING,
                       constants.AT_BEGINNING_LINE,
                       constants.AT_BEGINNING_STRING)
    if op is constants.SUBPATTERN:
        return _regex_subpattern_always_matches_at_start(arg[-1])
    if op is constants.BRANCH:
        return any(_regex_subpattern_always_matches_at_start(branch)
                   for branch in arg[1])
    if op is constants.ASSERT:
        direction, subpattern = arg
        return (direction > 0
                and _regex_subpattern_always_matches_at_start(subpattern))
    return op is constants.SUCCESS
def _regex_match_always_matches(pattern: str) -> bool:
    try:
        parsed = _re_parser.parse(pattern, 0)
    except (_re.error, OverflowError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_regex_match_always_matches:Exc')
        return False
    return _regex_subpattern_always_matches_at_start(parsed)
def _nullable_regex_call(node: ast.AST, pm: dict, scope_imports: dict) -> bool:
    if not isinstance(node, ast.Call):
        return False
    operation = _regex_api_name(node.func, node, pm, scope_imports)
    if operation is None:
        return False
    if operation == 'fullmatch':
        return True
    pattern = _literal_str_pattern(node)
    if pattern is None:
        return True
    always_matches = (_regex_search_always_matches(pattern)
                      if operation == 'search'
                      else _regex_match_always_matches(pattern))
    return not always_matches
def _nan_float_call_form(n: ast.AST, pm: dict) -> bool:
    return (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
            and n.func.id == 'float'
            and _is_unshadowed_builtin(n, 'float', pm)
            and len(n.args) == 1 and not n.keywords
            and isinstance(n.args[0], ast.Constant)
            and isinstance(n.args[0].value, (str, bytes))
            and n.args[0].value.strip().lower() in (
                'nan', '+nan', '-nan', b'nan', b'+nan', b'-nan'))
def _nan_math_attr_form(n: ast.AST, scope_imports: dict, pm: dict) -> bool:
    if not (isinstance(n, ast.Attribute) and n.attr == 'nan' and isinstance(n.value, ast.Name)):
        return False
    _rec = _import_binding_at(scope_imports, pm, n, n.value.id)
    return _module_binding_name(_rec) == 'math'
def _nan_from_math_name_form(n: ast.AST, scope_imports: dict, pm: dict) -> bool:
    if not isinstance(n, ast.Name):
        return False
    _rec = _import_binding_at(scope_imports, pm, n, n.id)
    return _from_binding(_rec) == ('math', 'nan')
def _b56_is_nan_expr(n: ast.AST, scope_imports: dict, pm: dict) -> bool:
    n = _unwrap_unary_sign(n)
    return (_nan_float_call_form(n, pm)
            or _nan_math_attr_form(n, scope_imports, pm)
            or _nan_from_math_name_form(n, scope_imports, pm))
def _b56_match(node: ast.AST, pm: dict,
               scope_imports: dict) -> DiagnoseIssue | None:
    if not isinstance(node, ast.Compare):
        return None
    for left, op, right in _iter_compare_pairs(node):
        if not isinstance(op, (ast.Eq, ast.NotEq)):
            continue
        if (_b56_is_nan_expr(left, scope_imports, pm)
                or _b56_is_nan_expr(right, scope_imports, pm)):
            return _issue(
                'B56',
                'NaN 参与 ==/!= 比较：== 恒 False、!= 恒 True，'
                '守卫语义失效（IEEE 754）',
                node.lineno,
                '改用 math.isnan(x) 判定 NaN')
    return None
def detect_b56_nan_equality(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _scan_use_sites(tree, _b56_match, 'B56', 'nan_equality', filepath)
def _iter_expr_nodes_shallow(stmt: ast.AST, *,
                             include_nested_statements: bool = True):
    stack = (list(_scope_header_nodes(stmt))
             if isinstance(stmt, _SCOPE_BOUNDARY_NODES) else [stmt])
    while stack:
        node = stack.pop()
        if isinstance(node, _SCOPE_BOUNDARY_NODES):
            stack.extend(_scope_header_nodes(node))
            continue
        yield node
        children = ast.iter_child_nodes(node)
        if not include_nested_statements:
            children = (child for child in children
                        if not isinstance(child, ast.stmt))
        stack.extend(children)
def _collect_scope_bodies(tree: ast.Module) -> list[list[ast.stmt]]:
    bodies: list[list[ast.stmt]] = []
    for node in tree_nodes(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bodies.append(node.body)
        elif isinstance(node, ast.Lambda):
            bodies.append([ast.Expr(value=node.body)])
    return bodies
def _name_store_hit(node: ast.AST, name: str) -> bool:
    if isinstance(node, ast.Name):
        if not isinstance(node.ctx, (ast.Store, ast.Del)):
            return False
        return node.id == name
    if isinstance(node, ast.alias):
        if node.asname is not None:
            return node.asname == name
        return node.name.split('.')[0] == name
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return node.name == name
    if isinstance(node, ast.ExceptHandler):
        return node.name == name
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        return node.name == name
    if isinstance(node, ast.MatchMapping):
        return node.rest == name
    return False
def _iter_arg_defaults(args: ast.arguments):
    yield from args.defaults
    yield from (d for d in args.kw_defaults if d is not None)
def _iter_arg_annotations(args: ast.arguments):
    parameters = [*args.posonlyargs, *args.args]
    if args.vararg is not None:
        parameters.append(args.vararg)
    parameters.extend(args.kwonlyargs)
    if args.kwarg is not None:
        parameters.append(args.kwarg)
    yield from (arg.annotation for arg in parameters
                if arg.annotation is not None)
def _scope_header_nodes(node: ast.AST):
    if isinstance(node, ast.Lambda):
        yield from _iter_arg_defaults(node.args)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        yield from node.decorator_list
        yield from _iter_arg_defaults(node.args)
        yield from _iter_arg_annotations(node.args)
        if node.returns is not None:
            yield node.returns
    elif isinstance(node, ast.ClassDef):
        yield from node.decorator_list
        yield from node.bases
        yield from (kw.value for kw in node.keywords)
def _stmt_touches_name_store(stmt: ast.AST, name: str) -> bool:
    stack = [stmt]
    while stack:
        node = stack.pop()
        if _name_store_hit(node, name):
            return True
        if isinstance(node, _SCOPE_BOUNDARY_NODES
                      + _COMPREHENSION_SCOPES):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                stack.extend(_scope_header_nodes(node))
            continue
        stack.extend(ast.iter_child_nodes(node))
    return False
class _LiteralBinding(NamedTuple):
    node: ast.AST
    tag: str
_SCOPE_BOUNDARY_NODES = (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)
_COMPREHENSION_SCOPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)
def _comprehension_target_names(comp: ast.AST) -> set[str]:
    if not isinstance(comp, _COMPREHENSION_SCOPES):
        return set()
    return {node.id for gen in comp.generators
            for node in walk_nodes(gen.target) if isinstance(node, ast.Name)}
def _inside_first_iter(pm: dict, node: ast.AST, comp: ast.AST) -> bool:
    if not isinstance(comp, _COMPREHENSION_SCOPES) or not comp.generators:
        return False
    first_iter = comp.generators[0].iter
    cur = node
    while cur is not comp and cur in pm:
        if cur is first_iter:
            return True
        cur = pm[cur]
    return False
def _comprehension_shadowed(pm: dict, node: ast.AST, name: str) -> bool:
    cur = node
    while cur in pm:
        parent = pm[cur]
        if (isinstance(parent, _COMPREHENSION_SCOPES)
                and name in _comprehension_target_names(parent)
                and not _inside_first_iter(pm, node, parent)):
            return True
        if isinstance(parent, _SCOPE_BOUNDARY_NODES + (ast.Module,)):
            return False
        cur = parent
    return False
_NESTED_BLOCK_STMTS = (ast.If, ast.For, ast.AsyncFor, ast.While,
                       ast.With, ast.AsyncWith, ast.Match) + _TRY_NODES
def _update_literal_bindings(stmt: ast.stmt,
                             bindings: dict[str, _LiteralBinding],
                             as_binding) -> None:
    if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
        return
    if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)):
        target, value = stmt.targets[0], stmt.value
    elif (isinstance(stmt, ast.AnnAssign)
          and isinstance(stmt.target, ast.Name)):
        target, value = stmt.target, stmt.value
    else:
        _pop_names_touched(stmt, bindings)
        return
    bound = as_binding(value)
    if bound is not None:
        bindings[target.id] = bound
    else:
        bindings.pop(target.id, None)
def _pop_names_touched(stmt: ast.stmt, bindings: dict) -> None:
    for name in list(bindings):
        if _stmt_touches_name_store(stmt, name):
            bindings.pop(name, None)
def _iter_nested_statement_bodies(stmt: ast.stmt):
    body = getattr(stmt, 'body', None)
    if body is not None:
        yield body
    for case in getattr(stmt, 'cases', ()):
        yield case.body
    for handler in getattr(stmt, 'handlers', ()):
        yield handler.body
    if hasattr(stmt, 'orelse'):
        yield stmt.orelse
    if hasattr(stmt, 'finalbody'):
        yield stmt.finalbody

def _scan_binding_bodies(bodies: list[list[ast.stmt]], match_sub,
                         value_of_binding,
                         pm: dict) -> list[DiagnoseIssue]:
    found: list[DiagnoseIssue] = []

    def scan_body(body: list[ast.stmt], bindings: dict) -> None:
        for stmt in body:
            nested = isinstance(stmt, _NESTED_BLOCK_STMTS)
            if nested:
                _pop_names_touched(stmt, bindings)
            for sub in _iter_expr_nodes_shallow(
                    stmt, include_nested_statements=not nested):
                visible = ({} if not bindings
                           else {name: bound
                                 for name, bound in bindings.items()
                                 if not _comprehension_shadowed(pm, sub, name)})
                issue = match_sub(sub, visible)
                if issue is not None:
                    found.append(issue)
            if nested:
                for nested_body in _iter_nested_statement_bodies(stmt):
                    scan_body(nested_body, dict(bindings))
            _update_literal_bindings(stmt, bindings, value_of_binding)

    for body in bodies:
        scan_body(body, {})
    return found
def _scan_binding_domain(check_id: str, detector: str, tree: ast.Module,
                         match_sub, value_of_binding,
                         filepath: str) -> list[DiagnoseIssue]:
    issues = _scan_binding_bodies(
        _collect_scope_bodies(tree), match_sub, value_of_binding,
        parent_map(tree))
    _log_hits(check_id, detector, issues, filepath)
    return issues
_EMPTY_CONTAINER_CTORS = frozenset({
    'list', 'tuple', 'set', 'dict', 'frozenset', 'bytes', 'str', 'bytearray',
})
def _is_empty_container_call(node: ast.AST, pm: dict) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _EMPTY_CONTAINER_CTORS
            and _is_unshadowed_builtin(node, node.func.id, pm)
            and not node.args and not node.keywords)
def _is_empty_literal(node: ast.AST, pm: dict) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    if _is_empty_container_call(node, pm):
        return True
    return isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)) and len(node.value) == 0
_DIV_ZERO_OPS = (ast.Div, ast.FloorDiv, ast.Mod)
def _iter_compare_pairs(node: ast.Compare):
    left = node.left
    for op, right in zip(node.ops, node.comparators, strict=True):
        yield left, op, right
        left = right
def _is_static_str_source(node: ast.AST) -> bool:
    if isinstance(node, ast.JoinedStr):
        return True
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)))
def _is_zero_numeric_const(node: ast.AST) -> bool:
    operand = _unwrap_unary_sign(node)
    return (isinstance(operand, ast.Constant)
            and isinstance(operand.value, (int, float, complex))
            and operand.value == 0)
def _len_arg_name(node: ast.AST, pm: dict) -> str | None:
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'len' and len(node.args) == 1
            and not node.keywords
            and _is_unshadowed_builtin(node, 'len', pm)
            and isinstance(node.args[0], ast.Name)):
        return node.args[0].id
    return None
def _is_zero_const(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            and not isinstance(node.value, bool)
            and node.value == 0)
def _is_type_call(node: ast.AST, pm: dict) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'type'
            and len(node.args) == 1
            and _is_unshadowed_builtin(node, 'type', pm)
            and not isinstance(node.args[0], ast.Starred)
            and not node.keywords)
def _compare_probe(op_types: tuple[type, ...], matcher, build_issue):
    def probe(node: ast.AST) -> DiagnoseIssue | None:
        hit = any(isinstance(op, op_types) and matcher(left, right)
                  for left, op, right in _iter_compare_pairs(node))
        return build_issue(node) if hit else None
    return probe
def _b05_none_pair(left: ast.AST, right: ast.AST) -> bool:
    return is_none_literal(left) or is_none_literal(right)
def _b05_issue(node: ast.Compare) -> DiagnoseIssue:
    return _issue(
        'B05',
        '使用 == / != 与 None 比较，应使用 is / is not',
        node.lineno,
        '改为 is None / is not None')
def detect_b05_none_comparison(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, ast.Compare,
                 _compare_probe((ast.Eq, ast.NotEq), _b05_none_pair, _b05_issue),
                 filepath, 'B05', 'none_comparison')
def _is_signed_numeric_literal(node: ast.AST) -> bool:
    if not (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))):
        return False
    operand = _unwrap_unary_sign(node)
    return (isinstance(operand, ast.Constant)
            and isinstance(operand.value, (int, float, complex)))
def _b08_is_non_singleton_literal(operand: ast.AST) -> bool:
    if isinstance(operand, ast.Constant):
        v = operand.value
        return not (v is Ellipsis or v is None or v is True or v is False)
    if _is_signed_numeric_literal(operand):
        return True
    return isinstance(operand, (ast.List, ast.Dict, ast.Set, ast.Tuple))
def _b08_literal_pair(left: ast.AST, right: ast.AST) -> bool:
    return any(_b08_is_non_singleton_literal(o) for o in (left, right))
def _b08_issue(node: ast.Compare) -> DiagnoseIssue:
    return _issue('B08', '使用 is 比较字面量/非单例对象，应使用 ==（is 用于身份比较）', node.lineno, '改用 == / != 比较值')
def detect_b08_is_literal_comparison(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, ast.Compare,
                 _compare_probe((ast.Is, ast.IsNot), _b08_literal_pair, _b08_issue),
                 filepath, 'B08', 'is_literal_comparison')
def _b14_type_pair(left: ast.AST, right: ast.AST, pm: dict) -> bool:
    return _is_type_call(left, pm) != _is_type_call(right, pm)
def _b14_issue(node: ast.Compare) -> DiagnoseIssue:
    return _issue(
        'B14',
        '使用 type(x) == 比较类型，破坏子类多态（子类实例将被排除）',
        node.lineno,
        '改用 isinstance(x, SomeType) 以支持子类')
def detect_b14_type_equality(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, _scope_imports = _scope_context(tree)
    return _emit(
        tree, ast.Compare,
        _compare_probe((ast.Eq, ast.NotEq),
                       lambda left, right: _b14_type_pair(left, right, pm),
                       _b14_issue),
        filepath, 'B14', 'type_equality')
def _b15_known_nonnumeric_literal(node: ast.AST) -> bool:
    operand = _unwrap_unary_sign(node)
    if isinstance(operand, ast.Constant):
        return not isinstance(operand.value, (int, float, complex))
    return isinstance(operand, (ast.List, ast.Tuple, ast.Set, ast.Dict,
                                ast.JoinedStr))
def _b15_complex_literal(node: ast.AST) -> bool:
    return isinstance(_literal_number_value(node), complex)
def _b15_has_zero_divisor(node: ast.AST) -> bool:
    left = None
    if isinstance(node, ast.BinOp):
        left, divisor, op = node.left, node.right, node.op
        if isinstance(op, ast.Mod) and _is_static_str_source(left):
            return False
    elif isinstance(node, ast.AugAssign):
        if isinstance(node.op, ast.Mod):
            return False
        divisor, op = node.value, node.op
    else:
        return False
    if left is not None and _b15_known_nonnumeric_literal(left):
        return False
    if (isinstance(op, (ast.FloorDiv, ast.Mod))
            and (_b15_complex_literal(divisor)
                 or (left is not None and _b15_complex_literal(left)))):
        return False
    return isinstance(op, _DIV_ZERO_OPS) and _is_zero_numeric_const(divisor)
def _b15_node_issue(node: ast.AST) -> DiagnoseIssue | None:
    if not _b15_has_zero_divisor(node):
        return None
    return _issue(
        'B15',
        '除零: 除数为字面量 0，运行时必然抛 ZeroDivisionError',
        node.lineno,
        '增加除数非零校验，或用 try/except 捕获 ZeroDivisionError',
        DiagnoseSeverity.ERROR)
def detect_b15_division_by_zero(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, (ast.BinOp, ast.AugAssign), _b15_node_issue, filepath,
                 'B15', 'division_by_zero')
def _unwrap_unary_sign(node: ast.AST) -> ast.AST:
    while (isinstance(node, ast.UnaryOp)
           and isinstance(node.op, (ast.USub, ast.UAdd))):
        node = node.operand
    return node
def _is_float_literal(node: ast.AST) -> bool:
    operand = _unwrap_unary_sign(node)
    return isinstance(operand, ast.Constant) and isinstance(operand.value, float)
def _b16_float_pair(left: ast.AST, right: ast.AST) -> bool:
    return _is_float_literal(left) or _is_float_literal(right)
def _b16_issue(node: ast.Compare) -> DiagnoseIssue:
    return _issue(
        'B16',
        '浮点等值比较: 使用 == / != 比较浮点数，二进制精度误差导致判断不可靠',
        node.lineno,
        '改用误差范围比较（abs(a - b) < epsilon）或 math.isclose()')
def detect_b16_float_equality(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, ast.Compare,
                 _compare_probe((ast.Eq, ast.NotEq), _b16_float_pair, _b16_issue),
                 filepath, 'B16', 'float_equality')
def _b20_is_const_bool(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            and (node.value is True or node.value is False))
def _b20_compare_issue(node: ast.Compare) -> DiagnoseIssue | None:
    for left, op, right in _iter_compare_pairs(node):
        if not isinstance(op, (ast.Eq, ast.NotEq)):
            continue
        if _b20_is_const_bool(left) == _b20_is_const_bool(right):
            continue
        return _issue(
            'B20',
            '布尔冗余: 显式与 True/False 比较，应直接用 truthiness 判断',
            node.lineno,
            '改为 if x / if not x（或 bool(x)）')
    return None
def _b20_return_const_bool(stmts: list) -> bool | None:
    if len(stmts) != 1:
        return None
    s = stmts[0]
    if (isinstance(s, ast.Return) and isinstance(s.value, ast.Constant)
            and (s.value.value is True or s.value.value is False)):
        return s.value.value
    return None
def _b20_if_issue(node: ast.If) -> DiagnoseIssue | None:
    bb = _b20_return_const_bool(node.body)
    ob = _b20_return_const_bool(node.orelse)
    if bb is None or ob is None or bb is ob:
        return None
    return _issue(
        'B20',
        '布尔冗余: if/else 返回 True/False，应直接返回条件',
        node.lineno,
        '改为 return bool(cond)（或 not cond），避免非布尔真值改变返回类型')
def _b20_ifexp_issue(node: ast.IfExp) -> DiagnoseIssue | None:
    if not (_b20_is_const_bool(node.body) and _b20_is_const_bool(node.orelse)):
        return None
    if node.body.value is node.orelse.value:
        return None
    return _issue(
        'B20',
        '布尔冗余: 用三元表达式构造布尔值（True if cond else False），应直接返回条件',
        node.lineno,
        '改为 return bool(cond)（或 not cond），避免非布尔真值改变返回类型')
_B20_SHAPES = (
    (ast.Compare, _b20_compare_issue),
    (ast.If, _b20_if_issue),
    (ast.IfExp, _b20_ifexp_issue),
)
def _b20_node_issue(node: ast.AST) -> DiagnoseIssue | None:
    for shape, build in _B20_SHAPES:
        if isinstance(node, shape):
            return build(node)
    return None
def detect_b20_bool_redundancy(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, ast.AST, _b20_node_issue, filepath,
                 'B20', 'bool_redundancy')
def _b31_param_asserts(func: ast.AST, params: set[str]):
    for stmt in same_scope_bfs_nodes(func):
        if not isinstance(stmt, ast.Assert) or isinstance(stmt.test, ast.Lambda):
            continue
        names = {n.id for n in walk_nodes(stmt.test) if isinstance(n, ast.Name)}
        if names & params:
            yield stmt
def _b31_func_issues(func: ast.AST) -> list[DiagnoseIssue]:
    params: set[str] = collect_param_names(func)
    if not params:
        return []
    return [_issue(
        'B31',
        f"assert 参数校验: 函数 '{func.name}' 用 assert 校验参数，python -O 优化模式下被剥离、校验失效",
        stmt.lineno,
        '改用显式校验并 raise ValueError/TypeError（如 if not isinstance(x, int): raise TypeError(...)）')
        for stmt in _b31_param_asserts(func, params)]
def detect_b31_assert_validation(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, (ast.FunctionDef, ast.AsyncFunctionDef),
                 _b31_func_issues, filepath, 'B31', 'assert_validation',
                 multi=True)
def _b33_issue_parts(left: ast.AST, right: ast.AST, op_ch: str,
                     pm: dict) -> tuple[str, str] | None:
    for subject, other in ((left, right), (right, left)):
        target = _len_arg_name(subject, pm)
        if target is not None:
            if _is_zero_const(other):
                return target, (f"空容器判断用 len(): len({target}) {op_ch} 0 "
                                f"应直接用 truthiness")
            continue
        if (isinstance(subject, ast.Name)
                and _is_empty_literal(other, pm)):
            return subject.id, (f"空容器判断与空字面量比较: {subject.id} {op_ch} "
                                f"空字面量应直接用 truthiness")
    return None
def _b33_node_issue(node: ast.AST, pm: dict) -> DiagnoseIssue | None:
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return None
    op = node.ops[0]
    if not isinstance(op, (ast.Eq, ast.NotEq)):
        return None
    op_ch = '==' if isinstance(op, ast.Eq) else '!='
    parts = _b33_issue_parts(node.left, node.comparators[0], op_ch, pm)
    if parts is None:
        return None
    target, message = parts
    suggestion = f"改为 if not {target}" if isinstance(op, ast.Eq) else f"改为 if {target}"
    return _issue('B33', message, node.lineno, suggestion)
def detect_b33_len_zero_check(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, _scope_imports = _scope_context(tree)
    return _emit(tree, ast.Compare, _b33_node_issue, filepath,
                 'B33', 'len_zero_check', args=(pm,))
_B44_CTORS = {'int': int, 'float': float, 'complex': complex}
_LITERAL_PARSE_BUILTIN_NAMES = frozenset(_B44_CTORS)
_RE_API = ('compile', 'match', 'search', 'fullmatch', 'split',
           'sub', 'subn', 'findall', 'finditer')
_RE_FLAG_POS = {'compile': 1, 'match': 2, 'search': 2, 'fullmatch': 2,
                'split': 3, 'sub': 4, 'subn': 4, 'findall': 2, 'finditer': 2}
def _b36_literal_mismatch(tgt: ast.Tuple | ast.List,
                          val: ast.Tuple | ast.List
                          ) -> tuple[ast.AST, int, int] | None:
    if _has_starred_element(tgt) or _has_starred_element(val):
        return None
    if len(tgt.elts) != len(val.elts):
        return val, len(tgt.elts), len(val.elts)
    for t_el, v_el in zip(tgt.elts, val.elts, strict=True):
        if (isinstance(t_el, (ast.Tuple, ast.List))
                and isinstance(v_el, (ast.Tuple, ast.List))):
            bad = _b36_literal_mismatch(t_el, v_el)
            if bad is not None:
                return bad
    return None
def _b36_assign_issues(node: ast.Assign) -> list[DiagnoseIssue]:
    if not isinstance(node.value, (ast.Tuple, ast.List)):
        return []
    issues = []
    for tgt in node.targets:
        if not isinstance(tgt, (ast.Tuple, ast.List)):
            continue
        bad = _b36_literal_mismatch(tgt, node.value)
        if bad is None:
            continue
        _, n_tgt, n_val = bad
        issues.append(_issue(
            'B36',
            f'字面量解包数量错配：左侧 {n_tgt} 个目标 '
            f'vs 右侧 {n_val} 个值，一执行即 '
            f'ValueError (too many/few values to unpack)',
            tgt.lineno,
            '对齐两侧元素数量，或用 *rest 星号目标吸收多余值',
            DiagnoseSeverity.ERROR))
    return issues
def _has_starred_element(seq: ast.Tuple | ast.List) -> bool:
    return any(isinstance(e, ast.Starred) for e in seq.elts)
def _b36_for_issue(node: ast.For) -> DiagnoseIssue | None:
    tgt = node.target
    if not (isinstance(tgt, (ast.Tuple, ast.List))
            and isinstance(node.iter, (ast.Tuple, ast.List))
            and node.iter.elts):
        return None
    if _has_starred_element(tgt):
        return None
    for el in node.iter.elts:
        if not isinstance(el, (ast.Tuple, ast.List)):
            continue
        bad = _b36_literal_mismatch(tgt, el)
        if bad is None:
            continue
        val_node, n_tgt, n_val = bad
        return _issue(
            'B36',
            f'for 循环头解包数量错配：目标 {n_tgt} 元 '
            f'vs 第 {val_node.lineno} 行元素 {n_val} 元，'
            f'迭代到该元素即 ValueError',
            val_node.lineno,
            '对齐解包目标与元素元组长度，或改用具名记录/dataclass',
            DiagnoseSeverity.ERROR)
    return None
def _b36_node_issues(node) -> list[DiagnoseIssue]:
    if isinstance(node, ast.Assign):
        return _b36_assign_issues(node)
    if isinstance(node, ast.For):
        issue = _b36_for_issue(node)
        return [issue] if issue is not None else []
    return []
def detect_b36_unpack_literal_mismatch(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, (ast.Assign, ast.For), _b36_node_issues, filepath, 'B36', 'unpack_literal_mismatch', multi=True)
def _re_flags_node(node: ast.Call, api_name: str) -> ast.AST | None:
    flag_node = None
    for kw in node.keywords:
        if kw.arg == 'flags':
            flag_node = kw.value
            break
    if flag_node is None:
        _pos = _RE_FLAG_POS.get(api_name)
        if _pos is not None and len(node.args) > _pos:
            flag_node = node.args[_pos]
    return flag_node
def _re_flags_name(flag_node: ast.AST, pm: dict,
                   scope_imports: dict) -> str | None:
    if (isinstance(flag_node, ast.Attribute)
            and isinstance(flag_node.value, ast.Name)):
        rec = _import_binding_at(
            scope_imports, pm, flag_node, flag_node.value.id)
        if _binding_is_re_module(rec):
            return flag_node.attr
    if isinstance(flag_node, ast.Name):
        binding = _from_binding(
            _import_binding_at(scope_imports, pm, flag_node, flag_node.id))
        if binding is not None and binding[0] == 're':
            return binding[1]
    return None
def _re_flags_eval(flag_node: ast.AST, pm: dict,
                   scope_imports: dict) -> tuple[object, bool]:
    if (isinstance(flag_node, ast.BinOp)
            and isinstance(flag_node.op, ast.BitOr)):
        left, left_ok = _re_flags_eval(flag_node.left, pm, scope_imports)
        right, right_ok = _re_flags_eval(flag_node.right, pm, scope_imports)
        if not (left_ok and right_ok
                and isinstance(left, int) and isinstance(right, int)):
            return 0, False
        return left | right, True
    if isinstance(flag_node, ast.Constant):
        return flag_node.value, True
    name = _re_flags_name(flag_node, pm, scope_imports)
    if name is None:
        return 0, False
    val = getattr(_re, name, None)
    return val, isinstance(val, int)
def _resolve_re_flags(node: ast.Call, api_name: str,
                      pm: dict, scope_imports: dict) -> tuple[object, bool]:
    flag_node = _re_flags_node(node, api_name)
    if flag_node is None:
        return 0, True
    return _re_flags_eval(flag_node, pm, scope_imports)
def detect_b42_invalid_regex_literal(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, scope_imports = _scope_context(tree)
    return _emit(tree, ast.Call, _b42_probe_call, filepath, 'B42', 'invalid_regex_literal', args=(pm, scope_imports))
def _b42_re_api_name(node: ast.Call, pm: dict,
                     scope_imports: dict) -> str | None:
    func = node.func
    if isinstance(func, ast.Attribute) and func.attr in _RE_API:
        if not isinstance(func.value, ast.Name):
            return None
        rec = _import_binding_at(scope_imports, pm, node, func.value.id)
        return func.attr if _binding_is_re_module(rec) else None
    if not isinstance(func, ast.Name):
        return None
    binding = _from_binding(
        _import_binding_at(scope_imports, pm, node, func.id))
    if binding is not None and binding[0] == 're' and binding[1] in _RE_API:
        return binding[1]
    return None
def _b42_pattern_node(node: ast.Call) -> ast.AST | None:
    if node.args:
        return node.args[0]
    for kw in node.keywords:
        if kw.arg == 'pattern':
            return kw.value
    return None
def _b42_probe_call(node: ast.Call, pm: dict,
                    scope_imports: dict) -> DiagnoseIssue | None:
    api_name = _b42_re_api_name(node, pm, scope_imports)
    if api_name is None:
        return None
    pat = _b42_pattern_node(node)
    if not (isinstance(pat, ast.Constant)
            and isinstance(pat.value, (str, bytes))):
        return None
    flags_val, flags_ok = _resolve_re_flags(
        node, api_name, pm, scope_imports)
    if not flags_ok:
        return None
    try:
        _re.compile(pat.value, flags_val)
    except (_re.error, OverflowError, ValueError, TypeError, RecursionError) as e:
        log_swallowed(__name__, e, context='_b42_probe_call:Exc+')
        exc_name = (f're.{type(e).__name__}' if isinstance(e, _re.error)
                    else type(e).__name__)
        return _issue(
            'B42',
            f're 调用字面量必失败: {e}——一执行即 {exc_name}',
            pat.lineno,
            '修正 pattern 语法（括号配对/转义/量词目标）或 flags 取值，'
            '或改用 r-string 复核',
            DiagnoseSeverity.ERROR)
    return None
def _b43_dict_literal_keys(dict_node: ast.Dict) -> set | None:
    keys = set()
    for k in dict_node.keys:
        if not (isinstance(k, ast.Constant) and isinstance(k.value, str)):
            return None
        keys.add(k.value)
    return keys
def _b43_call_issues(node: ast.Call) -> list[DiagnoseIssue]:
    provided = {kw.arg for kw in node.keywords if kw.arg}
    if not provided and not any(kw.arg is None for kw in node.keywords):
        return []
    issues = []
    for kw in node.keywords:
        if kw.arg is not None or not isinstance(kw.value, ast.Dict):
            continue
        keys = _b43_dict_literal_keys(kw.value)
        if keys is None:
            continue
        dup = sorted(provided & keys)
        if dup:
            issues.append(_issue(
                'B43',
                f'关键字实参重复：{dup} 由显式关键字或多个 '
                f'**dict 字面量重复提供，一执行即 '
                f'TypeError: got multiple values',
                kw.lineno,
                '删除重复键，确保每个关键字只由一处提供',
                DiagnoseSeverity.ERROR))
        provided.update(keys)
    return issues
def detect_b43_duplicate_keyword_arg(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, ast.Call, _b43_call_issues, filepath, 'B43', 'duplicate_keyword_arg', multi=True)
_B44_BASE_NONE = 'none'
_B44_BASE_LITERAL = 'literal'
_B44_BASE_DYNAMIC = 'dynamic'
_B44_BASE_CONFLICT = 'conflict'
_B44_UNEXPECTED_KEYWORD = 'unexpected_keyword'
_B44_TOO_MANY = 'too_many'
_B44_STRING_SECOND_ARG = 'string_second_arg'
_B44_ARGS_OVERFLOW = 3
def _b44_min_positional_args(args: list[ast.expr]) -> int:
    count = 0
    for arg in args:
        if not isinstance(arg, ast.Starred):
            count += 1
        elif (isinstance(arg.value, (ast.List, ast.Tuple))
              and not _has_starred_element(arg.value)):
            count += len(arg.value.elts)
        elif (isinstance(arg.value, ast.Set)
              and not _has_starred_element(arg.value)
              and all(isinstance(e, ast.Constant) for e in arg.value.elts)):
            count += len({e.value for e in arg.value.elts})
    return count
def _b44_static_positional_prefix(
        args: list[ast.expr]) -> tuple[list[ast.expr], bool]:
    prefix: list[ast.expr] = []
    for arg in args:
        if not isinstance(arg, ast.Starred):
            prefix.append(arg)
            continue
        value = arg.value
        if (isinstance(value, (ast.List, ast.Tuple))
                and not _has_starred_element(value)):
            prefix.extend(value.elts)
            continue
        if (isinstance(value, ast.Set) and not _has_starred_element(value)
                and all(isinstance(e, ast.Constant) for e in value.elts)):
            unique: list[ast.expr] = []
            seen = set()
            for element in value.elts:
                if element.value in seen:
                    continue
                seen.add(element.value)
                unique.append(element)
            if len(unique) <= 1:
                prefix.extend(unique)
                continue
        return prefix, True
    return prefix, False

def _b44_keyword_args(
        node: ast.Call) -> tuple[list[tuple[str, ast.AST]], bool]:
    items: list[tuple[str, ast.AST]] = []
    complete = True
    for kw in node.keywords:
        if kw.arg is not None:
            items.append((kw.arg, kw.value))
            continue
        if not isinstance(kw.value, ast.Dict):
            complete = False
            continue
        expanded: dict[str, ast.AST] = {}
        for key, value in zip(kw.value.keys, kw.value.values, strict=True):
            if not (isinstance(key, ast.Constant)
                    and isinstance(key.value, str)):
                complete = False
                break
            # 同一个 dict 字面量里的重复键在调用前已由 dict 自身覆盖。
            expanded[key.value] = value
        else:
            items.extend(expanded.items())
            continue
        break
    return items, complete

def _b44_unexpected_keywords(
        node: ast.Call, keyword_args: list[tuple[str, ast.AST]]) -> list[str]:
    allowed = {'base'} if node.func.id == 'int' else set()
    return sorted({name for name, _value in keyword_args
                   if name not in allowed})

def _b44_base_arg(
        node: ast.Call,
        keyword_args: list[tuple[str, ast.AST]]) -> tuple[object, str]:
    positional_args, dynamic_prefix = _b44_static_positional_prefix(node.args)
    positional = positional_args[1] if len(positional_args) >= 2 else None
    keyword = next((value for name, value in keyword_args if name == 'base'),
                   None)
    if keyword is not None and _b44_min_positional_args(node.args) >= 2:
        return None, _B44_BASE_CONFLICT
    if positional is None and dynamic_prefix:
        return None, _B44_BASE_DYNAMIC
    base_node = keyword if keyword is not None else positional
    if base_node is None:
        return None, _B44_BASE_NONE
    if isinstance(base_node, ast.Constant):
        return base_node.value, _B44_BASE_LITERAL
    return None, _B44_BASE_DYNAMIC
def _b44_literal_call(node: ast.Call, pm: dict
                       ) -> tuple[str, ast.Constant, object, str] | None:
    if not (isinstance(node.func, ast.Name)
            and node.func.id in _LITERAL_PARSE_BUILTIN_NAMES
            and _is_unshadowed_builtin(node, node.func.id, pm)
            and node.args):
        return None
    arg = node.args[0]
    if not (isinstance(arg, ast.Constant) and isinstance(arg.value, (str, bytes))):
        return None
    if _b44_min_positional_args(node.args) >= _B44_ARGS_OVERFLOW:
        return node.func.id, arg, None, _B44_TOO_MANY
    keyword_args, keywords_complete = _b44_keyword_args(node)
    if _b44_unexpected_keywords(node, keyword_args):
        return node.func.id, arg, None, _B44_UNEXPECTED_KEYWORD
    if not keywords_complete:
        return None
    base, base_state = _b44_base_arg(node, keyword_args)
    if base_state == _B44_BASE_DYNAMIC:
        positional_count = _b44_min_positional_args(node.args)
        if positional_count >= 2 and node.func.id == 'float':
            return node.func.id, arg, None, _B44_TOO_MANY
        if positional_count >= 2 and node.func.id == 'complex':
            return node.func.id, arg, None, _B44_STRING_SECOND_ARG
        return None
    return node.func.id, arg, base, base_state
def _b44_probe_node(node: ast.Call, pm: dict) -> DiagnoseIssue | None:
    hit = _b44_literal_call(node, pm)
    if hit is None:
        return None
    ctor_name, arg, base, base_state = hit
    if base_state == _B44_TOO_MANY:
        return _issue(
            'B44',
            f'{ctor_name}() 位置参数至少 {_b44_min_positional_args(node.args)} 个超出构造器接受的上界：'
            f'一执行即 TypeError (too many arguments)',
            arg.lineno,
            f'数字构造器只接受 ({ctor_name} 字符串[, base])，多余位置参数不得传入',
            DiagnoseSeverity.ERROR)
    if base_state == _B44_STRING_SECOND_ARG:
        return _issue(
            'B44',
            'complex() 的第一个参数为字符串/字节串时不能接受第二参数：'
            '一执行即 TypeError',
            arg.lineno,
            '字符串解析只保留一个参数；实部与虚部应改为数值分别传入',
            DiagnoseSeverity.ERROR)
    if base_state == _B44_BASE_CONFLICT:
        return _issue(
            'B44',
            f'{ctor_name}() 的 base 同时以位置参数与关键字给出，'
            f'一执行即 TypeError: argument for base given by name '
            f'and positionally',
            arg.lineno,
            '删除重复的一侧：base 只保留位置或关键字其中一种写法',
            DiagnoseSeverity.ERROR)
    if base_state == _B44_UNEXPECTED_KEYWORD:
        keyword_args, _complete = _b44_keyword_args(node)
        unexpected = _b44_unexpected_keywords(node, keyword_args)
        return _issue(
            'B44',
            f'{ctor_name}() 收到不支持的关键字参数 {unexpected}：一执行即 TypeError',
            arg.lineno,
            '删除未知关键字；数字字符串解析只保留构造器支持的形参',
            DiagnoseSeverity.ERROR)
    ctor = _B44_CTORS[ctor_name]
    try:
        if base_state == _B44_BASE_NONE:
            ctor(arg.value)
        else:
            ctor(arg.value, base)
    except (ValueError, TypeError) as e:
        log_swallowed(__name__, e, context='_b44_probe_node:ValueError+')
        return _issue(
            'B44',
            f'{ctor_name}({arg.value!r}) 解析必失败: {e}',
            arg.lineno,
            f'修正字面量内容，或改用 {ctor_name}(float(...)) 等两步解析并补异常处理',
            DiagnoseSeverity.ERROR)
    return None
def detect_b44_literal_number_parse_invalid(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, _scope_imports = _scope_context(tree)
    return _emit(tree, ast.Call, _b44_probe_node, filepath,
                 'B44', 'literal_number_parse_invalid', args=(pm,))
def _b45_container_length(v: ast.AST) -> int | None:
    if isinstance(v, ast.Constant) and isinstance(v.value, (str, bytes)):
        return len(v.value)
    if isinstance(v, (ast.Tuple, ast.List)) and not _has_starred_element(v):
        return len(v.elts)
    return None
def _b45_index_value(sl: ast.AST) -> int | None:
    value = _literal_number_value(sl)
    return value if isinstance(value, int) else None
def _b45_subscript_issue(node: ast.Subscript) -> DiagnoseIssue | None:
    length = _b45_container_length(node.value)
    if length is None:
        return None
    sl = node.slice
    idx = _b45_index_value(sl)
    if idx is None:
        return None
    if -length <= idx < length:
        return None
    return _issue(
        'B45',
        f'字面量容器（长度 {length}）下标 {idx} 越界，'
        f'一执行即 IndexError',
        sl.lineno,
        f'合法下标区间为 [{-length}, {length - 1}]，修正下标或容器内容',
        DiagnoseSeverity.ERROR)
def detect_b45_literal_subscript_out_of_range(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, ast.Subscript, _b45_subscript_issue, filepath, 'B45', 'literal_subscript_out_of_range')
_B50_NOT_LITERAL = object()
def _b50_number_value(node: ast.AST):
    value = _literal_number_value(node)
    if value is not _NOT_NUMBER:
        return value
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        left = _literal_number_value(node.left)
        right = _literal_number_value(node.right)
        if (left is not _NOT_NUMBER and right is not _NOT_NUMBER
                and (isinstance(left, complex) or isinstance(right, complex))):
            return (left + right if isinstance(node.op, ast.Add)
                    else left - right)
    return _B50_NOT_LITERAL
def _b50_literal_value(pat: ast.AST):
    _match_value = getattr(ast, 'MatchValue', None)
    if _match_value is None or not isinstance(pat, _match_value):
        return _B50_NOT_LITERAL
    node = pat.value
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
        return node.value
    return _b50_number_value(node)
def _b50_match_issues(node) -> list[DiagnoseIssue]:
    _match_singleton = getattr(ast, 'MatchSingleton', None)
    seen_values: dict = {}
    seen_singletons: dict = {}
    issues = []
    for case in node.cases:
        pat = case.pattern
        guarded = case.guard is not None
        value = _b50_literal_value(pat)
        if value is not _B50_NOT_LITERAL:
            earlier = seen_values.get(value)
            if earlier is None:
                earlier = seen_singletons.get(value)
            if earlier is not None:
                issues.append(_b50_dup_issue(pat, repr(value), earlier))
            elif not guarded:
                seen_values[value] = pat.lineno
            continue
        if _match_singleton is not None and isinstance(pat, _match_singleton):
            earlier = seen_singletons.get(pat.value)
            if earlier is None and pat.value is not None:
                earlier = seen_values.get(pat.value)
            if earlier is not None:
                issues.append(_b50_dup_issue(pat, repr(pat.value), earlier))
            elif not guarded:
                seen_singletons[pat.value] = pat.lineno
    return issues
def _b50_dup_issue(pat, label: str, earlier_line: int) -> DiagnoseIssue:
    return _issue(
        'B50',
        f'重复 case 模式 {label}：第 {earlier_line} 行已按 == 语义匹配，'
        f'本分支永不可达',
        pat.lineno,
        '删除重复分支或改为带 guard 的条件模式（case X if ...）',
        DiagnoseSeverity.ERROR)
def detect_b50_duplicate_case_pattern(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    _Match = getattr(ast, 'Match', None)
    if _Match is None:
        return []
    return _emit(tree, _Match, _b50_match_issues, filepath, 'B50', 'duplicate_case_pattern', multi=True)
def _b51_index_len_target(node: ast.Subscript, pm: dict) -> str | None:
    value = node.value
    index = node.slice
    if (not isinstance(value, ast.Name)
            or not isinstance(index, ast.Call) or index.keywords):
        return None
    return value.id if _len_arg_name(index, pm) == value.id else None
def _b51_subscript_issue(node: ast.Subscript, pm: dict) -> DiagnoseIssue | None:
    name = _b51_index_len_target(node, pm)
    if name is None:
        return None
    return _issue(
        'B51',
        f'{name}[len({name})] 下标必越界（合法上界为 '
        f'len({name})-1），一执行即 IndexError',
        node.lineno,
        f'末元素应为 {name}[-1] 或 {name}[len({name})-1]',
        DiagnoseSeverity.ERROR)
_B51_NON_SEQUENCE_CTORS = frozenset({
    'dict', 'set', 'frozenset', 'int', 'float', 'complex', 'bool', 'object',
})
def _b51_non_sequence_binding(value: ast.AST,
                              pm: dict) -> _LiteralBinding | None:
    non_sequence = isinstance(value, (
        ast.Dict, ast.Set, ast.DictComp, ast.SetComp, ast.GeneratorExp,
        ast.Lambda,
    ))
    if isinstance(value, ast.Constant) and not isinstance(value.value, (str, bytes)):
        non_sequence = True
    if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id in _B51_NON_SEQUENCE_CTORS
            and _is_unshadowed_builtin(value, value.func.id, pm)):
        non_sequence = True
    return _LiteralBinding(value, 'non_sequence') if non_sequence else None
def _b51_match_with_bindings(node: ast.AST, bindings: dict,
                             pm: dict) -> DiagnoseIssue | None:
    if not isinstance(node, ast.Subscript):
        return None
    if (isinstance(node.value, ast.Name)
            and node.value.id in bindings):
        return None
    return _b51_subscript_issue(node, pm)
def detect_b51_index_of_len_oob(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm = parent_map(tree)
    return _scan_binding_domain(
        'B51', 'index_of_len_oob', tree,
        lambda node, bindings: _b51_match_with_bindings(node, bindings, pm),
        lambda value: _b51_non_sequence_binding(value, pm), filepath)
def _b57_condition_issue(node) -> DiagnoseIssue | None:
    test = node.test
    negated = False
    while isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        negated = not negated
        test = test.operand
    if not (isinstance(test, ast.NamedExpr)
            and isinstance(test.value, ast.Constant)):
        return None
    truth = bool(test.value.value) != negated
    where = 'if' if isinstance(node, ast.If) else 'while'
    return _issue(
        'B57',
        f'{where} 条件为海象绑定常量 {test.value.value!r}（恒'
        f'{"真" if truth else "假"}），条件守卫失效——疑似漏写比较',
        test.lineno,
        '补全比较（如 if (x := f()) == 预期值），或移除海象直接判值')
def detect_b57_walrus_literal_condition(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    return _emit(tree, (ast.If, ast.While), _b57_condition_issue, filepath, 'B57', 'walrus_literal_condition')
def _bad_type_arg_el(el: ast.AST, pm: dict) -> str | None:
    if isinstance(el, ast.Constant):
        return f'{el.value!r}（字面量）'
    if isinstance(el, (ast.List, ast.Set, ast.Dict)):
        return f'{type(el).__name__.lower()} 字面量'
    if (isinstance(el, ast.Name) and el.id == 'NotImplemented'
            and _is_unshadowed_builtin(el, 'NotImplemented', pm)):
        return 'NotImplemented（非类型）'
    return None
def _b61_arg_issues(func_name: str, t: ast.AST, pm: dict) -> list[DiagnoseIssue]:
    if not isinstance(t, ast.Tuple):
        b = _bad_type_arg_el(t, pm)
        if not b:
            return []
        return [_issue(
            'B61',
            f'{func_name} 第二参数为 {b}——执行即 TypeError: '
            f'arg 2 must be a type, a tuple of types, or a union',
            t.lineno,
            '第二参数只放类型或类型元组（列表形态应改元组）',
            DiagnoseSeverity.ERROR)]
    issues = []
    for el in t.elts:
        if isinstance(el, ast.Tuple):
            issues.extend(_b61_arg_issues(func_name, el, pm))
            continue
        b = _bad_type_arg_el(el, pm)
        if b:
            issues.append(_issue(
                'B61',
                f'{func_name} 第二参数元组元素为 {b}——匹配到该元素时 TypeError'
                '（前序元素匹配成功时会短路）',
                el.lineno,
                '第二参数只放类型（如 int/str）或类型元组',
                DiagnoseSeverity.ERROR))
    return issues
def _b61_call_issues(node: ast.Call, pm: dict) -> list[DiagnoseIssue]:
    if not (isinstance(node.func, ast.Name)
            and node.func.id in ('isinstance', 'issubclass')
            and _is_unshadowed_builtin(node, node.func.id, pm)
            and len(node.args) >= 2):
        return []
    return _b61_arg_issues(node.func.id, node.args[1], pm)
def detect_b61_isinstance_invalid_type_arg(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, _scope_imports = _scope_context(tree)
    return _emit(tree, ast.Call, _b61_call_issues, filepath, 'B61',
                 'isinstance_invalid_type_arg', multi=True, args=(pm,))
_B63_BUILTINS = frozenset({'max', 'min'})
def _b63_single_arg(node: ast.Call) -> ast.AST | None:
    if len(node.args) != 1:
        return None
    if any(kw.arg != 'key' for kw in node.keywords):
        return None
    return node.args[0]
def _b63_hit_call(node: ast.AST, pm: dict) -> ast.Call | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if not isinstance(func, ast.Name) or func.id not in _B63_BUILTINS:
        return None
    if not _is_unshadowed_builtin(node, func.id, pm):
        return None
    arg = _b63_single_arg(node)
    if arg is None:
        return None
    if not _is_empty_literal(arg, pm):
        return None
    return node
def _b63_node_issue(node: ast.AST, pm: dict) -> DiagnoseIssue | None:
    hit = _b63_hit_call(node, pm)
    if hit is None:
        return None
    return _issue(
        'B63',
        f"{hit.func.id}() 对空字面量序列求值且无 default：必 ValueError: arg is an empty sequence",
        hit.lineno,
        f"补 default 参数（{hit.func.id}(seq, default=...)）或先判空",
        DiagnoseSeverity.ERROR)
def detect_b63_min_max_empty_literal(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, _scope_imports = _scope_context(tree)
    return _emit(tree, ast.Call, _b63_node_issue, filepath,
                 'B63', 'min_max_empty_literal', args=(pm,))
def _b67_is_input_call(n: ast.AST, pm: dict) -> bool:
    return (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
            and n.func.id == 'input'
            and _is_unshadowed_builtin(n, 'input', pm)
            and len(n.args) <= 1 and not n.keywords
            and all(not isinstance(arg, ast.Starred) for arg in n.args))
def _b67_issue(node: ast.BinOp, message: str,
               suggestion: str = '先转换类型：n = int(input()) 后再运算') -> DiagnoseIssue:
    return _issue('B67', message, node.lineno, suggestion, DiagnoseSeverity.ERROR)
_B67_OP_SYMBOLS = {
    ast.Sub: '-', ast.Div: '/', ast.FloorDiv: '//', ast.Pow: '**',
}
def _b67_literal_operand_value(node: ast.AST):
    if isinstance(node, ast.Constant):
        return node.value
    return _literal_number_value(node)
def _b67_issue_for_binop(node: ast.BinOp, pm: dict) -> DiagnoseIssue | None:
    left_in = _b67_is_input_call(node.left, pm)
    right_in = _b67_is_input_call(node.right, pm)
    if not (left_in or right_in):
        return None
    op = node.op
    symbol = _B67_OP_SYMBOLS.get(type(op))
    if symbol is not None:
        return _b67_issue(
            node,
            f'input() 返回 str 直接参与 {symbol} 数值运算：必 TypeError（漏写 int()/float() 转换）')
    if isinstance(op, ast.Mult):
        other = node.right if left_in else node.left
        literal = _b67_literal_operand_value(other)
        invalid_literal = (
            literal is not _NOT_NUMBER and not isinstance(literal, int))
        if (left_in and right_in) or invalid_literal or isinstance(
                other, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            return _b67_issue(
                node,
                'input() 返回 str 参与字符串乘法时，另一侧必须是整数：必 TypeError',
                '重复字符串请改用整数次数；数值乘法先转换 int()/float()')
    if isinstance(op, ast.Add):
        other = node.right if left_in else node.left
        literal = _b67_literal_operand_value(other)
        if literal is not _NOT_NUMBER and not isinstance(literal, str):
            return _b67_issue(
                node,
                f'input() 返回 str 与 {type(literal).__name__} 字面量相加：必 TypeError（漏写 int()/float() 转换或类型错误）')
        if isinstance(other, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            return _b67_issue(
                node,
                f'input() 返回 str 与 {type(other).__name__} 字面量相加：必 TypeError（str 只能与 str 拼接）',
                '先转换类型或改用字符串拼接')
    return None
def detect_b67_input_arithmetic(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    pm, _scope_imports = _scope_context(tree)
    return _emit(tree, ast.BinOp, _b67_issue_for_binop, filepath,
                 'B67', 'input_arithmetic', args=(pm,))
GATE_DETECTORS: dict[str, Any] = {
    "B05": detect_b05_none_comparison,
    "B08": detect_b08_is_literal_comparison,
    "B14": detect_b14_type_equality,
    "B15": detect_b15_division_by_zero,
    "B16": detect_b16_float_equality,
    "B20": detect_b20_bool_redundancy,
    "B21": detect_b21_mutator_return_used,
    "B31": detect_b31_assert_validation,
    "B33": detect_b33_len_zero_check,
    "B36": detect_b36_unpack_literal_mismatch,
    "B42": detect_b42_invalid_regex_literal,
    "B43": detect_b43_duplicate_keyword_arg,
    "B44": detect_b44_literal_number_parse_invalid,
    "B45": detect_b45_literal_subscript_out_of_range,
    "B50": detect_b50_duplicate_case_pattern,
    "B51": detect_b51_index_of_len_oob,
    "B56": detect_b56_nan_equality,
    "B57": detect_b57_walrus_literal_condition,
    "B61": detect_b61_isinstance_invalid_type_arg,
    "B63": detect_b63_min_max_empty_literal,
    "B67": detect_b67_input_arithmetic,
}

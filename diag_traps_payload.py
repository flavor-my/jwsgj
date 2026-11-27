from __future__ import annotations

import ast
import builtins
import codecs
import logging
import os
import re
import sys
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_bindings import ScopeEventIndex
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    as_format_call,
    build_parent_map,
    collect_param_names,
    is_docstring_stmt,
    is_none_literal,
    is_star_import,
    iter_arg_defaults,
    iter_scope_nodes,
    iter_unpack_target_names,
    kw_arg,
    segments_equal,
)
from jwsgj.diag_shared_ast_views import iter_nodes
from jwsgj.diag_shared_source_core import (
    FRAME_BOUNDARY_NODES,
    extract_code_lines,
)
from jwsgj.diag_shared_source_scan import (
    apply_rule_suppress,
    normalize_rule_source,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
__all__ = [
    "check_AT01",
    "check_AT02",
    "check_CF01",
    "check_CF02",
    "check_EN01",
    "check_EN03",
    "check_FM01",
    "check_FM02",
    "check_FM03",
    "check_GF02",
    "check_IN01",
    "check_SP01",
]
_log.info("diag_traps_payload 运行期载荷规则域已加载: %d 项导出", len(__all__))
def _is_str_constant(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and isinstance(node.value, str)
_SEGMENT_RE = re.compile(r'[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|[0-9]+')
def _text_segments(text: str) -> list[str]:
    segments: list[str] = []
    for chunk in re.split(r'[^A-Za-z0-9]+', text):
        if chunk:
            segments.extend(part.lower()
                            for part in _SEGMENT_RE.findall(chunk))
    return segments
def _definition_time_expressions(node: ast.AST) -> tuple:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return (*node.decorator_list, *iter_arg_defaults(node.args))
    if isinstance(node, ast.Lambda):
        return tuple(iter_arg_defaults(node.args))
    if isinstance(node, ast.ClassDef):
        return (*node.decorator_list, *node.bases,
                *(keyword.value for keyword in node.keywords))
    return ()
def _function_annotation_roots(scope: ast.AST) -> tuple:
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ()
    args = scope.args
    parameters = (*args.posonlyargs, *args.args, *args.kwonlyargs,
                  args.vararg, args.kwarg)
    annotations = [parameter.annotation for parameter in parameters
                   if parameter is not None and parameter.annotation is not None]
    if scope.returns is not None:
        annotations.append(scope.returns)
    return tuple(annotations)
def _definition_type_param_roots(scope: ast.AST) -> tuple:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return _function_annotation_roots(scope)
    if isinstance(scope, ast.ClassDef):
        return (*scope.bases, *(keyword.value for keyword in scope.keywords))
    return ()
def _outer_evaluation_roots(scope: ast.AST) -> tuple:
    roots = list(_definition_time_expressions(scope))
    roots.extend(_function_annotation_roots(scope))
    if isinstance(scope, COMP_SCOPE_NODES) and scope.generators:
        roots.append(scope.generators[0].iter)
    return tuple(roots)
def _outer_evaluation_scopes(tree: ast.AST) -> dict[int, set[int]]:
    outer: dict[int, set[int]] = {}
    for scope in walk_nodes(tree):
        for root in _outer_evaluation_roots(scope):
            for node in walk_nodes(root):
                outer.setdefault(id(node), set()).add(id(scope))
    return outer
_EVALUATION_SCOPE_NODES = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
    ast.ClassDef, *COMP_SCOPE_NODES)
def _evaluation_scope_chain(
        node: ast.AST, parents: dict[int, ast.AST],
        outer_scopes: dict[int, set[int]]) -> list[ast.AST]:
    chain: list[ast.AST] = []
    skipped = outer_scopes.get(id(node), set())
    current = parents.get(id(node))
    while current is not None:
        if isinstance(current, _EVALUATION_SCOPE_NODES):
            if id(current) in skipped:
                current = parents.get(id(current))
                continue
            if not (chain and isinstance(current, ast.ClassDef)):
                chain.append(current)
        current = parents.get(id(current))
    return chain
_AT01_ARTIFACT_TOKENS = (
    'temp', 'tmp', 'cache', 'report', 'state', 'log', 'lock', 'backup', 'plan',
    'anchor', 'store', 'history', 'chain', 'closure', 'script', 'mutant',
    'baseline', 'tracker', 'audit', 'evidence', 'artifact', 'snapshot',
    'fixture', 'dump', 'output', 'registry', 'adjustment',
)
# 产物目录常以复数命名（logs/、reports/、caches/、registries/）：
# 常规复数由尾部 (?:e?s)? 覆盖，y→ies 变体（registry→registries）在此显式补入，
# 否则复数产物目录会被误判为无产物证据而误报 AT-01。
_AT01_ARTIFACT_TOKENS_ALL = sorted(
    set(_AT01_ARTIFACT_TOKENS)
    | {token[:-1] + 'ies' for token in _AT01_ARTIFACT_TOKENS
       if token.endswith('y')},
    key=len, reverse=True)
_AT01_ARTIFACT_TOKEN_RE = re.compile(
    r'(?<![a-z0-9])(?:'
    + '|'.join(map(re.escape, _AT01_ARTIFACT_TOKENS_ALL))
    + r')(?:e?s)?(?![a-z0-9])')
_AT01_SRC_SUFFIXES = ('.py', '.pyw', '.md', '.yaml', '.yml', '.toml',
                      '.ini', '.cfg', '.sh', '.bat')
_AT01_ARTIFACT_FUNCS = (
    'tempfile', 'mkstemp', 'mkdtemp',
    'mktemp', 'gettempdir', 'NamedTemporaryFile', 'TemporaryFile',
    'TemporaryDirectory',
)
class _AT01ExprFacts(NamedTuple):
    names: list
    consts: list
    calls: list
def _at01_call_name(call: ast.Call) -> str:
    fn = call.func
    if isinstance(fn, ast.Name):
        return fn.id
    if isinstance(fn, ast.Attribute):
        return fn.attr
    return ""
def _at01_expr_facts(expr) -> _AT01ExprFacts:
    names: list = []
    consts: list = []
    calls: list = []
    for sub in walk_nodes(expr):
        if isinstance(sub, ast.Name):
            names.append(sub.id)
            continue
        if isinstance(sub, ast.Attribute):
            names.append(sub.attr)
            continue
        if isinstance(sub, ast.Call):
            calls.append(_at01_call_name(sub))
            continue
        if _is_str_constant(sub):
            consts.append(sub.value)
    return _AT01ExprFacts(names, consts, calls)
def _at01_facts_is_source(facts: _AT01ExprFacts) -> bool:
    return any(c.lower().endswith(_AT01_SRC_SUFFIXES) for c in facts.consts)
def _at01_facts_have_artifact(facts: _AT01ExprFacts) -> bool:
    if _at01_texts_have_artifact((*facts.consts, *facts.names)):
        return True
    return any(name in _AT01_ARTIFACT_FUNCS for name in facts.calls)
def _at01_iter_scope_nodes(scope):
    body = getattr(scope, 'body', None)
    stack = (list(body) if isinstance(body, list)
             else [body] if isinstance(body, ast.AST) else [])
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                             ast.ClassDef)):
            stack.extend(_definition_time_expressions(node))
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _at01_iter_scope_assignments(scope):
    for node in _at01_iter_scope_nodes(scope):
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                             ast.NamedExpr)):
            yield node
def _at01_star_import_before(scope, pos: tuple[int, int]) -> bool:
    return any(
        is_star_import(node)
        and (node.lineno, node.col_offset) < pos
        for node in _at01_iter_scope_nodes(scope))
def _at01_node_has_unknown_binding(node, var_name: str,
                                   match_attr: bool) -> bool:
    if is_star_import(node):
        return True
    bound_name = var_name.split('.', 1)[0] if match_attr else var_name
    extractor = _AT01_BINDING_EXTRACTORS.get(type(node), _at01_binding_none)
    local_names, _declared_global = extractor(node)
    return bound_name in local_names
def _at01_scope_has_unknown_binding(scope, pos: tuple[int, int],
                                    var_name: str, match_attr: bool) -> bool:
    for node in _at01_iter_scope_nodes(scope):
        if not hasattr(node, 'lineno'):
            continue
        if (node.lineno, node.col_offset) >= pos:
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        if (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                              ast.NamedExpr))
                and getattr(node, 'value', None) is not None):
            continue
        if _at01_node_has_unknown_binding(node, var_name, match_attr):
            return True
    return False
def _at01_scope_trace(scope, pos: tuple[int, int], var_name: str,
                      match_attr: bool) -> list:
    latest_values = None
    latest_key = None
    for node in _at01_iter_scope_nodes(scope):
        if not hasattr(node, 'lineno'):
            continue
        key = (node.lineno, node.col_offset)
        if key >= pos:
            continue
        value = getattr(node, 'value', None)
        if (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                              ast.NamedExpr)) and value is not None):
            values = _at01_assignment_values(node, var_name, match_attr)
            if values and (latest_key is None or key > latest_key):
                latest_key = key
                latest_values = values
                continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        if (_at01_node_has_unknown_binding(node, var_name, match_attr)
                and (latest_key is None or key > latest_key)):
            latest_key = key
            latest_values = []
    return [] if latest_values is None else latest_values
def _at01_enclosing_funcs(tree, node: ast.AST) -> list:
    chain = _evaluation_scope_chain(
        node, build_parent_map(tree), _outer_evaluation_scopes(tree))
    function_nodes = (ast.FunctionDef, ast.AsyncFunctionDef,
                      ast.Lambda, ast.ClassDef)
    return [scope for scope in chain if isinstance(scope, function_nodes)]
def _at01_trace_assignments(enclosing: list, pos, var_name,
                            tree=None, match_attr=False):
    for func in enclosing:
        if _at01_scope_writes(func, var_name, match_attr, pos):
            return _at01_scope_trace(func, pos, var_name, match_attr)
        if _at01_scope_has_unknown_binding(
                func, pos, var_name, match_attr):
            return []
        if not match_attr and var_name in _at01_local_binding_names(func):
            return []
    if isinstance(tree, ast.Module):
        return _at01_scope_trace(tree, pos, var_name, match_attr)
    return []
def _at01_scope_writes(scope, var_name: str, match_attr: bool,
                       pos: tuple[int, int]) -> bool:
    return any(
        getattr(node, 'value', None) is not None
        and (node.lineno, node.col_offset) < pos
        and _at01_assignment_values(node, var_name, match_attr)
        for node in _at01_iter_scope_assignments(scope))
def _at01_binding_none(_node) -> tuple[set, set]:
    return set(), set()
def _at01_binding_global(node) -> tuple[set, set]:
    return set(), set(node.names)
def _at01_binding_assign(node) -> tuple[set, set]:
    return set(iter_unpack_target_names(node.targets)), set()
def _at01_binding_single_target(node) -> tuple[set, set]:
    return set(iter_unpack_target_names(node.target)), set()
def _at01_binding_with(node) -> tuple[set, set]:
    names: set = set()
    for item in node.items:
        if item.optional_vars is not None:
            names |= set(iter_unpack_target_names(item.optional_vars))
    return names, set()
def _at01_binding_optional_name(node) -> tuple[set, set]:
    return ({node.name} if node.name else set()), set()
def _at01_binding_import(node) -> tuple[set, set]:
    names: set = set()
    for alias in node.names:
        names.add(alias.asname or alias.name.split('.')[0])
    return names, set()
def _at01_binding_importfrom(node) -> tuple[set, set]:
    return {alias.asname or alias.name for alias in node.names
            if alias.name != '*'}, set()
def _at01_binding_definition(node) -> tuple[set, set]:
    return {node.name}, set()
def _at01_binding_namedexpr(node) -> tuple[set, set]:
    if isinstance(node.target, ast.Name):
        return {node.target.id}, set()
    return set(), set()
def _at01_binding_match_mapping(node) -> tuple[set, set]:
    return ({node.rest} if node.rest else set()), set()
_AT01_BINDING_EXTRACTORS = {
    ast.Global: _at01_binding_global,
    ast.Nonlocal: _at01_binding_global,
    ast.Assign: _at01_binding_assign,
    ast.AnnAssign: _at01_binding_single_target,
    ast.AugAssign: _at01_binding_single_target,
    ast.For: _at01_binding_single_target,
    ast.AsyncFor: _at01_binding_single_target,
    ast.With: _at01_binding_with,
    ast.AsyncWith: _at01_binding_with,
    ast.ExceptHandler: _at01_binding_optional_name,
    ast.Import: _at01_binding_import,
    ast.ImportFrom: _at01_binding_importfrom,
    ast.FunctionDef: _at01_binding_definition,
    ast.AsyncFunctionDef: _at01_binding_definition,
    ast.ClassDef: _at01_binding_definition,
    ast.NamedExpr: _at01_binding_namedexpr,
    ast.MatchAs: _at01_binding_optional_name,
    ast.MatchStar: _at01_binding_optional_name,
    ast.MatchMapping: _at01_binding_match_mapping,
}
def _at01_local_binding_names(func) -> set:
    names = set(collect_param_names(func))
    names.update(
        _name for _name in (getattr(_param, "name", "")
                            for _param in getattr(func, "type_params", ()))
        if _name)
    global_names: set = set()
    for node in _at01_iter_scope_nodes(func):
        if (isinstance(func, ast.ClassDef)
                and isinstance(node, ast.AnnAssign) and node.value is None):
            continue
        extractor = _AT01_BINDING_EXTRACTORS.get(type(node), _at01_binding_none)
        local_names, declared_global = extractor(node)
        names |= local_names
        global_names |= declared_global
    return names - global_names
def _at01_target_contains(target: ast.AST, var_name: str,
                          match_attr: bool) -> bool:
    if isinstance(target, ast.Name):
        return not match_attr and target.id == var_name
    if isinstance(target, ast.Attribute):
        return match_attr and _at01_dotted_path(target) == var_name
    if isinstance(target, ast.Starred):
        return _at01_target_contains(target.value, var_name, match_attr)
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_at01_target_contains(elt, var_name, match_attr)
                   for elt in target.elts)
    return False
def _at01_target_values(target: ast.AST, value: ast.AST, var_name: str,
                        match_attr: bool) -> list:
    if not _at01_target_contains(target, var_name, match_attr):
        return []
    if isinstance(target, (ast.Name, ast.Attribute)):
        return [value]
    if isinstance(target, ast.Starred):
        return [None]
    if not (isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(elt, ast.Starred) for elt in target.elts)):
        return [None]
    values = []
    for target_elt, value_elt in zip(target.elts, value.elts, strict=True):
        values.extend(_at01_target_values(
            target_elt, value_elt, var_name, match_attr))
    return values
def _at01_assignment_values(node: ast.AST, var_name: str,
                            match_attr: bool) -> list:
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    if isinstance(node, ast.AugAssign):
        value = ast.copy_location(ast.BinOp(
            left=node.target, op=node.op, right=node.value), node)
    else:
        value = node.value
    return [bound
            for target in targets
            for bound in _at01_target_values(
                target, value, var_name, match_attr)]
def _at01_texts_have_artifact(texts) -> bool:
    return any(_AT01_ARTIFACT_TOKEN_RE.search(str(text).lower())
               for text in texts)
def _at01_dotted_path(expr) -> str | None:
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Attribute):
        base = _at01_dotted_path(expr.value)
        return f"{base}.{expr.attr}" if base else None
    return None
def _at01_first_path_root(candidates):
    for candidate in candidates:
        root = _at01_path_root(candidate)
        if root is not None:
            return root
    return None
def _at01_path_root(expr) -> tuple[str, bool] | None:
    dotted = _at01_dotted_path(expr)
    if dotted:
        return dotted, isinstance(expr, ast.Attribute)
    if isinstance(expr, ast.BinOp):
        return _at01_first_path_root((expr.left, expr.right))
    if isinstance(expr, ast.JoinedStr):
        return _at01_first_path_root(
            value.value for value in expr.values
            if isinstance(value, ast.FormattedValue))
    if isinstance(expr, (ast.Subscript, ast.Starred)):
        return _at01_path_root(expr.value)
    if isinstance(expr, ast.IfExp):
        return _at01_first_path_root((expr.body, expr.orelse))
    if isinstance(expr, ast.Call):
        return _at01_first_path_root(
            (*expr.args, *(kw.value for kw in expr.keywords)))
    return None
def _at01_should_exempt(tree, path_arg, lineno, pos=None):
    if path_arg is None:
        return False
    facts = _at01_expr_facts(path_arg)
    if _at01_facts_is_source(facts):
        return False
    if isinstance(path_arg, ast.Constant):
        return _at01_texts_have_artifact((str(path_arg.value),))
    if _at01_facts_have_artifact(facts):
        return True
    if pos is None:
        pos = (lineno, 0)
    return _at01_trace_has_artifact(tree, path_arg, pos)
_AT01_ALIAS_MAX_DEPTH = 5
def _at01_rhs_has_artifact(rhs: ast.AST, tree=None,
                           pos: tuple[int, int] | None = None,
                           depth: int = 0) -> bool:
    facts = _at01_expr_facts(rhs)
    if _at01_facts_is_source(facts):
        return False
    if _at01_facts_have_artifact(facts):
        return True
    if (tree is not None and pos is not None
            and depth < _AT01_ALIAS_MAX_DEPTH
            and _at01_path_root(rhs) is not None):
        return _at01_trace_has_artifact(
            tree, rhs, (rhs.lineno, rhs.col_offset), depth + 1)
    return False
def _at01_trace_has_artifact(tree, path_arg, pos: tuple[int, int],
                             depth: int = 0) -> bool:
    root = _at01_path_root(path_arg)
    if root is None:
        return False
    root_var, match_attr = root
    if _fm01_shadowed_by_nearer_scope(tree, path_arg, root_var):
        return False
    enclosing = _at01_enclosing_funcs(tree, path_arg)
    return any(
        rhs is not None and _at01_rhs_has_artifact(rhs, tree, pos, depth)
        for rhs in _at01_trace_assignments(
            enclosing, pos, root_var, tree=tree, match_attr=match_attr))
def _at01_call_mode(node: ast.Call) -> str | None:
    if len(node.args) > 1:
        return node.args[1].value if _is_str_constant(node.args[1]) else None
    for kw in node.keywords:
        if kw.arg == "mode":
            return kw.value.value if _is_str_constant(kw.value) else None
    return ""
def _at01_call_args(
        node: ast.Call) -> tuple[ast.expr | None, str | None]:
    if node.args:
        path_arg = node.args[0]
    else:
        path_arg = next(
            (kw.value for kw in node.keywords if kw.arg == "file"),
            None)
    return path_arg, _at01_call_mode(node)
class _OpenCallIdentity:
    def __init__(self, tree: ast.AST) -> None:
        self._bindings = _ModuleApiScopeBindings(
            tree, frozenset({"io", "builtins"}), frozenset({"open"}))
    def is_open(self, node: ast.Call) -> bool:
        func = node.func
        if isinstance(func, ast.Name):
            found, api = self._bindings.resolve_api(node, func.id, None)
            if found:
                return api == "open"
            return func.id == "open"
        return (isinstance(func, ast.Attribute)
                and func.attr == "open"
                and isinstance(func.value, ast.Name)
                and self._bindings.resolve_api(
                    node, func.value.id, "open")[1] == "open")
def _at01_resolve_open_write(node: ast.AST,
                             identity: _OpenCallIdentity) -> ast.expr | None:
    if not isinstance(node, ast.Call):
        return None
    if not identity.is_open(node):
        return None
    path_arg, mode = _at01_call_args(node)
    if path_arg is None:
        return None
    if mode is None or not any(ch in mode for ch in ("w", "a", "+", "x")):
        return None
    return path_arg
def _scoped_open_calls_missing_encoding(tree: ast.AST) -> list[ast.Call]:
    identity = _OpenCallIdentity(tree)
    calls: list[ast.Call] = []
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call) or not identity.is_open(node):
            continue
        path_arg, mode = _at01_call_args(node)
        if path_arg is None or mode is None or 'b' in mode:
            continue
        if (any(isinstance(arg, ast.Starred) for arg in node.args)
                or any(kw.arg is None for kw in node.keywords)):
            continue
        if (len(node.args) >= 4
                and not is_none_literal(node.args[3])):
            continue
        encoding = kw_arg(node, "encoding")
        if encoding is not None and not is_none_literal(encoding.value):
            continue
        calls.append(node)
    return calls
def check_AT01(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    issues = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    identity = _OpenCallIdentity(tree)
    for node in walk_nodes(tree):
        path_arg = _at01_resolve_open_write(node, identity)
        if path_arg is None:
            continue
        pos = (getattr(path_arg, 'lineno', node.lineno),
               getattr(path_arg, 'col_offset', node.col_offset))
        if _at01_should_exempt(tree, path_arg, node.lineno, pos=pos):
            continue
        issues.append(DiagnoseFinding(
            id="AT-01", severity="P2", dimension="artifact_safety",
            file=filepath, line=node.lineno, col_offset=node.col_offset,
            title="open() 覆盖写非产物路径",
            description="覆盖写模式 open() 且路径无产物证据, 可能误写源码/文档.",
            code_snippet=extract_code_lines(source, node.lineno),
            suggestion="根因: 覆盖写目标路径未限定在产物/临时目录, 误写源码/文档后不可恢复。\n修复策略: 输出统一写入项目约定的产物目录或临时目录, 源码/文档只读或原子替换.\n参考标准: CWE-377 / 临时文件安全创建",
            rule_ref="artifact-open-overwrite"))
    return apply_rule_suppress(issues, source, 'AT-01')
def _at02_slot_str(args: list, idx: int) -> str | None:
    if len(args) > idx and _is_str_constant(args[idx]):
        return args[idx].value
    return None
def _at02_kw_slot_value(node: ast.Call, slot: str) -> str | None:
    for kw in node.keywords:
        if kw.arg == slot and _is_str_constant(kw.value):
            return kw.value.value
    return None
def _at02_rename_pair(node: ast.Call) -> tuple[str, str] | None:
    src_val = _at02_slot_str(node.args, 0)
    if src_val is None:
        src_val = _at02_kw_slot_value(node, 'src')
    dst_val = _at02_slot_str(node.args, 1)
    if dst_val is None:
        dst_val = _at02_kw_slot_value(node, 'dst')
    if src_val is None or dst_val is None:
        return None
    return (src_val, dst_val)
def _at02_same_directory(pair: tuple[str, str]) -> bool:
    src_dir, dst_dir = (
        os.path.normcase(os.path.dirname(os.path.normpath(p)))
        for p in pair)
    return src_dir == dst_dir
def _at02_os_rename_call(node: ast.AST,
                         bindings: _ModuleApiScopeBindings) -> ast.Call | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.attr == 'rename'
            and bindings.resolve_api(
                node, func.value.id, 'rename')[1] == 'rename'):
        return node
    if (isinstance(func, ast.Name)
            and bindings.resolve_api(node, func.id, None)[1] == 'rename'):
        return node
    return None
def check_AT02(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    bindings = _ModuleApiScopeBindings(
        tree, frozenset({'os'}), frozenset({'rename'}))
    for node in walk_nodes(tree):
        if _at02_os_rename_call(node, bindings) is None:
            continue
        pair = _at02_rename_pair(node)
        if pair is not None and _at02_same_directory(pair):
            continue
        issues.append(DiagnoseFinding(
            id="AT-02", severity="P2", dimension="atomic_safety",
            file=filepath, line=node.lineno, col_offset=node.col_offset,
            title="os.rename() 跨文件系统非原子,应使用 shutil.move 或 os.replace",
            description=(
                "os.rename() 在跨文件系统时失败(OSError [Errno 18])."
                "对于原子替换需求,应使用 os.replace()(同盘原子)."
            ),
            code_snippet=extract_code_lines(source, node.lineno),
            suggestion='根因: os.rename() 跨文件系统会失败（OSError [Errno 18]）, 且覆盖语义随平台变化, 不构成原子替换保证。\n修复策略: 同盘原子替换使用 os.replace();跨盘使用 shutil.move().\n参考标准: PEP 8 / CWE-377',
            rule_ref="atomic-os-rename",
        ))
    return apply_rule_suppress(issues, source, 'AT-02')
def _gf02_dangling_string(body: list) -> ast.Expr | None:
    if len(body) < 2:
        return None
    if not is_docstring_stmt(body[0]):
        return None
    if not is_docstring_stmt(body[1]):
        return None
    return body[1]
def check_GF02(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        second = _gf02_dangling_string(node.body)
        if second is None:
            continue
        issues.append(DiagnoseFinding(
            id="GF-02", severity="P1", dimension="docstring",
            file=filepath, line=second.lineno, col_offset=second.col_offset,
            title="docstring断裂: 文档字符串后存在悬挂字符串常量",
            description="docstring 之后紧跟第二个字符串常量表达式, "
                        "疑似 docstring 闭合引号被截断的坏编辑残留, 文档边界失真.",
            code_snippet=extract_code_lines(source, second.lineno),
            suggestion=("根因: docstring 边界损坏。该问题属于文档质量类别。\n"
                        "修复策略: 合并悬挂字符串到 docstring 或删除\n参考标准: PEP 257"),
            rule_ref="docstring-dangling-string",
        ))
    return apply_rule_suppress(issues, source, 'GF-02')
def _cf01_environ_subscript(node: ast.AST,
                            bindings: _ModuleApiScopeBindings,
                            ) -> ast.Subscript | None:
    if not isinstance(node, ast.Subscript):
        return None
    target = node.value
    if (isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.attr == 'environ'
            and bindings.resolve_api(
                node, target.value.id, 'environ')[1] == 'environ'):
        return node
    if (isinstance(target, ast.Name)
            and bindings.resolve_api(node, target.id, None)[1] == 'environ'):
        return node
    return None
def check_CF01(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    bindings = _ModuleApiScopeBindings(
        tree, frozenset({'os'}), frozenset({'environ'}))
    for node in walk_nodes(tree):
        augassign = node if isinstance(node, ast.AugAssign) else None
        subscript = _cf01_environ_subscript(
            augassign.target if augassign is not None else node, bindings)
        if subscript is None:
            continue
        if augassign is None and isinstance(subscript.ctx, ast.Store):
            continue
        reported = augassign if augassign is not None else subscript
        issues.append(DiagnoseFinding(
            id="CF-01", severity="P1", dimension="config_safety",
            file=filepath, line=reported.lineno,
            col_offset=reported.col_offset,
            title="os.environ 使用索引访问,缺少环境变量时抛出 KeyError",
            description=(
                "os.environ['KEY'] 在环境变量不存在时抛出 KeyError."
                "应使用 os.environ.get('KEY') 并提供默认值."
            ),
            code_snippet=extract_code_lines(source, node.lineno),
            suggestion="根因: os.environ 是映射视图, 索引缺失键直接抛 KeyError——部署环境变量差异会让配置读取路径中断。\n修复策略: 改用 os.environ.get('KEY', default_value).\n参考标准: PEP 8 / 12-factor app / os.environ",
            rule_ref="config-environ-keyerror",
        ))
    return apply_rule_suppress(issues, source, 'CF-01')
_CF02_SENSITIVE_KEYWORDS = [
    'password', 'passwd', 'secret', 'api_key', 'apikey', 'token',
    'access_key', 'private_key', 'credential',
]
def _cf02_keyword_hit(name: str, keyword: str) -> bool:
    name_segments = _text_segments(name)
    keyword_segments = _text_segments(keyword)
    if not keyword_segments:
        return False
    width = len(keyword_segments)
    for start in range(len(name_segments) - width + 1):
        if all(segments_equal(name_segments[start + offset],
                                    keyword_segments[offset])
               for offset in range(width)):
            return True
    return False
_CF02_LEXICAL_TOKEN_SEGMENTS = frozenset({
    'rule', 'rules', 'identifier', 'identifiers', 'pattern', 'patterns',
    'regex', 'keyword', 'keywords', 'symbol', 'symbols', 'lexer', 'parser',
    'grammar', 'action', 'actions', 'label', 'labels', 'type', 'types',
    'name', 'names', 'word', 'words',
})
def _cf02_is_sensitive_name(name: str) -> bool:
    if any(_cf02_keyword_hit(name, kw)
           for kw in _CF02_SENSITIVE_KEYWORDS if kw != 'token'):
        return True
    if _cf02_keyword_hit(name, 'token'):
        return not any(segment in _CF02_LEXICAL_TOKEN_SEGMENTS
                       for segment in _text_segments(name))
    return _cf02_keyword_hit(name, 'auth')
def _cf02_is_secret_value(val: str) -> bool:
    if re.fullmatch(r'[a-z_]+', val) and any(
            kw in val for kw in _CF02_SENSITIVE_KEYWORDS):
        return False
    return len(val) > 8
def _cf02_target_name(target: ast.expr) -> str | None:
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        return target.attr
    if isinstance(target, ast.Subscript) and _is_str_constant(target.slice):
        return target.slice.value
    return None
def _cf02_assignment_parts(node: ast.AST) -> tuple[list, ast.AST] | None:
    if isinstance(node, ast.Assign):
        return node.targets, node.value
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return [node.target], node.value
    if isinstance(node, ast.NamedExpr):
        return [node.target], node.value
    return None
def _cf02_literal_target_values(target: ast.AST, value: ast.AST):
    if isinstance(target, (ast.Name, ast.Attribute, ast.Subscript)):
        if _is_str_constant(value):
            yield target, value
        return
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return
    starred = [index for index, element in enumerate(target.elts)
               if isinstance(element, ast.Starred)]
    if len(starred) > 1:
        return
    if not starred:
        if len(target.elts) != len(value.elts):
            return
        pairs = zip(target.elts, value.elts, strict=True)
    else:
        star_index = starred[0]
        fixed_count = len(target.elts) - 1
        if len(value.elts) < fixed_count:
            return
        pairs = [*zip(target.elts[:star_index],
                      value.elts[:star_index], strict=False)]
        suffix = target.elts[star_index + 1:]
        pairs.extend(zip(
            suffix, value.elts[len(value.elts) - len(suffix):],
            strict=False))
    for target_elt, value_elt in pairs:
        yield from _cf02_literal_target_values(target_elt, value_elt)
def _cf02_sensitive_targets(node: ast.AST):
    extracted = _cf02_assignment_parts(node)
    if extracted is None:
        return
    targets, value = extracted
    reported: set[str] = set()
    for target in targets:
        for bound_target, literal in _cf02_literal_target_values(target, value):
            if not _cf02_is_secret_value(literal.value):
                continue
            tname = _cf02_target_name(bound_target)
            if (tname is not None and tname not in reported
                    and _cf02_is_sensitive_name(tname)):
                reported.add(tname)
                yield tname
def check_CF02(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node in walk_nodes(tree):
        for tname in _cf02_sensitive_targets(node):
            issues.append(DiagnoseFinding(
                id="CF-02", severity="P0", dimension="config_safety",
                file=filepath, line=node.lineno, col_offset=node.col_offset,
                title=f"疑似硬编码敏感信息: '{tname}'",
                description="代码中直接赋值了疑似密钥/密码/Token的字符串.",
                code_snippet="***隐藏***",
                suggestion=(
                    '根因: 密钥/密码/Token 以字面量固化在源码中, 随仓库扩散且无法按环境轮换。\n'
                    '修复策略: 使用环境变量或密钥管理服务:\n'
                    f"{tname} = os.environ.get('SECRET_KEY')\n"
                    '参考标准: PEP 8 / 12-factor app'
                ),
                rule_ref="config-hardcoded-secret",
            ))
    return apply_rule_suppress(issues, source, 'CF-02')
_FORMAT_DIMENSION = "format_safety"
def _append_format_issue(issues: list, head: dict[str, Any], source: Any,
                         filepath: Any, line: int) -> None:
    issues.append({
        **head,
        "dimension": _FORMAT_DIMENSION,
        "file": filepath,
        "line": line,
        "code_snippet": extract_code_lines(source, line),
    })
def _fm01_parse_width_or_precision(fmt_str: str, j: int, n: int) -> tuple[int, int]:
    if j < n and fmt_str[j] == '*':
        return j + 1, 1
    while j < n and fmt_str[j].isdigit():
        j += 1
    return j, 0
def _fm01_probe_conv_tail(fmt_str: str, j: int, n: int) -> int | None:
    if j < n and fmt_str[j] in 'hlL':
        j += 1
    if j < n and fmt_str[j] in 'diouxXeEfFgGcrsa':
        return j + 1
    return None
def _fm01_parse_map_key_prefix(fmt_str: str, j: int,
                              n: int) -> tuple[int, str | None] | None:
    if not (j < n and fmt_str[j] == '('):
        return j, None
    close = fmt_str.find(')', j)
    if close < 0:
        return None
    return close + 1, fmt_str[j + 1:close]
def _fm01_parse_conv_spec(fmt_str: str, i: int) -> tuple[int, int, str | None] | None:
    n = len(fmt_str)
    key_parsed = _fm01_parse_map_key_prefix(fmt_str, i + 1, n)
    if key_parsed is None:
        return None
    j, map_key = key_parsed
    while j < n and fmt_str[j] in '-+ #0':
        j += 1
    j, width_extra = _fm01_parse_width_or_precision(fmt_str, j, n)
    arg_usage = 1 + width_extra
    if j < n and fmt_str[j] == '.':
        j, prec_extra = _fm01_parse_width_or_precision(fmt_str, j + 1, n)
        arg_usage += prec_extra
    end = _fm01_probe_conv_tail(fmt_str, j, n)
    if end is None:
        return None
    return end, arg_usage, map_key
def _fm01_scan_step(fmt_str: str, i: int, pos_count: int,
                    map_star: bool
                    ) -> tuple[int, int, bool, str | None] | None:
    if fmt_str[i] != '%':
        return i + 1, pos_count, map_star, None
    if i + 1 < len(fmt_str) and fmt_str[i + 1] == '%':
        return i + 2, pos_count, map_star, None
    parsed = _fm01_parse_conv_spec(fmt_str, i)
    if parsed is None:
        return None
    i_next, arg_usage, map_key = parsed
    if map_key is None:
        return i_next, pos_count + arg_usage, map_star, None
    return i_next, pos_count, map_star or arg_usage > 1, map_key
def _fm01_scan_placeholders(fmt_str: str) -> tuple[int, list[str], bool, bool]:
    pos_count = 0
    map_keys: list[str] = []
    map_star = False
    i = 0
    n = len(fmt_str)
    while i < n:
        step = _fm01_scan_step(fmt_str, i, pos_count, map_star)
        if step is None:
            return pos_count, map_keys, map_star, True
        i, pos_count, map_star, _key = step
        if _key is not None:
            map_keys.append(_key)
    return pos_count, map_keys, map_star, False
def _fm01_first_conv_is_map(fmt_str: str) -> bool:
    i, n = 0, len(fmt_str)
    while i < n:
        if fmt_str[i] != '%':
            i += 1
            continue
        if i + 1 < n and fmt_str[i + 1] == '%':
            i += 2
            continue
        parsed = _fm01_parse_conv_spec(fmt_str, i)
        if parsed is None:
            return False
        return parsed[2] is not None
    return False
def _fm01_report(issues: list, source: Any, filepath: Any, node: ast.BinOp,
                 spec: tuple[str, str, str, str]) -> None:
    title, description, suggestion, rule_ref = spec
    _append_format_issue(issues, {
        "rule_id": "FM-01", "severity": "P0",
        "title": title,
        "description": description,
        "suggestion": suggestion,
        "rule_ref": rule_ref,
    }, source, filepath, node.lineno)
def _fm01_mapping_star_spec(map_count: int) -> tuple[str, str, str, str]:
    return (
        f"%格式化有{map_count}个映射键占位符携带*宽度/精度",
        ("映射键占位符 %(w)*d 携带 * 宽度/精度: * 仅从"
         "位置参数取值, 映射模式无位置参数供给, 运行时"
         "将抛 TypeError(not enough arguments)."),
        ('根因: 映射键占位符的 * 宽度/精度仅从'
         '位置参数取值, 与映射模式互斥.\n'
         '修复策略: 映射键占位符改用字面宽度'
         '(%(w)10d), 或改用位置占位符 %*d 配'
         '元组.\n参考标准: PEP 8 / printf-style '
         'string formatting / pylint W1309'),
        "format-percent-mapping-star",
    )
def _fm01_mapping_mix_spec(map_count: int,
                            pos_count: int) -> tuple[str, str, str, str]:
    if pos_count > 0:
        title = (f"%格式化混用映射键占位符({map_count}个)与"
                 f"位置占位符({pos_count}个)")
        description = (f"格式字符串同时含 {map_count} 个映射键占位符"
                       f"与 {pos_count} 个位置占位符."
                       "映射键与位置占位符互斥,"
                       "运行时将抛 TypeError.")
    else:
        title = (f"%格式化有{map_count}个映射键占位符"
                 "但右操作数是元组")
        description = ("映射键占位符 %(name)s 需要字典右操作数,"
                       "元组形态运行时将抛 "
                       "TypeError(format requires a mapping).")
    return (
        title, description,
        ('根因: 映射键与位置占位符在 % 格式化文法中互斥.\n'
         '修复策略: 统一占位符形态——全部用 %s 配元组,或全部用 '
         '%(name)s 配字典.\n参考标准: PEP 8 / printf-style '
         'string formatting / pylint W1309'),
        "format-percent-mapping-mix",
    )
def _fm01_nonmapping_literal_spec(
        map_count: int) -> tuple[str, str, str, str]:
    return (
        f"%格式化有{map_count}个映射键占位符但右操作数非映射",
        ("映射键占位符 %(name)s 需要 dict 映射右操作数,"
         "list/set/常量字面量形态运行时将抛 "
         "TypeError(format requires a mapping 或 "
         "indices must be integers)."),
        ('根因: 映射键占位符要求 dict 映射右操作数.\n'
         '修复策略: 改用 %(name)s % {"name": value} 字典形态,'
         '或全部改用位置占位符 %s 配元组.\n'
         '参考标准: PEP 8 / printf-style string formatting'),
        "format-percent-mapping-requires-mapping",
    )
def _fm01_mapping_key_spec(node: ast.BinOp, pos_count: int,
                           map_keys: list[str], map_star: bool,
                           tree: ast.AST
                           ) -> tuple[str, str, str, str] | None:
    map_count = len(map_keys)
    if map_star:
        return _fm01_mapping_star_spec(map_count)
    if pos_count >= 2:
        return _fm01_mapping_mix_spec(map_count, pos_count)
    if isinstance(node.right, ast.Tuple):
        return _fm01_mapping_mix_spec(map_count, pos_count)
    if isinstance(node.right, ast.Name):
        values = _fm01_traced_assignment_values(node.right, tree)
        if values and all(isinstance(value, ast.Dict) for value in values):
            missing: list[str] = []
            for value in values:
                part = _fm01_dict_missing_keys(value, map_keys)
                if part is None:
                    if pos_count and _fm01_first_conv_is_map(node.left.value):
                        return _fm01_mapping_mix_spec(map_count, pos_count)
                    return None
                missing.extend(part)
            missing = list(dict.fromkeys(missing))
            if missing:
                return _fm01_missing_key_spec(missing)
            if pos_count and _fm01_first_conv_is_map(node.left.value):
                return _fm01_mapping_mix_spec(map_count, pos_count)
            return None
    if isinstance(node.right, ast.Dict):
        return None
    shape = _fm01_operand_shape(node.right, tree)
    if shape.startswith("tuple:"):
        return _fm01_mapping_mix_spec(map_count, pos_count)
    if shape == "non_tuple":
        return (_fm01_mapping_mix_spec(map_count, pos_count) if pos_count
                else _fm01_nonmapping_literal_spec(map_count))
    return None
def _fm01_dict_operand_spec(node: ast.BinOp, pos_count: int,
                            map_keys: list[str]
                            ) -> tuple[str, str, str, str] | None:
    if pos_count >= 2:
        return (
            f"%格式化有{pos_count}个位置占位符但右操作数是dict字面量",
            (f"格式字符串有 {pos_count} 个位置占位符,"
             "但dict字面量被当作单个值(str化), "
             "运行时将抛 TypeError(not enough arguments)."),
            ('根因: 多个位置占位符需要元组参数.\n'
             '修复策略: 改用 % (arg1, arg2) 元组形态,'
             '或全部用 %(name)s 映射键配字典.\n'
             '参考标准: PEP 8 / printf-style string '
             'formatting / pylint W1309'),
            "format-percent-dict-single-value",
        )
    if (pos_count == 1 and map_keys
            and _fm01_first_conv_is_map(node.left.value)):
        return _fm01_mapping_mix_spec(len(map_keys), pos_count)
    if pos_count == 0 and not map_keys:
        return None
    missing = _fm01_dict_missing_keys(node.right, map_keys)
    if missing is None:
        return None
    return _fm01_missing_key_spec(missing) if missing else None
def _fm01_missing_key_spec(
        missing: list[str]) -> tuple[str, str, str, str]:
    keys = ','.join(missing)
    return (
        f"%格式化映射键缺失:{keys}",
        (f"字典缺少映射键占位符所需键: {keys}."
         "运行时将抛 KeyError."),
        ('根因: 映射键占位符所需键未在字典中提供.\n'
         '修复策略: 补齐缺失键,或改用位置占位符 %s 配元组.\n'
         '参考标准: PEP 8 / printf-style string '
         'formatting / pylint W1309'),
        "format-percent-missing-key",
    )
def _fm01_dict_missing_keys(dict_node: ast.Dict,
                            map_keys: list[str]) -> list[str] | None:
    dict_keys: set[str] = set()
    for key_node in dict_node.keys:
        if key_node is None or not isinstance(key_node, ast.Constant):
            return None
        if isinstance(key_node.value, str):
            dict_keys.add(key_node.value)
    return [k for k in dict.fromkeys(map_keys) if k not in dict_keys]
def _fm01_tuple_count_spec(
        pos_count: int, arg_count: int) -> tuple[str, str, str, str] | None:
    if pos_count == arg_count:
        return None
    return (
        f"%格式化占位符数({pos_count})与参数数({arg_count})不匹配",
        (f"格式字符串有 {pos_count} 个占位符,"
         f"但提供了 {arg_count} 个参数.将导致 TypeError."),
        ('根因: 代码使用了不规范或有风险的实现方式。该问题属于格式化字符串类别。\n'
         '修复策略: 确保占位符数量与参数数量一致,或改用 f-string.\n'
         '参考标准: PEP 8 / pylint W1309'),
        "format-percent-arg-count",
    )
def _fm01_tuple_operand_spec(node: ast.BinOp, pos_count: int,
                             truncated: bool
                             ) -> tuple[str, str, str, str] | None:
    if any(isinstance(e, ast.Starred) for e in node.right.elts):
        return None
    arg_count = len(node.right.elts)
    if truncated and arg_count > pos_count:
        return None
    return _fm01_tuple_count_spec(pos_count, arg_count)
def _fm01_is_const_str_mod(node: ast.AST) -> bool:
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod)
            and isinstance(node.left, ast.Constant)
            and isinstance(node.left.value, str))
_FM01_COMPREHENSION_NODES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
def _fm01_value_shape(value: ast.AST | None) -> str:
    if isinstance(value, ast.Tuple):
        if any(isinstance(elt, ast.Starred) for elt in value.elts):
            return "unknown"
        return f"tuple:{len(value.elts)}"
    if value is not None and _fm01_is_definite_single_value(value):
        return "non_tuple"
    return "unknown"
def _comprehension_shadows(scope: ast.AST, node: ast.AST,
                           name: str) -> bool:
    visible_generators = scope.generators
    for index, generator in enumerate(scope.generators):
        if any(candidate is node for candidate in walk_nodes(generator.iter)):
            visible_generators = scope.generators[:index]
            break
        if any(candidate is node
               for condition in generator.ifs
               for candidate in walk_nodes(condition)):
            visible_generators = scope.generators[:index + 1]
            break
    return any(
        name in iter_unpack_target_names(generator.target)
        for generator in visible_generators)
def _fm01_in_lambda_defaults(scope: ast.AST, node: ast.AST) -> bool:
    for default in (*scope.args.defaults,
                    *(value for value in scope.args.kw_defaults
                      if value is not None)):
        if any(candidate is node for candidate in walk_nodes(default)):
            return True
    return False
def _fm01_shadowed_by_nearer_scope(
        tree: ast.AST, node: ast.Name, name: str) -> bool:
    parents = build_parent_map(tree)
    scope = parents.get(id(node))
    while scope is not None:
        if isinstance(scope, ast.Lambda):
            if (not _fm01_in_lambda_defaults(scope, node)
                    and name in collect_param_names(scope)):
                return True
        elif (isinstance(scope, _FM01_COMPREHENSION_NODES)
              and _comprehension_shadows(scope, node, name)):
            return True
        scope = parents.get(id(scope))
    return False
def _fm01_non_assign_binding_names(node: ast.AST) -> set[str]:
    if isinstance(node, ast.AugAssign):
        return set(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return set(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        names: set[str] = set()
        for item in node.items:
            if item.optional_vars is not None:
                names |= set(iter_unpack_target_names(item.optional_vars))
        return names
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return {alias.asname or alias.name.split('.')[0]
                for alias in node.names if alias.name != '*'}
    if isinstance(node, ast.Delete):
        return set(iter_unpack_target_names(node.targets))
    return set(_module_api_pattern_bindings(node))
def _fm01_rebound_before(
        scope: ast.AST, var_name: str, pos: tuple[int, int]) -> bool:
    has_star_import = _at01_star_import_before(scope, pos)
    latest_rebind = None
    latest_assignment = None
    for node in _at01_iter_scope_nodes(scope):
        if not hasattr(node, 'lineno'):
            continue
        key = (node.lineno, node.col_offset)
        if key >= pos:
            continue
        if (((has_star_import and is_star_import(node))
             or var_name in _fm01_non_assign_binding_names(node))
                and (latest_rebind is None or key > latest_rebind)):
            latest_rebind = key
        if (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                              ast.NamedExpr))
                and getattr(node, 'value', None) is not None
                and _at01_assignment_values(node, var_name, False)
                and (latest_assignment is None or key > latest_assignment)):
            latest_assignment = key
    if latest_rebind is None:
        return False
    return latest_assignment is None or latest_rebind >= latest_assignment
def _fm01_traced_assignment_values(
        node: ast.Name, tree: ast.AST) -> tuple:
    if _fm01_shadowed_by_nearer_scope(tree, node, node.id):
        return ()
    pos = (node.lineno, node.col_offset)
    scopes = list(_at01_enclosing_funcs(tree, node))
    if isinstance(tree, ast.Module):
        scopes.append(tree)
    for scope in scopes:
        if _fm01_rebound_before(scope, node.id, pos):
            return ()
    return tuple(_at01_trace_assignments(
        _at01_enclosing_funcs(tree, node),
        pos, node.id, tree=tree))
def _fm01_operand_shape(node: ast.AST, tree: ast.AST) -> str:
    if isinstance(node, ast.Name):
        values = _fm01_traced_assignment_values(node, tree)
        shapes = {_fm01_value_shape(value) for value in values}
        if len(shapes) == 1:
            return shapes.pop()
        return "unknown"
    return "non_tuple" if _fm01_is_definite_single_value(node) else "unknown"
def _fm01_break_spec(node: ast.AST, tree: ast.AST
                     ) -> tuple[str, str, str, str] | None:
    if not _fm01_is_const_str_mod(node):
        return None
    pos_count, map_keys, map_star, truncated = _fm01_scan_placeholders(
        node.left.value)
    if map_keys:
        spec = _fm01_mapping_key_spec(
            node, pos_count, map_keys, map_star, tree)
        if spec is not None:
            return spec
    if isinstance(node.right, ast.Dict):
        return _fm01_dict_operand_spec(node, pos_count, map_keys)
    if isinstance(node.right, ast.Tuple):
        return _fm01_tuple_operand_spec(node, pos_count, truncated)
    return _fm01_fallback_operand_spec(
        node, pos_count, map_keys, truncated, tree)
_FM01_DEFINITE_SINGLE_VALUE_NODES = (
    ast.Constant, ast.List, ast.Dict, ast.Set, ast.JoinedStr, ast.Lambda,
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
    ast.Compare, ast.UnaryOp,
)
def _fm01_is_definite_single_value(node: ast.AST) -> bool:
    return isinstance(node, _FM01_DEFINITE_SINGLE_VALUE_NODES)
def _fm01_is_bytes_literal(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (bytes, bytearray)))
def _fm01_no_placeholder_operand_exempt(node: ast.AST,
                                        tree: ast.AST) -> bool:
    values = (_fm01_traced_assignment_values(node, tree)
              if isinstance(node, ast.Name) else (node,))
    return bool(values) and all(
        isinstance(value, (ast.List, ast.ListComp, ast.Dict, ast.DictComp))
        or _fm01_is_bytes_literal(value)
        for value in values)
def _fm01_fallback_operand_spec(
        node: ast.BinOp, pos_count: int, map_keys: list[str],
        truncated: bool, tree: ast.AST) -> tuple[str, str, str, str] | None:
    shape = _fm01_operand_shape(node.right, tree)
    if shape.startswith("tuple:"):
        arg_count = int(shape.split(":", 1)[1])
        if truncated and arg_count > pos_count:
            return None
        return _fm01_tuple_count_spec(pos_count, arg_count)
    if pos_count > 1 and shape == "non_tuple":
        return (
            f"%格式化有{pos_count}个占位符但只提供单个参数",
            "多个占位符需要元组参数: % (a, b).",
            ('根因: 代码实现中存在格式化字符串方面的问题, 需要规范化处理。\n'
             '修复策略: 将参数包装为元组: % (arg1, arg2).\n'
             '参考标准: PEP 8 / pylint W1309'),
            "format-percent-mismatch",
        )
    if (pos_count == 0 and not map_keys and not truncated
            and shape == "non_tuple"
            and not _fm01_no_placeholder_operand_exempt(node.right, tree)):
        return (
            "%格式化无占位符但携带%操作数",
            ("格式字符串无占位符, 右操作数被当作单个值而"
             "无消耗, 运行时将抛 TypeError"
             "(not all arguments converted)."),
            ('根因: 无占位符的格式串不应携带 '
             '% 操作数.\n'
             '修复策略: 删除多余的 % 操作数, 或补齐'
             '格式占位符.\n参考标准: PEP 8 / '
             'printf-style string formatting / '
             'pylint W1309'),
            "format-percent-no-placeholder",
        )
    return None
def check_FM01(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH,
               index: list | None = None) -> Any:
    _log.debug("规则入口 check_FM01 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node in iter_nodes(tree, index):
        spec = _fm01_break_spec(node, tree)
        if spec is None:
            continue
        _fm01_report(issues, source, filepath, node, spec)
    return apply_rule_suppress(issues, source, 'FM-01')
def _fm02_comp_generator_nodes(n: Any) -> tuple:
    return tuple(x for g in n.generators for x in (g.iter, *g.ifs))
_FM02_CHILD_NODES = {
    ast.Attribute: lambda n: (n.value,),
    ast.Subscript: lambda n: (n.value,)
    + ((n.slice,) if n.slice is not None else ()),
    ast.BinOp: lambda n: (n.left, n.right),
    ast.UnaryOp: lambda n: (n.operand,),
    ast.BoolOp: lambda n: tuple(n.values),
    ast.IfExp: lambda n: (n.test, n.body, n.orelse),
    ast.Compare: lambda n: (n.left, *n.comparators),
    ast.Starred: lambda n: (n.value,),
    ast.Await: lambda n: (n.value,),
    ast.Yield: lambda n: (n.value,) if n.value is not None else (),
    ast.YieldFrom: lambda n: (n.value,),
    ast.NamedExpr: lambda n: (n.value,),
    ast.Call: lambda n: (n.func, *n.args,
                         *(k.value for k in n.keywords)),
    ast.List: lambda n: tuple(n.elts),
    ast.Tuple: lambda n: tuple(n.elts),
    ast.Set: lambda n: tuple(n.elts),
    ast.Dict: lambda n: tuple(k for k in n.keys if k is not None)
    + tuple(n.values),
    ast.ListComp: lambda n: (n.elt, *_fm02_comp_generator_nodes(n)),
    ast.SetComp: lambda n: (n.elt, *_fm02_comp_generator_nodes(n)),
    ast.GeneratorExp: lambda n: (n.elt, *_fm02_comp_generator_nodes(n)),
    ast.DictComp: lambda n: (n.key, n.value,
                             *_fm02_comp_generator_nodes(n)),
    ast.Slice: lambda n: tuple(p for p in (n.lower, n.upper, n.step)
                               if p is not None),
    ast.Lambda: lambda n: (
        n.body, *n.args.defaults,
        *(default for default in n.args.kw_defaults if default is not None),
    ),
}
def _fm02_iter_name_nodes(n: Any):
    if isinstance(n, ast.Name):
        yield n
        return
    extractor = _FM02_CHILD_NODES.get(type(n))
    if extractor is None:
        return
    for child in extractor(n):
        yield from _fm02_iter_name_nodes(child)
_TYPE_PARAM_NODES = (
    (ast.TypeVar, ast.ParamSpec, ast.TypeVarTuple)
    if sys.version_info >= (3, 12) else ())
_FM02_TYPE_ALIAS_NODES = (
    (ast.TypeAlias,) if sys.version_info >= (3, 12) else ())
def _fm02_ann_only_target_ids(tree: ast.AST) -> set[int]:
    return {
        id(n.target) for n in walk_nodes(tree)
        if isinstance(n, ast.AnnAssign) and n.value is None
        and isinstance(n.target, ast.Name)
    }
_FM02_MODULE_INJECTED_NAMES = frozenset({
    '__name__', '__doc__', '__package__', '__loader__', '__spec__',
    '__file__', '__cached__', '__builtins__',
})
_FM02_CLASS_BODY_NAMES = frozenset({'__module__', '__qualname__'})
_FM02_CLASS_CELL_NAME = '__class__'
_FM02_BUILTIN_NAMES = frozenset(dir(builtins))
_FM02_VISIBLE_BASE = _FM02_BUILTIN_NAMES | _FM02_MODULE_INJECTED_NAMES
_FM02_FUNCTION_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_FM02_COMPREHENSION_NODES = (
    ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
_FM02_SCOPE_BOUNDARY_NODES = (
    *_FM02_FUNCTION_NODES, ast.ClassDef, *_FM02_COMPREHENSION_NODES)
_FM02_EMPTY_SCOPE_IDS = frozenset()
def _fm02_iter_module_frame_nodes(tree: ast.AST):
    stack = [tree]
    while stack:
        node = stack.pop()
        yield node
        stack.extend(
            child for child in ast.iter_child_nodes(node)
            if not isinstance(child, _FM02_SCOPE_BOUNDARY_NODES))
def _fm02_annotations_defined(scope_node: ast.AST) -> bool:
    if not isinstance(scope_node, (ast.Module, ast.ClassDef)):
        return False
    return any(isinstance(node, ast.AnnAssign)
               for node in _fm02_iter_module_frame_nodes(scope_node))
def _fm02_local_annotation_roots(tree: ast.AST) -> tuple:
    parents = build_parent_map(tree)
    roots = []
    boundaries = (ast.Module, ast.ClassDef, *_FM02_FUNCTION_NODES)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.AnnAssign) or node.annotation is None:
            continue
        parent = parents.get(id(node))
        while parent is not None and not isinstance(parent, boundaries):
            parent = parents.get(id(parent))
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
            roots.append(node.annotation)
    return tuple(roots)
def _fm02_deferred_annotation_roots(tree: ast.AST) -> tuple:
    roots = list(_fm02_local_annotation_roots(tree))
    deferred = any(
        isinstance(node, ast.ImportFrom) and node.module == '__future__'
        and any(alias.name == 'annotations' for alias in node.names)
        for node in walk_nodes(tree))
    if not deferred:
        return tuple(roots)
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.AnnAssign, ast.arg))
                and node.annotation is not None):
            roots.append(node.annotation)
        elif (isinstance(node, _FM02_FUNCTION_NODES)
              and getattr(node, 'returns', None) is not None):
            roots.append(node.returns)
    return tuple(roots)
def _fm02_end_position(node: ast.AST) -> tuple[int, int]:
    lineno = getattr(node, 'end_lineno', None) or getattr(node, 'lineno', 0)
    col_offset = getattr(node, 'end_col_offset', None)
    if col_offset is None:
        col_offset = getattr(node, 'col_offset', 0)
    return lineno, col_offset
def _fm02_binding_positions(tree: ast.AST) -> dict[int, tuple[int, int]]:
    positions: dict[int, tuple[int, int]] = {}
    def record_target(target: ast.AST, value: ast.AST) -> None:
        position = _fm02_end_position(value)
        for sub in walk_nodes(target):
            if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Store):
                positions[id(sub)] = position
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            positions[id(node)] = _fm02_end_position(node)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                record_target(target, node.value)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
            if node.value is not None:
                record_target(node.target, node.value)
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            record_target(node.target, node.iter)
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is not None:
                    record_target(item.optional_vars, item.context_expr)
        elif isinstance(node, ast.ExceptHandler):
            if node.name and node.type is not None:
                positions[id(node)] = _fm02_end_position(node.type)
        elif isinstance(node, ast.comprehension):
            record_target(node.target, node.iter)
        elif _FM02_TYPE_ALIAS_NODES and isinstance(
                node, _FM02_TYPE_ALIAS_NODES):
            record_target(node.name, node.value)
    return positions
class _ScopeFrameGraph:
    def __init__(self, tree: ast.AST, deferred_roots: tuple,
                 binding_positions: dict[int, tuple[int, int]] | None = None):
        self.tree = tree
        self.deferred_root_ids = {id(node) for node in deferred_roots}
        self.binding_positions = (
            _fm02_binding_positions(tree) if binding_positions is None
            else binding_positions)
        self.scope_of: dict[int, int] = {}
        self.bindings: dict[int, set] = {}
        self.binding_sites: dict[int, dict[str, list[tuple[int, int]]]] = {}
        self.unbinding_sites: dict[int, dict[str, list[tuple[int, int]]]] = {}
        self.nonlocal_declarations: dict[int, set[str]] = {}
        self.global_declarations: dict[int, set[str]] = {}
        self.parents: dict[int, int | None] = {}
        self.syntax_parents: dict[int, int | None] = {}
        self.boundary_ids: dict[int, ast.AST] = {}
        self.class_cell: dict[int, bool] = {}
        self.class_type_params: dict[int, set] = {}
        self.inherited_params: dict[int, set] = {}
        self.ann_only = _fm02_ann_only_target_ids(tree)
    def build(self) -> tuple:
        self._visit(self.tree, id(self.tree))
        return (self.scope_of, self.bindings, self.parents,
                self.boundary_ids, self.class_cell, self.inherited_params,
                self.binding_sites, self.unbinding_sites,
                self.nonlocal_declarations, self.global_declarations)
    def _bind(self, scope_id: int, names, node: ast.AST | None = None) -> None:
        names = tuple(name for name in names if name)
        if not names:
            return
        self.bindings.setdefault(scope_id, set()).update(names)
        if node is None or not hasattr(node, 'lineno'):
            return
        position = self.binding_positions.get(
            id(node), (node.lineno, getattr(node, 'col_offset', 0)))
        sites = self.binding_sites.setdefault(scope_id, {})
        for name in names:
            sites.setdefault(name, []).append(position)
    def _unbind(self, scope_id: int, name: str, node: ast.AST,
                position: tuple[int, int] | None = None) -> None:
        self.bindings.setdefault(scope_id, set()).add(name)
        if position is None:
            position = (node.lineno, getattr(node, 'col_offset', 0))
        sites = self.unbinding_sites.setdefault(scope_id, {})
        sites.setdefault(name, []).append(position)
    def _lexical_parent(self, scope_id: int) -> int | None:
        while isinstance(self.boundary_ids.get(scope_id), ast.ClassDef):
            scope_id = self.parents.get(scope_id)
            if scope_id is None:
                return None
        return scope_id
    def _enter_scope(self, node: ast.AST, scope_id: int) -> int:
        new_id = id(node)
        self.scope_of[id(node)] = new_id
        self.boundary_ids[new_id] = node
        self.syntax_parents[new_id] = scope_id
        self.parents[new_id] = self._lexical_parent(scope_id)
        inherited: set = set()
        probe: int | None = scope_id
        while isinstance(self.boundary_ids.get(probe), ast.ClassDef):
            inherited |= self.class_type_params.get(probe, set())
            probe = self.syntax_parents.get(probe)
        if inherited:
            self.inherited_params[new_id] = inherited
        is_function = isinstance(node, _FM02_FUNCTION_NODES)
        self.class_cell[new_id] = bool(
            self.class_cell.get(scope_id)
            or (is_function
                and isinstance(self.boundary_ids.get(scope_id),
                               ast.ClassDef)))
        self.bindings.setdefault(new_id, set())
        return new_id
    def _visit_arguments(self, args: ast.arguments, new_id: int,
                         outer_id: int) -> tuple:
        self.scope_of[id(args)] = new_id
        parameters = (*args.posonlyargs, *args.args, *args.kwonlyargs,
                      args.vararg, args.kwarg)
        for parameter in parameters:
            if parameter is None:
                continue
            self.scope_of[id(parameter)] = new_id
            self._bind(new_id, (parameter.arg,), parameter)
            if parameter.annotation is not None:
                self._visit(parameter.annotation, outer_id)
        defaults = (*args.defaults, *args.kw_defaults)
        for default in defaults:
            if default is not None:
                self._visit(default, outer_id)
        return tuple(
            parameter.annotation for parameter in parameters
            if parameter is not None and parameter.annotation is not None)
    def _scope_type_param_refs(self, node: ast.AST, scope_id: int,
                               new_id: int, roots: tuple) -> None:
        names = {
            getattr(param, "name", "")
            for param in getattr(node, "type_params", ())
        } - {""}
        if not names:
            return
        for root in roots:
            if root is None:
                continue
            for sub in walk_nodes(root):
                if (not isinstance(sub, ast.Name)
                        or not isinstance(sub.ctx, ast.Load)
                        or sub.id not in names):
                    continue
                probe: int | None = self.scope_of.get(id(sub), scope_id)
                shadowed = False
                while probe != scope_id and probe is not None:
                    if sub.id in self.bindings.get(probe, set()):
                        shadowed = True
                        break
                    probe = self.parents.get(probe)
                if not shadowed:
                    self.scope_of[id(sub)] = new_id
    def _visit_function(self, node: ast.AST, scope_id: int) -> None:
        new_id = self._enter_scope(node, scope_id)
        self._bind(scope_id, (getattr(node, "name", None),), node)
        for decorator in getattr(node, "decorator_list", ()):
            self._visit(decorator, scope_id)
        annotation_roots = self._visit_arguments(
            node.args, new_id, scope_id)
        for type_param in getattr(node, "type_params", ()):
            self._visit(type_param, new_id)
        returns = getattr(node, "returns", None)
        if returns is not None:
            self._visit(returns, scope_id)
        if isinstance(node, ast.Lambda):
            self._visit(node.body, new_id)
        else:
            for statement in node.body:
                self._visit(statement, new_id)
        self._scope_type_param_refs(
            node, scope_id, new_id, (*annotation_roots, returns))
    def _visit_class(self, node: ast.ClassDef, scope_id: int) -> None:
        new_id = self._enter_scope(node, scope_id)
        self._bind(scope_id, (node.name,), node)
        for expression in (*node.decorator_list, *node.bases,
                           *(keyword.value for keyword in node.keywords)):
            self._visit(expression, scope_id)
        for type_param in getattr(node, "type_params", ()):
            self._visit(type_param, new_id)
        for statement in node.body:
            self._visit(statement, new_id)
        self._scope_type_param_refs(
            node, scope_id, new_id,
            (*node.bases, *(keyword.value for keyword in node.keywords)))
    def _visit_type_alias(self, node: Any, scope_id: int) -> None:
        new_id = self._enter_scope(node, scope_id)
        self.scope_of[id(node.name)] = scope_id
        self._bind(scope_id, (node.name.id,), node.name)
        for type_param in getattr(node, "type_params", ()):
            self._visit(type_param, new_id)
        self._visit(node.value, new_id)
    def _visit_comprehension(self, node: ast.AST, scope_id: int) -> None:
        new_id = self._enter_scope(node, scope_id)
        for position, generator in enumerate(node.generators):
            self.scope_of[id(generator)] = new_id
            self._visit(generator.iter, scope_id if position == 0 else new_id)
            self._visit(generator.target, new_id)
            for condition in generator.ifs:
                self._visit(condition, new_id)
        if isinstance(node, ast.DictComp):
            self._visit(node.key, new_id)
            self._visit(node.value, new_id)
        else:
            self._visit(node.elt, new_id)
    def _nearest_non_comprehension(self, scope_id: int) -> int:
        while isinstance(self.boundary_ids.get(scope_id),
                         _FM02_COMPREHENSION_NODES):
            scope_id = self.parents[scope_id]
        return scope_id
    def _import_bindings(self, node: ast.AST) -> tuple | None:
        if isinstance(node, ast.Import):
            return tuple((alias.asname or alias.name).split('.')[0]
                         for alias in node.names)
        if isinstance(node, ast.ImportFrom):
            return tuple(alias.asname or alias.name for alias in node.names)
        return None
    def _bind_node(self, node: ast.AST, scope_id: int) -> None:
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and id(node) not in self.ann_only):
            if isinstance(node.ctx, ast.Del):
                self._unbind(scope_id, node.id, node)
            else:
                self._bind(scope_id, (node.id,), node)
            return
        if isinstance(node, ast.arg):
            self._bind(scope_id, (node.arg,), node)
            return
        imported = self._import_bindings(node)
        if imported is not None:
            self._bind(scope_id, imported, node)
            return
        if isinstance(node, (ast.ExceptHandler, ast.MatchAs,
                             ast.MatchStar)):
            self._bind(scope_id, (node.name,), node)
            return
        if isinstance(node, ast.MatchMapping):
            self._bind(scope_id, (node.rest,), node)
            return
        if _TYPE_PARAM_NODES and isinstance(node, _TYPE_PARAM_NODES):
            self._bind(scope_id, (node.name,), node)
            if isinstance(self.boundary_ids.get(scope_id), ast.ClassDef):
                self.class_type_params.setdefault(scope_id, set()).add(
                    node.name)
    def _visit(self, node: ast.AST, scope_id: int) -> None:
        self.scope_of[id(node)] = scope_id
        if id(node) in self.deferred_root_ids:
            return
        if isinstance(node, ast.Global):
            if scope_id != id(self.tree):
                self.global_declarations.setdefault(
                    scope_id, set()).update(node.names)
            return
        if isinstance(node, ast.Nonlocal):
            self.nonlocal_declarations.setdefault(scope_id, set()).update(node.names)
            return
        if _FM02_TYPE_ALIAS_NODES and isinstance(
                node, _FM02_TYPE_ALIAS_NODES):
            self._visit_type_alias(node, scope_id)
            return
        if isinstance(node, _FM02_FUNCTION_NODES):
            self._visit_function(node, scope_id)
            return
        if isinstance(node, ast.ClassDef):
            self._visit_class(node, scope_id)
            return
        if isinstance(node, _FM02_COMPREHENSION_NODES):
            self._visit_comprehension(node, scope_id)
            return
        if (isinstance(node, ast.NamedExpr)
                and isinstance(self.boundary_ids.get(scope_id),
                               _FM02_COMPREHENSION_NODES)):
            self._visit(node.target, self._nearest_non_comprehension(scope_id))
            self._visit(node.value, scope_id)
            return
        if (isinstance(node, ast.AnnAssign) and node.value is None
                and isinstance(node.target, ast.Name)
                and isinstance(self.boundary_ids.get(scope_id),
                               _FM02_FUNCTION_NODES)):
            self._unbind(scope_id, node.target.id, node, position=(0, 0))
        self._bind_node(node, scope_id)
        for child in ast.iter_child_nodes(node):
            self._visit(child, scope_id)
        if isinstance(node, ast.ExceptHandler) and node.name:
            end_col = (node.end_col_offset if node.end_col_offset is not None
                       else node.col_offset)
            self._unbind(
                scope_id, node.name, node,
                position=(node.end_lineno or node.lineno, end_col + 1))
def _fm02_deferred_global_facts(
        bindings: dict, binding_sites: dict, global_declarations: dict,
        parents: dict, boundary_ids: dict
) -> tuple[dict[str, frozenset[int]], frozenset[int]]:
    deferred_scope_ids: set[int] = set()
    for scope_id in boundary_ids:
        probe = scope_id
        while probe is not None:
            if isinstance(boundary_ids.get(probe), _FM02_FUNCTION_NODES):
                deferred_scope_ids.add(scope_id)
                break
            probe = parents.get(probe)
    owners: dict[str, set[int]] = {}
    for scope_id, names in global_declarations.items():
        if scope_id not in deferred_scope_ids:
            continue
        for name in names:
            if binding_sites.get(scope_id, {}).get(name):
                owners.setdefault(name, set()).add(scope_id)
    frozen_owners = {
        name: frozenset(scope_ids) for name, scope_ids in owners.items()
    }
    return frozen_owners, frozenset(deferred_scope_ids)
def _fm02_propagate_immediate_global_events(
        tree: ast.AST, bindings: dict, binding_sites: dict,
        unbinding_sites: dict, global_declarations: dict,
        deferred_scope_ids: frozenset[int]) -> None:
    module_id = id(tree)
    for scope_id, names in global_declarations.items():
        if scope_id == module_id or scope_id in deferred_scope_ids:
            continue
        for name in names:
            bound = binding_sites.get(scope_id, {}).get(name, ())
            deleted = unbinding_sites.get(scope_id, {}).get(name, ())
            if not bound and not deleted:
                continue
            bindings.setdefault(module_id, set()).add(name)
            if bound:
                binding_sites.setdefault(module_id, {}).setdefault(
                    name, []).extend(bound)
            if deleted:
                unbinding_sites.setdefault(module_id, {}).setdefault(
                    name, []).extend(deleted)
def _fm02_propagate_immediate_nonlocal_events(
        bindings: dict, binding_sites: dict,
        unbinding_sites: dict, nonlocal_declarations: dict,
        parents: dict, boundary_ids: dict) -> None:
    for scope_id, names in nonlocal_declarations.items():
        if not isinstance(boundary_ids.get(scope_id), ast.ClassDef):
            continue
        target_id = parents.get(scope_id)
        if not isinstance(boundary_ids.get(target_id), _FM02_FUNCTION_NODES):
            continue
        for name in names:
            bound = binding_sites.get(scope_id, {}).get(name, ())
            deleted = unbinding_sites.get(scope_id, {}).get(name, ())
            if not bound and not deleted:
                continue
            bindings.setdefault(target_id, set()).add(name)
            if bound:
                binding_sites.setdefault(target_id, {}).setdefault(
                    name, []).extend(bound)
            if deleted:
                unbinding_sites.setdefault(target_id, {}).setdefault(
                    name, []).extend(deleted)
def _fm02_visible_sets(
        tree: ast.AST, bindings: dict, parents: dict,
        boundary_ids: dict, class_cell: dict, inherited_params: dict,
        deferred_global_owners: dict[str, frozenset[int]] | None = None,
        deferred_scope_ids: frozenset[int] = _FM02_EMPTY_SCOPE_IDS):
    deferred_global_owners = deferred_global_owners or {}
    memo: dict[int, set] = {}
    def _visible(scope_id: int) -> set:
        cached = memo.get(scope_id)
        if cached is not None:
            return cached
        names = set(bindings.get(scope_id, ()))
        names |= inherited_params.get(scope_id, set())
        if scope_id in deferred_scope_ids:
            names.update(deferred_global_owners)
        if isinstance(boundary_ids.get(scope_id), ast.ClassDef):
            names |= _FM02_CLASS_BODY_NAMES
        if class_cell.get(scope_id):
            names.add(_FM02_CLASS_CELL_NAME)
        parent = parents.get(scope_id)
        if parent is not None:
            names |= _visible(parent)
        names |= _FM02_VISIBLE_BASE
        scope_node = (tree if scope_id == id(tree)
                      else boundary_ids.get(scope_id))
        if _fm02_annotations_defined(scope_node):
            names.add('__annotations__')
        memo[scope_id] = names
        return names
    return _visible
def _fm02_star_import_positions(tree: ast.AST) -> tuple:
    return tuple(
        (node.lineno, node.col_offset)
        for node in walk_nodes(tree) if is_star_import(node))
def _fm02_iter_fstring_name_refs(tree: ast.AST,
                                 index: list | None):
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.JoinedStr):
            continue
        for value in node.values:
            if not isinstance(value, ast.FormattedValue):
                continue
            for name_node in _fm02_iter_name_nodes(value.value):
                yield node, name_node
def _fm02_report_undefined(issues: list, source: Any, filepath: Any,
                           node: ast.JoinedStr, vn: str) -> None:
    _append_format_issue(issues, {
        "rule_id": "FM-02", "severity": "P1",
        "title": f"f-string 引用了未定义的变量 '{vn}'",
        "description": (
            f"f-string 表达式中引用了 '{vn}', 但该名称在当前作用域的"
            "绑定链上不可见（本作用域、外层函数与模块帧均无赋值/导入/"
            "定义/参数绑定）, 运行时必然 NameError."
        ),
        "suggestion": '根因: f-string 引用了未定义的变量。该问题属于格式化字符串类别。\n修复策略: 检查变量名拼写, 或将变量定义/导入移到 f-string 之前\n参考标准: PEP 8 / pylint W1309',
        "rule_ref": "fstring-undefined-name",
    }, source, filepath, node.lineno)
def _fm02_comprehension_elt_name_ids(tree: ast.AST) -> dict[int, set[int]]:
    elt_ids: dict[int, set[int]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, ast.DictComp):
            roots = (node.key, node.value)
        elif isinstance(node, _FM02_COMPREHENSION_NODES):
            roots = (node.elt,)
        else:
            continue
        elt_ids[id(node)] = {
            id(sub) for root in roots for sub in walk_nodes(root)
            if isinstance(sub, ast.Name)
        }
    return elt_ids
def _fm02_comprehension_iter_exclusions(
        tree: ast.AST, binding_positions: dict[int, tuple[int, int]]
) -> dict[int, set[tuple[int, int]]]:
    exclusions: dict[int, set[tuple[int, int]]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, _FM02_COMPREHENSION_NODES):
            continue
        for generator in node.generators:
            target_positions = {
                binding_positions.get(
                    id(sub), (sub.lineno, sub.col_offset))
                for sub in walk_nodes(generator.target)
                if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Store)
            }
            if not target_positions:
                continue
            for sub in walk_nodes(generator.iter):
                if isinstance(sub, ast.Name):
                    exclusions.setdefault(id(sub), set()).update(
                        target_positions)
    return exclusions
def _fm02_literal_truth(node: ast.AST) -> bool | None:
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.NamedExpr):
        return _fm02_literal_truth(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        value = _fm02_literal_truth(node.operand)
        return None if value is None else not value
    return None
def _fm02_unreachable_expression_roots(node: ast.AST) -> tuple:
    roots: list[ast.AST] = []
    def visit(current: ast.AST) -> None:
        if isinstance(current, ast.BoolOp):
            for index, value in enumerate(current.values):
                visit(value)
                truth = _fm02_literal_truth(value)
                if ((isinstance(current.op, ast.And) and truth is False)
                        or (isinstance(current.op, ast.Or) and truth is True)):
                    roots.extend(current.values[index + 1:])
                    break
            return
        if isinstance(current, ast.IfExp):
            visit(current.test)
            truth = _fm02_literal_truth(current.test)
            if truth is True:
                roots.append(current.orelse)
                visit(current.body)
            elif truth is False:
                roots.append(current.body)
                visit(current.orelse)
            else:
                visit(current.body)
                visit(current.orelse)
            return
        for child in ast.iter_child_nodes(current):
            visit(child)
    visit(node)
    return tuple(roots)
def _fm02_unreachable_fstring_facts(
        tree: ast.AST, binding_positions: dict[int, tuple[int, int]]
) -> tuple[set[int], set[tuple[int, int]]]:
    roots = [
        root
        for node in walk_nodes(tree) if isinstance(node, ast.JoinedStr)
        for value in node.values if isinstance(value, ast.FormattedValue)
        for root in _fm02_unreachable_expression_roots(value.value)
    ]
    name_ids = {
        id(sub) for root in roots for sub in walk_nodes(root)
        if isinstance(sub, ast.Name)
    }
    binding_sites: set[tuple[int, int]] = set()
    for root in roots:
        for sub in walk_nodes(root):
            if not (isinstance(sub, ast.NamedExpr)
                    and isinstance(sub.target, ast.Name)):
                continue
            target = sub.target
            binding_sites.add(binding_positions.get(
                id(target), (target.lineno, target.col_offset)))
    return name_ids, binding_sites
def _fm02_intersect_binding_paths(paths: list[set]) -> set:
    if not paths:
        return set()
    result = set(paths[0])
    for path in paths[1:]:
        result &= path
    return result
def _fm02_walrus_truth_bindings(node: ast.AST) -> tuple[set, set]:
    if isinstance(node, ast.NamedExpr):
        true_value, false_value = _fm02_walrus_truth_bindings(node.value)
        targets = {node.target} if isinstance(node.target, ast.Name) else set()
        return targets | true_value, targets | false_value
    if isinstance(node, ast.BoolOp):
        parts = [(value, *_fm02_walrus_truth_bindings(value))
                 for value in node.values]
        truths = [_fm02_literal_truth(value) for value in node.values]
        if isinstance(node.op, ast.And):
            true_bound = (set() if any(truth is False for truth in truths)
                          else set().union(*(true for _v, true, _f in parts)))
            paths = []
            prior_true = set()
            for (_value, true, false), truth in zip(parts, truths, strict=True):
                if truth is not True:
                    paths.append(prior_true | false)
                if truth is False:
                    break
                prior_true |= true
            return true_bound, _fm02_intersect_binding_paths(paths)
        false_bound = (set() if any(truth is True for truth in truths)
                       else set().union(*(false for _v, _t, false in parts)))
        paths = []
        prior_false = set()
        for (_value, true, false), truth in zip(parts, truths, strict=True):
            if truth is not False:
                paths.append(prior_false | true)
            if truth is True:
                break
            prior_false |= false
        return _fm02_intersect_binding_paths(paths), false_bound
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        true_bound, false_bound = _fm02_walrus_truth_bindings(node.operand)
        return false_bound, true_bound
    if isinstance(node, ast.IfExp):
        test_true, test_false = _fm02_walrus_truth_bindings(node.test)
        body_true, body_false = _fm02_walrus_truth_bindings(node.body)
        else_true, else_false = _fm02_walrus_truth_bindings(node.orelse)
        test_truth = _fm02_literal_truth(node.test)
        if test_truth is True:
            return test_true | body_true, test_true | body_false
        if test_truth is False:
            return test_false | else_true, test_false | else_false
        true_paths = []
        false_paths = []
        if _fm02_literal_truth(node.body) is not False:
            true_paths.append(test_true | body_true)
        if _fm02_literal_truth(node.orelse) is not False:
            true_paths.append(test_false | else_true)
        if _fm02_literal_truth(node.body) is not True:
            false_paths.append(test_true | body_false)
        if _fm02_literal_truth(node.orelse) is not True:
            false_paths.append(test_false | else_false)
        return (_fm02_intersect_binding_paths(true_paths),
                _fm02_intersect_binding_paths(false_paths))
    if isinstance(node, ast.Compare):
        evaluated = []
        for value in (node.left, *node.comparators):
            true_value, false_value = _fm02_walrus_truth_bindings(value)
            evaluated.append(true_value & false_value)
        if len(evaluated) == 2:
            bound = evaluated[0] | evaluated[1]
            return bound, bound
        false_paths = [set().union(*evaluated[:index + 2])
                       for index in range(len(node.comparators))]
        return (set().union(*evaluated),
                _fm02_intersect_binding_paths(false_paths))
    if isinstance(node, ast.Lambda):
        defaults = (*node.args.defaults, *node.args.kw_defaults)
        bound = set()
        for default in defaults:
            if default is not None:
                true_default, false_default = _fm02_walrus_truth_bindings(default)
                bound |= true_default & false_default
        return bound, bound
    if isinstance(node, _FM02_COMPREHENSION_NODES):
        bound = set()
        if node.generators:
            true_iter, false_iter = _fm02_walrus_truth_bindings(
                node.generators[0].iter)
            bound = true_iter & false_iter
        return bound, bound
    bound = set()
    for child in ast.iter_child_nodes(node):
        true_child, false_child = _fm02_walrus_truth_bindings(child)
        bound |= true_child & false_child
    return bound, bound
def _fm02_comprehension_elt_active_sites(
        tree: ast.AST, binding_positions: dict[int, tuple[int, int]]
) -> dict[int, set[tuple[int, int]]]:
    active: dict[int, set[tuple[int, int]]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, _FM02_COMPREHENSION_NODES):
            continue
        targets = set()
        for generator in node.generators:
            for condition in generator.ifs:
                true_bound, _false_bound = _fm02_walrus_truth_bindings(condition)
                targets |= true_bound
        if not targets:
            continue
        positions: dict[str, set[tuple[int, int]]] = {}
        for target in targets:
            position = binding_positions.get(
                id(target), (target.lineno, target.col_offset))
            positions.setdefault(target.id, set()).add(position)
        roots = ((node.key, node.value) if isinstance(node, ast.DictComp)
                 else (node.elt,))
        for root in roots:
            for sub in walk_nodes(root):
                if not (isinstance(sub, ast.Name)
                        and isinstance(sub.ctx, ast.Load)):
                    continue
                sites = positions.get(sub.id)
                if sites:
                    active.setdefault(id(sub), set()).update(sites)
    return active
def _fm02_name_unbound_at_use(
        name_node: ast.Name, scope_id: int, binding_sites: dict,
        unbinding_sites: dict, nonlocal_declarations: dict,
        global_declarations: dict, module_bindings: set,
        *, comprehension_elt: bool = False,
        excluded_binding_sites: set[tuple[int, int]] | None = None,
        active_binding_sites: set[tuple[int, int]] | None = None,
        fallback_visible: bool = False,
        deleted_fallback_visible: bool = False,
        deferred_global_owners: dict[str, frozenset[int]] | None = None,
        deferred_scope_ids: frozenset[int] = _FM02_EMPTY_SCOPE_IDS) -> bool:
    name = name_node.id
    position = (name_node.lineno, name_node.col_offset)
    excluded = excluded_binding_sites or set()
    active = active_binding_sites or set()
    scope_bound = binding_sites.get(scope_id, {}).get(name, ())
    bound = tuple(site for site in scope_bound if site not in excluded)
    deleted = tuple(
        site for site in unbinding_sites.get(scope_id, {}).get(name, ())
        if site not in excluded)
    if (excluded and not bound and not deleted
            and any(site in excluded for site in scope_bound)):
        return not fallback_visible
    if comprehension_elt and bound:
        return False
    prior_events = [(site, False) for site in bound
                    if site <= position or site in active]
    prior_events.extend((site, True) for site in deleted if site <= position)
    if prior_events:
        latest_unbound = max(prior_events)[1]
        return latest_unbound and not deleted_fallback_visible
    if name in nonlocal_declarations.get(scope_id, set()):
        return False
    if name in global_declarations.get(scope_id, set()):
        if name in module_bindings or name in _FM02_BUILTIN_NAMES:
            return False
        owners = (deferred_global_owners or {}).get(name, ())
        external_owner = any(owner != scope_id for owner in owners)
        deferred_only_reader = bool(owners) and not (bound or deleted)
        if (scope_id in deferred_scope_ids
                and (external_owner or deferred_only_reader)):
            return False
    if fallback_visible:
        return False
    return bool(bound or deleted)
def _fm02_immediate_outer_unbound(
        tree: ast.AST, name_node: ast.Name, scope_id: int,
        parents: dict, boundary_ids: dict, bindings: dict,
        binding_sites: dict, unbinding_sites: dict,
        nonlocal_declarations: dict, global_declarations: dict, *,
        comprehension_elt: bool = False,
        excluded_binding_sites: set[tuple[int, int]] | None = None,
        active_binding_sites: set[tuple[int, int]] | None = None,
        deferred_global_owners: dict[str, frozenset[int]] | None = None,
        deferred_scope_ids: frozenset[int] = _FM02_EMPTY_SCOPE_IDS) -> bool:
    vn = name_node.id
    excluded = excluded_binding_sites or set()
    active = active_binding_sites or set()
    bound = tuple(
        site for site in binding_sites.get(scope_id, {}).get(vn, ())
        if site not in excluded)
    deleted = tuple(
        site for site in unbinding_sites.get(scope_id, {}).get(vn, ())
        if site not in excluded)
    position = (name_node.lineno, name_node.col_offset)
    prior_events = [(site, False) for site in bound
                    if site <= position or site in active]
    prior_events.extend((site, True) for site in deleted if site <= position)
    current_active = (
        bool(comprehension_elt and bound)
        or bool(prior_events and not max(prior_events)[1]))
    if current_active:
        return False
    frame_id = parents.get(scope_id)
    immediate_nodes = (ast.ClassDef, *_FM02_COMPREHENSION_NODES)
    while isinstance(boundary_ids.get(frame_id), immediate_nodes):
        frame_id = parents.get(frame_id)
    if frame_id is None or vn not in bindings.get(frame_id, set()):
        return False
    fallback_visible = False
    deleted_fallback_visible = False
    if vn in global_declarations.get(frame_id, set()):
        fallback_visible = deleted_fallback_visible = (
            vn in _FM02_BUILTIN_NAMES)
    elif frame_id == id(tree):
        fallback_visible = vn in _FM02_VISIBLE_BASE
        deleted_fallback_visible = vn in _FM02_BUILTIN_NAMES
    return _fm02_name_unbound_at_use(
        name_node, frame_id, binding_sites, unbinding_sites,
        nonlocal_declarations, global_declarations,
        bindings.get(id(tree), set()),
        excluded_binding_sites=excluded,
        active_binding_sites=active,
        fallback_visible=fallback_visible,
        deleted_fallback_visible=deleted_fallback_visible,
        deferred_global_owners=deferred_global_owners,
        deferred_scope_ids=deferred_scope_ids)
def check_FM02(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH,
               index: list | None = None) -> Any:
    _log.debug("规则入口 check_FM02 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    star_import_positions = _fm02_star_import_positions(tree)
    deferred_roots = _fm02_deferred_annotation_roots(tree)
    deferred_ids = {
        id(sub)
        for root in deferred_roots
        for sub in walk_nodes(root)
    }
    binding_positions = _fm02_binding_positions(tree)
    unreachable_name_ids, unreachable_binding_sites = (
        _fm02_unreachable_fstring_facts(tree, binding_positions))
    (scope_of, bindings, parents, boundary_ids,
     class_cell, inherited_params, binding_sites, unbinding_sites,
     nonlocal_declarations, global_declarations) = _ScopeFrameGraph(
        tree, deferred_roots, binding_positions).build()
    deferred_global_owners, deferred_scope_ids = _fm02_deferred_global_facts(
        bindings, binding_sites, global_declarations, parents, boundary_ids)
    _fm02_propagate_immediate_global_events(
        tree, bindings, binding_sites, unbinding_sites,
        global_declarations, deferred_scope_ids)
    _fm02_propagate_immediate_nonlocal_events(
        bindings, binding_sites, unbinding_sites,
        nonlocal_declarations, parents, boundary_ids)
    visible_of = _fm02_visible_sets(
        tree, bindings, parents, boundary_ids, class_cell, inherited_params,
        deferred_global_owners, deferred_scope_ids)
    reported = set()
    comprehension_elt_ids = _fm02_comprehension_elt_name_ids(tree)
    comprehension_iter_exclusions = _fm02_comprehension_iter_exclusions(
        tree, binding_positions)
    comprehension_elt_active_sites = _fm02_comprehension_elt_active_sites(
        tree, binding_positions)
    for node, name_node in _fm02_iter_fstring_name_refs(tree, index):
        if id(name_node) in deferred_ids or id(name_node) in unreachable_name_ids:
            continue
        vn = name_node.id
        scope_id = scope_of.get(id(name_node), id(tree))
        if star_import_positions and (
                scope_id in deferred_scope_ids
                or any(site <= (name_node.lineno, name_node.col_offset)
                       for site in star_import_positions)):
            continue
        dedup_key = (scope_id, vn, node.lineno)
        if dedup_key in reported:
            continue
        scope_node = boundary_ids.get(scope_id)
        fallback_visible = False
        deleted_fallback_visible = False
        if vn in global_declarations.get(scope_id, set()):
            fallback_visible = deleted_fallback_visible = (
                vn in _FM02_BUILTIN_NAMES)
        elif scope_id == id(tree):
            fallback_visible = vn in _FM02_VISIBLE_BASE
            deleted_fallback_visible = vn in _FM02_BUILTIN_NAMES
        elif isinstance(scope_node, ast.ClassDef):
            parent_scope = parents.get(scope_id)
            outer_visible = (
                parent_scope is not None and vn in visible_of(parent_scope))
            fallback_visible = outer_visible or vn in _FM02_CLASS_BODY_NAMES
            deleted_fallback_visible = outer_visible
        excluded_sites = (
            comprehension_iter_exclusions.get(id(name_node), set())
            | unreachable_binding_sites)
        active_sites = comprehension_elt_active_sites.get(id(name_node), set())
        comprehension_elt = (
            isinstance(scope_node, _FM02_COMPREHENSION_NODES)
            and id(name_node) in comprehension_elt_ids.get(scope_id, ()))
        visible = vn in visible_of(scope_id)
        unbound = _fm02_name_unbound_at_use(
            name_node, scope_id, binding_sites, unbinding_sites,
            nonlocal_declarations, global_declarations,
            bindings.get(id(tree), set()),
            comprehension_elt=comprehension_elt,
            excluded_binding_sites=excluded_sites,
            active_binding_sites=active_sites,
            fallback_visible=fallback_visible,
            deleted_fallback_visible=deleted_fallback_visible,
            deferred_global_owners=deferred_global_owners,
            deferred_scope_ids=deferred_scope_ids)
        if (visible and not unbound
                and isinstance(scope_node,
                               (ast.ClassDef, *_FM02_COMPREHENSION_NODES))):
            unbound = _fm02_immediate_outer_unbound(
                tree, name_node, scope_id, parents, boundary_ids, bindings,
                binding_sites, unbinding_sites, nonlocal_declarations,
                global_declarations,
                comprehension_elt=comprehension_elt,
                excluded_binding_sites=excluded_sites,
                active_binding_sites=active_sites,
                deferred_global_owners=deferred_global_owners,
                deferred_scope_ids=deferred_scope_ids)
        if visible and not unbound:
            continue
        reported.add(dedup_key)
        _fm02_report_undefined(issues, source, filepath, node, vn)
    return apply_rule_suppress(issues, source, 'FM-02')
class _Fm03Fields:
    __slots__ = ("auto", "demand", "manual", "mixed", "named", "valid")
    def __init__(self) -> None:
        self.named: set[str] = set()
        self.auto = 0
        self.demand = 0
        self.manual: set[int] = set()
        self.mixed = False
        self.valid = True
    def add_auto(self) -> None:
        if self.mixed:
            return
        if self.manual:
            self.mixed = True
            return
        self.auto += 1
        self.demand = self.auto
    def add_manual(self, index: int) -> None:
        if self.mixed:
            return
        if self.auto:
            self.mixed = True
            return
        self.manual.add(index)
        self.demand = max(self.demand, index + 1)
    def positional_demand(self) -> int | None:
        return self.demand if self.valid else None
_FM03_MAX_SPEC_RECURSION = 2
def _fm03_extent_in(seg: str, start: int) -> int:
    depth, j = 1, start + 1
    m = len(seg)
    while j < m:
        c = seg[j]
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return j
        j += 1
    return -1
def _fm03_exclaim_malformed(content: str, d: int, p: int) -> bool:
    if d < 0 or (p >= 0 and d > p):
        return False
    return (d + 1 >= len(content)
            or (d + 2 < len(content) and content[d + 2] != ':'))
def _fm03_field_delimiters(content: str) -> tuple[int, int]:
    bracket_depth = 0
    conversion = -1
    for index, char in enumerate(content):
        if char == '[':
            bracket_depth += 1
        elif char == ']' and bracket_depth:
            bracket_depth -= 1
        elif bracket_depth == 0 and char == '!' and conversion < 0:
            conversion = index
        elif bracket_depth == 0 and char == ':':
            return conversion, index
    return conversion, -1
def _fm03_field_head(content: str, d: int, p: int
                     ) -> tuple[str | None, bool]:
    stop = len(content)
    if d >= 0:
        stop = min(stop, d)
    if p >= 0:
        stop = min(stop, p)
    raw = content[:stop]
    if '{' in raw:
        return None, True
    if _fm03_exclaim_malformed(content, d, p):
        return None, True
    return raw.split('.', 1)[0].split('[', 1)[0], False
def _fm03_record_field(fields: _Fm03Fields, head: str) -> None:
    if not head:
        fields.add_auto()
    elif head.isdecimal():
        fields.add_manual(int(head))
    else:
        fields.named.add(head)
def _fm03_scan_field(seg: str, i: int, fields: _Fm03Fields,
                     depth: int) -> int | None:
    end = _fm03_extent_in(seg, i)
    if end < 0:
        return None
    content = seg[i + 1:end]
    d, p = _fm03_field_delimiters(content)
    head, malformed = _fm03_field_head(content, d, p)
    if malformed:
        return None
    _fm03_record_field(fields, head)
    if (p >= 0 and '{' in content[p + 1:]
            and not _fm03_segment(content[p + 1:], fields, depth + 1)):
        return None
    return end + 1
def _fm03_escaped_double(seg: str, i: int, ch: str) -> bool:
    return i + 1 < len(seg) and seg[i + 1] == ch
def _fm03_open_brace_step(seg: str, i: int, fields: _Fm03Fields,
                          depth: int) -> int | None:
    if _fm03_escaped_double(seg, i, '{'):
        return i + 2
    return _fm03_scan_field(seg, i, fields, depth)
def _fm03_close_brace_step(seg: str, i: int) -> int | None:
    if _fm03_escaped_double(seg, i, '}'):
        return i + 2
    return None
def _fm03_segment(seg: str, fields: _Fm03Fields, depth: int = 0) -> bool:
    if depth >= _FM03_MAX_SPEC_RECURSION:
        return False
    i, m = 0, len(seg)
    while i < m:
        c = seg[i]
        if c == '{':
            nxt = _fm03_open_brace_step(seg, i, fields, depth)
        elif c == '}':
            nxt = _fm03_close_brace_step(seg, i)
        else:
            i += 1
            continue
        if nxt is None:
            return False
        i = nxt
    return True
def _fm03_scan_fields(fmt_str: str) -> _Fm03Fields:
    fields = _Fm03Fields()
    if not _fm03_segment(fmt_str, fields):
        fields.valid = False
    return fields
def _fm03_missing_kwargs(node: ast.Call,
                        named_placeholders: set) -> set | None:
    if any(kw.arg is None for kw in node.keywords):
        return None
    kwarg_names = {kw.arg for kw in node.keywords}
    return named_placeholders - kwarg_names
def _fm03_call_const_format_str(node: ast.Call) -> str | None:
    if as_format_call(node) is None:
        return None
    if not isinstance(node.func.value, ast.Constant):
        return None
    if not isinstance(node.func.value.value, str):
        return None
    return node.func.value.value
def _fm03_report_missing_keys(issues: list, source: Any, filepath: Any,
                              node: ast.Call, missing: set) -> None:
    missing_txt = "{" + ", ".join(map(repr, sorted(missing))) + "}"
    _append_format_issue(issues, {
        "rule_id": "FM-03", "severity": "P1",
        "title": f".format() 缺少关键字参数: {missing_txt}",
        "description": (
            f"格式字符串引用了 {missing_txt} 但在 .format() 调用中未提供对应关键字参数."
            "将导致 KeyError."
        ),
        "suggestion": f'根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于格式化字符串类别。\n修复策略: 在 .format() 中添加 {missing_txt} 关键字参数.\n参考标准: PEP 8 / pylint W1309',
        "rule_ref": "format-missing-keys",
    }, source, filepath, node.lineno)
def _fm03_report_mixed_field_numbering(
        issues: list, source: Any, filepath: Any, node: ast.Call) -> None:
    _append_format_issue(issues, {
        "rule_id": "FM-03", "severity": "P1",
        "title": ".format() 混用手动编号与自动编号字段",
        "description": (
            "格式字符串同时包含手动编号字段({0})与自动编号字段({}), "
            "str.format 不支持切换编号模式, 运行时将抛 ValueError."
        ),
        "suggestion": (
            "根因: 手动编号与自动编号字段混用导致格式化状态机切换失败。\n"
            "修复策略: 统一使用手动编号({0} {1})或自动编号({} {}), "
            "或改用有意义的关键字字段。\n"
            "参考标准: str.format 文档 / Python 格式化字符串语法"
        ),
        "rule_ref": "format-mixed-field-numbering",
    }, source, filepath, node.lineno)
def _fm03_missing_positional(node: ast.Call, demand: int) -> bool:
    if any(isinstance(arg, ast.Starred) for arg in node.args):
        return False
    return len(node.args) < demand
def _fm03_report_missing_positional(issues: list, source: Any, filepath: Any,
                                    node: ast.Call, demand: int) -> None:
    provided = len(node.args)
    _append_format_issue(issues, {
        "rule_id": "FM-03", "severity": "P1",
        "title": f".format() 缺少位置参数: 需要 {demand} 个, 提供 {provided} 个",
        "description": (
            f"格式字符串的自动/显式编号字段至少需要 {demand} 个位置参数,"
            f"但调用只提供 {provided} 个, 运行时将抛 IndexError"
            "(Replacement index out of range)."
        ),
        "suggestion": (
            "根因: 位置字段(``{}``/``{0}``)按编号取值, 实参数不足即 IndexError。\n"
            f"修复策略: 补齐 {demand - provided} 个位置参数, "
            "或改用关键字字段 + .format(name=value)。\n"
            "参考标准: PEP 8 / pylint W1309 / str.format 文档"
        ),
        "rule_ref": "format-missing-positional",
    }, source, filepath, node.lineno)
def check_FM03(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH,
               index: list | None = None) -> Any:
    _log.debug("规则入口 check_FM03 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        fmt_str = _fm03_call_const_format_str(node)
        if fmt_str is None:
            continue
        fields = _fm03_scan_fields(fmt_str)
        if fields.valid and fields.mixed:
            _fm03_report_mixed_field_numbering(
                issues, source, filepath, node)
        # 解析未完整（未闭合/非法转换/超深嵌套）时，named 只是残片：
        # 此时格式串运行时会先抛 ValueError，不应按残片判定 KeyError。
        missing = (_fm03_missing_kwargs(node, fields.named)
                   if fields.valid else None)
        if missing:
            _fm03_report_missing_keys(issues, source, filepath, node, missing)
        demand = None if fields.mixed else fields.positional_demand()
        if demand is not None and _fm03_missing_positional(node, demand):
            _fm03_report_missing_positional(
                issues, source, filepath, node, demand)
    return apply_rule_suppress(issues, source, 'FM-03')
def check_IN01(tree: Any, source_lines: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    if tree is None:
        return []
    issues = []
    if finding_scan_exempt(filepath):
        return issues
    for node in _scoped_open_calls_missing_encoding(tree):
        issues.append(DiagnoseFinding(
            id="IN-01", severity="P1", dimension="input_validation",
            file=filepath, line=node.lineno, col_offset=node.col_offset,
            title="open() 文本模式缺少 encoding 参数",
            description="open()文本模式缺少encoding参数",
            code_snippet=extract_code_lines(source_lines, node.lineno),
            suggestion=(
                "根因: open()未指定encoding参数, 在不同操作系统(Windows GBK/Linux UTF-8)上行为不一致。\n"
                "修复策略:\n"
                "1. 显式指定encoding(首选): open(path, encoding='utf-8')\n"
                "2. 使用pathlib.Path.read_text(encoding='utf-8')\n"
                "3. 使用io.open()明确编码\n"
                "4. 项目级配置: pyproject.toml中指定默认编码\n"
                "参考: PEP 597 / PEP 540"
            ),
            rule_ref="PEP 597 / Python文档 / Unicode最佳实践"))
    return apply_rule_suppress(issues, source_lines, 'IN-01')
def check_EN01(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    if tree is None:
        return []
    issues = []
    if finding_scan_exempt(filepath):
        return issues
    for node in _scoped_open_calls_missing_encoding(tree):
        issues.append({
            "rule_id": "EN-01", "severity": "P2", "dimension": "encoding_safety",
            "file": filepath, "line": node.lineno,
            "title": "open() 未指定 encoding 参数",
            "description": (
                "open() 未指定 encoding 参数,将使用平台默认编码（Windows: cp936/gbk,"
                "Linux: UTF-8）.跨平台运行时可能导致 UnicodeDecodeError."
            ),
            "code_snippet": extract_code_lines(source, node.lineno),
            "suggestion": "根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于编码规范类别。\n修复策略: 添加 encoding='utf-8' 参数以明确编码.\n参考标准: PEP 8 / PEP 263 / PEP 597",
            "rule_ref": "encoding-open-default",
        })
    return apply_rule_suppress(issues, source, 'EN-01')
_PEP263_COOKIE_RE = re.compile(r'^\s*#.*?coding[:=]\s*([-\w.]+)')
_PEP263_FIRST_LINE_SKIP_RE = re.compile(r'^[ \t\f]*(?:[#\r\n]|$)')
_EN03_UTF8_FAMILY = frozenset({'utf-8', 'utf8', 'utf-8-sig'})
def _en03_is_utf8_family(codec: str) -> bool:
    normalized = codec.replace('_', '-')
    if normalized in _EN03_UTF8_FAMILY:
        return True
    try:
        canonical = codecs.lookup(normalized).name
    except LookupError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_en03_is_utf8_family:LookupError')
        return False
    return canonical in _EN03_UTF8_FAMILY
def _pep263_cookie(lines: list[str]) -> tuple[str, int, str] | None:
    if not lines:
        return None
    match = _PEP263_COOKIE_RE.search(lines[0])
    if match:
        return match.group(1).lower(), 1, lines[0]
    if not _PEP263_FIRST_LINE_SKIP_RE.match(lines[0]) or len(lines) < 2:
        return None
    match = _PEP263_COOKIE_RE.search(lines[1])
    if match:
        return match.group(1).lower(), 2, lines[1]
    return None
def check_EN03(tree: Any, source: Any,
               filepath: Any = _DEFAULT_FILEPATH) -> Any:
    issues = []
    if finding_scan_exempt(filepath):
        return issues
    src = normalize_rule_source(source)
    if not src:
        return issues
    if src.isascii():
        return issues
    cookie = _pep263_cookie(src.split('\n'))
    if cookie is None:
        return issues
    cookie_codec, cookie_line, cookie_text = cookie
    if _en03_is_utf8_family(cookie_codec):
        return issues
    issues.append({
        "rule_id": "EN-03", "severity": "P3", "dimension": "encoding_safety",
        "file": filepath, "line": cookie_line,
        "title": f"编码声明与 Python 3 默认 UTF-8 不一致 (coding: {cookie_codec})",
        "description": (
            f"文件声明了非 UTF-8 家族编码 ({cookie_codec}) 且包含非 ASCII 字符，"
            "不同工具链按声明/按默认解码结果会不一致，存在乱码风险."
        ),
        "code_snippet": cookie_text[:80],
        "suggestion": '根因: 编码声明与实际内容不匹配，属于编码陷阱。\n修复策略: 移除非 UTF-8 编码声明（Python 3 默认 UTF-8），或将文件转为声明编码一致的字节序列\n参考标准: PEP 263 / PEP 3120',
        "rule_ref": "encoding-pep263",
    })
    return apply_rule_suppress(issues, src, 'EN-03')
def _kw_constant_truthy(node: ast.Call, arg_name: str) -> bool:
    kw = kw_arg(node, arg_name)
    return (kw is not None and isinstance(kw.value, ast.Constant)
            and kw.value.value is not None and bool(kw.value.value))
_ModuleApiBinding = tuple[str, str]
def _module_api_import_module(alias: ast.alias,
                              modules: frozenset[str]) -> str | None:
    if alias.name in modules:
        return alias.name
    root = alias.name.split('.')[0]
    if alias.asname is None and alias.name != root and root in modules:
        return root
    return None
def _module_api_collect_from_bindings(
        node: ast.ImportFrom, from_names: dict[str, _ModuleApiBinding],
        modules: frozenset[str], apis: frozenset[str]) -> None:
    if node.level or node.module not in modules:
        return
    for alias in node.names:
        if alias.name == "*":
            for api in apis:
                from_names[api] = (node.module, api)
        elif alias.name in apis:
            from_names[alias.asname or alias.name] = (
                node.module, alias.name)
_SUBPROCESS_TEXT_APIS = frozenset({
    "run", "call", "check_call", "check_output", "Popen",
})
_SP01_MODULE_ALIAS = "subprocess"
def _module_api_scope_body(scope: ast.AST) -> list[ast.AST]:
    body = getattr(scope, "body", None)
    if isinstance(body, list):
        return body
    return [body] if isinstance(body, ast.AST) else []
def _module_api_shadow_import_names(
        node: ast.Import | ast.ImportFrom,
        modules: frozenset[str], apis: frozenset[str]) -> set[str]:
    names: set[str] = set()
    for alias in node.names:
        if alias.name == "*":
            if (isinstance(node, ast.ImportFrom)
                    and (node.level or node.module not in modules)):
                names.update(apis)
            continue
        bound = alias.asname or alias.name.split(".")[0]
        if isinstance(node, ast.Import):
            if _module_api_import_module(alias, modules) is not None:
                continue
        elif (not node.level and node.module in modules
              and alias.name in apis):
            continue
        names.add(bound)
    return names
def _module_api_comprehension_walrus_targets(scope: ast.AST):
    stack = [scope]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
            yield node.target
        if node is not scope and isinstance(node, FRAME_BOUNDARY_NODES):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _module_api_iter_binding_nodes(scope: ast.AST):
    stack = list(_module_api_scope_body(scope))
    while stack:
        node = stack.pop()
        if isinstance(node, COMP_SCOPE_NODES):
            yield from _module_api_comprehension_walrus_targets(node)
            continue
        yield node
        if isinstance(node, FRAME_BOUNDARY_NODES):
            stack.extend(_definition_time_expressions(node))
            continue
        stack.extend(ast.iter_child_nodes(node))
def _module_api_pattern_bindings(node: ast.AST) -> tuple[str, ...]:
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        return (node.name,) if node.name else ()
    if isinstance(node, ast.MatchMapping):
        return (node.rest,) if node.rest else ()
    if _TYPE_PARAM_NODES and isinstance(node, _TYPE_PARAM_NODES):
        _name = getattr(node, "name", "")
        return (_name,) if _name else ()
    return ()
def _module_api_scope_shadow_names(
        scope: ast.AST, modules: frozenset[str],
        apis: frozenset[str]) -> set[str]:
    names = collect_param_names(scope)
    names.update(
        _name for _name in (getattr(_param, "name", "")
                            for _param in getattr(scope, "type_params", ()))
        if _name)
    for node in _module_api_iter_binding_nodes(scope):
        if isinstance(node, FRAME_BOUNDARY_NODES):
            name = getattr(node, "name", "")
            if name:
                names.add(name)
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names.update(_module_api_shadow_import_names(
                node, modules, apis))
            continue
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            continue
        pattern_names = _module_api_pattern_bindings(node)
        if pattern_names:
            names.update(pattern_names)
            continue
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            names.add(node.id)
        elif isinstance(node, ast.ExceptHandler) and node.name:
            names.add(node.name)
    return names
def _sp01_tree_imports(tree: ast.AST) -> tuple[bool, set[str]]:
    has_module = False
    api_names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            if any(alias.name == _SP01_MODULE_ALIAS for alias in node.names):
                has_module = True
        elif isinstance(node, ast.ImportFrom) and not node.level \
                and node.module == _SP01_MODULE_ALIAS:
            if any(alias.name == "*" for alias in node.names):
                api_names.update(_SUBPROCESS_TEXT_APIS)
            else:
                api_names.update(
                    alias.asname or alias.name for alias in node.names
                    if alias.name in _SUBPROCESS_TEXT_APIS)
    return has_module, api_names
def _module_api_scope_imports(
        scope: ast.AST, modules: frozenset[str], apis: frozenset[str]
) -> tuple[dict[str, str], dict[str, _ModuleApiBinding]]:
    module_names: dict[str, str] = {}
    from_names: dict[str, _ModuleApiBinding] = {}
    for node in iter_scope_nodes(scope):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module = _module_api_import_module(alias, modules)
                if module is not None:
                    module_names[alias.asname or alias.name.split('.')[0]] = module
        elif isinstance(node, ast.ImportFrom):
            _module_api_collect_from_bindings(
                node, from_names, modules, apis)
    return module_names, from_names
class _ModuleApiScopeBindings(ScopeEventIndex):
    def __init__(self, tree: ast.AST, modules: frozenset[str],
                 apis: frozenset[str]) -> None:
        super().__init__(tree)
        self._modules = modules
        self._apis = apis
        self._imports: dict[int, tuple[
            dict[str, str], dict[str, _ModuleApiBinding]]] = {}
        self._shadow: dict[int, set[str]] = {}
        self._inherited_params_cache: dict[int, frozenset[str]] = {}
        self._external_declaration_cache: dict[int, dict[str, bool]] = {}
        self._external_event_cache: dict[int, dict] = {}
        self._tree = tree
        self._binding_positions = _fm02_binding_positions(tree)
        self._outer_evaluation_scopes = _outer_evaluation_scopes(tree)
    def _chain(self, node: ast.AST) -> list[ast.AST]:
        return _evaluation_scope_chain(
            node, self._parents, self._outer_evaluation_scopes)
    def _definition_type_param_shadows(self, node: ast.AST,
                                       name: str) -> bool:
        current = self._parents.get(id(node))
        while current is not None:
            if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef)):
                names = {getattr(param, 'name', '')
                         for param in getattr(current, 'type_params', ())}
                if name in names and any(
                        candidate is node
                        for root in _definition_type_param_roots(current)
                        for candidate in walk_nodes(root)):
                    return True
            current = self._parents.get(id(current))
        return False
    def _binding_api(self, binding: _ModuleApiBinding | None,
                     attr: str | None) -> str | None:
        if binding is None:
            return None
        _module, member = binding
        if attr is None:
            return member if member in self._apis else None
        return attr if not member and attr in self._apis else None
    def resolve_api(self, node: ast.AST, name: str,
                    attr: str | None) -> tuple[bool, str | None]:
        if self._definition_type_param_shadows(node, name):
            return True, None
        deferred = False
        chain = self._chain(node)
        for index, scope in enumerate(chain):
            if (isinstance(scope, _FM02_FUNCTION_NODES)
                    and self._external_declarations(scope).get(name) is True):
                chain = [*chain[:index + 1], self._tree]
                break
        for scope in chain:
            if isinstance(scope, ast.ClassDef):
                own_type_params = {
                    getattr(param, 'name', '')
                    for param in getattr(scope, 'type_params', ())}
                if (name in own_type_params
                        or name in self._inherited_type_params(scope)):
                    return True, None
            if isinstance(scope, COMP_SCOPE_NODES):
                if _comprehension_shadows(scope, node, name):
                    return True, None
                if name in self._comprehension_type_params(scope):
                    return True, None
                continue
            if isinstance(scope, (ast.Module, ast.ClassDef)):
                found, binding = self._resolve_event(
                    scope, name, node, latest=deferred)
            else:
                found, binding = self._static_resolve(
                    scope, name, node, latest=deferred)
            if found:
                return True, self._binding_api(binding, attr)
            if isinstance(scope, _FM02_FUNCTION_NODES):
                deferred = True
        return False, None
    def _external_declarations(self, scope: ast.AST) -> dict[str, bool]:
        cached = self._external_declaration_cache.get(id(scope))
        if cached is None:
            cached = {
                name: isinstance(node, ast.Global)
                for node in _module_api_iter_binding_nodes(scope)
                if isinstance(node, (ast.Global, ast.Nonlocal))
                for name in node.names
            }
            self._external_declaration_cache[id(scope)] = cached
        return cached
    def _external_scope_events(self, scope: ast.AST) -> dict:
        cached = self._external_event_cache.get(id(scope))
        if cached is not None:
            return cached
        events: dict = {}
        for node in _module_api_iter_binding_nodes(scope):
            if isinstance(node, (ast.Global, ast.Nonlocal)):
                continue
            self._record_binding_event(events, node, scope, set())
        for values in events.values():
            values.sort(key=lambda event: event[0])
        self._external_event_cache[id(scope)] = events
        return events
    def _resolve_external_event(
            self, scope: ast.AST, name: str, node: ast.AST, latest: bool
    ) -> tuple[bool, _ModuleApiBinding | None]:
        events = self._external_scope_events(scope).get(name, [])
        if latest:
            return (True, events[-1][1]) if events else (False, None)
        return self._prior_value(events, node)
    def _static_resolve(
            self, scope: ast.AST, name: str, node: ast.AST, latest: bool
    ) -> tuple[bool, _ModuleApiBinding | None]:
        if name in self._external_declarations(scope):
            return self._resolve_external_event(scope, name, node, latest)
        module_names, from_names = self._scope_imports(scope)
        if name in module_names or name in from_names:
            found, binding = self._resolve_event(
                scope, name, node, latest=latest)
            return True, binding if found else None
        if name in self._shadow_names(scope):
            return True, None
        if self._scope_events(scope).get(name):
            return self._resolve_event(scope, name, node, latest=latest)
        return False, None
    def _resolve_event(
            self, scope: ast.AST, name: str, node: ast.AST, latest: bool
    ) -> tuple[bool, _ModuleApiBinding | None]:
        events = self._scope_events(scope).get(name, [])
        if latest:
            return (True, events[-1][1]) if events else (False, None)
        return self._prior_value(events, node)
    def _inherited_type_params(self, scope: ast.AST) -> frozenset[str]:
        cached = self._inherited_params_cache.get(id(scope))
        if cached is not None:
            return cached
        names: set[str] = set()
        current = self._parents.get(id(scope))
        while current is not None:
            if isinstance(current, ast.ClassDef):
                names.update(
                    _name for _name in
                    (getattr(_param, "name", "")
                     for _param in getattr(current, "type_params", ()))
                    if _name)
            current = self._parents.get(id(current))
        cached = frozenset(names)
        self._inherited_params_cache[id(scope)] = cached
        return cached
    def _comprehension_type_params(self, scope: ast.AST) -> frozenset[str]:
        current = self._parents.get(id(scope))
        while current is not None:
            if isinstance(current, COMP_SCOPE_NODES):
                current = self._parents.get(id(current))
                continue
            if isinstance(current, (ast.Module, *_FM02_FUNCTION_NODES,
                                    ast.ClassDef)):
                break
            current = self._parents.get(id(current))
        if isinstance(current, ast.ClassDef):
            return self._inherited_type_params(scope)
        return frozenset()
    def _shadow_names(self, scope: ast.AST) -> set[str]:
        cached = self._shadow.get(id(scope))
        if cached is None:
            cached = (_module_api_scope_shadow_names(
                scope, self._modules, self._apis)
                | self._inherited_type_params(scope))
            self._shadow[id(scope)] = cached
        return cached
    def _scope_imports(self, scope: ast.AST) -> tuple[
            dict[str, str], dict[str, _ModuleApiBinding]]:
        cached = self._imports.get(id(scope))
        if cached is None:
            cached = _module_api_scope_imports(
                scope, self._modules, self._apis)
            self._imports[id(scope)] = cached
        return cached
    def _propagate_immediate_class_globals(
            self, scope: ast.AST, events: dict) -> None:
        stack = list(_module_api_scope_body(scope))
        while stack:
            node = stack.pop()
            if isinstance(node, (*_FM02_FUNCTION_NODES, *COMP_SCOPE_NODES)):
                continue
            if isinstance(node, ast.ClassDef):
                names: set[str] = set()
                class_events: dict = {}
                external_names: set[str] = set()
                for child in _module_api_iter_binding_nodes(node):
                    if isinstance(child, ast.Global):
                        names.update(child.names)
                    self._record_binding_event(
                        class_events, child, node, external_names)
                for name in names:
                    events.setdefault(name, []).extend(
                        class_events.get(name, ()))
                stack.extend(node.body)
                continue
            stack.extend(ast.iter_child_nodes(node))
    def _scope_events(
            self, scope: ast.AST
    ) -> dict[str, list[tuple[tuple[int, int], _ModuleApiBinding | None]]]:
        cached = self._events.get(id(scope))
        if cached is not None:
            return cached
        events: dict[
            str, list[tuple[tuple[int, int], _ModuleApiBinding | None]]] = {}
        external_names: set[str] = set()
        for node in _module_api_iter_binding_nodes(scope):
            self._record_binding_event(events, node, scope, external_names)
        self._propagate_immediate_class_globals(scope, events)
        for values in events.values():
            values.sort(key=lambda event: event[0])
        self._events[id(scope)] = events
        return events
    def _add_binding_event(
            self, events: dict[str, list[
                tuple[tuple[int, int], _ModuleApiBinding | None]]],
            name: str, node: ast.AST,
            value: _ModuleApiBinding | None) -> None:
        position = self._binding_positions.get(
            id(node), (getattr(node, "lineno", -1),
                       getattr(node, "col_offset", -1)))
        events.setdefault(name, []).append((position, value))
    def _record_binding_event(
            self, events: dict[str, list[
                tuple[tuple[int, int], _ModuleApiBinding | None]]],
            node: ast.AST, scope: ast.AST, external_names: set[str]) -> None:
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            external_names.update(node.names)
            return
        pattern_names = _module_api_pattern_bindings(node)
        if pattern_names:
            for pattern_name in pattern_names:
                if pattern_name not in external_names:
                    self._add_binding_event(events, pattern_name, node, None)
            return
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            self._record_import_events(events, node, external_names)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node is not scope and node.name not in external_names:
                self._add_binding_event(events, node.name, node, None)
            return
        if isinstance(node, ast.ExceptHandler) and node.name:
            if node.name not in external_names:
                self._add_binding_event(events, node.name, node, None)
            return
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and node.id not in external_names):
            parent = self._parents.get(id(node))
            if (isinstance(scope, (ast.Module, ast.ClassDef))
                    and isinstance(parent, ast.AnnAssign)
                    and parent.target is node and parent.value is None):
                return
            self._add_binding_event(events, node.id, node, None)
    def _record_import_events(
            self, events: dict[str, list[
                tuple[tuple[int, int], _ModuleApiBinding | None]]],
            node: ast.Import | ast.ImportFrom, external_names: set[str]) -> None:
        for alias in node.names:
            if alias.name == "*":
                if isinstance(node, ast.ImportFrom):
                    known = not node.level and node.module in self._modules
                    for api in self._apis:
                        if api not in external_names:
                            binding = (node.module, api) if known else None
                            self._add_binding_event(events, api, node, binding)
                continue
            bound, binding = self._import_binding(node, alias)
            if bound not in external_names:
                self._add_binding_event(events, bound, node, binding)
    def _import_binding(
            self, node: ast.Import | ast.ImportFrom, alias: ast.alias
    ) -> tuple[str, _ModuleApiBinding | None]:
        bound = alias.asname or alias.name.split(".")[0]
        if isinstance(node, ast.Import):
            module = _module_api_import_module(alias, self._modules)
            return bound, (module, "") if module is not None else None
        if (not node.level and node.module in self._modules
                and alias.name in self._apis):
            return bound, (node.module, alias.name)
        return bound, None
def _sp01_call_api(node: ast.Call,
                   bindings: _ModuleApiScopeBindings) -> str | None:
    func = node.func
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return bindings.resolve_api(node, func.value.id, func.attr)[1]
    if isinstance(func, ast.Name):
        return bindings.resolve_api(node, func.id, None)[1]
    return None
def _sp01_positional_text_enabled(node: ast.Call) -> bool:
    if len(node.args) <= 11:
        return False
    if any(isinstance(arg, ast.Starred) for arg in node.args[:12]):
        return False
    universal_newlines = node.args[11]
    return (isinstance(universal_newlines, ast.Constant)
            and bool(universal_newlines.value))
def _sp01_missing_encoding(node: ast.Call,
                           bindings: _ModuleApiScopeBindings) -> str | None:
    api = _sp01_call_api(node, bindings)
    if api is None:
        return None
    errors = kw_arg(node, "errors")
    errors_enable_text = (
        errors is not None and isinstance(errors.value, ast.Constant)
        and bool(errors.value.value))
    if not (_sp01_positional_text_enabled(node)
            or _kw_constant_truthy(node, "text")
            or _kw_constant_truthy(node, "universal_newlines")
            or errors_enable_text):
        return None
    if any(kw.arg is None for kw in node.keywords):
        return None
    kw_encoding = kw_arg(node, "encoding")
    if kw_encoding is None or is_none_literal(kw_encoding.value):
        return api
    return None
def check_SP01(tree: ast.AST, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    has_module, api_names = _sp01_tree_imports(tree)
    if not has_module and not api_names:
        return issues
    bindings = _ModuleApiScopeBindings(
        tree, frozenset({_SP01_MODULE_ALIAS}), _SUBPROCESS_TEXT_APIS)
    for node in walk_nodes(tree):
        api = (_sp01_missing_encoding(node, bindings)
               if isinstance(node, ast.Call) else None)
        if api is None:
            continue
        issues.append(DiagnoseFinding(
            id="SP-01", severity="P1", dimension="subprocess",
            file=filepath, line=node.lineno, col_offset=node.col_offset,
            title="subprocess 文本模式未指定 encoding",
            description=(f"subprocess.{api}() 文本模式未指定 encoding"
                         "：Windows 下按 GBK 解码，非 ASCII 输出崩溃"),
            suggestion=("根因: text/universal_newlines/errors 均会启用文本模式，"
                        "未指定 encoding 时解码用系统本地代码页（Windows 为 GBK），"
                        "UTF-8 输出即 UnicodeDecodeError。"
                        "该问题属于跨平台编码类别。\n"
                        "修复策略: 显式指定 encoding='utf-8'（必要时加 "
                        "errors='replace' 兜底）\n"
                        "参考标准: subprocess 文档 / PEP 540"),
        ))
    return apply_rule_suppress(issues, source_lines, 'SP-01')
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "rule_bindings": {
                'AT02': check_AT02,
                'CF01': check_CF01, 'CF02': check_CF02,
                'EN01': check_EN01, 'EN03': check_EN03,
                'FM01': check_FM01, 'FM02': check_FM02, 'FM03': check_FM03,
                'GF02': check_GF02,
                'IN01': check_IN01,
            },
            "traps_bindings": {'SP01': check_SP01},
        },
    }

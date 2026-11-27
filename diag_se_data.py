from __future__ import annotations

import ast
import bisect
import builtins
import logging
import re
from collections.abc import Callable, Iterator
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    collect_shadow_bindings,
)
from jwsgj.diag_shared_ast_nodes import (
    TYPE_ALIAS_NODES,
    assign_targets_value,
    build_parent_map,
    collect_param_names,
    is_static_literal_expr,
    iter_evaluation_scope_chain,
    iter_module_scope_nodes,
    iter_own_scope,
    iter_unpack_target_names,
    pattern_capture_name,
    resolve_call_name,
    resolve_module_member_call,
    segments_equal,
    split_identifier,
)
from jwsgj.diag_shared_ast_views import (
    collect_module_bindings_detailed,
    file_bound_names,
    iter_nodes,
    materialized_index,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    decode_source_bytes,
    is_regex_pattern_text,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
    get_code_snippet,
    string_comment_spans,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    ImplicitFlowFinding,
    VulnerabilityFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    VulnerabilityCategory,
    normalize_filepath,
)

__all__ = [
    "CREDENTIAL_KEYWORDS",
    "CREDENTIAL_PATTERNS",
    "SENSITIVE_VAR_PATTERNS",
    "ImplicitFlowAnalyzer",
    "analyze_implicit_flow",
    "check_SE03",
    "check_SE10",
    "check_SE28",
    "check_SE36",
    "check_hardcoded_credentials",
    "is_placeholder_secret",
    "is_sensitive_name",
    "scan_env_default_secrets",
    "scan_hardcoded_secrets",
]
_log = logging.getLogger(__name__)
_DEFAULT_FLOW_LABEL = "<string>"
_DEFAULT_FILEPATH = ""
def _normalize_text_source(source: Any) -> str:
    if isinstance(source, (bytes, bytearray)):
        text = decode_source_bytes(bytes(source))
    elif isinstance(source, str):
        text = source
    else:
        return ""
    if "\r" in text:
        text = text.replace("\r\n", "\n").replace("\r", "\n")
    return text
def _coerce_tree(tree: Any) -> ast.AST | None:
    return tree if isinstance(tree, ast.AST) else None
def _coerce_index(index: Any) -> list | None:
    return list(index) if isinstance(index, (list, tuple)) else None
_AUTHOR_NON_CREDENTIAL = re.compile(r'author(?!ization)')
def _auth_sensitive(name_lower: str) -> bool:
    if 'auth' not in name_lower:
        return False
    return not _AUTHOR_NON_CREDENTIAL.search(name_lower)
_SENSITIVE_SAFE_SUFFIXES = ("_used", "_budget", "_count", "_limit", "_max", "_size", "_len", "_total", "_required", "_enabled", "_disabled", "_mode", "_type", "_flag", "_check", "_status")
_SENSITIVE_SAFE_PREFIXES = ("is_", "has_", "should_", "can_")
_MIN_SECRET_LEN = 8
_SENSITIVE_VAR_PATTERNS = (
    "password", "passwd", "pwd", "secret", "token", "api_key", "apikey",
    "private_key", "ssh_key", "access_key", "credential", "cookie",
    "session_id", "ssn", "auth", "auth_token", "access_token",
    "refresh_token", "csrf_token", "nonce", "credit_card",
    "social_security", "encryption_key", "master_key",
    "seed_phrase", "recovery_seed", "wallet_seed", "mnemonic",
)
def is_sensitive_name(name: str) -> bool:
    if not isinstance(name, str):
        return False
    return _name_is_sensitive(name)
_TRY_NODE_TYPES = (ast.Try, getattr(ast, "TryStar", ast.Try))
_MSG_SYNTAX_ERROR_SKIP = "[ImplicitFlow] 源码含语法错误，跳过检测"
_REF_STANDARDS = "参考标准: CWE-203/CWE-208/CWE-209 / OWASP"
def _leak_suggestion(cause: str, strategy: str) -> str:
    return (f"根因: {cause}。该问题属于安全类别。\n"
            f"修复策略: {strategy}\n"
            f"{_REF_STANDARDS}")
_STRUCTURAL_COLLECTION_SUFFIXES = (
    "tokens", "_regex", "_pattern", "_patterns",
    "_starts", "_spans", "_lines", "_nodes", "_pairs",
)
def _is_structural_collection(name: str) -> bool:
    lower = name.lower()
    return any(lower.endswith(sfx) for sfx in _STRUCTURAL_COLLECTION_SUFFIXES)
def _loop_sensitive_expr(node: ast.AST) -> ast.AST | None:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return node.iter
    if isinstance(node, ast.While):
        return node.test
    return None
def _iter_inline_bodies(stmt: ast.stmt) -> Iterator[list[ast.stmt]]:
    _match_type = getattr(ast, "Match", None)
    if _match_type is not None and isinstance(stmt, _match_type):
        for case in stmt.cases:
            yield case.body
        return
    if isinstance(stmt, (ast.If, ast.For, ast.AsyncFor, ast.While)):
        yield stmt.body
        if stmt.orelse:
            yield stmt.orelse
        return
    if isinstance(stmt, _TRY_NODE_TYPES):
        yield stmt.body
        for handler in stmt.handlers:
            yield handler.body
        if stmt.orelse:
            yield stmt.orelse
        if stmt.finalbody:
            yield stmt.finalbody
        return
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        yield stmt.body
def _describe_observable(stmt: ast.stmt) -> str:
    if isinstance(getattr(stmt, 'value', None), (ast.Yield, ast.YieldFrom)):
        return "yield"
    if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
        return resolve_call_name(stmt.value)
    if isinstance(stmt, ast.Return):
        return "return"
    if isinstance(stmt, ast.Raise) and isinstance(stmt.exc, ast.Call):
        return f"raise {resolve_call_name(stmt.exc)}"
    return "observable_output"
SENSITIVE_VAR_PATTERNS: frozenset[str] = frozenset(_SENSITIVE_VAR_PATTERNS)
_PATTERN_SEGMENTS: frozenset[tuple[str, ...]] = frozenset(
    split_identifier(pattern) for pattern in _SENSITIVE_VAR_PATTERNS
)
def _scope_binding_targets(node: ast.AST) -> list[ast.expr]:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    if isinstance(node, ast.AnnAssign):
        return [node.target] if node.value is not None else []
    if isinstance(node, (ast.AugAssign, ast.NamedExpr)):
        return [node.target]
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    return []
def _bound_target_names(node: ast.AST) -> set[str]:
    names: set[str] = set()
    for target in _scope_binding_targets(node):
        names.update(iter_unpack_target_names(target))
    return names
def _value_root_name(value: ast.AST | None) -> str:
    node = value
    while isinstance(node, (ast.Call, ast.Attribute, ast.Subscript)):
        node = node.func if isinstance(node, ast.Call) else node.value
    return node.id if isinstance(node, ast.Name) else ""
_STATIC_CONTAINER_CTORS: frozenset[str] = frozenset(
    {'frozenset', 'set', 'tuple', 'list', 'dict'})
def _is_static_module_constant_value(node: ast.AST | None) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return all(_is_static_module_constant_value(elt) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return all(key is not None
                   and _is_static_module_constant_value(key)
                   and _is_static_module_constant_value(value)
                   for key, value in zip(node.keys, node.values, strict=True))
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in _STATIC_CONTAINER_CTORS
            and not node.keywords):
        return all(_is_static_module_constant_value(arg) for arg in node.args)
    return node is not None and is_static_literal_expr(node)
def _module_scope_bindings(tree: ast.Module
                           ) -> tuple[frozenset[str], frozenset[int]]:
    names: set[str] = set()
    dynamic_names: set[str] = set()
    node_ids: set[int] = set()
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if not isinstance(node, ast.stmt) or isinstance(node, ast.ClassDef):
            continue
        node_ids.add(id(node))
        value = getattr(node, "value", None)
        is_static = (not isinstance(node, ast.AugAssign)
                     and _is_static_module_constant_value(value))
        for target in _scope_binding_targets(node):
            for name in iter_unpack_target_names(target):
                if not _is_constant_style_name(name):
                    continue
                if is_static:
                    if not (isinstance(value, ast.Constant)
                            and isinstance(value.value, (str, bytes))):
                        names.add(name)
                else:
                    dynamic_names.add(name)
    return frozenset(names - dynamic_names), frozenset(node_ids)
def _collect_sensitive_vars(tree: ast.Module,
                            module_constants: frozenset[str] | None = None,
                            module_nodes: frozenset[int] | None = None
                            ) -> set[str]:
    if module_constants is None or module_nodes is None:
        module_constants, module_nodes = _module_scope_bindings(tree)
    sensitive: set[str] = set()
    for node in tree_nodes(tree):
        _scope_constants = (module_constants if id(node) in module_nodes
                            else frozenset())
        _collect_assignment_bindings(node, sensitive, _scope_constants)
        _collect_target_bindings(node, sensitive, _scope_constants)
        _collect_introduced_names(node, sensitive, _scope_constants)
    return sensitive
def _collect_assignment_bindings(node: ast.AST, out: set[str],
                                 module_constants: frozenset[str]) -> None:
    if isinstance(node, ast.Assign):
        for target in node.targets:
            _add_sensitive_bindings(target, out, module_constants)
        return
    if isinstance(node, ast.AnnAssign):
        _add_sensitive_bindings(node.target, out, module_constants)
        return
    if isinstance(node, ast.AugAssign):
        _add_sensitive_bindings(node.target, out, module_constants)
        return
    if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
        _add_sensitive_name(node.target.id, out, module_constants)
def _collect_target_bindings(node: ast.AST, out: set[str],
                             module_constants: frozenset[str]) -> None:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        _add_sensitive_bindings(node.target, out, module_constants)
        return
    if isinstance(node, (ast.With, ast.AsyncWith)):
        for item in node.items:
            if item.optional_vars is None:
                continue
            _add_sensitive_bindings(item.optional_vars, out, module_constants)
        return
    if isinstance(node, ast.comprehension):
        _add_sensitive_bindings(node.target, out, module_constants)
def _collect_introduced_names(node: ast.AST, out: set[str],
                              module_constants: frozenset[str]) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        for _p in collect_param_names(node):
            if _name_is_sensitive(_p, module_constants):
                out.add(_p)
    elif (isinstance(node, ast.ExceptHandler)
          and node.name
          and _name_is_sensitive(node.name, module_constants)):
        out.add(node.name)
    elif isinstance(node, (ast.MatchAs, ast.MatchStar)):
        _capture = getattr(node, "name", None)
        if isinstance(_capture, str):
            _add_sensitive_name(_capture, out, module_constants)
    elif isinstance(node, ast.MatchMapping):
        _rest = getattr(node, "rest", None)
        if isinstance(_rest, str):
            _add_sensitive_name(_rest, out, module_constants)
def _add_sensitive_name(name: str, out: set[str],
                        module_constants: frozenset[str]) -> None:
    if _name_is_sensitive(name, module_constants):
        out.add(name)
def _binding_target_names(target: ast.AST) -> Iterator[str]:
    if isinstance(target, ast.Name):
        yield target.id
        return
    if isinstance(target, ast.Attribute):
        yield target.attr
        return
    if isinstance(target, ast.Subscript):
        _key = _se03_target_name(target)
        if _key is not None:
            yield _key
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        for _element in target.elts:
            yield from _binding_target_names(_element)
        return
    if isinstance(target, ast.Starred):
        yield from _binding_target_names(target.value)
def _add_sensitive_bindings(target: ast.expr, out: set[str],
                            module_constants: frozenset[str]) -> None:
    for _name in _binding_target_names(target):
        if _name_is_sensitive(_name, module_constants):
            out.add(_name)
def _deleted_target_names(target: ast.AST) -> Iterator[str]:
    if isinstance(target, ast.Name):
        yield target.id
    elif isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            yield from _deleted_target_names(element)
def _is_constant_style_name(name: str) -> bool:
    core = str(name).lstrip("_")
    return bool(core) and core == core.upper() and any(
        ch.isalpha() for ch in core)
def _segments_match_pattern(segs: tuple, pattern: tuple) -> bool:
    width = len(pattern)
    if not width or len(segs) < width:
        return False
    return any(
        all(segments_equal(segs[start + offset], pattern[offset])
            for offset in range(width))
        for start in range(len(segs) - width + 1))
def _name_is_sensitive(name: str,
                       module_constants: frozenset[str] = frozenset()) -> bool:
    if name in module_constants:
        return False
    lower = name.lower()
    if any(lower.endswith(suffix) for suffix in _SENSITIVE_SAFE_SUFFIXES):
        return False
    if lower.startswith(_SENSITIVE_SAFE_PREFIXES):
        return False
    if _auth_sensitive(lower):
        return True
    segs = split_identifier(name)
    return any(_segments_match_pattern(segs, pat)
               for pat in _PATTERN_SEGMENTS)
def _parse_flow_tree(source_code: str) -> ast.Module | None:
    try:
        return ast.parse(source_code)
    except SyntaxError:
        _log.warning(_MSG_SYNTAX_ERROR_SKIP)
        return None
    except (ValueError, RecursionError, MemoryError) as _parse_err:
        _log.warning(
            "[ImplicitFlow] 源码不可解析(%s: %s)，跳过检测",
            type(_parse_err).__name__, _parse_err)
        return None
class _LeakSpec(NamedTuple):
    severity: str
    confidence: float
    cause: str
    strategy: str
    cwe_id: str
_LEAK_SPECS: dict[str, _LeakSpec] = {
    "conditional_leak": _LeakSpec(
        "MEDIUM", 0.7,
        '基于敏感数据的条件分支可能产生可观测的输出差异, '
        '导致侧信道信息泄露',
        '避免基于敏感数据的条件分支产生可观测的输出差异',
        "CWE-203"),
    "loop_leak": _LeakSpec(
        "MEDIUM", 0.65,
        '循环次数依赖敏感数据, 攻击者可通过观察循环执行时间推断敏感信息',
        '循环耗时与迭代次数应与敏感数据无关，将依赖敏感数据的循环'
        '改为常数时间处理',
        "CWE-208"),
    "exception_leak": _LeakSpec(
        "LOW", 0.5,
        '异常处理中暴露了敏感数据的上下文信息, '
        '攻击者可利用异常消息推断敏感数据',
        '异常处理中避免暴露敏感数据的上下文信息',
        "CWE-209"),
}
_SCOPE_DEF_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_REBIND_NODE_TYPES = (ast.Assign, ast.AugAssign, ast.AnnAssign,
                      ast.NamedExpr, ast.For, ast.AsyncFor, ast.With,
                      ast.AsyncWith, ast.Delete)
_PATTERN_BINDING_NODES = (ast.MatchAs, ast.MatchStar, ast.MatchMapping)
_COMP_SCOPE_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                     ast.GeneratorExp)
_SCOPE_MISS = object()
class _BindingEvent(NamedTuple):
    line: int
    column: int
    kind: str
    identity: str = ""
def _scope_key(scope: str, name: str) -> str:
    return f"{scope}.{name}" if scope else name
class _ScopeBindings:
    def __init__(self, tree: ast.AST | None, *,
                 derived_module_names: frozenset[str] = frozenset(),
                 assignment_aliases: frozenset[str] = frozenset(),
                 real_import_modules: frozenset[str] | None = None) -> None:
        self._scope_of: dict[int, str] = {}
        self._locals: dict[str, frozenset[str]] = {}
        self._imports: dict[str, frozenset[str]] = {}
        self._import_identities: dict[str, dict[str, str]] = {}
        self._star_import_modules: dict[str, list[str]] = {}
        self._binding_events: dict[
            str, dict[str, list[_BindingEvent]]] = {}
        self._real_import_modules = real_import_modules
        self._rebound: dict[str, frozenset[str]] = {}
        self._class_scopes: frozenset[str] = frozenset()
        self._global_names: dict[str, frozenset[str]] = {}
        self._parents: dict[int, ast.AST] = {}
        self._derived_module_names = derived_module_names
        self._assignment_aliases = assignment_aliases
        self._alias_sources: dict[str, dict[str, str]] = {}
        self._inner_scopes: dict[int, str] = {}
        if not isinstance(tree, ast.AST):
            return
        self._scope_of = build_scope_index(tree)
        local, _global, class_scopes = collect_shadow_bindings(tree)
        self._locals = local
        self._global_names = _global
        self._class_scopes = class_scopes
        self._parents = build_parent_map(tree)
        self._imports, self._rebound = self._scan_bindings(tree)
    @staticmethod
    def _node_position(node: ast.AST) -> tuple[int, int]:
        return (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
    def _record_binding(self, scope: str, name: str, node: ast.AST,
                        kind: str, identity: str = "") -> None:
        line, column = self._node_position(node)
        event = _BindingEvent(line, column, kind, identity)
        self._binding_events.setdefault(scope, {}).setdefault(
            name, []).append(event)
    def _scan_bindings(self, tree: ast.AST) -> tuple[dict[str, frozenset[str]],
                                                     dict[str, frozenset[str]]]:
        imports: dict[str, set[str]] = {}
        rebound: dict[str, set[str]] = {}
        for node in tree_nodes(tree):
            if not isinstance(node, (*_SCOPE_DEF_NODES, ast.Import,
                                      ast.ImportFrom, ast.ExceptHandler,
                                      *_REBIND_NODE_TYPES,
                                      *_PATTERN_BINDING_NODES,
                                      *TYPE_ALIAS_NODES)):
                continue
            scope = self._binding_scope(node)
            if isinstance(node, ast.Import):
                for alias in node.names:
                    bound = alias.asname or alias.name.split(".", 1)[0]
                    if bound:
                        imports.setdefault(scope, set()).add(bound)
                        self._import_identities.setdefault(scope, {})[bound] = (
                            alias.name)
                        self._record_binding(
                            scope, bound, node, "import", alias.name)
                continue
            if isinstance(node, ast.ImportFrom):
                module = "." * node.level + (node.module or "")
                for alias in node.names:
                    if alias.name == "*":
                        self._star_import_modules.setdefault(scope, []).append(
                            module)
                        self._record_binding(scope, "*", node, "star", module)
                        continue
                    bound = alias.asname or alias.name
                    if bound:
                        imports.setdefault(scope, set()).add(bound)
                        identity = (f"{module}.{alias.name}" if module
                                    else alias.name)
                        self._import_identities.setdefault(scope, {})[bound] = (
                            identity)
                        self._record_binding(
                            scope, bound, node, "import", identity)
                continue
            if isinstance(node, _SCOPE_DEF_NODES):
                rebound.setdefault(scope, set()).add(node.name)
                self._record_binding(scope, node.name, node, "rebound")
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    inner_scope = self._inner_scope(node, scope)
                    rebound.setdefault(inner_scope, set()).update(
                        collect_param_names(node))
                    for param in collect_param_names(node):
                        self._record_binding(
                            inner_scope, param, node, "rebound")
                continue
            if isinstance(node, ast.Delete):
                for target in node.targets:
                    for name in _deleted_target_names(target):
                        if name in self._global_names.get(scope, frozenset()):
                            kind = "delete_global"
                        else:
                            kind = ("delete" if self._is_ordered_scope(scope)
                                    else "rebound")
                        rebound.setdefault(scope, set()).add(name)
                        self._record_binding(scope, name, node, kind)
                continue
            capture = pattern_capture_name(node)
            if capture is not None:
                rebound.setdefault(scope, set()).add(capture)
                self._record_binding(scope, capture, node, "rebound")
                continue
            if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
                target = node.name
                if isinstance(target, ast.Name):
                    rebound.setdefault(scope, set()).add(target.id)
                    self._record_binding(scope, target.id, node, "rebound")
                continue
            value = getattr(node, "value", None)
            derived = _value_root_name(value)
            for name in _bound_target_names(node):
                if name == derived:
                    continue
                if (name in self._assignment_aliases
                        and derived in self._derived_module_names
                        and isinstance(value, ast.Name)):
                    imports.setdefault(scope, set()).add(name)
                    self._alias_sources.setdefault(scope, {})[name] = derived
                    self._record_binding(scope, name, node, "alias", derived)
                else:
                    rebound.setdefault(scope, set()).add(name)
                    self._record_binding(scope, name, node, "rebound")
        return ({key: frozenset(value) for key, value in imports.items()},
                {key: frozenset(value) for key, value in rebound.items()})
    def _is_ordered_scope(self, scope: str) -> bool:
        return not scope or scope in self._class_scopes
    def _inner_scope(self, node: ast.AST, scope: str) -> str:
        cached = self._inner_scopes.get(id(node))
        if cached is not None:
            return cached
        inner = _scope_key(scope, node.name)
        for child in iter_own_scope(node):
            child_scope = self._scope_of.get(id(child), _SCOPE_MISS)
            if child_scope is not _SCOPE_MISS and child_scope != scope:
                inner = child_scope
                break
        self._inner_scopes[id(node)] = inner
        return inner
    def _binding_scope(self, node: ast.AST) -> str:
        scope = self._scope_of.get(id(node), _SCOPE_MISS)
        if scope is not _SCOPE_MISS:
            return scope
        parent = self._parents.get(id(node))
        while parent is not None:
            if isinstance(parent, _SCOPE_DEF_NODES):
                return self._inner_scope(
                    parent, self._scope_of.get(id(parent), ""))
            parent = self._parents.get(id(parent))
        return ""
    def _chain(self, scope: str) -> tuple[str, ...]:
        if not scope:
            return ("",)
        parts = scope.split(".")
        chain = [key for key in (".".join(parts[:size])
                                 for size in range(len(parts), 0, -1))
                 if key == scope or key not in self._class_scopes]
        chain.append("")
        return tuple(chain)
    def _ordered_evaluation_scope(self, node: ast.AST,
                                  current_scope: str) -> str | None:
        evaluation_scopes = iter_evaluation_scope_chain(node, self._parents)
        if (evaluation_scopes
                and isinstance(evaluation_scopes[0],
                               (ast.Module, ast.ClassDef))):
            return current_scope
        return None
    def _branch_below(self, node: ast.AST, ancestor: ast.AST) -> ast.AST | None:
        current = node
        while current is not ancestor:
            parent = self._parents.get(id(current))
            if parent is None:
                return None
            if parent is ancestor:
                return current
            current = parent
        return None
    def _comprehension_shadowed(self, node: ast.AST, name: str) -> bool:
        current = node
        while current is not None:
            parent = self._parents.get(id(current))
            if isinstance(parent, _COMP_SCOPE_NODES):
                generators = parent.generators
                owner_index = next((
                    index for index, generator in enumerate(generators)
                    if self._branch_below(node, generator) is not None), None)
                if owner_index is None:
                    visible = generators
                else:
                    generator = generators[owner_index]
                    branch = self._branch_below(node, generator)
                    count = owner_index + int(branch in generator.ifs)
                    visible = generators[:count]
                if any(name in iter_unpack_target_names(generator.target)
                       for generator in visible):
                    return True
            current = parent
        return False
    def is_shadowed(self, node: ast.AST, name: str, *,
                    real_imports: bool = False) -> bool:
        current_scope = self._scope_of.get(id(node), "")
        chain = self._chain(current_scope)
        evaluation_scopes = iter_evaluation_scope_chain(node, self._parents)
        if any(isinstance(scope, ast.Lambda)
               and name in collect_param_names(scope)
               for scope in evaluation_scopes):
            return True
        if self._comprehension_shadowed(node, name):
            return True
        ordered_scope = self._ordered_evaluation_scope(node, current_scope)
        if real_imports:
            return self._real_import_shadowed(
                name, chain, frozenset(), node, ordered_scope)
        ordered_local = bool(evaluation_scopes) and isinstance(
            evaluation_scopes[0], (ast.Module, ast.ClassDef))
        for scope in chain:
            if name not in self._locals.get(scope, frozenset()):
                continue
            if ordered_local and scope == current_scope:
                if self._latest_binding_event(scope, name, node) is not None:
                    return True
                continue
            return True
        return False
    @staticmethod
    def _deleted_global_identity(name: str) -> str:
        return f"builtins.{name}" if hasattr(builtins, name) else ""
    def import_identity(self, node: ast.AST, name: str) -> str | None:
        current_scope = self._scope_of.get(id(node), "")
        ordered_scope = self._ordered_evaluation_scope(node, current_scope)
        return self._visible_import_identity(
            name, self._chain(current_scope), frozenset(), node, ordered_scope)
    def _visible_import_identity(
            self, name: str, chain: tuple[str, ...],
            seen: frozenset[tuple[str, str]], node: ast.AST,
            ordered_scope: str | None) -> str | None:
        for scope in chain:
            event = self._latest_binding_event(scope, name, node)
            if event is not None:
                if event.kind == "delete_global":
                    return self._deleted_global_identity(name)
                if event.kind == "delete":
                    if scope == ordered_scope:
                        continue
                    return ""
                if event.kind == "rebound":
                    return ""
                if event.kind == "alias":
                    key = (scope, name)
                    if key in seen:
                        return ""
                    return self._visible_import_identity(
                        event.identity, self._chain(scope), seen | {key}, node,
                        ordered_scope)
                if event.kind == "star":
                    return f"{event.identity}.*"
                return event.identity
            if scope == ordered_scope:
                continue
            if name in self._rebound.get(scope, frozenset()):
                return ""
            source = self._alias_sources.get(scope, {}).get(name)
            if source is not None:
                key = (scope, name)
                if key in seen:
                    return ""
                return self._visible_import_identity(
                    source, self._chain(scope), seen | {key}, node,
                    ordered_scope)
            if name in self._imports.get(scope, frozenset()):
                return self._import_identities.get(scope, {}).get(name, "")
            star_modules = self._star_import_modules.get(scope)
            if star_modules:
                return f"{star_modules[-1]}.*"
        return None
    def _real_import_identity_matches(self, identity: str) -> bool:
        if self._real_import_modules is None:
            return True
        return any(identity == module or identity.startswith(module + ".")
                   for module in self._real_import_modules)
    def _latest_binding_event(self, scope: str, name: str,
                              node: ast.AST) -> _BindingEvent | None:
        bindings = self._binding_events.get(scope, {})
        position = self._node_position(node)
        events = [
            event
            for bound_name in (name, "*")
            for event in bindings.get(bound_name, ())
            if (event.line, event.column) <= position
        ]
        return max(events, key=lambda event: (event.line, event.column),
                   default=None)
    def _binding_event_shadowed(
            self, event: _BindingEvent, scope: str, name: str,
            seen: frozenset[tuple[str, str]], node: ast.AST,
            ordered_scope: str | None) -> bool:
        if event.kind == "rebound":
            return True
        if event.kind == "alias":
            key = (scope, name)
            if key in seen:
                return True
            return self._real_import_shadowed(
                event.identity, self._chain(scope), seen | {key}, node,
                ordered_scope)
        return not self._real_import_identity_matches(event.identity)
    def _real_import_shadowed(self, name: str, chain: tuple[str, ...],
                              seen: frozenset[tuple[str, str]],
                              node: ast.AST,
                              ordered_scope: str | None) -> bool:
        for scope in chain:
            event = self._latest_binding_event(scope, name, node)
            if event is not None:
                if event.kind == "delete_global":
                    identity = self._deleted_global_identity(name)
                    return (not identity
                            or not self._real_import_identity_matches(identity))
                if event.kind == "delete":
                    if scope == ordered_scope:
                        continue
                    return True
                return self._binding_event_shadowed(
                    event, scope, name, seen, node, ordered_scope)
            if scope == ordered_scope:
                continue
            if name in self._rebound.get(scope, frozenset()):
                return True
            source = self._alias_sources.get(scope, {}).get(name)
            if source is not None:
                key = (scope, name)
                if key in seen:
                    return True
                return self._real_import_shadowed(
                    source, self._chain(scope), seen | {key}, node,
                    ordered_scope)
            if name in self._imports.get(scope, frozenset()):
                identity = self._import_identities.get(scope, {}).get(name, "")
                return not self._real_import_identity_matches(identity)
            star_modules = self._star_import_modules.get(scope)
            if star_modules:
                return not self._real_import_identity_matches(star_modules[-1])
        return False
class ImplicitFlowAnalyzer:
    OBSERVABLE_SINKS: ClassVar[set[str]] = {
        'print', 'jsonify', 'Response', 'HttpResponse', 'render_template',
    }
    _SINK_TAIL_NAMES: ClassVar[frozenset[str]] = frozenset(
        {'write', 'send', 'info', 'warning', 'warn', 'error',
         'debug', 'critical', 'exception', 'fatal', 'log', 'dumps'})
    def analyze(self, source_code: str | bytes | bytearray | None,
                file_path: str = _DEFAULT_FLOW_LABEL,
                _tree: ast.Module | None = None) -> list[ImplicitFlowFinding]:
        findings: list[ImplicitFlowFinding] = []
        file_path = normalize_filepath(file_path) or _DEFAULT_FLOW_LABEL
        if finding_scan_exempt(file_path):
            return findings
        tree = _tree if isinstance(_tree, ast.Module) else None
        if source_code is None:
            _log.debug("[ImplicitFlow] source_code 为 None，跳过检测")
        elif not isinstance(source_code, (str, bytes, bytearray)):
            _log.warning(
                "[ImplicitFlow] source_code 非文本类型 %s，跳过检测",
                type(source_code).__name__)
        source_code = _normalize_text_source(source_code)
        if not source_code and tree is None:
            return findings
        if tree is None:
            tree = _parse_flow_tree(source_code)
            if tree is None:
                return findings
        source_lines = source_code.split('\n')
        module_constants, module_nodes = _module_scope_bindings(tree)
        sensitive_vars = _collect_sensitive_vars(
            tree, module_constants, module_nodes)
        findings.extend(self._detect_conditional_leak(
            tree, source_lines, file_path, sensitive_vars, module_constants))
        findings.extend(self._detect_loop_leak(
            tree, source_lines, file_path, sensitive_vars, module_constants))
        findings.extend(self._detect_exception_leak(
            tree, source_lines, file_path, sensitive_vars, module_constants))
        return findings
    def _detect_conditional_leak(
        self, tree: ast.Module, source_lines: list[str], file_path: str,
        sensitive_vars: set[str], module_constants: frozenset[str],
    ) -> list[ImplicitFlowFinding]:
        findings: list[ImplicitFlowFinding] = []
        def _nested_if_sensitive(stmt: ast.stmt) -> bool:
            return (isinstance(stmt, ast.If)
                    and bool(self._find_sensitive_in_expr(
                        stmt.test, sensitive_vars, module_constants)))
        for node in tree_nodes(tree):
            if not isinstance(node, ast.If):
                continue
            used = self._find_sensitive_in_expr(
                node.test, sensitive_vars, module_constants)
            if not used:
                continue
            hit = self._first_observable(
                [node.body, node.orelse], _nested_if_sensitive)
            if hit is None:
                continue
            findings.append(self._new_finding(
                "conditional_leak", file_path, node.lineno,
                used, hit, source_lines))
        return findings
    def _detect_loop_leak(
        self, tree: ast.Module, source_lines: list[str], file_path: str,
        sensitive_vars: set[str], module_constants: frozenset[str],
    ) -> list[ImplicitFlowFinding]:
        findings: list[ImplicitFlowFinding] = []
        def _loop_used(expr: ast.AST) -> set[str]:
            return {name for name in self._find_sensitive_in_expr(
                expr, sensitive_vars, module_constants)
                if not _is_structural_collection(name)}
        def _nested_loop_sensitive(stmt: ast.stmt) -> bool:
            gate = _loop_sensitive_expr(stmt)
            return gate is not None and bool(_loop_used(gate))
        for node in tree_nodes(tree):
            gate = _loop_sensitive_expr(node)
            if gate is None:
                continue
            used = _loop_used(gate)
            if not used:
                continue
            hit = self._first_observable(
                [node.body, node.orelse], _nested_loop_sensitive)
            if hit is None:
                continue
            findings.append(self._new_finding(
                "loop_leak", file_path, node.lineno,
                used, hit, source_lines))
        return findings
    def _detect_exception_leak(
        self, tree: ast.Module, source_lines: list[str], file_path: str,
        sensitive_vars: set[str], module_constants: frozenset[str],
    ) -> list[ImplicitFlowFinding]:
        findings: list[ImplicitFlowFinding] = []
        def _nested_try_sensitive(stmt: ast.stmt) -> bool:
            return (isinstance(stmt, _TRY_NODE_TYPES)
                    and any(self._find_sensitive_in_expr(
                        s, sensitive_vars, module_constants)
                        for s in stmt.body))
        for node in tree_nodes(tree):
            if not isinstance(node, _TRY_NODE_TYPES):
                continue
            used: set[str] = set()
            for stmt in node.body:
                used |= self._find_sensitive_in_expr(
                    stmt, sensitive_vars, module_constants)
            if not used:
                continue
            hit = self._first_observable(
                [h.body for h in node.handlers], _nested_try_sensitive)
            if hit is None:
                continue
            findings.append(self._new_finding(
                "exception_leak", file_path, node.lineno,
                used, hit, source_lines))
        return findings
    def _new_finding(self, category: str, file_path: str, line: int,
                     used: set[str], hit: ast.stmt,
                     source_lines: list[str]) -> ImplicitFlowFinding:
        spec = _LEAK_SPECS[category]
        return ImplicitFlowFinding(
            category=category, severity=spec.severity,
            file=file_path, line=line,
            variable=min(used),
            sink=_describe_observable(hit),
            code_snippet=get_code_snippet(source_lines, line),
            confidence=spec.confidence,
            suggestion=_leak_suggestion(spec.cause, spec.strategy),
            cwe_id=spec.cwe_id,
        )
    def _scan_block(self, body: list[ast.stmt],
                    skip_gate: Callable[[ast.stmt], bool] | None = None
                    ) -> ast.stmt | None:
        frames: list[Iterator[ast.stmt]] = [iter(body)]
        while frames:
            stmt = next(frames[-1], None)
            if stmt is None:
                frames.pop()
                continue
            if self._has_observable_output(stmt):
                return stmt
            if skip_gate is not None and skip_gate(stmt):
                continue
            frames.extend(iter(sub) for sub in reversed(
                list(_iter_inline_bodies(stmt))))
        return None
    def _first_observable(self, branch_bodies: list[list[ast.stmt]],
                          skip_gate: Callable[[ast.stmt], bool] | None = None
                          ) -> ast.stmt | None:
        for body in branch_bodies:
            hit = self._scan_block(body, skip_gate)
            if hit is not None:
                return hit
        return None
    @staticmethod
    def _call_data_children(node: ast.Call) -> list[ast.AST]:
        func = node.func
        children: list[ast.AST] = []
        if isinstance(func, ast.Attribute):
            children.append(func.value)
        elif not isinstance(func, ast.Name):
            children.append(func)
        if isinstance(func, ast.Lambda):
            children.append(func.body)
        children.extend(node.args)
        children.extend(kw.value for kw in node.keywords)
        return children
    def _find_sensitive_in_expr(
        self, expr: ast.AST, sensitive_vars: set[str],
        module_constants: frozenset[str],
    ) -> set[str]:
        found: set[str] = set()
        stack: list[ast.AST] = [expr]
        while stack:
            node = stack.pop()
            if isinstance(node, ast.Lambda):
                stack.extend(
                    default for default in (
                        *node.args.defaults, *node.args.kw_defaults)
                    if default is not None)
                continue
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                stack.extend(node.decorator_list)
                stack.extend(
                    default for default in (
                        *node.args.defaults, *node.args.kw_defaults)
                    if default is not None)
                continue
            if isinstance(node, ast.ClassDef):
                stack.extend(node.decorator_list)
                stack.extend(node.bases)
                stack.extend(keyword.value for keyword in node.keywords)
                stack.extend(node.body)
                continue
            if isinstance(node, ast.Call):
                stack.extend(self._call_data_children(node))
                continue
            if isinstance(node, ast.Name):
                if node.id in sensitive_vars:
                    found.add(node.id)
            elif isinstance(node, ast.Attribute):
                if _name_is_sensitive(node.attr, module_constants):
                    found.add(node.attr)
            elif isinstance(node, ast.Subscript):
                key = node.slice
                if (isinstance(key, ast.Constant)
                        and isinstance(key.value, str)
                        and _name_is_sensitive(key.value, module_constants)):
                    found.add(key.value)
            stack.extend(ast.iter_child_nodes(node))
        return found
    def _has_observable_output(self, stmt: ast.stmt) -> bool:
        return (self._is_yield_output(stmt)
                or self._is_sink_call_output(stmt)
                or self._is_raise_output(stmt)
                or self._is_return_output(stmt))
    @staticmethod
    def _is_yield_output(stmt: ast.stmt) -> bool:
        return (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, (ast.Yield, ast.YieldFrom)))
    def _is_sink_call_output(self, stmt: ast.stmt) -> bool:
        if not (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Call)):
            return False
        name = resolve_call_name(stmt.value)
        if not name:
            return False
        return (name in self.OBSERVABLE_SINKS
                or name.rsplit('.', 1)[-1] in self._SINK_TAIL_NAMES)
    @staticmethod
    def _is_raise_output(stmt: ast.stmt) -> bool:
        return isinstance(stmt, ast.Raise)
    @staticmethod
    def _is_return_output(stmt: ast.stmt) -> bool:
        return isinstance(stmt, ast.Return)
def analyze_implicit_flow(
    source_code: str = "",
    tree: ast.Module | None = None,
    filepath: str = _DEFAULT_FILEPATH,
) -> list[dict[str, Any]]:
    if source_code is None:
        source_code = ""
    if not source_code and not isinstance(tree, ast.Module):
        return []
    analyzer = ImplicitFlowAnalyzer()
    return [f.to_dict() for f in analyzer.analyze(
        source_code, filepath or _DEFAULT_FLOW_LABEL, _tree=tree)]
_SE03_PLACEHOLDERS = ('os.environ', 'os.getenv', 'getenv')
_SE03_TEMPLATE_RE = re.compile(
    r'(?:\{[^{}]+\}|\$[A-Za-z_][A-Za-z0-9_]*|<[^<>]+>)')
def _se03_target_name(target: ast.AST) -> str | None:
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        return target.attr
    if (isinstance(target, ast.Subscript)
            and isinstance(target.slice, ast.Constant)
            and isinstance(target.slice.value, str)):
        return target.slice.value
    return None
def _se03_star_index(elts: list[ast.AST]) -> int:
    for _i, _el in enumerate(elts):
        if isinstance(_el, ast.Starred):
            return _i
    return -1
def _se03_aligned_pairs(target: ast.Tuple | ast.List,
                        val_node: ast.Tuple | ast.List
                        ) -> list[tuple[ast.AST, ast.AST | list[ast.AST] | None]]:
    targets, values = target.elts, val_node.elts
    _star = _se03_star_index(targets)
    if _star < 0:
        if len(targets) != len(values):
            return []
        return list(zip(targets, values, strict=False))
    if len(values) < len(targets) - 1:
        return []
    _tail = len(targets) - _star - 1
    aligned = list(zip(targets[:_star], values[:_star], strict=False))
    star_end = len(values) - _tail if _tail else len(values)
    aligned.append((targets[_star], values[_star:star_end]))
    if _tail:
        aligned.extend(
            zip(targets[_star + 1:], values[len(values) - _tail:],
                strict=False))
    return aligned
def _se03_pairs_for_target(target: ast.AST,
                           val_node: ast.AST | list[ast.AST],
                           lineno: int) -> tuple[tuple[str, Any, int], ...]:
    if isinstance(target, ast.Starred):
        values = val_node if isinstance(val_node, list) else [val_node]
        return tuple(pair
                     for value in values
                     for pair in _se03_pairs_for_target(
                         target.value, value, lineno))
    _name = _se03_target_name(target)
    if _name is not None:
        return ((_name, val_node, lineno),)
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(val_node, (ast.Tuple, ast.List))):
        _pairs: list[tuple[str, Any, int]] = []
        for _t, _v in _se03_aligned_pairs(target, val_node):
            if _v is None:
                continue
            _pairs.extend(_se03_pairs_for_target(_t, _v, lineno))
        return tuple(_pairs)
    return ()
def _se03_iter_literal_elements(iter_node: ast.AST) -> Iterator[ast.AST]:
    if isinstance(iter_node, (ast.List, ast.Tuple, ast.Set)):
        yield from iter_node.elts
        return
    if isinstance(iter_node, ast.Dict):
        yield from (key for key in iter_node.keys if key is not None)
        return
    if (isinstance(iter_node, ast.Constant)
            and isinstance(iter_node.value, (str, bytes))):
        return
    yield iter_node
def _se03_iter_arg_default_pairs(args: ast.arguments
                                 ) -> Iterator[tuple[str, Any, int]]:
    positional = [*args.posonlyargs, *args.args]
    if args.defaults:
        paired = zip(positional[-len(args.defaults):], args.defaults,
                     strict=True)
        for arg, default in paired:
            yield arg.arg, default, default.lineno
    for arg, default in zip(args.kwonlyargs, args.kw_defaults, strict=True):
        if default is not None:
            yield arg.arg, default, default.lineno
def _se03_iter_target_value_pairs(tree: Any, index: list | None
                                  ) -> Iterator[tuple[str, Any, int]]:
    for node in iter_nodes(tree, index):
        if isinstance(node, ast.arguments):
            yield from _se03_iter_arg_default_pairs(node)
            continue
        _pair = assign_targets_value(node)
        if _pair is None:
            if isinstance(node, (ast.NamedExpr, ast.AugAssign)):
                _pair = ([node.target], node.value)
            elif isinstance(node, (ast.For, ast.AsyncFor)):
                for _element in _se03_iter_literal_elements(node.iter):
                    yield from _se03_pairs_for_target(
                        node.target, _element, node.lineno)
                continue
            elif isinstance(node, (ast.With, ast.AsyncWith)):
                for _item in node.items:
                    if _item.optional_vars is not None:
                        yield from _se03_pairs_for_target(
                            _item.optional_vars, _item.context_expr,
                            node.lineno)
                continue
            else:
                continue
        targets, val_node = _pair
        for target in targets:
            yield from _se03_pairs_for_target(target, val_node, node.lineno)
_SE03_REGEX_HINT_RE = re.compile(r"\\[sdwSDWbB]|\(\?:|\.\*|\.\+")
def _se03_name_echo(target_name: str, value: str) -> bool:
    norm_name = re.sub(r"[^a-z0-9]", "", target_name.lower())
    norm_value = re.sub(r"[^a-z0-9]", "", value.lower())
    if len(norm_value) < 6 or not norm_name:
        return False
    return norm_value != norm_name and norm_value in norm_name
_EMBEDDED_ASSIGNMENT_RE = re.compile(
    r"^\s*(?P<name>[A-Za-z_][A-Za-z0-9_]{1,40})\s*[:=]\s*\S.*$")
def _is_embedded_assignment_text(value: str) -> bool:
    if not isinstance(value, str):
        return False
    match = _EMBEDDED_ASSIGNMENT_RE.match(value)
    return bool(match) and is_sensitive_name(match.group("name"))
def _se03_looks_like_credential(text: str, target_name: str = "") -> bool:
    value = text.strip()
    if len(value) < _MIN_SECRET_LEN:
        return False
    if _SE03_REGEX_HINT_RE.search(value):
        return False
    if _is_embedded_assignment_text(value):
        return False
    if target_name and _se03_name_echo(target_name, value):
        return False
    if any(ch.isdigit() for ch in value):
        return True
    if any(not ch.isalnum() and not ch.isspace() for ch in value):
        return True
    return (value.isascii() and len(value) >= 16
            and len(set(value.lower())) >= 8)
def _se03_literal_strings(value_node: ast.AST | list[ast.AST]) -> Iterator[str]:
    if isinstance(value_node, list):
        for _value in value_node:
            yield from _se03_literal_strings(_value)
        return
    if isinstance(value_node, ast.Constant):
        if isinstance(value_node.value, str):
            yield value_node.value
        elif isinstance(value_node.value, bytes):
            yield value_node.value.decode("utf-8", "replace")
        return
    if isinstance(value_node, (ast.List, ast.Tuple, ast.Set)):
        for _element in value_node.elts:
            yield from _se03_literal_strings(_element)
        return
    if isinstance(value_node, ast.Dict):
        for _value in value_node.values:
            yield from _se03_literal_strings(_value)
        return
    if isinstance(value_node, ast.Starred):
        yield from _se03_literal_strings(value_node.value)
def _se03_report_if_hardcoded(issues: list, target_name: str,
                              val_node: ast.AST | list[ast.AST], lineno: int,
                              filepath: Any, source_lines: Any) -> None:
    if not is_sensitive_name(target_name) or _is_rule_table_target(target_name):
        return
    for _text in _se03_literal_strings(val_node):
        if len(_text) <= 3:
            continue
        if (is_placeholder_secret(_text)
                or _SE03_TEMPLATE_RE.fullmatch(_text.strip())
                or _is_embedded_assignment_text(_text)
                or any(ph in _text.lower() for ph in _SE03_PLACEHOLDERS)):
            continue
        if not _se03_looks_like_credential(_text, target_name):
            continue
        issues.append({
            "rule_id": "SE-03",
            "severity": "P1",
            "dimension": "security",
            "line": lineno,
            "file": filepath,
            "message": "Hardcoded secret: " + target_name,
            "code_snippet": get_code_snippet(source_lines, lineno),
        })
def check_SE03(tree: Any, source: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    tree = _coerce_tree(tree)
    if tree is None:
        return []
    index = _coerce_index(index)
    issues = []
    filepath = normalize_filepath(filepath)
    for target_name, val_node, lineno in _se03_iter_target_value_pairs(
            tree, index):
        _se03_report_if_hardcoded(issues, target_name, val_node, lineno,
                                  filepath, source)
    return issues
def _hashlib_new_algo_name(node: ast.Call) -> str | None:
    if (node.args and isinstance(node.args[0], ast.Constant)
            and isinstance(node.args[0].value, str)):
        return node.args[0].value
    for kw in node.keywords:
        if (kw.arg == 'name' and isinstance(kw.value, ast.Constant)
                and isinstance(kw.value.value, str)):
            return kw.value.value
    return None
_SE10_WEAK_ALGOS = frozenset({'md5', 'sha1'})
_SE10_HASHLIB_MEMBERS = (*sorted(_SE10_WEAK_ALGOS), 'new')
_SUGGESTION_SAFE_ALTERNATIVE = ('根因: 代码使用了不规范或有风险的实现方式。该问题属于安全类别。\n'
                                '修复策略: Use safe alternative\n参考标准: OWASP Top 10 / CWE / Bandit')
_SE10_NON_SECURITY_SEGMENT_WORDS = frozenset({'id'})
_SE10_NON_SECURITY_SUBSTRINGS = frozenset(
    {'hash', 'cache', 'fingerprint', 'digest', 'checksum', 'etag'})
def _se10_map_calls_to_names(value: ast.AST, names: list[str],
                              assigned_names_of: dict[int, list[str]]) -> None:
    if not names or isinstance(
            value, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)):
        return
    for child in iter_own_scope(value, skip_lambda=True, include_self=True):
        if isinstance(child, ast.Call):
            assigned_names_of.setdefault(id(child), []).extend(names)
def _se10_assignment_names(node: ast.AST) -> list[str]:
    return [name for target in _scope_binding_targets(node)
            for name in _binding_target_names(target)]
def _se10_build_exempt_infra(tree: Any,
                             index: list | None = None) -> dict[int, list[str]]:
    assigned_names_of: dict[int, list[str]] = {}
    for node in iter_nodes(tree, index):
        if not isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign,
                                 ast.NamedExpr)):
            continue
        value = node.value
        if value is None:
            continue
        _se10_map_calls_to_names(
            value, _se10_assignment_names(node), assigned_names_of)
    return assigned_names_of
def _se10_collect_weak_hash_calls(
        tree: Any, idx: list, hashlib_names: set, hash_from: dict,
        scope_bindings: _ScopeBindings | None = None,
) -> tuple[list, dict[int, str]]:
    md5_calls: list = []
    algo_label_of: dict[int, str] = {}
    for node in iter_nodes(tree, idx):
        if not isinstance(node, ast.Call):
            continue
        scoped_hash_from = hash_from
        if scope_bindings is not None:
            receiver = _call_receiver_name(node)
            identity = (scope_bindings.import_identity(node, receiver)
                        if receiver else None)
            if identity and identity.startswith('hashlib.'):
                member = identity.removeprefix('hashlib.')
                if member in _SE10_HASHLIB_MEMBERS:
                    scoped_hash_from = {**hash_from, receiver: member}
        member = resolve_module_member_call(
            node, hashlib_names, _SE10_HASHLIB_MEMBERS, scoped_hash_from)
        if member in _SE10_WEAK_ALGOS:
            md5_calls.append(node)
            algo_label_of[id(node)] = f"hashlib.{member}()"
        elif member == 'new':
            new_algo = _hashlib_new_algo_name(node)
            if (new_algo or '').lower() in _SE10_WEAK_ALGOS:
                md5_calls.append(node)
                algo_label_of[id(node)] = f"hashlib.new('{new_algo}')"
    return md5_calls, algo_label_of
def _call_receiver_name(node: ast.Call) -> str:
    func = node.func
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return func.value.id
    if isinstance(func, ast.Name):
        return func.id
    return ""
def _se10_name_is_non_security(name: str) -> bool:
    if name in {'_', '__'}:
        return True
    if is_sensitive_name(name):
        return False
    if any(word in split_identifier(name)
           for word in _SE10_NON_SECURITY_SEGMENT_WORDS):
        return True
    lower = name.lower()
    return any(word in lower for word in _SE10_NON_SECURITY_SUBSTRINGS)
def _se10_is_non_security_context(md5_call: ast.Call,
                                  assigned_names_of: dict[int, list[str]]) -> bool:
    assigned_names = assigned_names_of.get(id(md5_call), ())
    return bool(assigned_names) and all(
        _se10_name_is_non_security(var_name) for var_name in assigned_names)
def check_SE10(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    tree = _coerce_tree(tree)
    if tree is None:
        return []
    index = _coerce_index(index)
    filepath = normalize_filepath(filepath)
    _idx = materialized_index(index)
    _hashlib_names, _hash_from = collect_module_bindings_detailed(
        tree, 'hashlib', _SE10_HASHLIB_MEMBERS)
    _assigned_aliases = _module_alias_names(tree, _hashlib_names)
    _hashlib_names |= _assigned_aliases
    _assigned_names_of = _se10_build_exempt_infra(tree, _idx)
    _scope_bindings = _ScopeBindings(
        tree, derived_module_names=frozenset(_hashlib_names),
        assignment_aliases=frozenset(_assigned_aliases),
        real_import_modules=frozenset({'hashlib'}))
    md5_calls, _algo_label_of = _se10_collect_weak_hash_calls(
        tree, _idx, _hashlib_names, _hash_from, _scope_bindings)
    issues = []
    for md5_call in md5_calls:
        if any(kw.arg == "usedforsecurity"
               and isinstance(kw.value, ast.Constant)
               and not kw.value.value
               for kw in md5_call.keywords):
            continue
        _receiver = _call_receiver_name(md5_call)
        _is_module_receiver = _receiver in _hashlib_names
        _is_function_receiver = _receiver in _hash_from
        if ((_is_module_receiver or _is_function_receiver)
                and _scope_bindings.is_shadowed(
                    md5_call, _receiver, real_imports=True)):
            continue
        if _se10_is_non_security_context(md5_call, _assigned_names_of):
            continue
        issues.append(DiagnoseFinding(id='SE-10', severity='P1', dimension='security', file=filepath, line=md5_call.lineno, message=_algo_label_of[id(md5_call)] + ' 弱哈希算法, 存在碰撞风险', suggestion=_SUGGESTION_SAFE_ALTERNATIVE, code_snippet=get_code_snippet(source_lines, md5_call.lineno)))
    return issues
def _module_alias_names(tree: Any, base_names: set[str]) -> set[str]:
    aliases: set[str] = set()
    known = set(base_names)
    changed = True
    while changed:
        changed = False
        for node in tree_nodes(tree):
            pair = assign_targets_value(node)
            if pair is None:
                continue
            targets, value = pair
            if not (isinstance(value, ast.Name) and value.id in known):
                continue
            for target in targets:
                name = _se03_target_name(target)
                if name and name not in aliases:
                    aliases.add(name)
                    known.add(name)
                    changed = True
    return aliases
def _module_namespaces(tree: Any) -> frozenset[str]:
    if not isinstance(tree, ast.AST):
        return frozenset()
    names: set[str] = set()
    for node in tree_nodes(tree):
        if isinstance(node, ast.Import):
            names.update(alias.asname or alias.name.split('.')[0]
                         for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            names.update(alias.asname or alias.name
                         for alias in node.names
                         if alias.name != '*')
    return frozenset(names)
def _data_bound_names(tree: Any) -> frozenset[str]:
    if not isinstance(tree, ast.AST):
        return frozenset()
    return frozenset(file_bound_names(tree)) - _module_namespaces(tree)
def _data_face_call_children(node: Any, data_names: frozenset[str] | None = None,
                             *, with_receiver: bool = False) -> list[ast.AST]:
    if not isinstance(node, ast.Call):
        return [node]
    roots: list[ast.AST] = []
    func = node.func
    if isinstance(func, ast.Lambda):
        roots.append(func.body)
    elif with_receiver and isinstance(func, ast.Attribute):
        receiver = func.value
        if not (isinstance(receiver, ast.Name) and data_names is not None
                and receiver.id not in data_names):
            roots.append(receiver)
    roots.extend(node.args)
    roots.extend(kw.value for kw in node.keywords)
    return roots
_SE28_SUGGESTION = ('根因: print()输出敏感信息到stdout,日志收集器/终端记录可泄露。该问题属于安全类别。\n'
                    '修复策略: 移除敏感信息的print或使用脱敏函数\n参考标准: OWASP A09:2021 / CWE-532')
def _sensitive_leaf_name(node: ast.AST) -> tuple[str | None, bool]:
    if isinstance(node, ast.Name):
        return (node.id, False) if is_sensitive_name(node.id) else (None, False)
    if isinstance(node, ast.Attribute):
        return ((node.attr, True) if is_sensitive_name(node.attr)
                else (None, False))
    _key_name = _sensitive_key_access_name(node)
    if _key_name is not None:
        return _key_name, False
    return None, False
def _se28_iter_leaves(arg: ast.AST, data_names: frozenset[str] | None,
                      *, in_fstring: bool = False
                      ) -> Iterator[tuple[str, bool, bool]]:
    stack: list[tuple[ast.AST, bool]] = [(arg, in_fstring)]
    while stack:
        cur, _fstring = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef)):
            continue
        _name, _is_attr = _sensitive_leaf_name(cur)
        if _name is not None:
            yield _name, _fstring, _is_attr
            if isinstance(cur, ast.Name):
                continue
        if isinstance(cur, ast.JoinedStr):
            stack.extend((val.value, True) for val in reversed(cur.values)
                         if isinstance(val, ast.FormattedValue))
            continue
        if isinstance(cur, ast.Call):
            stack.extend((child, _fstring) for child in reversed(
                _data_face_call_children(cur, data_names, with_receiver=True)))
            continue
        stack.extend((child, _fstring) for child in reversed(
            list(ast.iter_child_nodes(cur))))
def _se28_make_report(issues: list, filepath: str, source_lines: Any,
                     lineno: int):
    _emitted: set[tuple[str, bool, bool]] = set()
    def _report(name: str, *, in_fstring: bool = False, is_attr: bool = False) -> None:
        _key = (name, in_fstring, is_attr)
        if _key in _emitted:
            return
        _emitted.add(_key)
        _where = " f-string" if in_fstring else ""
        _kind = "(属性)" if is_attr else ""
        issues.append(DiagnoseFinding(
            id='SE-28', severity='P2', dimension='security', file=filepath,
            line=lineno,
            message=f"print(){_where}可能输出敏感信息{_kind}: {name}",
            suggestion=_SE28_SUGGESTION,
            code_snippet=get_code_snippet(source_lines, lineno)))
    return _report
def _se28_is_print_call(node: ast.AST,
                        scope_bindings: _ScopeBindings) -> bool:
    if not isinstance(node, ast.Call):
        return False
    call_name = resolve_call_name(node)
    if not call_name:
        return False
    head, dot, rest = call_name.partition(".")
    identity = scope_bindings.import_identity(node, head)
    if dot:
        if rest != "print" or identity != "builtins":
            return False
    elif identity != "builtins.print" and (
            head != "print" or identity not in {None, "builtins.*"}):
        return False
    return not scope_bindings.is_shadowed(
        node, head, real_imports=True)
def check_SE28(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    tree = _coerce_tree(tree)
    if tree is None:
        return []
    index = _coerce_index(index)
    issues = []
    filepath = normalize_filepath(filepath)
    _data_names = _data_bound_names(tree)
    _scope_bindings = _ScopeBindings(
        tree, real_import_modules=frozenset({'builtins'}))
    for node in iter_nodes(tree, index):
        if not _se28_is_print_call(node, _scope_bindings):
            continue
        _report = _se28_make_report(issues, filepath, source_lines,
                                    node.lineno)
        output_args = [*node.args, *(kw.value for kw in node.keywords
                                   if kw.arg in {'sep', 'end'})]
        for arg in output_args:
            for _name, _in_fstring, _is_attr in _se28_iter_leaves(
                    arg, _data_names):
                _report(_name, in_fstring=_in_fstring, is_attr=_is_attr)
    return issues
_SE36_LOG_METHODS = ("debug", "info", "warning", "warn", "error",
                     "exception", "critical", "fatal", "log")
_SE36_LOGGER_RECEIVERS = frozenset(
    {"logging", "log", "logger", "_log", "_logger"})
def _se36_logging_receiver(call_name: str) -> bool:
    prefix, _sep, method = call_name.rpartition(".")
    if not prefix or method not in _SE36_LOG_METHODS:
        return False
    if prefix == "logging" or prefix.startswith("logging."):
        return True
    tail = prefix.rsplit(".", 1)[-1].lower()
    return (tail in _SE36_LOGGER_RECEIVERS
            or tail.endswith(("_log", "_logger", "logger")))
def _logging_module_rebind(node: ast.Call, scope_bindings: _ScopeBindings,
                          module_bindings: dict[str, str],
                          func_bindings: dict[str, str]) -> bool:
    receiver = _call_receiver_name(node)
    if not receiver:
        func = node.func
        if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Call):
            _inner = resolve_call_name(func.value)
            receiver = _inner.split(".", 1)[0] if _inner else ""
    if receiver in func_bindings:
        if not func_bindings[receiver].startswith("logging."):
            return False
    elif module_bindings.get(receiver, receiver) != "logging":
        return False
    return scope_bindings.is_shadowed(node, receiver, real_imports=True)
def _sensitive_key_access_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Subscript):
        key = node.slice
    elif isinstance(node, ast.Call):
        func = node.func
        is_get = (isinstance(func, ast.Attribute)
                  and func.attr == 'get' and bool(node.args))
        is_getenv = ((isinstance(func, ast.Attribute)
                      and func.attr == 'getenv')
                     or (isinstance(func, ast.Name)
                         and func.id == 'getenv'))
        if is_get:
            key = node.args[0]
        elif is_getenv:
            key = node.args[0] if node.args else next(
                (kw.value for kw in node.keywords if kw.arg == 'key'),
                None)
        else:
            return None
    else:
        return None
    if (isinstance(key, ast.Constant) and isinstance(key.value, str)
            and is_sensitive_name(key.value)):
        return key.value
    return None
def _se36_scan_sensitive_vars(
        node: Any, data_names: frozenset[str] | None = None
) -> list[tuple[str, bool]]:
    occurrences: list[tuple[str, bool]] = []
    stack: list[tuple[Any, bool]] = [
        (root, False) for root in reversed(_data_face_call_children(node))]
    while stack:
        cur, protected = stack.pop()
        if isinstance(cur, ast.Lambda):
            continue
        sensitive_name = _sensitive_leaf_name(cur)[0]
        if sensitive_name is not None:
            occurrences.append((sensitive_name, protected))
            if isinstance(cur, ast.Name):
                continue
        if isinstance(cur, ast.Call):
            stack.extend((child, protected) for child in reversed(
                _data_face_call_children(
                    cur, data_names, with_receiver=True)))
            continue
        if _se36_is_empty_slice(cur):
            continue
        if _se36_is_truncation_slice(cur):
            stack.append((cur.value, True))
            continue
        stack.extend((child, protected) for child in reversed(
            list(ast.iter_child_nodes(cur))))
    return _se36_merge_protected(occurrences)
def _se36_merge_protected(occurrences: list[tuple[str, bool]]) -> list[tuple[str, bool]]:
    merged: dict[str, bool] = {}
    for name, protected in occurrences:
        merged[name] = merged.get(name, True) and protected
    return list(merged.items())
def _se36_log_names(sensitive_pairs: list[tuple[str, bool]]) -> str:
    return ", ".join(name for name, _ in sensitive_pairs)
def _se36_build_issue(node: Any, filepath: Any,
                      sensitive_pairs: list[tuple[str, bool]],
                      source_lines: Any = None) -> dict:
    return {
        "rule_id": "SE-36",
        "severity": "P1",
        "dimension": "security",
        "line": node.lineno,
        "file": filepath,
        "code_snippet": get_code_snippet(source_lines, node.lineno),
        "message": "[SE-36] Sensitive data in log: " + _se36_log_names(
            sensitive_pairs),
        "suggestion": ('根因: 日志输出包含敏感数据，日志收集器/终端记录可泄露凭据。'
                       '该问题属于安全类别。\n'
                       '修复策略: 移除敏感字段或使用脱敏函数后再记录日志\n'
                       '参考标准: OWASP A09:2021 / CWE-532'),
    }
def _se36_optional_slice_bound(node: ast.AST | None) -> ast.AST | None:
    if isinstance(node, ast.Constant) and node.value is None:
        return None
    return node
def _se36_slice_int(node: ast.AST | None) -> int | None:
    if (isinstance(node, ast.Constant)
            and isinstance(node.value, int)
            and not isinstance(node.value, bool)):
        return node.value
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub))):
        operand = _se36_slice_int(node.operand)
        if operand is not None:
            return operand if isinstance(node.op, ast.UAdd) else -operand
    return None
def _se36_is_empty_slice(node: Any) -> bool:
    if not (isinstance(node, ast.Subscript)
            and isinstance(node.slice, ast.Slice)):
        return False
    step_node = _se36_optional_slice_bound(node.slice.step)
    step = _se36_slice_int(step_node) if step_node is not None else 1
    if step is None or step == 0:
        return False
    lower_node = _se36_optional_slice_bound(node.slice.lower)
    upper_node = _se36_optional_slice_bound(node.slice.upper)
    lower = (_se36_slice_int(lower_node) if lower_node is not None
             else 0 if step > 0 else None)
    upper = _se36_slice_int(upper_node)
    if upper is None:
        return False
    if lower is None:
        return step < 0 and upper == -1
    if lower < 0:
        if upper >= 0:
            return step > 0 and upper == 0
    elif upper < 0:
        return step < 0 and upper == -1
    return lower >= upper if step > 0 else lower <= upper
def _se36_is_truncation_slice(node: Any) -> bool:
    if not (isinstance(node, ast.Subscript)
            and isinstance(node.slice, ast.Slice)):
        return False
    step = _se36_optional_slice_bound(node.slice.step)
    if step is not None and not (
            isinstance(step, ast.Constant)
            and isinstance(step.value, int)
            and not isinstance(step.value, bool)
            and step.value > 0):
        return False
    upper = node.slice.upper
    if not (isinstance(upper, ast.Constant)
            and isinstance(upper.value, int)
            and not isinstance(upper.value, bool)
            and upper.value > 0):
        return False
    lower = _se36_optional_slice_bound(node.slice.lower)
    if lower is None:
        return True
    return (isinstance(lower, ast.Constant)
            and isinstance(lower.value, int)
            and not isinstance(lower.value, bool)
            and lower.value == 0)
def _se36_apply_truncation_downgrade(issue: dict,
                                     sensitive_pairs: list[tuple[str, bool]]) -> None:
    if not all(protected for _, protected in sensitive_pairs):
        return
    issue["severity"] = "P3"
    issue["message"] = ("[SE-36] Sensitive data in log (truncated): "
                        + _se36_log_names(sensitive_pairs))
    issue["note"] = "已检测到截断保护，自动降级"
def check_SE36(tree: Any, source: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    tree = _coerce_tree(tree)
    if tree is None:
        return []
    index = _coerce_index(index)
    issues = []
    filepath = normalize_filepath(filepath)
    data_names = _data_bound_names(tree)
    scope_bindings = _ScopeBindings(
        tree, real_import_modules=frozenset({'logging'}))
    func_bindings, module_bindings = _collect_import_call_bindings(tree)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        canonical_name = _canonical_call_name(
            node, func_bindings, module_bindings, scope_bindings)
        if not _se36_logging_receiver(canonical_name or resolve_call_name(node)):
            continue
        if _logging_module_rebind(
                node, scope_bindings, module_bindings, func_bindings):
            continue
        sensitive_pairs = _se36_scan_sensitive_vars(node, data_names)
        if not sensitive_pairs:
            continue
        issue = _se36_build_issue(node, filepath, sensitive_pairs, source)
        _se36_apply_truncation_downgrade(issue, sensitive_pairs)
        issues.append(issue)
    return issues
_FROM_FUNC_BIND_TARGETS: frozenset[str] = frozenset(
    {'os.getenv', 'logging.getLogger'}
    | {f'logging.{method}' for method in _SE36_LOG_METHODS})
_FROM_MODULE_BIND_TARGETS: frozenset[str] = frozenset({'os.environ'})
_MODULE_ALIAS_BIND_TARGETS: frozenset[str] = frozenset({'os', 'logging'})
def _collect_import_call_bindings(
        tree: ast.Module) -> tuple[dict[str, str], dict[str, str]]:
    func_bindings: dict[str, str] = {}
    module_bindings: dict[str, str] = {}
    for imp in tree_nodes(tree):
        if isinstance(imp, ast.Import):
            for alias in imp.names:
                _bind_module_alias(alias, module_bindings)
            continue
        if isinstance(imp, ast.ImportFrom) and imp.module and not imp.level:
            for alias in imp.names:
                if alias.name == '*':
                    _activate_star_import(imp, func_bindings, module_bindings)
                else:
                    _bind_from_import(imp, alias, func_bindings, module_bindings)
    return func_bindings, module_bindings
def _bind_module_alias(alias: ast.alias,
                       module_bindings: dict[str, str]) -> None:
    if alias.name not in _MODULE_ALIAS_BIND_TARGETS:
        return
    if alias.asname:
        module_bindings[alias.asname] = alias.name
    else:
        _root = alias.name.split('.')[0]
        module_bindings[_root] = _root
def _activate_star_import(imp: ast.ImportFrom, func_bindings: dict[str, str],
                           module_bindings: dict[str, str]) -> None:
    prefix = imp.module + '.'
    for target in (_FROM_FUNC_BIND_TARGETS | _FROM_MODULE_BIND_TARGETS):
        member = (target[len(prefix):]
                  if target.startswith(prefix) else '')
        if member and '.' not in member:
            if target in _FROM_FUNC_BIND_TARGETS:
                func_bindings[member] = target
            else:
                module_bindings[member] = target
def _bind_from_import(imp: ast.ImportFrom, alias: ast.alias,
                       func_bindings: dict[str, str],
                       module_bindings: dict[str, str]) -> None:
    local = alias.asname or alias.name
    canonical = f"{imp.module}.{alias.name}"
    if canonical in _FROM_FUNC_BIND_TARGETS:
        func_bindings[local] = canonical
    elif canonical in _FROM_MODULE_BIND_TARGETS:
        module_bindings[local] = canonical
def _canonical_call_name(
        node: ast.Call, func_bindings: dict[str, str],
        module_bindings: dict[str, str],
        scope_bindings: _ScopeBindings | None = None) -> str:
    call_name = resolve_call_name(node)
    if not call_name:
        func = node.func
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Call)):
            inner = _canonical_call_name(
                func.value, func_bindings, module_bindings, scope_bindings)
            if inner == "logging" or inner.startswith("logging."):
                return f"logging.{func.attr}"
        return call_name
    head, _sep, rest = call_name.partition('.')
    scoped_identity = (scope_bindings.import_identity(node, head)
                       if scope_bindings is not None else None)
    if scoped_identity is not None:
        if scoped_identity.endswith('.*'):
            imported = f"{scoped_identity[:-2]}.{head}"
            if not rest and imported in _FROM_FUNC_BIND_TARGETS:
                return imported
            if rest and imported in _FROM_MODULE_BIND_TARGETS:
                return f"{imported}.{rest}"
        elif not rest and scoped_identity in _FROM_FUNC_BIND_TARGETS:
            return scoped_identity
        elif rest and (scoped_identity in _MODULE_ALIAS_BIND_TARGETS
                       or scoped_identity in _FROM_MODULE_BIND_TARGETS):
            return f"{scoped_identity}.{rest}"
        return call_name
    if not rest:
        return func_bindings.get(head, call_name)
    if head in module_bindings:
        return f"{module_bindings[head]}.{rest}"
    return call_name
_SECRET_PLACEHOLDER_WORDS = frozenset({
    'test', 'example', 'placeholder', 'dummy', 'fake', 'sample', 'mock',
    'xxx', 'yyy', 'zzz', 'todo', 'fixme', 'changeme', 'default',
    'none', 'null',
})
_SECRET_PLACEHOLDER_PHRASES: tuple[tuple[str, ...], ...] = (
    ('change', 'me'), ('replace', 'me'),
    ('your',), ('your', 'key'), ('your', 'api', 'key'),
)
_SECRET_EXACT_PLACEHOLDERS = frozenset({
    '123456', '000000', '111111', 'abcdef', 'aabbcc',
    'aaaaaa', 'bbbbbb', 'cccccc', 'abc123', 'password',
})
_SECRET_PATTERNS_BUILTIN: list[tuple[str, str, str, str]] = [
    ('AWS_ACCESS_KEY_ID', r'AKIA[0-9A-Z]{16}', 'CWE-798', 'CRITICAL'),
    ('AWS_SECRET_ACCESS_KEY',
     r'aws_secret_access_key\s*=\s*["\'][A-Za-z0-9/+=]{40}["\']',
     'CWE-798', 'CRITICAL'),
    ('GOOGLE_API_KEY', r'AIza[0-9A-Za-z\-_]{35}', 'CWE-798', 'CRITICAL'),
    ('GITHUB_TOKEN', r'gh[ps]_[A-Za-z0-9]{36}', 'CWE-798', 'CRITICAL'),
    ('SLACK_TOKEN', r'xox[bp]-[0-9A-Za-z-]+', 'CWE-798', 'HIGH'),
    ('API_KEY',
     r'(?:api[_-]?key|apikey)\s*=\s*["\'][A-Za-z0-9\-_]{16,}["\']',
     'CWE-798', 'HIGH'),
    ('SECRET_KEY',
     r'(?:secret[_-]?key|secret)\s*=\s*["\'][A-Za-z0-9\-_]{16,}["\']',
     'CWE-798', 'HIGH'),
    ('PASSWORD',
     r'(?:password|passwd|pwd)\s*=\s*["\'][^"\']{8,}["\']',
     'CWE-798', 'MEDIUM'),
    ('JWT_SECRET',
     r'(?:jwt[_-]?secret|jwt[_-]?key)\s*=\s*["\'][A-Za-z0-9\-_]{16,}["\']',
     'CWE-798', 'HIGH'),
    ('PRIVATE_KEY',
     r'-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----',
     'CWE-798', 'CRITICAL'),
    ('DB_PASSWORD',
     r'(?:postgres|mysql|mongodb|redis)://[^:]+:([^@]+)@',
     'CWE-798', 'HIGH'),
    ('BEARER_TOKEN', r'Bearer\s+[A-Za-z0-9\-_\.]{20,}', 'CWE-798', 'HIGH'),
]
_CODE_SNIPPET_PREFIXES = ('import ', 'from ', 'def ', 'class ')
def _is_code_snippet_text(value_str: str) -> bool:
    return '\n' in value_str or value_str.startswith(_CODE_SNIPPET_PREFIXES)
# 规则编号常量：``_TOKEN_OVER_RULE_ID = "TOKEN-OVER"`` 这类赋值的目标名里
# 带 TOKEN/PASSWORD/SECRET 等敏感词，但值是**规则标识符**（全大写字母数字
# 以连字符/下划线分段），不存在凭据熵，也不应进 .env。此前会被判成
# “硬编码 HARDCODED_SECRET”（本仓 2/2 条均属此形态）。
_RULE_ID_TEXT_RE = re.compile(r'[A-Z][A-Z0-9]*(?:[-_][A-Z0-9]+)+')
def _is_rule_identifier_text(value_str: str) -> bool:
    stripped = (value_str or '').strip()
    if not stripped or len(stripped) > 48:
        return False
    if not _RULE_ID_TEXT_RE.fullmatch(stripped):
        return False
    # 需要至少一个分段边界（避免把单个全大写单词当规则号）
    return any(sep in stripped for sep in ('-', '_'))
def _segments_contain_phrase(segments: tuple[str, ...],
                            phrase: tuple[str, ...]) -> bool:
    width = len(phrase)
    if not width or len(segments) < width:
        return False
    return any(segments[start:start + width] == phrase
               for start in range(len(segments) - width + 1))
def _is_placeholder_text(text: str) -> bool:
    segments = split_identifier(text)
    if not segments:
        return False
    if any(word in segments for word in _SECRET_PLACEHOLDER_WORDS):
        return True
    if any(_segments_contain_phrase(segments, phrase)
           for phrase in _SECRET_PLACEHOLDER_PHRASES):
        return True
    head = segments[0]
    return any(head.startswith(word) and head[len(word):].isdigit()
               for word in _SECRET_PLACEHOLDER_WORDS)
def is_placeholder_secret(value: str) -> bool:
    if not isinstance(value, str):
        return True
    if not value:
        return True
    lower = value.lower()
    return any((
        _is_placeholder_text(value),
        lower.strip('"\'') in _SECRET_EXACT_PLACEHOLDERS,
        '${' in value or ('<' in value and '>' in value),
        len(set(value)) == 1,
        value.isdigit() and len(value) <= 8,
    ))
def _assemble_value_str(value_node: ast.AST) -> str | None:
    if isinstance(value_node, ast.Constant):
        if isinstance(value_node.value, str):
            return value_node.value
        if isinstance(value_node.value, bytes):
            return value_node.value.decode("utf-8", "replace")
    if isinstance(value_node, ast.JoinedStr):
        return "".join(
            part.value for part in value_node.values
            if isinstance(part, ast.Constant) and isinstance(part.value, str))
    if isinstance(value_node, (ast.BinOp, ast.Call)):
        try:
            return ast.unparse(value_node)
        except Exception as _e:  # noqa: BLE001 - 撕裂节点降级契约
            _log.warning("[SecretScan] ast.unparse failed for node at line %s: %s",
                         getattr(value_node, 'lineno', '?'), _e)
            return None
    return ""
_NEGATED_SECRET_MARKERS = (
    'non_credential', 'non_secret', 'no_secret', 'not_secret',
    'without_secret', 'without_credential', 'fake_secret', 'dummy_secret',
    'example_secret', 'sample_secret', 'placeholder_secret',
)
def _target_name_matches(target_name: str, keyword: str) -> bool:
    return _segments_match_pattern(
        split_identifier(target_name), split_identifier(keyword))
def _token_target_name(target_name: str) -> bool:
    return any(segments_equal(seg, "token")
               for seg in split_identifier(target_name))
_RULE_TABLE_SUFFIXES: tuple[str, ...] = (
    '_patterns', '_keywords', '_placeholders', '_pattern', '_keyword',
    '_placeholder', '_patterns_builtin', '_pattern_builtin', '_markers',
    '_prefixes', '_suffixes', '_rules', '_builtin',
)
_RULE_TABLE_NAMES: frozenset[str] = frozenset({
    'patterns', 'rules', 'keywords', 'placeholders', 'markers',
    'prefixes', 'suffixes',
})
def _is_rule_table_target(name: str) -> bool:
    lower = str(name or '').lower()
    return (lower.startswith('rule_')
            or lower.endswith(_RULE_TABLE_SUFFIXES)
            or lower in _RULE_TABLE_NAMES)
def _classify_secret_target(target_name: str) -> tuple[bool, bool]:
    target_lower = target_name.lower()
    _negated = any(marker in target_lower
                   for marker in _NEGATED_SECRET_MARKERS)
    _token_target = (not _negated) and _token_target_name(target_name)
    _is_rule_config = _is_rule_table_target(target_name)
    is_secret_target = (not _is_rule_config) and (not _negated) and (
        any(_target_name_matches(target_name, kw) for kw in (
            'secret', 'password', 'passwd', 'pwd', 'api_key', 'apikey',
            'access_key', 'private_key', 'jwt', 'credential',
        )) or _token_target
    )
    return is_secret_target, _is_rule_config
def _match_known_pattern(value_str: str) -> tuple[str, str, str] | None:
    for pattern_name, pattern, cwe, severity in _SECRET_PATTERNS_BUILTIN:
        if re.search(pattern, value_str, re.IGNORECASE):
            return pattern_name, severity, cwe
    return None
def _match_by_target_name(target_name: str,
                          value_str: str) -> tuple[str, str, str] | None:
    if is_placeholder_secret(value_str) or len(value_str) < _MIN_SECRET_LEN:
        return None
    if is_regex_pattern_text(value_str):
        return None
    for pattern_name, _pattern, cwe, severity in _SECRET_PATTERNS_BUILTIN:
        if _target_name_matches(target_name, pattern_name.lower()):
            return pattern_name, severity, cwe
    return None
def _match_by_value_format(value_str: str) -> tuple[str, str, str] | None:
    if is_placeholder_secret(value_str):
        return None
    return _match_known_pattern(value_str)
def _looks_like_secret_value(text: str) -> bool:
    if len(text) < _MIN_SECRET_LEN or not text.isascii():
        return False
    has_digit = any(ch.isdigit() for ch in text)
    has_symbol = any((not ch.isalnum()) and (not ch.isspace())
                     and ch not in "_-" for ch in text)
    has_case_mix = (any(ch.islower() for ch in text)
                    and any(ch.isupper() for ch in text))
    return has_digit or has_symbol or has_case_mix
def _match_container_element(_ev: str, is_secret_target: bool,
                              *, allow_generic: bool = True
                              ) -> tuple[str, str, str] | None:
    if is_placeholder_secret(_ev):
        return None
    if _is_code_snippet_text(_ev) or is_regex_pattern_text(_ev):
        return None
    matched = _match_known_pattern(_ev)
    if matched is not None:
        return matched
    if (allow_generic and is_secret_target
            and _looks_like_secret_value(_ev)):
        return 'HARDCODED_SECRET', 'HIGH', 'CWE-798'
    return None
def _container_key_is_secret(key: ast.AST | None) -> bool:
    if isinstance(key, ast.Constant):
        return isinstance(key.value, str) and is_sensitive_name(key.value)
    return _sensitive_leaf_name(key)[0] is not None
def _iter_container_strings(
    value_node: ast.AST, *, allow_generic: bool = True,
    secret_scope: bool = False,
) -> Iterator[tuple[str, bool, bool]]:
    if isinstance(value_node, ast.Constant):
        if isinstance(value_node.value, str):
            yield value_node.value, allow_generic, secret_scope
        elif isinstance(value_node.value, bytes):
            yield (value_node.value.decode("utf-8", "replace"),
                   allow_generic, secret_scope)
        return
    if isinstance(value_node, ast.Dict):
        for key, value in zip(value_node.keys, value_node.values, strict=True):
            if key is not None:
                yield from _iter_container_strings(
                    key, allow_generic=False, secret_scope=False)
            yield from _iter_container_strings(
                value, allow_generic=True,
                secret_scope=secret_scope or _container_key_is_secret(key))
        return
    if isinstance(value_node, (ast.List, ast.Tuple, ast.Set)):
        for element in value_node.elts:
            yield from _iter_container_strings(
                element, allow_generic=allow_generic,
                secret_scope=secret_scope)
        return
    if isinstance(value_node, ast.Starred):
        yield from _iter_container_strings(
            value_node.value, allow_generic=allow_generic,
            secret_scope=secret_scope)
def _match_container_elements(value_node: ast.AST,
                              is_secret_target: bool) -> tuple[str, str, str] | None:
    for text, allow_generic, secret_scope in _iter_container_strings(value_node):
        matched = _match_container_element(
            text, is_secret_target or secret_scope,
            allow_generic=allow_generic)
        if matched is not None:
            return matched
    return None
def _match_by_keyword(value_str: str) -> tuple[str, str, str] | None:
    if is_placeholder_secret(value_str):
        return None
    if len(value_str) < _MIN_SECRET_LEN:
        return None
    if is_regex_pattern_text(value_str):
        return None
    if _is_rule_identifier_text(value_str):
        return None
    return 'HARDCODED_SECRET', 'HIGH', 'CWE-798'
def _build_secret_finding(matched: tuple[str, str, str], node: ast.AST,
                          target_names: list[str], filepath: str,
                          code: str) -> VulnerabilityFinding:
    matched_pn, matched_sev, matched_cwe = matched
    return VulnerabilityFinding(
        category=VulnerabilityCategory.HARDCODED_SECRET,
        severity=matched_sev,
        file=filepath,
        line=node.lineno,
        source=matched_pn,
        sink='='.join(target_names) if target_names else 'assignment',
        code_snippet=get_code_snippet(code, node.lineno),
        confidence=0.9 if matched_pn != 'HARDCODED_SECRET' else 0.75,
        suggestion="检测到硬编码" + matched_pn + ",应从环境变量或密钥管理服务获取",
        cwe_id=matched_cwe,
    )
class _LineFallbackState:
    def __init__(self) -> None:
        self.comment_spans: dict[int, list[tuple[int, int]]] | None = None
        self.string_spans: dict[int, list[tuple[int, int]]] | None = None
        self.line_starts: list[int] = []
        self.position_loaded = False
        self.emitted: set[tuple[int, str]] = set()
        self.literal_values: set[tuple[int, str]] = set()
    def load_position_tables(self, code: str) -> None:
        if self.position_loaded:
            return
        self.comment_spans = comment_only_spans(code)
        self.string_spans = string_comment_spans(code)
        self.line_starts = _source_line_starts(code)
        self.position_loaded = True
def _build_line_fallback_finding(pattern_name: str, severity: str, cwe: str,
                                 lineno: int, filepath: str,
                                 code: str) -> VulnerabilityFinding:
    return VulnerabilityFinding(
        category=VulnerabilityCategory.HARDCODED_SECRET,
        severity=severity,
        file=filepath,
        line=lineno,
        source=pattern_name,
        sink='regex_match',
        code_snippet=get_code_snippet(code, lineno),
        confidence=0.8,
        suggestion="检测到" + pattern_name + "格式密钥,应从环境变量或密钥管理服务获取",
        cwe_id=cwe,
    )
_LINE_FALLBACK_HINTS: tuple[str, ...] = (
    'akia', 'aws_secret_access_key', 'aiza', 'ghp_', 'ghs_', 'xoxb-', 'xoxp-',
    'api_key', 'api-key', 'apikey', 'secret', 'password', 'passwd', 'pwd',
    'jwt', 'private key', 'postgres', 'mysql', 'mongodb', 'redis', 'bearer',
)
def _line_may_hold_secret(line_text: str) -> bool:
    lower = line_text.lower()
    return any(hint in lower for hint in _LINE_FALLBACK_HINTS)
def _iter_line_text_fallbacks(
        lineno: int, code_lines: list[str], code: str, filepath: str,
        state: _LineFallbackState) -> Iterator[VulnerabilityFinding]:
    if not 0 < lineno <= len(code_lines):
        return
    line_text = code_lines[lineno - 1]
    if not _line_may_hold_secret(line_text):
        return
    state.load_position_tables(code)
    _line_start = state.line_starts[lineno - 1]
    for pattern_name, pattern, cwe, severity in _SECRET_PATTERNS_BUILTIN:
        emitted_key = (lineno, pattern_name)
        if emitted_key in state.emitted:
            continue
        for match in re.finditer(pattern, line_text, re.IGNORECASE):
            _match_offset = _line_start + match.start()
            if _offset_in_spans(_match_offset, state.line_starts,
                                state.comment_spans):
                continue
            _matched_value = match.group(0)
            if (_is_embedded_assignment_text(_matched_value)
                    and _offset_in_spans(_match_offset, state.line_starts,
                                         state.string_spans)):
                continue
            _quoted = re.search(r'["\']([^"\']+)["\']', _matched_value)
            if _quoted is not None:
                _matched_value = _quoted.group(1)
            if (lineno, _matched_value) in state.literal_values:
                continue
            if is_placeholder_secret(_matched_value):
                continue
            state.emitted.add(emitted_key)
            yield _build_line_fallback_finding(
                pattern_name, severity, cwe, lineno, filepath, code)
            break
def _strategy_literal_applicable(value_node: ast.AST, *,
                                 blocked: bool) -> bool:
    return (not blocked and not isinstance(value_node, ast.Call)
            and is_static_literal_expr(value_node))
def _strategy_value_format_applicable(value_str: str, value_node: ast.AST,
                                      is_rule_config: bool) -> bool:
    if is_rule_config or isinstance(value_node, ast.Call):
        return False
    return not (_is_code_snippet_text(value_str)
                or _is_embedded_assignment_text(value_str))
def _strategy_container_applicable(value_node: ast.AST,
                                   is_rule_config: bool) -> bool:
    return (not is_rule_config
            and isinstance(value_node, (ast.Dict, ast.List, ast.Tuple,
                                        ast.Set)))
def _match_secret_strategies(value_node: ast.AST,
                             value_str: str, target_name: str,
                             is_secret_target: bool,
                             is_rule_config: bool) -> tuple[str, str, str] | None:
    if _strategy_literal_applicable(
            value_node, blocked=is_rule_config or not is_secret_target):
        matched = _match_by_target_name(target_name, value_str)
        if matched is not None:
            return matched
    if _strategy_value_format_applicable(value_str, value_node,
                                         is_rule_config):
        matched = _match_by_value_format(value_str)
        if matched is not None:
            return matched
    if _strategy_container_applicable(value_node, is_rule_config):
        matched = _match_container_elements(value_node, is_secret_target)
        if matched is not None:
            return matched
    if _strategy_literal_applicable(
            value_node, blocked=not is_secret_target):
        return _match_by_keyword(value_str)
    return None
def _assign_target_names(_targets: list[ast.AST]) -> list[str]:
    _names: list[str] = []
    for target in _targets:
        _name = _se03_target_name(target)
        if _name is not None:
            _names.append(_name)
    return _names
def _scan_secret_value(node: ast.AST, value_node: ast.AST,
                       target_names: list[str], filepath: str, code: str
                       ) -> tuple[VulnerabilityFinding | None, bool]:
    value_str = _assemble_value_str(value_node)
    if value_str is None:
        return None, False
    if not value_str and not target_names:
        return None, True
    target_name = '_'.join(target_names)
    is_secret_target, is_rule_config = _classify_secret_target(target_name)
    matched = _match_secret_strategies(
        value_node, value_str, target_name,
        is_secret_target, is_rule_config)
    if matched is None:
        return None, True
    return _build_secret_finding(
        matched, node, target_names, filepath, code), True
def _secret_assignment_pair(node: ast.AST):
    pair = assign_targets_value(node)
    if pair is None and isinstance(node, (ast.NamedExpr, ast.AugAssign)):
        pair = ([node.target], node.value)
    return pair
def _scan_secret_assign_node(node: ast.AST, code: str, filepath: str
                             ) -> VulnerabilityFinding | None:
    pair = _secret_assignment_pair(node)
    if pair is None:
        return None
    targets, value_node = pair
    finding, assembled = _scan_secret_value(
        node, value_node, _assign_target_names(targets), filepath, code)
    if finding is not None:
        return finding
    if not assembled:
        return None
    for target in targets:
        if _se03_target_name(target) is not None:
            continue
        for name, aligned_value, _line in _se03_pairs_for_target(
                target, value_node, node.lineno):
            finding, _assembled = _scan_secret_value(
                node, aligned_value, [name], filepath, code)
            if finding is not None:
                return finding
    return None
def scan_hardcoded_secrets(tree: ast.Module, code: str,
                           filepath: str = _DEFAULT_FILEPATH
                           ) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    code = _normalize_text_source(code)
    filepath = normalize_filepath(filepath)
    if finding_scan_exempt(filepath):
        return findings
    tree = _coerce_tree(tree)
    if tree is None:
        _log.debug("[SecretScan] 缺少可遍历的 AST，跳过硬编码凭据扫描")
        return findings
    code_lines = code.split('\n')
    _fallback_state = _LineFallbackState()
    for node in tree_nodes(tree):
        finding = _scan_secret_assign_node(node, code, filepath)
        if finding is not None:
            findings.append(finding)
            pair = _secret_assignment_pair(node)
            if pair is not None and isinstance(pair[1], ast.Constant):
                literal_value = _assemble_value_str(pair[1])
                if literal_value:
                    _fallback_state.literal_values.add(
                        (finding.line, literal_value))
    _fallback_state.emitted.update(
        (finding.line, finding.source) for finding in findings)
    for lineno in range(1, len(code_lines) + 1):
        findings.extend(_iter_line_text_fallbacks(
            lineno, code_lines, code, filepath, _fallback_state))
    findings.extend(scan_env_default_secrets(tree, code, filepath))
    return findings
def _env_receiver_shadowed(node: ast.Call,
                           scope_bindings: _ScopeBindings,
                           module_bindings: dict[str, str],
                           func_bindings: dict[str, str]) -> bool:
    local_name = resolve_call_name(node)
    if not local_name:
        return False
    head = local_name.split('.', 1)[0]
    identity = func_bindings.get(
        head, module_bindings.get(head, head if head == 'os' else ''))
    if identity != 'os' and not identity.startswith('os.'):
        return False
    return scope_bindings.is_shadowed(node, head, real_imports=True)
_ENV_KEY_HINT_WORDS = frozenset({
    'secret', 'password', 'passwd', 'pwd', 'key', 'token', 'credential',
    'apikey',
})
_CONFIG_RECEIVER_NAMES = frozenset({
    'config', 'conf', 'cfg', 'configuration', 'configs',
    'setting', 'settings', 'option', 'options',
})
def _env_hint_is_secret(hint: str) -> bool:
    return any(word in _ENV_KEY_HINT_WORDS
               for word in split_identifier(hint))
def _is_config_receiver(receiver: str) -> bool:
    tail = receiver.rsplit(".", 1)[-1].lower()
    return (tail in _CONFIG_RECEIVER_NAMES
            or tail.endswith(("_config", "_settings", "_options")))
def _report_env_default(findings: list, node: ast.Call, sink: str,
                        hint: str, code: str, filepath: str) -> bool:
    if not _env_hint_is_secret(hint):
        return False
    findings.append(VulnerabilityFinding(
        category=VulnerabilityCategory.HARDCODED_SECRET,
        severity="MEDIUM",
        file=filepath,
        line=node.lineno,
        source="env_default",
        sink=sink,
        code_snippet=get_code_snippet(code, node.lineno),
        confidence=0.7,
        suggestion="环境变量默认值包含密钥,移除硬编码默认值",
        cwe_id="CWE-798",
    ))
    return True
_ENV_DEFAULT_CALL_KINDS: frozenset[str] = frozenset({
    'os.getenv', 'config.get', 'os.environ.get', 'os.environ.setdefault',
})
def _env_default_call_kind(call_name: str) -> str | None:
    if call_name in _ENV_DEFAULT_CALL_KINDS:
        return call_name
    if not call_name.endswith('.get'):
        return None
    receiver = call_name[:-4]
    if not _is_config_receiver(receiver):
        return None
    return 'config.get'
def scan_env_default_secrets(tree: ast.Module, code: str,
                             filepath: str = _DEFAULT_FILEPATH
                             ) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    filepath = normalize_filepath(filepath)
    if finding_scan_exempt(filepath):
        return findings
    tree = _coerce_tree(tree)
    if tree is None:
        _log.debug("[SecretScan] 缺少可遍历的 AST，跳过环境变量默认值扫描")
        return findings
    func_bindings, module_bindings = _collect_import_call_bindings(tree)
    scope_bindings = _ScopeBindings(
        tree, real_import_modules=frozenset({'os'}))
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        cn = _canonical_call_name(
            node, func_bindings, module_bindings, scope_bindings)
        call_kind = _env_default_call_kind(cn)
        if call_kind is None:
            continue
        if _env_receiver_shadowed(
                node, scope_bindings, module_bindings, func_bindings):
            continue
        reported = _report_env_default(
            findings, node, call_kind,
            _positional_env_hint(node, call_kind), code, filepath)
        if not reported:
            for hint in _keyword_env_hints(node, call_kind):
                if _report_env_default(
                        findings, node, call_kind, hint, code, filepath):
                    break
    return findings
def _positional_env_hint(node: ast.Call, call_name: str) -> str:
    if call_name == 'config.get':
        if len(node.args) not in (2, 3):
            return ''
        if any(kw.arg in {'default', 'fallback'} for kw in node.keywords):
            return ''
        default_arg = node.args[-1]
        if not (isinstance(default_arg, ast.Constant)
                and isinstance(default_arg.value, str)
                and not is_placeholder_secret(default_arg.value)):
            return ''
        hint = _config_option_name(node)
        if len(node.args) == 2 and not _env_hint_is_secret(hint):
            return ''
        return hint
    default_index = 1
    if len(node.args) <= default_index:
        return ''
    default_arg = node.args[default_index]
    if not (isinstance(default_arg, ast.Constant)
            and isinstance(default_arg.value, str)
            and not is_placeholder_secret(default_arg.value)):
        return ''
    return _positional_env_name(node)
def _keyword_env_hints(node: ast.Call, call_name: str) -> list[str]:
    return [hint for hint in (
        _keyword_env_hint(kw, node, call_name) for kw in node.keywords)
            if hint]
def _keyword_env_hint(kw: ast.keyword, node: ast.Call,
                      call_name: str) -> str:
    hint = (kw.arg or '').lower()
    is_default = hint == 'default' or (
        hint == 'fallback' and call_name == 'config.get')
    if not is_default:
        return ''
    if not (isinstance(kw.value, ast.Constant)
            and isinstance(kw.value.value, str)):
        return ''
    if is_placeholder_secret(kw.value.value):
        return ''
    return (_config_option_name(node) if call_name == 'config.get'
            else _positional_env_name(node))
def _env_name_arg(arg: ast.AST) -> str:
    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        return arg.value
    return ''
def _keyword_string_arg(node: ast.Call, names: tuple[str, ...]) -> str:
    for kw in node.keywords:
        if kw.arg in names:
            return _env_name_arg(kw.value)
    return ''
def _positional_env_name(node: ast.Call) -> str:
    if node.args:
        return _env_name_arg(node.args[0])
    return _keyword_string_arg(node, ('key', 'name'))
def _config_option_name(node: ast.Call) -> str:
    keyword = _keyword_string_arg(node, ('option', 'name', 'key'))
    if keyword:
        return keyword
    if len(node.args) >= 3:
        return _env_name_arg(node.args[1])
    if len(node.args) == 2:
        if any(kw.arg in {'default', 'fallback'} for kw in node.keywords):
            return _env_name_arg(node.args[1])
        return _env_name_arg(node.args[0])
    return _positional_env_name(node)
CREDENTIAL_KEYWORDS = (
    "password", "passwd", "pwd", "secret", "api_key",
    "apikey", "access_key", "token", "private_key", "auth_token",
)
CREDENTIAL_PATTERNS = re.compile(
    r'(?:' + '|'.join(CREDENTIAL_KEYWORDS) + r')'
    r'\s*[:=]\s*(?:[A-Za-z_]\w*\s*=\s*)?["\']([^"\']{4,})["\']',
    re.IGNORECASE,
)
_CREDENTIAL_PLACEHOLDER_VALUES = frozenset({
    'hardcoded_secret', 'sk-abc123', 'test_secret', 'example_key',
    'your_api_key', 'placeholder', 'xxxx', 'test_token', 'fake_secret'})
def _credential_placeholder(value: str) -> bool:
    lower = value.lower()
    return (lower in _CREDENTIAL_PLACEHOLDER_VALUES
            or is_placeholder_secret(value)
            or _is_code_snippet_text(value)
            or is_regex_pattern_text(value)
            or any(ph in lower for ph in _SE03_PLACEHOLDERS))
def _source_line_starts(source: str) -> list[int]:
    _starts = [0]
    _idx = source.find('\n')
    while _idx != -1:
        _starts.append(_idx + 1)
        _idx = source.find('\n', _idx + 1)
    return _starts
def _offset_in_spans(offset: int, starts: list[int],
                     spans: dict[int, list[tuple[int, int]]] | None) -> bool:
    if not spans:
        return False
    _row = bisect.bisect_right(starts, offset)
    _col = offset - starts[_row - 1]
    return any(_s <= _col < _e for _s, _e in spans.get(_row, ()))
def check_hardcoded_credentials(source: str,
                                rel_path: str = _DEFAULT_FILEPATH,
                                cred_pattern: re.Pattern | None = None
                                ) -> list[dict]:
    if isinstance(cred_pattern, str):
        try:
            cred_pattern = re.compile(cred_pattern)
        except re.error as _re_err:  # jwsgj:silent-ok 自定义正则无效即回退内置模式
            _log.warning("[SE-03] 自定义凭据正则无效，回退内置模式: %s", _re_err)
            cred_pattern = None
    if cred_pattern is not None and not isinstance(cred_pattern, re.Pattern):
        _log.warning("[SE-03] 自定义凭据模式非正则对象 %s，回退内置模式",
                     type(cred_pattern).__name__)
        cred_pattern = None
    _pattern = cred_pattern if cred_pattern is not None else CREDENTIAL_PATTERNS
    if _pattern.groups < 1:
        _log.warning("[SE-03] 自定义凭据正则缺少捕获组，回退内置模式")
        _pattern = CREDENTIAL_PATTERNS
    _source = _normalize_text_source(source)
    rel_path = normalize_filepath(rel_path)
    if finding_scan_exempt(rel_path):
        return []
    _exempt_spans = string_comment_spans(_source)
    _starts = _source_line_starts(_source)
    findings: list[dict] = []
    for match in _pattern.finditer(_source):
        _matched_val = match.group(1)
        if not isinstance(_matched_val, str):
            continue
        if _credential_placeholder(_matched_val):
            continue
        if _offset_in_spans(match.start(), _starts, _exempt_spans):
            continue
        _line_num = bisect.bisect_right(_starts, match.start())
        _target = re.split(r'\s*[:=]\s*', match.group(0), maxsplit=1)[0]
        findings.append({
            "file": rel_path, "line": _line_num,
            "type": "hardcoded_credential", "severity": "high",
            "message": f"疑似硬编码凭据: {_target} = '<已脱敏>'...",
        })
    return findings
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "sec_registry_fns": {
                'SE10': check_SE10, 'SE28': check_SE28,
                'SE36': check_SE36,
            },
            "se_checks": {
                'SE03': check_SE03, 'SE10': check_SE10, 'SE28': check_SE28,
                'SE36': check_SE36,
            },
            "rule_bindings": {'IF-01': analyze_implicit_flow},
        },
    }

from __future__ import annotations

import ast
import hashlib
import logging
import re
import threading
import urllib.parse as _urlparse
from collections import Counter
from collections.abc import Callable
from copy import deepcopy
from dataclasses import dataclass, field
from typing import Any

from jwsgj.diag_se_data import scan_hardcoded_secrets
from jwsgj.diag_se_knowledge import get_security_knowledge
from jwsgj.diag_se_stdlib import yaml_load_is_safe
from jwsgj.diag_shared_ast_bindings import build_scope_index
from jwsgj.diag_shared_ast_nodes import (
    ASTPreciseParser,
    build_parent_map,
    collect_param_names,
    dotted_name,
    is_static_literal_expr,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_views import (
    collect_module_bindings_detailed,
    tree_nodes,
)
from jwsgj.diag_shared_source_scan import get_code_snippet
from jwsgj.diag_taint_dataflow import (
    SCALAR_SANITIZER_CALLS,
    TAINT_SOURCE_CALLS,
    PreciseTaintAnalyzer,
    ScopeFacts,
    _is_literal_value,
    _is_scalar_sanitizer_call,
    _sanitized_before,
    collect_regex_guards,
    collect_sanitized_keys,
    collect_scalar_sanitized_vars,
    collect_scope_facts,
    is_sanitized,
    iter_expr_origins,
    lookup_name_assignment,
    resolve_taint_source,
    scope_visible_taints,
)
from jwsgj.diag_taint_model import (
    CFGBuilder,
    DUChainAnalyzer,
    TaintNameResolution,
    _element_binding_pairs,
)
from jwsgj.diag_types_defs import (
    VulnerabilityFinding,
)
from jwsgj.diag_types_vocab import (
    SUBPROCESS_CHECK_CALL,
    SUBPROCESS_CHECK_OUTPUT,
    VULN_RENDER_TEMPLATE_STRING,
    VulnerabilityCategory,
    normalize_filepath,
)
from jwsgj.engine_d2_flow import (
    POWERSHELL_PROGRAMS,
    interpreter_option_consumes_value,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'CALL_ALIAS_MODULES',
    'CMD_DANGER_FUNCTIONS',
    'DESER_DANGER_FUNCTIONS',
    'PATH_DANGER_FUNCTIONS',
    'ImportCallResolver',
    'PreciseVulnDetector',
    'build_vulnerability_finding',
    'origin_from_binding',
    'release_scanner_caches',
    'scan_command_injection',
    'scan_deserialization',
    'scan_ldap_injection',
    'scan_path_traversal',
    'scan_pattern_channels',
    'scan_sql_injection',
    'scan_ssti',
    'scan_xss',
    'scan_xxe',
]
logger = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
_EMPTY_NAME_SET: frozenset[str] = frozenset()
_KNOWLEDGE_CATEGORY_MAP: dict[str, VulnerabilityCategory] = {
    "sql_injection": VulnerabilityCategory.SQL_INJECTION,
    "path_traversal": VulnerabilityCategory.PATH_TRAVERSAL,
    "code_injection": VulnerabilityCategory.COMMAND_INJECTION,
    "command_injection": VulnerabilityCategory.COMMAND_INJECTION,
    "deserialization": VulnerabilityCategory.DESERIALIZATION,
    "ssti": VulnerabilityCategory.SSTI,
    "xss": VulnerabilityCategory.XSS,
    "weak_crypto": VulnerabilityCategory.WEAK_CRYPTO,
    "insecure_config": VulnerabilityCategory.INSECURE_CONFIG,
    "xxe": VulnerabilityCategory.XXE,
    "open_redirect": VulnerabilityCategory.OPEN_REDIRECT,
    "secret": VulnerabilityCategory.HARDCODED_SECRET,
    "ssrf": VulnerabilityCategory.INSECURE_CONFIG,
    "ldap_injection": VulnerabilityCategory.LDAP_INJECTION,
}
_KNOWLEDGE_SEVERITY_MAP: dict[str, str] = {
    "P0": "CRITICAL", "P1": "HIGH", "P2": "MEDIUM", "P3": "LOW",
    "CRITICAL": "CRITICAL", "HIGH": "HIGH", "MEDIUM": "MEDIUM",
    "LOW": "LOW",
}
def _clean_knowledge_rules(rules: Any) -> list[dict]:
    if not isinstance(rules, (list, tuple)):
        return []
    return [rule for rule in rules
            if isinstance(rule, dict)
            and isinstance(rule.get("name"), str) and rule.get("name")]
def _compile_knowledge_patterns(rules: list[dict]) -> dict[str, re.Pattern]:
    return {
        name: re.compile(r"\b" + re.escape(name) + r"\b")
        for name in {rule.get("name", "") for rule in rules}
        if isinstance(name, str) and name
    }
def _normalize_knowledge_severity(severity: str) -> str:
    return _KNOWLEDGE_SEVERITY_MAP.get(str(severity).upper(), "MEDIUM")
def _knowledge_finding(rule: dict, pattern_name: str, node: ast.AST,
                       filepath: str) -> VulnerabilityFinding:
    category_name = rule.get("category", "general")
    if not isinstance(category_name, str):
        category_name = "general"
    category = _KNOWLEDGE_CATEGORY_MAP.get(
        category_name, VulnerabilityCategory.INSECURE_CONFIG)
    description = rule.get("description")
    return VulnerabilityFinding(
        category=category,
        severity=_normalize_knowledge_severity(rule.get("severity", "P2")),
        file=filepath,
        line=getattr(node, "lineno", 0),
        source=f"knowledge:{pattern_name}",
        sink=pattern_name,
        suggestion=description if isinstance(description, str) else "",
        cwe_id="",
    )
def _iter_knowledge_hits(rules: list[dict], node_srcs: list,
                         compiled: dict, emitted: set):
    for rule in rules:
        pattern_name = rule.get("name", "")
        if not pattern_name:
            continue
        pattern = compiled.get(pattern_name)
        for node, src in node_srcs:
            if pattern is not None and pattern.search(src):
                key = (pattern_name, getattr(node, "lineno", 0),
                       getattr(node, "col_offset", 0))
                if key in emitted:
                    continue
                emitted.add(key)
                yield rule, pattern_name, node
def _iter_interp_nodes(expr: ast.AST, prune=None,
                       tree: ast.AST | None = None):
    if prune is None:
        prune = lambda node: _is_scalar_sanitizer_call(node, tree)
    if prune(expr):
        return
    stack = [expr]
    while stack:
        cur = stack.pop()
        yield cur
        for child in ast.iter_child_nodes(cur):
            if not prune(child):
                stack.append(child)
def _expr_contains_taint(expr: ast.AST, taint: set,
                        tree: ast.AST | None = None) -> bool:
    for _sub in _iter_interp_nodes(expr, tree=tree):
        if isinstance(_sub, ast.Name):
            if _sub.id in taint:
                return True
            continue
        if (resolve_taint_source(_sub, TAINT_SOURCE_CALLS, tree)
                is not None):
            return True
    return False
def _stmt_has_input_channel(first_arg: ast.AST,
                            taint: frozenset,
                            params_here: set,
                            tree: ast.AST | None = None) -> bool:
    if isinstance(first_arg, (ast.BinOp, ast.JoinedStr)):
        return _interp_has_input_channel(
            first_arg, taint, params_here, tree)
    if isinstance(first_arg, ast.BoolOp):
        return any(_stmt_has_input_channel(value, taint, params_here, tree)
                   for value in first_arg.values)
    if isinstance(first_arg, ast.IfExp):
        return (_stmt_has_input_channel(
                    first_arg.body, taint, params_here, tree)
                or _stmt_has_input_channel(
                    first_arg.orelse, taint, params_here, tree))
    if isinstance(first_arg, ast.NamedExpr):
        return _stmt_has_input_channel(
            first_arg.value, taint, params_here, tree)
    if isinstance(first_arg, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
        return _interp_has_input_channel(
            first_arg, taint, params_here, tree)
    if isinstance(first_arg, ast.Name):
        return first_arg.id in taint or first_arg.id in params_here
    if isinstance(first_arg, (ast.Call, ast.Attribute, ast.Subscript)):
        return (resolve_taint_source(first_arg, TAINT_SOURCE_CALLS, tree)
                is not None
                or _interp_has_input_channel(
                    first_arg, taint, params_here, tree))
    return False
def _interp_has_input_channel(expr: ast.AST, taint: frozenset,
                              params_here: set,
                              tree: ast.AST | None = None) -> bool:
    interp_names = [sub.id for sub in _iter_interp_nodes(expr, tree=tree)
                    if isinstance(sub, ast.Name)]
    return (_expr_contains_taint(expr, taint, tree)
            or any(name in params_here for name in interp_names))
def _collect_func_param_ranges(tree: ast.Module,
                                scope_idx: dict | None = None) -> list:
    ranges: list = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
            continue
        ps = collect_param_names(node)
        if not ps:
            continue
        end = getattr(node, "end_lineno", node.lineno) or node.lineno
        scope = _function_body_scope(node, scope_idx or {})
        ranges.append((node.lineno, end, ps, scope, node))
    return ranges
def _function_body_scope(node: ast.AST, scope_idx: dict) -> str:
    parent = scope_idx.get(id(node), "")
    name = getattr(node, "name", "")
    if not name:
        return parent
    return f"{parent}.{name}" if parent else name
def _params_at(ranges: list, lineno: int) -> set:
    out: set = set()
    for s, e, ps, _scope, _node in ranges:
        if s <= lineno <= e:
            out |= ps
    return out
# 外部边界函数：只有这些函数的形参才代表“进程外部输入”。本扫描器是
# 进程内（intraprocedural）分析，无法证明内部辅助函数的实参来自用户，把
# 所有形参一律当作污点源会让每个 `open(path)` / `subprocess.run(argv)`
# 辅助函数都变成 P1 误报（实测 354/354 条 path_traversal 均由此产生）。
# 因此污点源收敛到进程边界：CLI 分发入口 `cmd_*` 与 `main`。
_EXTERNAL_BOUNDARY_PREFIXES: tuple[str, ...] = ("cmd_",)
_EXTERNAL_BOUNDARY_NAMES: frozenset[str] = frozenset({"main"})
def _is_external_boundary(node) -> bool:
    name = getattr(node, "name", "") or ""
    if not isinstance(name, str):
        return False
    return (name in _EXTERNAL_BOUNDARY_NAMES
            or any(name.startswith(p) for p in _EXTERNAL_BOUNDARY_PREFIXES))
def _external_params_at(ranges: list, lineno: int) -> set:
    out: set = set()
    for s, e, ps, _scope, node in ranges:
        if s <= lineno <= e and _is_external_boundary(node):
            out |= ps
    return out
def _lambda_param_ranges_at(ranges: list, lineno: int,
                            name: str | None = None) -> list:
    return [
        entry for entry in ranges
        if isinstance(entry[4], ast.Lambda)
        and entry[0] <= lineno <= entry[1]
        and (name is None or name in entry[2])
    ]
def _binding_param_shadowed(ctx: _ScanContext, name: str, stmt_scope: str,
                            scope: str, lineno: int, stmt: ast.AST) -> bool:
    for start, end, params, _fn_scope, fn_node in ctx.func_param_ranges:
        if (isinstance(fn_node, ast.Lambda) and name in params
                and start <= lineno <= end
                and not start <= stmt.lineno <= end):
            return True
    if stmt_scope == scope:
        return False
    for start, end, params, fn_scope, fn_node in ctx.func_param_ranges:
        if isinstance(fn_node, ast.Lambda):
            continue
        if name not in params or not start <= lineno <= end:
            continue
        if fn_scope == stmt_scope:
            continue
        if stmt_scope and not fn_scope.startswith(stmt_scope + "."):
            continue
        if fn_scope != scope and not scope.startswith(fn_scope + "."):
            continue
        return True
    return False
CALL_ALIAS_MODULES: dict[str, dict[str, tuple[str, ...]]] = {
    "path": {
        "os": ("open", "remove", "unlink", "rmdir", "mkdir", "makedirs"),
        "shutil": ("copy", "move", "rmtree"),
        "zipfile": ("ZipFile",),
        "tarfile": ("open",),
    },
    "cmd": {
        "os": ("system", "popen", "popen2", "popen3", "popen4",
               "execv", "execve", "execl", "execle"),
        "subprocess": ("call", "Popen", "run", "check_call", "check_output",
                       "getoutput", "getstatusoutput"),
    },
    "deser": {
        "pickle": ("load", "loads", "dump", "dumps"),
        "yaml": ("load", "unsafe_load", "safe_load", "dump"),
        "marshal": ("load", "loads"),
        "dill": ("load", "loads"),
        "torch": ("load",),
    },
    "xss": {
        "flask": ("render_template_string", "jsonify", "make_response"),
        "markupsafe": ("Markup",),
        "django.http": ("HttpResponse",),
        "django.utils.safestring": ("mark_safe",),
        "fastapi.responses": ("HTMLResponse",),
        "starlette.responses": ("Response",),
    },
    "ldap": {"ldap": ("search", "search_s", "search_ext", "search_ext_s")},
}
def origin_from_binding(aliases: set, from_origins: dict, head: str,
                        rest: str, module: str,
                        members: tuple[str, ...],
                        star_bound: bool = False) -> str:
    if rest:
        return f"{module}.{rest}" if head in aliases and rest in members else ""
    origin = from_origins.get(head)
    if origin:
        return f"{module}.{origin}"
    if star_bound and head in members:
        return f"{module}.{head}"
    return ""
class ImportCallResolver:
    __slots__ = ("_bindings", "_star_modules", "_table", "_tree")
    def __init__(self, tree: Any, table: dict[str, tuple[str, ...]]) -> None:
        self._tree = tree
        self._table = table
        self._bindings: dict[str, tuple[set, dict]] = {}
        self._star_modules: frozenset[str] | None = None
    def _star_bound(self, module: str) -> bool:
        return False
    def _binding(self, module: str) -> tuple[set, dict]:
        hit = self._bindings.get(module)
        if hit is None:
            hit = collect_module_bindings_detailed(
                self._tree, module, self._table[module])
            self._bindings[module] = hit
        return hit
    def resolve(self, call_name: str) -> str:
        if not call_name:
            return call_name
        head, _sep, rest = call_name.partition(".")
        for module, members in self._table.items():
            aliases, from_origins = self._binding(module)
            resolved = origin_from_binding(
                aliases, from_origins, head, rest, module, members,
                star_bound=self._star_bound(module))
            if resolved:
                return resolved
        return call_name
def build_vulnerability_finding(category: Any, *, code: Any, filepath: Any,
                                line: int,
                                source: str, sink: str, severity: str,
                                confidence: float, suggestion: str, cwe_id: str,
                                taint_origin: str = "") -> VulnerabilityFinding:
    filepath = normalize_filepath(filepath)
    return VulnerabilityFinding(
        category=category,
        severity=severity,
        file=filepath,
        line=line,
        source=source,
        sink=sink,
        code_snippet=get_code_snippet(code, line, context=0),
        taint_origin=taint_origin,
        confidence=confidence,
        suggestion=suggestion,
        cwe_id=cwe_id,
    )
_SQL_DANGER_PATTERNS = frozenset({
    'execute', 'executemany', 'raw', 'extra',
})
_SQL_STATEMENT_KWARGS = (
    'sql', 'statement', 'query', 'operation', 'raw_query',
)
_SQL_EXTRA_STATEMENT_KWARGS = ('select', 'where', 'tables', 'order_by')
_DDL_KEYWORDS = frozenset({'CREATE', 'DROP', 'ALTER', 'RENAME', 'TRUNCATE'})
_TAINT_TRANSPARENT_CALLS = frozenset({'str', 'repr', 'ascii', 'format'})
def _is_static_transparent_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    values = [*node.args, *(kw.value for kw in node.keywords)]
    if isinstance(func, ast.Name) and func.id in _TAINT_TRANSPARENT_CALLS:
        return all(is_static_literal_expr(value) for value in values)
    if isinstance(func, ast.Attribute) and func.attr == 'format':
        values.append(func.value)
        return all(is_static_literal_expr(value) for value in values)
    return False
@dataclass(frozen=True)
class _SqlCallSite:
    node: ast.Call
    call_name: str
    taint: frozenset
    params_here: frozenset
    first_arg: ast.AST
@dataclass
class _ScanContext:
    tree: ast.Module
    code: str
    filepath: str
    facts: ScopeFacts
    func_param_ranges: list
    input_origins: dict = field(default_factory=dict)
    binding_index: list = field(default_factory=list)
    parent_map: dict = field(default_factory=dict)
    vis_cache: dict[str, frozenset] = field(default_factory=dict)
@dataclass
class _CmdScanContext(_ScanContext):
    sanitized: dict = field(default_factory=dict)
    sanitized_keys: dict = field(default_factory=dict)
    guards: dict = field(default_factory=dict)
def _collect_input_origins(tree: ast.Module, facts: ScopeFacts,
                           func_param_ranges: list,
                           binding_index: list) -> dict:
    origins = dict(facts.origins)
    shadow = (facts.local_bindings, facts.global_names, facts.class_scopes)
    for _start, _end, params, scope, node in func_param_ranges:
        if isinstance(node, ast.Lambda) or not _is_external_boundary(node):
            continue
        for name in params:
            key = TaintNameResolution.owner_key(scope, name, shadow)
            origins.setdefault(key, _FUNCTION_PARAMETER_ORIGIN)
    changed = True
    while changed:
        changed = False
        for _position, scope, names, value, _stmt in binding_index:
            def _origin_of(name: str, scope: str = scope) -> str | None:
                key = TaintNameResolution.resolve_taint_key(
                    scope, name, origins, shadow)
                return origins.get(key) if key is not None else None
            origin = next(
                iter_expr_origins(value, _origin_of, tree=tree), None)
            if origin is None:
                continue
            for name in names:
                key = TaintNameResolution.owner_key(scope, name, shadow)
                if key not in origins:
                    origins[key] = origin
                    changed = True
    return origins
def _build_scan_context(analyzer: PreciseTaintAnalyzer, tree: ast.Module,
                         code: str, filepath: str,
                         facts: ScopeFacts | None = None) -> _ScanContext:
    facts = facts or collect_scope_facts(analyzer, tree)
    func_param_ranges = _collect_func_param_ranges(tree, facts.scope_idx)
    binding_index = _build_binding_index(tree, facts.scope_idx)
    return _ScanContext(
        tree=tree, code=code, filepath=filepath, facts=facts,
        func_param_ranges=func_param_ranges,
        input_origins=_collect_input_origins(
            tree, facts, func_param_ranges, binding_index),
        binding_index=binding_index,
        parent_map=build_parent_map(tree),
    )
def _build_cmd_scan_context(analyzer: PreciseTaintAnalyzer,
                            tree: ast.Module, code: str,
                            filepath: str) -> _CmdScanContext:
    base = _build_scan_context(analyzer, tree, code, filepath)
    facts = base.facts
    shadow = (facts.local_bindings, facts.global_names, facts.class_scopes)
    return _CmdScanContext(
        tree=tree, code=code, filepath=filepath, facts=facts,
        func_param_ranges=base.func_param_ranges,
        input_origins=base.input_origins,
        binding_index=base.binding_index,
        parent_map=base.parent_map,
        sanitized=collect_scalar_sanitized_vars(
            tree, facts.scope_idx, facts.origins, shadow=shadow),
        sanitized_keys=collect_sanitized_keys(
            tree, set(_CMD_SHELL_QUOTE_CALLS), facts.scope_idx, shadow),
        guards=collect_regex_guards(tree),
    )
def _visible_taints(ctx: _ScanContext, scope: str) -> frozenset:
    facts = ctx.facts
    return scope_visible_taints(
        ctx.input_origins or facts.origins, scope,
        facts.local_bindings, facts.global_names,
        facts.class_scopes, ctx.vis_cache)
def _visible_input_taints(ctx: _ScanContext, scope: str,
                          lineno: int, col: int | None = None) -> frozenset:
    taints = _visible_taints(ctx, scope)
    params = _external_params_at(ctx.func_param_ranges, lineno)
    if params:
        taints = taints.union(params)
    return frozenset(
        name for name in taints
        if not _literal_binding_dominates(ctx, name, scope, lineno, col))
def _lambda_sanitized_keys(ctx: _ScanContext, sanitized_keys: dict,
                           lineno: int, scope: str,
                           name: str | None = None) -> dict:
    ranges = _lambda_param_ranges_at(ctx.func_param_ranges, lineno, name)
    if not ranges:
        return sanitized_keys
    shadow = (ctx.facts.local_bindings, ctx.facts.global_names,
              ctx.facts.class_scopes)
    filtered = dict(sanitized_keys)
    for _start, _end, params, _fn_scope, node in ranges:
        names = (name,) if name is not None else params
        start_pos = (node.lineno, getattr(node, "col_offset", 0) or 0)
        end_pos = (getattr(node, "end_lineno", node.lineno) or node.lineno,
                   getattr(node, "end_col_offset", 0) or 0)
        for param in names:
            key = TaintNameResolution.resolve_taint_key(
                scope, param, sanitized_keys, shadow)
            if key is None:
                continue
            filtered[key] = [
                entry for entry in filtered.get(key, ())
                if start_pos <= (entry[0], entry[1]) <= end_pos
            ]
    return filtered
def _target_name_ids(target: ast.AST | list[ast.AST]) -> list[str]:
    if isinstance(target, list):
        return [name for elt in target for name in _target_name_ids(elt)]
    if isinstance(target, ast.Name):
        return [target.id]
    if isinstance(target, (ast.Tuple, ast.List)):
        names: list[str] = []
        for elt in target.elts:
            names.extend(_target_name_ids(elt))
        return names
    if isinstance(target, ast.Starred):
        return _target_name_ids(target.value)
    return []
def _binding_statement_targets(stmt: ast.AST) -> list[ast.AST]:
    if isinstance(stmt, ast.Assign):
        return list(stmt.targets)
    if isinstance(stmt, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
        return [stmt.target]
    return []
def _binding_scope_visible(scope: str, stmt_scope: str,
                           class_scopes: frozenset[str]) -> bool:
    if stmt_scope == "":
        return True
    if stmt_scope in class_scopes:
        return scope == stmt_scope
    return scope == stmt_scope or scope.startswith(stmt_scope + ".")
def _build_binding_index(tree: ast.Module,
                         scope_idx: dict) -> list[tuple]:
    entries: list[tuple] = []
    for stmt in tree_nodes(tree):
        if not isinstance(stmt, (ast.Assign, ast.AnnAssign,
                                 ast.AugAssign, ast.NamedExpr)):
            continue
        targets = _binding_statement_targets(stmt)
        value = getattr(stmt, 'value', None)
        if not targets or value is None:
            continue
        position = (stmt.lineno, getattr(stmt, 'col_offset', 0) or 0)
        stmt_scope = scope_idx.get(id(stmt), "")
        for target, bound_value in _element_binding_pairs(targets, value):
            names = frozenset(_target_name_ids(target))
            if names:
                entries.append(
                    (position, stmt_scope, names, bound_value, stmt))
    entries.sort(key=lambda entry: entry[0])
    return entries
def _binding_entries_before(ctx: _ScanContext, name: str, lineno: int,
                            col: int | None, scope: str
                            ) -> list[tuple[ast.AST, ast.AST]]:
    use_pos = (lineno, col or 0)
    entries: list[tuple[ast.AST, ast.AST]] = []
    for position, stmt_scope, names, value, stmt in ctx.binding_index:
        if position >= use_pos:
            continue
        if not _binding_scope_visible(scope, stmt_scope,
                                      ctx.facts.class_scopes):
            continue
        if name not in names:
            continue
        if _binding_param_shadowed(
                ctx, name, stmt_scope, scope, lineno, stmt):
            continue
        entries.append((stmt, value))
    if entries and isinstance(entries[-1][0], ast.AugAssign):
        latest_stmt, _latest_value = entries[-1]
        base_stmt = next(
            (stmt for stmt, _value in reversed(entries[:-1])
             if not isinstance(stmt, ast.AugAssign)), None)
        if (base_stmt is not None
                and _statement_is_conditional(
                    ctx.tree, base_stmt, ctx.parent_map)):
            base: ast.AST = latest_stmt.target
            augmented: list[tuple[ast.AST, ast.AST]] = []
            for stmt, value in reversed(entries):
                if not isinstance(stmt, ast.AugAssign):
                    break
                augmented.append((stmt, value))
            for stmt, value in reversed(augmented):
                base = ast.BinOp(left=base, op=stmt.op, right=value)
            effective = base
        else:
            effective = lookup_name_assignment(
                ctx.tree, name, lineno, scope=scope,
                scope_idx=ctx.facts.scope_idx, use_col=col)
        if effective is not None:
            entries[-1] = (latest_stmt, effective)
    return entries
def _statement_is_conditional(tree: ast.Module, stmt: ast.AST,
                              parent_map: dict) -> bool:
    if not parent_map:
        return True
    parent = parent_map.get(id(stmt))
    while parent is not None and parent is not tree:
        if isinstance(parent, (ast.If, ast.Try,
                               getattr(ast, 'TryStar', ast.Try), ast.Match,
                               ast.For, ast.AsyncFor, ast.While)):
            return True
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef, ast.Lambda)):
            return False
        parent = parent_map.get(id(parent))
    return False
def _literal_binding_dominates(ctx: _ScanContext, name: str, scope: str,
                                 lineno: int, col: int | None) -> bool:
    entries = _binding_entries_before(ctx, name, lineno, col, scope)
    if not entries:
        return False
    latest_stmt, latest_value = entries[-1]
    return (not _statement_is_conditional(
                ctx.tree, latest_stmt, ctx.parent_map)
            and (_is_literal_value(latest_value)
                 or is_static_literal_expr(latest_value)
                 or _is_static_transparent_call(latest_value)))
def scan_sql_injection(tree: ast.Module, code: str, filepath: str,
                       analyzer: PreciseTaintAnalyzer) -> list[VulnerabilityFinding]:
    ctx = _build_scan_context(analyzer, tree, code, filepath)
    findings: list[VulnerabilityFinding] = []
    for node in tree_nodes(tree):
        for site in _sql_call_sites(node, ctx):
            finding = _sql_judge(ctx, site)
            if finding is not None:
                findings.append(finding)
                break
    return findings
def _sql_statement_exprs(node: ast.Call,
                         call_name: str) -> tuple[ast.AST, ...]:
    if node.args:
        return (node.args[0],)
    keyword_names = (
        _SQL_EXTRA_STATEMENT_KWARGS
        if call_name.rsplit('.', 1)[-1] == 'extra'
        else _SQL_STATEMENT_KWARGS
    )
    return tuple(
        kw.value for kw in node.keywords if kw.arg in keyword_names)
def _sql_call_sites(node: ast.AST,
                    ctx: _ScanContext) -> list[_SqlCallSite]:
    if not isinstance(node, ast.Call):
        return []
    call_name = resolve_call_name(node)
    if call_name.rsplit('.', 1)[-1] not in _SQL_DANGER_PATTERNS:
        return []
    stmt_args = _sql_statement_exprs(node, call_name)
    if not stmt_args:
        return []
    scope = ctx.facts.scope_idx.get(id(node), "")
    taint = _sql_visible_input_taints(ctx, scope, node)
    params_here = frozenset(
        _params_at(ctx.func_param_ranges, node.lineno)).intersection(taint)
    return [
        _SqlCallSite(
            node=node,
            call_name=call_name,
            taint=taint,
            params_here=params_here,
            first_arg=_sql_first_arg(
                ctx, node, stmt_arg, scope, params_here),
        )
        for stmt_arg in stmt_args
    ]
def _sql_judge(ctx: _ScanContext,
               site: _SqlCallSite) -> VulnerabilityFinding | None:
    if _sql_parameterized_exempt(site):
        return None
    if _sql_pragma_or_ddl_exempt(site, ctx.tree):
        return None
    direct = _sql_direct_taint(ctx, site)
    if direct is not None:
        return direct
    if not ASTPreciseParser.is_string_concatenation(site.first_arg):
        return None
    return _sql_concat_finding(ctx, site)
def _sql_params_container(node: ast.Call) -> ast.AST | None:
    extra_args = node.args[1:]
    if extra_args:
        return extra_args[0]
    for kw in node.keywords:
        if kw.arg in ('params', 'parameters'):
            return kw.value
    return None
def _sql_parameterized_exempt(site: _SqlCallSite) -> bool:
    """参数化查询仅在 **SQL 文本本身是静态字面量** 时豁免。

    参数容器只约束“值走占位符”，不约束语句文本：
    ``execute('... WHERE a = ' + user, (user,))`` 与
    ``execute(f'... {user}', (user,))`` 的文本仍由拼接生成，绑定参数
    并不能中和它。原实现只按污点通道判断，非边界 helper 内污点不可见，
    这类调用被整段豁免（漏报）；而不带参数时反而报 MEDIUM dynamic_expr。
    """
    container = _sql_params_container(site.node)
    if container is None:
        return False
    if _is_empty_container_literal(container) or isinstance(container, ast.Constant):
        return False
    return is_static_literal_expr(site.first_arg)
def _is_empty_container_literal(container: ast.AST | None) -> bool:
    if isinstance(container, (ast.Tuple, ast.List)):
        return not container.elts
    if isinstance(container, ast.Dict):
        return not container.keys
    return False
def _sql_unconditional_binding_value(
        ctx: _ScanContext, entries: list[tuple[ast.AST, ast.AST]],
        ) -> ast.AST | None:
    if not entries:
        return None
    stmt, value = entries[-1]
    if (isinstance(stmt, ast.AugAssign)
            or _statement_is_conditional(ctx.tree, stmt, ctx.parent_map)):
        return None
    return value
def _sql_visible_input_taints(
        ctx: _ScanContext, scope: str, node: ast.Call,
        ) -> frozenset:
    current = set(_visible_input_taints(
        ctx, scope, node.lineno, node.col_offset))
    while current:
        overwritten: set[str] = set()
        for name in current:
            entries = _binding_entries_before(
                ctx, name, node.lineno, node.col_offset, scope)
            value = _sql_unconditional_binding_value(ctx, entries)
            if (value is not None
                    and not _expr_contains_taint(value, current, ctx.tree)):
                overwritten.add(name)
        if not overwritten:
            break
        current.difference_update(overwritten)
    return frozenset(current)
def _sql_binding_evidence(ctx: _ScanContext, name: str, node: ast.Call,
                          scope: str,
                          params_here: frozenset) -> ast.AST | None:
    entries = _binding_entries_before(
        ctx, name, node.lineno, node.col_offset, scope)
    if not entries:
        return None
    overwriting = _sql_unconditional_binding_value(ctx, entries)
    if overwriting is not None:
        return overwriting
    values = [value for _stmt, value in entries]
    taint = _visible_taints(ctx, scope)
    search = set(taint) | set(params_here)
    for value in reversed(values):
        if resolve_taint_source(value, TAINT_SOURCE_CALLS, ctx.tree) is not None:
            return value
        if _expr_contains_taint(value, search, ctx.tree):
            return value
    if all(is_static_literal_expr(value)
           or _is_static_transparent_call(value) for value in values):
        return values[-1]
    if name in taint:
        return None
    for value in reversed(values):
        if isinstance(value, (ast.BinOp, ast.JoinedStr, ast.Call,
                              ast.Subscript, ast.Attribute)):
            return value
    return values[-1]
def _sql_first_arg(ctx: _ScanContext, node: ast.Call,
                   stmt_arg: ast.AST, scope: str,
                   params_here: frozenset) -> ast.AST:
    first_arg: ast.AST = stmt_arg
    if isinstance(first_arg, ast.Name):
        _evidence = _sql_binding_evidence(
            ctx, first_arg.id, node, scope, params_here)
        if _evidence is not None:
            first_arg = _evidence
    return first_arg
def _sql_direct_taint(ctx: _ScanContext,
                      site: _SqlCallSite) -> VulnerabilityFinding | None:
    if _stmt_has_input_channel(
            site.first_arg, site.taint, site.params_here, ctx.tree):
        return _sql_report(ctx, site, "user_input", "HIGH", 0.95)
    return None
def _sql_const_text(node: ast.AST) -> str:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value.strip().upper()
    return ''
def _sql_lead_text(first_arg: ast.AST) -> str:
    if isinstance(first_arg, ast.JoinedStr):
        return _sql_const_text(first_arg.values[0]) if first_arg.values else ''
    if isinstance(first_arg, ast.BinOp):
        left = first_arg
        while isinstance(left, ast.BinOp):
            left = left.left
        return _sql_const_text(left)
    return ''
def _sql_is_pragma_or_ddl(lead: str) -> bool:
    keyword = lead.split(None, 1)[0] if lead else ''
    return lead.startswith('PRAGMA') or keyword in _DDL_KEYWORDS
def _is_chr_39_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "chr"
            and len(node.args) == 1 and not node.keywords
            and isinstance(node.args[0], ast.Constant)
            and node.args[0].value == 39)
def _is_single_quote_pat(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return node.value == "'"
    return _is_chr_39_call(node)
def _is_chr39_doubled(node: ast.AST) -> bool:
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult)):
        return False
    for chr_side, num_side in ((node.left, node.right),
                               (node.right, node.left)):
        if (_is_chr_39_call(chr_side)
                and isinstance(num_side, ast.Constant)
                and num_side.value == 2):
            return True
    return False
def _is_double_single_quote_pat(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return node.value == "''"
    if _is_chr39_doubled(node):
        return True
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return _is_chr_39_call(node.left) and _is_chr_39_call(node.right)
    return False
def _is_sql_quote_escaped_call(node: ast.AST) -> bool:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "replace"):
        return False
    if not isinstance(node.func.value, ast.Name):
        return False
    if len(node.args) != 2 or node.keywords:
        return False
    return (_is_single_quote_pat(node.args[0])
            and _is_double_single_quote_pat(node.args[1]))
def _trailing_single_quotes(text: str) -> int:
    n = 0
    for ch in reversed(text):
        if ch == "'":
            n += 1
        else:
            break
    return n
def _joinedstr_components(template: ast.JoinedStr) -> list[tuple] | None:
    comps: list[tuple] = []
    for v in template.values:
        if isinstance(v, ast.Constant) and isinstance(v.value, str):
            comps.append(("const", v.value, None))
        elif isinstance(v, ast.FormattedValue):
            if v.format_spec is not None or v.conversion != -1:
                return None
            comps.append(("dyn", v.value, v))
        else:
            return None
    return comps
def _binop_add_components(top: ast.BinOp) -> list[tuple]:
    comps: list[tuple] = []
    stack: list[ast.AST] = [top]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Add):
            stack.append(cur.right)
            stack.append(cur.left)
        elif isinstance(cur, ast.Constant) and isinstance(cur.value, str):
            comps.append(("const", cur.value, None))
        else:
            comps.append(("dyn", cur, None))
    return comps
def _concat_components(first_arg: ast.AST) -> list[tuple] | None:
    if isinstance(first_arg, ast.JoinedStr):
        return _joinedstr_components(first_arg)
    if isinstance(first_arg, ast.BinOp) and isinstance(first_arg.op, ast.Add):
        return _binop_add_components(first_arg)
    return None
def _concat_all_components_sanitized(first_arg: ast.AST,
                                     tree: ast.AST | None = None) -> bool:
    comps = _concat_components(first_arg)
    if not comps:
        return False
    dyn_count = 0
    for i, (kind, val, _fv) in enumerate(comps):
        if kind == "const":
            continue
        dyn_count += 1
        expr = val
        if _is_scalar_sanitizer_call(expr, tree):
            continue
        if not _is_sql_quote_escaped_call(expr):
            return False
        if not _sql_escape_slot_closed(comps, i):
            return False
    return dyn_count > 0
def _sql_escape_slot_closed(comps: list[tuple], index: int) -> bool:
    prev_ok = (index > 0 and comps[index - 1][0] == "const"
               and _trailing_single_quotes(comps[index - 1][1]) % 2 == 1)
    next_ok = (index + 1 < len(comps)
               and comps[index + 1][0] == "const"
               and comps[index + 1][1].startswith("'"))
    return prev_ok and next_ok
def _sql_pragma_or_ddl_exempt(site: _SqlCallSite,
                               tree: ast.AST | None = None) -> bool:
    # 豁免的是「静态建表 / PRAGMA 配置语句」，判据必须是语句文本为静态
    # 字面量。原判据“无污点通道”在非边界 helper 内恒真，
    # ``execute('DROP TABLE ' + user)`` 被当作静态 DDL 整段豁免（漏报）。
    lead = _sql_lead_text(site.first_arg)
    if not _sql_is_pragma_or_ddl(lead):
        return False
    if is_static_literal_expr(site.first_arg):
        return True
    return (lead.startswith('PRAGMA')
            and _concat_all_components_sanitized(site.first_arg, tree))
def _sql_concat_finding(ctx: _ScanContext,
                        site: _SqlCallSite) -> VulnerabilityFinding | None:
    _has_taint = _expr_contains_taint(
        site.first_arg, site.taint, ctx.tree)
    nodes = list(_iter_interp_nodes(site.first_arg, tree=ctx.tree))
    calls = [n for n in nodes if isinstance(n, ast.Call)]
    callee_ids = {id(n.func) for n in calls if isinstance(n.func, ast.Name)}
    _dynamic_call = any(
        not _is_static_transparent_call(call) for call in calls)
    scope = ctx.facts.scope_idx.get(id(site.node), "")
    _interp_names = [
        n.id for n in nodes
        if (isinstance(n, ast.Name) and id(n) not in callee_ids
            and not _literal_binding_dominates(
                ctx, n.id, scope, site.node.lineno, site.node.col_offset))
    ]
    if not (_has_taint or _interp_names or _dynamic_call):
        return None
    if _has_taint or any(n in site.params_here for n in _interp_names):
        return _sql_report(ctx, site, "user_input", "HIGH", 0.95)
    return _sql_report(ctx, site, "dynamic_expr", "MEDIUM", 0.8)
def _sql_report(ctx: _ScanContext, site: _SqlCallSite,
                source: str, severity: str,
                confidence: float) -> VulnerabilityFinding:
    return build_vulnerability_finding(
        VulnerabilityCategory.SQL_INJECTION,
        code=ctx.code,
        filepath=ctx.filepath,
        line=site.node.lineno,
        source=source,
        sink=site.call_name,
        severity=severity,
        confidence=confidence,
        suggestion=f"使用参数化查询: {site.call_name}(query, params=...)",
        cwe_id="CWE-89",
    )
_DOTDOT_RE = re.compile(r"(?:^|[/\\])\.\.(?:[/\\]|$)")
_DEFAULT_SCENE = "user_input"
_FUNCTION_PARAMETER_ORIGIN = "function_parameter"
# 本工具是本地 CLI：环境变量与命令行参数由操作员在自己的机器上给定，
# 不构成路径穿越的攻击面（与 ``_cli_operator_output_path`` 同一口径）。
# 这些来源一经声明即必须在**判定**层生效，而不只是用于挑选展示用的来源名。
_TRUSTED_ORIGIN_NAMES = frozenset({
    'os.environ', 'os.getenv', 'os.environ.get', 'sys.argv',
})
PATH_DANGER_FUNCTIONS = frozenset(
    {"open"} | {f"{module}.{member}"
                for module, members in CALL_ALIAS_MODULES["path"].items()
                for member in members})
_PATH_ARG_ARITY = {
    'shutil.copy': 2, 'shutil.move': 2,
}
_PATH_ARG_KWARGS: dict[str, tuple[str, ...]] = {
    'open': ('file',),
    'os.open': ('path',),
    'os.remove': ('path',),
    'os.unlink': ('path',),
    'os.rmdir': ('path',),
    'os.mkdir': ('path',),
    'os.makedirs': ('name',),
    'shutil.copy': ('src', 'dst'),
    'shutil.move': ('src', 'dst'),
    'shutil.rmtree': ('path',),
    'zipfile.ZipFile': ('file',),
    'tarfile.open': ('name',),
}
_PATH_SUGGESTIONS = {
    "symlink_bypass": "os.path.resolve()展开符号链接后islink()失效,在resolve前检测符号链接或用abspath+目录验证",
    "dot_dot_slash": "路径含../回溯序列,用realpath规范化并验证在允许目录内",
    "absolute_path_injection": "用户输入可能为绝对路径,验证路径在允许根目录内",
    "encoding_bypass": "路径含URL编码回溯序列,先解码再验证路径安全",
    "user_input": "使用os.path.realpath()规范化路径并验证在允许目录内",
}
def scan_path_traversal(tree: ast.Module, code: str, filepath: str,
                         analyzer: PreciseTaintAnalyzer) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    ctx = _build_scan_context(analyzer, tree, code, filepath)
    resolver = _StarImportCallResolver(tree, CALL_ALIAS_MODULES["path"])
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        call_name = resolver.resolve(
            resolve_call_name(node))
        if call_name not in PATH_DANGER_FUNCTIONS:
            continue
        path_args = _path_argument_nodes(call_name, node)
        if not path_args:
            continue
        hit, traversal_type, origin = _path_scan_call(
            ctx, node, call_name, path_args)
        if not hit:
            continue
        if _cli_operator_output_path(tree, node, call_name, path_args):
            continue
        findings.append(_path_finding(
            node, call_name, code, filepath, traversal_type, origin))
    return findings
_WRITE_MODES = frozenset({'w', 'wb', 'a', 'ab', 'x', 'xb', 'w+', 'a+',
                           'x+', 'wb+', 'ab+', 'xb+'})
def _cli_operator_output_path(tree: ast.Module, node: ast.Call, call_name: str,
                              path_args: list[ast.AST]) -> bool:
    """写模式的 ``open(args.out, 'w')``：路径由**操作员命令行**指定。

    路径穿越的危害是攻击者控制路径导致越权读取/写入。本工具是本地 CLI，
    ``--json-out`` / ``--out`` 这类参数就是操作员在**自己的机器**上指定的
    输出文件，不存在越权面（写到哪里正是操作员的意图）。判据：写模式 +
    路径形如 ``args.<name>`` 且同一模块存在 ``parse_args`` 调用。
    """
    if call_name not in {'open', 'io.open', 'codecs.open'}:
        return False
    mode_literals = [arg for arg in list(node.args)[1:2]
                     if isinstance(arg, ast.Constant)
                     and isinstance(arg.value, str)]
    for kw in node.keywords:
        if kw.arg == 'mode' and isinstance(kw.value, ast.Constant) \
                and isinstance(kw.value.value, str):
            mode_literals.append(kw.value)
    if not mode_literals or mode_literals[0].value not in _WRITE_MODES:
        return False
    if not path_args or not isinstance(path_args[0], ast.Attribute):
        return False
    if not isinstance(path_args[0].value, ast.Name):
        return False
    if not any(isinstance(n, ast.Call)
               and (getattr(n.func, 'id', None) == 'parse_args'
                    or getattr(n.func, 'attr', None) == 'parse_args')
               for n in walk_nodes(tree)):
        return False
    return True
def _path_argument_nodes(call_name: str, node: ast.Call) -> list[ast.AST]:
    args = list(node.args)
    for idx, name in enumerate(_PATH_ARG_KWARGS.get(call_name, ())):
        if idx < len(args):
            continue
        for kw in node.keywords:
            if kw.arg == name:
                args.append(kw.value)
                break
    return args
def _path_scan_call(ctx: _ScanContext, node: ast.Call, call_name: str,
                    path_args: list[ast.AST]) -> tuple[bool, str, str]:
    scope = ctx.facts.scope_idx.get(id(node), "")
    for path_arg in path_args[:_PATH_ARG_ARITY.get(call_name, 1)]:
        hit, traversal_type, origin = _path_analyze_arg(
            ctx, path_arg, scope, node)
        if hit:
            return True, traversal_type, origin
    return False, _DEFAULT_SCENE, ""
_PATH_RESOLVE_CALLS = frozenset({
    'os.path.resolve', 'os.path.realpath', 'pathlib.Path.resolve',
})
def _path_pick_origin(cands: list) -> str:
    for cand in cands:
        if cand not in _TRUSTED_ORIGIN_NAMES:
            return cand
    return cands[0]
def _path_expr_origins(ctx: _ScanContext, expr: ast.AST,
                       scope: str,
                       params: frozenset = _EMPTY_NAME_SET) -> list:
    """表达式实际流入的**不可信**输入来源（已剔除 ``_TRUSTED_ORIGIN_NAMES``）。

    所有调用方都把非空结果当作“存在用户输入”，因此可信来源必须在这里
    统一剔除，而不是留给各调用点自行记忆。
    """
    def _origin_of(name: str) -> str | None:
        origin = ctx.facts.scoped_value(
            scope, name, ctx.input_origins or ctx.facts.origins, default="")
        if origin:
            return origin
        return _FUNCTION_PARAMETER_ORIGIN if name in params else None
    _out: list = []
    for _o in iter_expr_origins(expr, _origin_of, tree=ctx.tree):
        if _o in _TRUSTED_ORIGIN_NAMES:
            continue
        if _o not in _out:
            _out.append(_o)
    return _out
def _path_analyze_arg(ctx: _ScanContext, path_arg: ast.AST,
                      scope: str, node: ast.Call) -> tuple[bool, str, str]:
    params = frozenset(_external_params_at(
        ctx.func_param_ranges, node.lineno))
    has_user_input, traversal_type, hit_origin, path_arg = (
        _path_name_scene(ctx, path_arg, scope, node, params))
    if not isinstance(path_arg, ast.Constant):
        candidates = _path_expr_origins(ctx, path_arg, scope, params)
        if candidates:
            has_user_input = True
            hit_origin = _path_pick_origin(candidates)
    static_kind = _path_static_kind(path_arg, has_user_input)
    if static_kind:
        return True, static_kind, hit_origin
    return has_user_input, traversal_type, hit_origin
def _path_static_kind(path_arg: ast.AST, has_user_input: bool) -> str | None:
    if isinstance(path_arg, ast.Constant) and isinstance(path_arg.value, str):
        return _path_traversal_kind(path_arg.value)
    if not has_user_input and isinstance(path_arg, (ast.BinOp,
                                                    ast.JoinedStr)):
        return _path_concat_traversal(path_arg)
    if not has_user_input and isinstance(path_arg, ast.Call):
        call_name = resolve_call_name(path_arg)
        if call_name in {'os.path.join', 'join', 'pathlib.Path', 'Path'}:
            return _path_concat_traversal(path_arg)
    return None
def _path_name_scene(ctx: _ScanContext, path_arg: ast.AST,
                     scope: str, node: ast.Call,
                     params: frozenset) -> tuple[bool, str, str, ast.AST]:
    if not isinstance(path_arg, ast.Name):
        return False, _DEFAULT_SCENE, "", path_arg
    entries = _binding_entries_before(
        ctx, path_arg.id, node.lineno, node.col_offset, scope)
    assigned = _path_rebind_expr(path_arg, entries)
    if (isinstance(assigned, ast.Call)
            and resolve_call_name(assigned)
            in _PATH_RESOLVE_CALLS):
        candidates = _path_expr_origins(ctx, assigned, scope, params)
        if candidates:
            return (True, "symlink_bypass",
                    _path_pick_origin(candidates), path_arg)
        return False, _DEFAULT_SCENE, "", assigned
    if entries:
        latest_stmt, latest_value = entries[-1]
        if (not _statement_is_conditional(ctx.tree, latest_stmt, ctx.parent_map)
                and not _path_expr_origins(ctx, latest_value, scope, params)
                and _path_static_kind(latest_value, False) is None):
            return False, _DEFAULT_SCENE, "", latest_value
    if path_arg.id in params:
        origin = (ctx.facts.scoped_value(
            scope, path_arg.id, ctx.input_origins or ctx.facts.origins, default="")
            or _FUNCTION_PARAMETER_ORIGIN)
        return True, "absolute_path_injection", origin, path_arg
    tainted_binding = None
    tainted_origins: list = []
    for _stmt, value in reversed(entries):
        origins = _path_expr_origins(ctx, value, scope, params)
        if origins:
            tainted_binding = value
            tainted_origins = origins
            break
    if assigned is path_arg or tainted_binding is not None:
        origin = ctx.facts.scoped_value(
            scope, path_arg.id, ctx.input_origins or ctx.facts.origins, default="")
        if origin in _TRUSTED_ORIGIN_NAMES:
            # 变量级来源可能只是先流入的可信源（如 environ）：改用绑定表达式里
            # 真正不可信的来源；没有则说明仅有可信来源，不构成用户输入。
            origin = (_path_pick_origin(tainted_origins)
                      if tainted_origins else "")
        if origin:
            return True, "absolute_path_injection", origin, path_arg
        if tainted_binding is not None:
            return False, _DEFAULT_SCENE, "", tainted_binding
    return False, _DEFAULT_SCENE, "", assigned
def _path_rebind_expr(path_arg: ast.Name,
                      entries: list[tuple[ast.AST, ast.AST]]) -> ast.AST:
    _assigned = entries[-1][1] if entries else path_arg
    _is_replaceable = isinstance(
        _assigned, (ast.BinOp, ast.JoinedStr, ast.Call)) or (
        isinstance(_assigned, ast.Constant)
        and isinstance(_assigned.value, str))
    return _assigned if _is_replaceable else path_arg
def _path_traversal_kind(text: str) -> str | None:
    if _DOTDOT_RE.search(text):
        return "dot_dot_slash"
    decoded = text
    while True:
        next_decoded = _urlparse.unquote(decoded)
        if _DOTDOT_RE.search(next_decoded):
            return "encoding_bypass"
        if next_decoded == decoded:
            return None
        decoded = next_decoded
def _static_path_text(expr: ast.AST) -> str | None:
    if isinstance(expr, ast.Constant) and isinstance(expr.value, str):
        return expr.value
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
        left = _static_path_text(expr.left)
        right = _static_path_text(expr.right)
        return left + right if left is not None and right is not None else None
    if isinstance(expr, ast.JoinedStr):
        parts: list[str] = []
        for value in expr.values:
            if isinstance(value, ast.FormattedValue):
                if value.conversion != -1 or value.format_spec is not None:
                    return None
                value = value.value
            part = _static_path_text(value)
            if part is None:
                return None
            parts.append(part)
        return "".join(parts)
    return None
def _path_concat_traversal(expr: ast.AST) -> str | None:
    static_text = _static_path_text(expr)
    if static_text is not None:
        return _path_traversal_kind(static_text)
    for sub in walk_nodes(expr):
        text = getattr(sub, "value", None)
        if isinstance(text, str):
            kind = _path_traversal_kind(text)
            if kind is not None:
                return kind
    return None
def _path_finding(node: ast.Call, call_name: str, code: str,
                  filepath: str, traversal_type: str,
                  hit_origin: str) -> VulnerabilityFinding:
    return build_vulnerability_finding(
        VulnerabilityCategory.PATH_TRAVERSAL,
        code=code,
        filepath=filepath,
        line=node.lineno,
        source=traversal_type,
        sink=call_name,
        severity="HIGH",
        confidence=0.85,
        suggestion=_PATH_SUGGESTIONS.get(
            traversal_type, _PATH_SUGGESTIONS[_DEFAULT_SCENE]),
        cwe_id="CWE-22",
        taint_origin=hit_origin,
    )
CMD_DANGER_FUNCTIONS: frozenset[str] = frozenset(
    f"{module}.{member}"
    for module, members in CALL_ALIAS_MODULES["cmd"].items()
    for member in members)
_SHELL_SINK_CALLS = frozenset({
    'os.system', 'os.popen', 'os.popen2', 'os.popen3', 'os.popen4',
    'subprocess.getoutput', 'subprocess.getstatusoutput',
})
_CMD_SHELL_QUOTE_CALLS = frozenset({'shlex.quote', 'pipes.quote'})
_SUBPROCESS_FAMILY = frozenset({
    'subprocess.call', 'subprocess.Popen', 'subprocess.run',
    SUBPROCESS_CHECK_CALL, SUBPROCESS_CHECK_OUTPUT,
})
_CMD_PAYLOAD_KEYWORDS: dict[str, tuple[str, ...]] = {
    'os.system': ('command',),
    'os.popen': ('command', 'cmd'),
    'os.popen2': ('command', 'cmd'),
    'os.popen3': ('command', 'cmd'),
    'os.popen4': ('command', 'cmd'),
    'os.execv': ('path', 'args'),
    'os.execve': ('path', 'args', 'env'),
    'os.execl': ('path',),
    'os.execle': ('path',),
    'subprocess.getoutput': ('cmd',),
    'subprocess.getstatusoutput': ('cmd',),
}
_INLINE_INTERPRETERS = frozenset({
    'sh', 'bash', 'zsh', 'dash', 'ash', 'ksh', 'csh', 'tcsh',
    'sh.exe', 'bash.exe', 'zsh.exe', 'dash.exe', 'ksh.exe',
    'cmd', 'cmd.exe', 'powershell', 'powershell.exe', 'pwsh', 'pwsh.exe',
    'python', 'python.exe', 'python3', 'python3.exe', 'py', 'py.exe',
})
_SHELL_INLINE_FLAGS = frozenset({'-c', '-command'})
_CMD_SHELL_PROGRAMS = frozenset({'cmd', 'cmd.exe'})
_CMD_SHELL_INLINE_FLAGS = frozenset({'/c', '/k'})
_POWERSHELL_INLINE_FLAGS = frozenset({
    '-encodedcommand', '-encodedarguments', '-encoded', '-enc', '-en', '-e', '-ec',
})
_BASH_PROGRAMS = frozenset({'bash', 'bash.exe'})
_BASH_STARTUP_FILE_FLAGS = frozenset({'--init-file', '--rcfile'})
def scan_command_injection(
        tree: ast.Module, code: str, filepath: str,
        analyzer: PreciseTaintAnalyzer) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    ctx = _build_cmd_scan_context(analyzer, tree, code, filepath)
    resolver = _StarImportCallResolver(tree, CALL_ALIAS_MODULES["cmd"])
    for node in tree_nodes(tree):
        finding = _cmd_scan_node(ctx, node, resolver)
        if finding is not None:
            findings.append(finding)
    return findings
def _cmd_scan_node(ctx: _CmdScanContext, node: ast.AST,
                   resolver: ImportCallResolver) -> VulnerabilityFinding | None:
    if not isinstance(node, ast.Call):
        return None
    call_name = resolver.resolve(resolve_call_name(node))
    if call_name not in CMD_DANGER_FUNCTIONS:
        return None
    has_shell_true = _cmd_has_shell_true(node, call_name)
    first_arg = _cmd_effective_first_argument(ctx, node)
    if (_cmd_sequence_param_exempt(
            ctx, call_name, has_shell_true, first_arg, node.lineno)
            and not _cmd_argv_executable_tainted(
                ctx, first_arg, node, call_name)):
        return None
    if (_cmd_list_argv_exempt(call_name, has_shell_true, first_arg)
            and not _cmd_argv_executable_tainted(
                ctx, first_arg, node, call_name)):
        return None
    if _cmd_exec_argv_exempt(ctx, node, call_name):
        return None
    has_variable_arg = _cmd_has_dynamic_arg(ctx, node, call_name)
    if not (has_shell_true or has_variable_arg):
        return None
    return _cmd_finding(ctx, node, call_name,
                        has_shell_true, has_variable_arg)
def _cmd_argument_nodes(node: ast.Call, call_name: str):
    if call_name in _SUBPROCESS_FAMILY:
        if node.args:
            yield node.args[0]
    else:
        yield from node.args
    payload_keywords = _CMD_PAYLOAD_KEYWORDS.get(call_name, ())
    for kw in node.keywords:
        if kw.arg == 'args' or kw.arg in payload_keywords:
            yield kw.value
    if call_name in _SUBPROCESS_FAMILY:
        executable = _cmd_executable_override(node, call_name)
        if executable is not None:
            yield executable
def _cmd_first_argument(node: ast.Call) -> ast.AST | None:
    if node.args:
        return node.args[0]
    for kw in node.keywords:
        if kw.arg == 'args':
            return kw.value
    return None
def _cmd_executable_override(node: ast.Call,
                             call_name: str) -> ast.AST | None:
    for kw in node.keywords:
        if kw.arg == 'executable':
            return kw.value
    if call_name in _SUBPROCESS_FAMILY and len(node.args) > 2:
        return node.args[2]
    return None
def _cmd_expand_argv_aliases(ctx: _CmdScanContext, expr: ast.AST,
                             node: ast.Call,
                             seen: frozenset[str] = _EMPTY_NAME_SET) -> ast.AST:
    scope = ctx.facts.scope_idx.get(id(node), "")
    if isinstance(expr, ast.Name):
        if (expr.id in seen or expr.id in _params_at(
                ctx.func_param_ranges, node.lineno)):
            return expr
        entries = _binding_entries_before(
            ctx, expr.id, node.lineno, node.col_offset, scope)
        if entries:
            latest_stmt, assigned = entries[-1]
            if _statement_is_conditional(
                    ctx.tree, latest_stmt, ctx.parent_map):
                return expr
        else:
            assigned = lookup_name_assignment(
                ctx.tree, expr.id, node.lineno, scope=scope,
                scope_idx=ctx.facts.scope_idx, use_col=node.col_offset)
        if assigned is None:
            return expr
        return _cmd_expand_argv_aliases(
            ctx, assigned, node, seen | {expr.id})
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
        return ast.BinOp(
            left=_cmd_expand_argv_aliases(ctx, expr.left, node, seen),
            op=expr.op,
            right=_cmd_expand_argv_aliases(ctx, expr.right, node, seen))
    if isinstance(expr, ast.List):
        return ast.List(
            elts=[_cmd_expand_argv_aliases(ctx, elt, node, seen)
                  for elt in expr.elts], ctx=expr.ctx)
    if isinstance(expr, ast.Tuple):
        return ast.Tuple(
            elts=[_cmd_expand_argv_aliases(ctx, elt, node, seen)
                  for elt in expr.elts], ctx=expr.ctx)
    if isinstance(expr, ast.Starred):
        return ast.Starred(
            value=_cmd_expand_argv_aliases(ctx, expr.value, node, seen),
            ctx=expr.ctx)
    return expr
def _cmd_effective_first_argument(ctx: _CmdScanContext,
                                  node: ast.Call) -> ast.AST | None:
    first = _cmd_first_argument(node)
    if first is None:
        return None
    if isinstance(first, ast.Name) and first.id not in _params_at(
            ctx.func_param_ranges, node.lineno):
        scope = ctx.facts.scope_idx.get(id(node), "")
        assigned = lookup_name_assignment(
            ctx.tree, first.id, node.lineno, scope=scope,
            scope_idx=ctx.facts.scope_idx, use_col=node.col_offset)
        if assigned is not None:
            first = assigned
    return _cmd_expand_argv_aliases(ctx, first, node)
def _cmd_has_dynamic_arg(ctx: _CmdScanContext, node: ast.Call,
                         call_name: str) -> bool:
    return any(_cmd_arg_is_tainted(ctx, arg, node, call_name)
               for arg in _cmd_argument_nodes(node, call_name))
def _cmd_finding(ctx: _ScanContext, node: ast.Call, call_name: str,
                 has_shell_true: bool,
                 has_variable_arg: bool) -> VulnerabilityFinding:
    shell_execution = has_shell_true or call_name in _SHELL_SINK_CALLS
    return build_vulnerability_finding(
        VulnerabilityCategory.COMMAND_INJECTION,
        code=ctx.code,
        filepath=ctx.filepath,
        line=node.lineno,
        source="user_input" if has_variable_arg else "shell=True",
        sink=call_name,
        severity="CRITICAL" if shell_execution else "HIGH",
        confidence=0.95 if shell_execution else 0.7,
        suggestion=(
            "使用 subprocess.run([cmd, arg1, arg2], shell=False)"
            if shell_execution else "避免拼接用户输入到命令参数"
        ),
        cwe_id="CWE-78",
    )
# 形参注解为字符串序列时，``subprocess.*(cmd, ...)`` 的 ``cmd`` 是**参数向量**
# 而非 shell 命令串：``shell=False``（默认）下逐元素作为 argv 传递，不存在
# 元字符注入面。此前只识别字面量 ``[a, b]``，对 ``cmd: list[str]`` 参数
# 一律误报（本仓 7/7 条 command_injection 均属此类）。
_SEQUENCE_ANNOTATION_HINTS: tuple[str, ...] = (
    'list[', 'List[', 'Sequence[', 'Iterable[', 'tuple[', 'Tuple[',
    'set[', 'Set[', 'frozenset[', 'Collection[',
)
def _cmd_param_annotation_is_sequence(ctx: _CmdScanContext, name: str,
                                     lineno: int) -> bool:
    for start, end, params, _scope, node in ctx.func_param_ranges:
        if not (start <= lineno <= end) or name not in params:
            continue
        args = getattr(node, 'args', None)
        if args is None:
            continue
        groups = (getattr(args, 'posonlyargs', None) or [],
                  getattr(args, 'args', None) or [],
                  getattr(args, 'kwonlyargs', None) or [])
        for group in groups:
            for arg_node in group:
                if getattr(arg_node, 'arg', None) != name:
                    continue
                annotation = getattr(arg_node, 'annotation', None)
                if annotation is None:
                    continue
                try:
                    text = ast.unparse(annotation)
                except (AttributeError, ValueError, TypeError):
                    continue
                if any(hint in text for hint in _SEQUENCE_ANNOTATION_HINTS):
                    return True
    return False
def _cmd_sequence_param_exempt(ctx: _CmdScanContext, call_name: str,
                               has_shell_true: bool,
                               first: ast.AST | None,
                               lineno: int) -> bool:
    return bool(call_name in _SUBPROCESS_FAMILY
                and not has_shell_true
                and isinstance(first, ast.Name)
                and _cmd_param_annotation_is_sequence(ctx, first.id, lineno))
def _cmd_list_argv_exempt(call_name: str,
                          has_shell_true: bool,
                          first: ast.AST | None) -> bool:
    if not (call_name in _SUBPROCESS_FAMILY and not has_shell_true
            and first is not None and _cmd_is_list_argv(first)):
        return False
    return not _cmd_argv_runs_shell_inline(first)
# exec 家族：``execv(path, args)`` / ``execve(path, args, env)`` /
# ``execl(path, *args)`` / ``execle(path, *args, env)`` 直接以 argv 替换进程映像，
# 不经 shell：程序本体由 ``path`` 决定，``args`` 只是参数向量（同列表 argv 的
# ``subprocess.*``）。注入面仅剩「程序是 shell / 解释器且带内联执行选项」。
# 原实现把 args 的每个元素都当命令串负载，``os.execv('/bin/ls', ['ls', user])``
# 被报 HIGH。
_EXEC_ARGV_CALLS: frozenset[str] = frozenset({'os.execv', 'os.execve'})
_EXEC_VARARG_CALLS: frozenset[str] = frozenset({'os.execl', 'os.execle'})
def _cmd_exec_argv_exempt(ctx: _CmdScanContext, node: ast.Call,
                          call_name: str) -> bool:
    if (call_name not in _EXEC_ARGV_CALLS
            and call_name not in _EXEC_VARARG_CALLS):
        return False
    program = node.args[0] if node.args else next(
        (kw.value for kw in node.keywords if kw.arg == 'path'), None)
    program = (_cmd_expand_argv_aliases(ctx, program, node)
               if program is not None else None)
    # 程序本体必须可证明为静态路径：动态 / 污点程序名意味着攻击者选择可执行文件，照报
    if not (isinstance(program, ast.Constant)
            and isinstance(program.value, str)):
        return False
    if call_name in _EXEC_VARARG_CALLS:
        elts = [_cmd_expand_argv_aliases(ctx, arg, node)
                for arg in node.args[1:]]
    else:
        argv = (node.args[1] if len(node.args) > 1 else next(
            (kw.value for kw in node.keywords if kw.arg == 'args'), None))
        argv = (_cmd_expand_argv_aliases(ctx, argv, node)
                if argv is not None else None)
        if not isinstance(argv, (ast.List, ast.Tuple)):
            return False
        elts = list(argv.elts)
    # argv[0] 惯例上是程序名，但可被伪造成任意值：三种头部分别求值，
    # 任一呈内联 shell 形态即照报（保守）。
    heads = [elts, [program, *elts]]
    if elts and isinstance(elts[0], ast.Constant) and isinstance(elts[0].value, str):
        heads.append([program, *elts[1:]])
    return not any(
        _cmd_argv_runs_shell_inline(ast.List(elts=head, ctx=ast.Load()))
        for head in heads)
def _cmd_argv_with_program_runs_shell_inline(arg: ast.AST | None,
                                              program: Any) -> bool:
    """``executable=`` 指定程序后 argv[0] 不再代表程序本体。

    ``subprocess.run(['-c', cmd], executable='sh')`` 实际执行
    ``sh -c cmd``：须以 ``[program, *argv]`` 重新判定内联 shell 形态，
    否则被「列表 argv + shell=False」豁免吞掉。
    """
    if arg is None or not isinstance(program, str):
        return False
    elts = _cmd_argv_head_elts(arg, None)
    return _cmd_argv_runs_shell_inline(
        ast.List(elts=[ast.Constant(value=program), *elts], ctx=ast.Load()))
def _cmd_argv_executable_tainted(ctx: _CmdScanContext,
                                 arg: ast.AST | None,
                                 node: ast.Call,
                                 node_call_name: str) -> bool:
    scope = ctx.facts.scope_idx.get(id(node), "")
    executable = _cmd_executable_override(node, node_call_name)
    if executable is not None:
        if _cmd_expr_tainted(
                ctx, executable, node.lineno, scope, node.col_offset):
            return True
        effective = (_cmd_alias_binding(
            ctx, scope, executable.id, node.lineno, node.col_offset)
            if isinstance(executable, ast.Name) else executable)
        if not (isinstance(effective, ast.Constant)
                and effective.value is None):
            return _cmd_argv_with_program_runs_shell_inline(
                arg, getattr(effective, 'value', None))
    if arg is None:
        return False
    heads = _cmd_argv_head_elts(arg, 1)
    if not heads:
        return False
    return _cmd_expr_tainted(
        ctx, heads[0], node.lineno, scope, node.col_offset)
def _cmd_argv_head_elts(arg: ast.AST, limit: int | None = 2) -> list:
    out: list = []
    queue: list = [arg]
    while queue and (limit is None or len(out) < limit):
        cur = queue.pop(0)
        if isinstance(cur, (ast.List, ast.Tuple)):
            out.extend(cur.elts)
        elif isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Add):
            queue = [cur.left, cur.right, *queue]
        else:
            out.append(cur)
    return out if limit is None else out[:limit]
def _cmd_argv_shape_is_static(arg: ast.AST) -> bool:
    if isinstance(arg, (ast.List, ast.Tuple)):
        return all(not isinstance(elt, ast.Starred) for elt in arg.elts)
    if isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Add):
        return (_cmd_argv_shape_is_static(arg.left)
                and _cmd_argv_shape_is_static(arg.right))
    return False
def _cmd_argv_runs_shell_inline(arg: ast.AST) -> bool:
    elts = _cmd_argv_head_elts(arg, None)
    if not elts:
        return False
    program = elts[0]
    if not (isinstance(program, ast.Constant)
            and isinstance(program.value, str)):
        return False
    _name = program.value.strip().replace('\\', '/').rsplit('/', 1)[-1].lower()
    if _name not in _INLINE_INTERPRETERS:
        return False
    index = 1
    while index < len(elts):
        elt = elts[index]
        if not (isinstance(elt, ast.Constant)
                and isinstance(elt.value, str)):
            return True
        token = elt.value.strip()
        option = token.lower()
        if interpreter_option_consumes_value(_name, token):
            if index + 1 >= len(elts):
                return True
            option_value = elts[index + 1]
            if (_name in _BASH_PROGRAMS
                    and option in _BASH_STARTUP_FILE_FLAGS
                    and not (isinstance(option_value, ast.Constant)
                             and isinstance(option_value.value, str))):
                return True
            index += 2
            continue
        if _is_shell_inline_token(elt, _name):
            return True
        is_option = token.startswith('-') or (
            _name in _CMD_SHELL_PROGRAMS and token.startswith('/'))
        if not is_option or token == '--':
            break
        index += 1
    return not _cmd_argv_shape_is_static(arg)
def _is_shell_inline_token(node: ast.AST, program: str) -> bool:
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return False
    token = node.value.strip().lower()
    if not token:
        return False
    if token in _SHELL_INLINE_FLAGS:
        return True
    if program in _CMD_SHELL_PROGRAMS and token in _CMD_SHELL_INLINE_FLAGS:
        return True
    if program in POWERSHELL_PROGRAMS:
        return token in _POWERSHELL_INLINE_FLAGS
    return (token.startswith('-') and not token.startswith('--')
            and 'c' in token[1:])
def _cmd_has_shell_true(node: ast.Call, call_name: str) -> bool:
    for kw in node.keywords:
        if kw.arg == 'shell':
            return (not isinstance(kw.value, ast.Constant)
                    or bool(kw.value.value))
    if call_name in _SUBPROCESS_FAMILY and len(node.args) > 8:
        shell = node.args[8]
        return not isinstance(shell, ast.Constant) or bool(shell.value)
    return False
def _cmd_arg_is_tainted(ctx: _CmdScanContext, arg: ast.AST,
                        node: ast.Call, call_name: str) -> bool:
    scope = ctx.facts.scope_idx.get(id(node), "")
    return (_cmd_expr_tainted(ctx, arg, node.lineno, scope,
                              node.col_offset)
            or _cmd_shell_dynamic_arg(ctx, arg, call_name,
                                      node.lineno, scope, node.col_offset)
            or _cmd_assigned_arg_tainted(ctx, arg, node, scope))
def _cmd_shell_dynamic_arg(ctx: _CmdScanContext, arg: ast.AST,
                           call_name: str, line: int, scope: str,
                           col: int | None = None) -> bool:
    return (call_name in _SHELL_SINK_CALLS
            and not isinstance(arg, ast.Constant)
            and not _cmd_interp_all_exempt(ctx, arg, line, scope, col))
def _cmd_assigned_arg_tainted(ctx: _CmdScanContext, arg: ast.AST,
                              node: ast.Call, scope: str) -> bool:
    if not isinstance(arg, ast.Name):
        return False
    if arg.id in _params_at(ctx.func_param_ranges, node.lineno):
        return False
    _assigned = lookup_name_assignment(
        ctx.tree, arg.id, node.lineno,
        scope=scope, scope_idx=ctx.facts.scope_idx,
        use_col=node.col_offset)
    if not isinstance(_assigned, (ast.BinOp, ast.JoinedStr,
                                  ast.List, ast.Tuple)):
        return False
    if (_cmd_is_list_argv(_assigned)
            and not _cmd_argv_runs_shell_inline(_assigned)):
        return False
    return _cmd_expr_tainted(
        ctx, _assigned, node.lineno, scope, node.col_offset)
def _cmd_sanitized_exempt(ctx: _CmdScanContext, scope: str,
                          name: str, line: int) -> bool:
    if _lambda_param_ranges_at(ctx.func_param_ranges, line, name):
        return False
    if name in ctx.sanitized.get(scope, ()):
        return (scope, name) not in ctx.facts.origins
    if name in ctx.sanitized.get('', ()):
        return ((scope, name) not in ctx.facts.origins
                and ('', name) not in ctx.facts.origins
                and ctx.facts.module_visible(scope, name))
    return False
def _cmd_name_exempt(ctx: _CmdScanContext, scope: str, name: str,
                     line: int, col: int | None = None) -> bool:
    if _cmd_sanitized_exempt(ctx, scope, name, line):
        return True
    shadow = (ctx.facts.local_bindings, ctx.facts.global_names,
              ctx.facts.class_scopes)
    key = TaintNameResolution.resolve_taint_key(
        scope, name, ctx.sanitized_keys, shadow)
    pos = (line, 0 if col is None else col)
    sanitized_keys = _lambda_sanitized_keys(
        ctx, ctx.sanitized_keys, line, scope, name)
    if (key is not None and _sanitized_before(
            sanitized_keys, key, pos, scope)):
        return True
    if any(g0 <= line <= g1 for g0, g1 in ctx.guards.get(name, ())):
        return True
    return _cmd_binding_exempt(ctx, scope, name, line, col)
def _cmd_alias_binding(ctx: _CmdScanContext, scope: str, name: str,
                       line: int, col: int | None = None
                       ) -> ast.AST | None:
    seen: set[str] = set()
    current = name
    while current not in seen:
        seen.add(current)
        assigned = lookup_name_assignment(
            ctx.tree, current, line, scope=scope,
            scope_idx=ctx.facts.scope_idx, use_col=col)
        if not isinstance(assigned, ast.Name):
            return assigned
        current = assigned.id
    return None
def _cmd_binding_exempt(ctx: _CmdScanContext, scope: str, name: str,
                        line: int, col: int | None = None) -> bool:
    entries = _binding_entries_before(ctx, name, line, col, scope)
    is_param = name in _params_at(ctx.func_param_ranges, line)
    if entries:
        latest_stmt, latest_value = entries[-1]
        if not _statement_is_conditional(
                ctx.tree, latest_stmt, ctx.parent_map):
            return (_is_shell_quote_call(latest_value, ctx.tree)
                    or _is_scalar_sanitizer_call(latest_value, ctx.tree)
                    or (isinstance(latest_stmt, ast.AugAssign)
                        and _cmd_augmented_value_exempt(ctx, latest_value)))
        if is_param:
            return False
        return all(_is_shell_quote_call(value, ctx.tree)
                   or _is_scalar_sanitizer_call(value, ctx.tree)
                   for _stmt, value in entries)
    if is_param:
        return False
    assigned = _cmd_alias_binding(ctx, scope, name, line, col)
    if not isinstance(assigned, ast.Call):
        return False
    return (_is_shell_quote_call(assigned, ctx.tree)
            or _is_scalar_sanitizer_call(assigned, ctx.tree))
def _cmd_literal_binding(ctx: _CmdScanContext, scope: str, name: str,
                         line: int, col: int | None = None) -> bool:
    entries = _binding_entries_before(ctx, name, line, col, scope)
    is_param = name in _params_at(ctx.func_param_ranges, line)
    if entries:
        latest_stmt, latest_value = entries[-1]
        if not _statement_is_conditional(
                ctx.tree, latest_stmt, ctx.parent_map):
            return _cmd_is_literal_value(latest_value)
        if is_param:
            return False
        return all(_cmd_is_literal_value(value)
                   for _stmt, value in entries)
    if is_param:
        return False
    return _cmd_is_literal_value(
        _cmd_alias_binding(ctx, scope, name, line, col))
def _cmd_component_exempt(ctx: _CmdScanContext, scope: str, name: str,
                          line: int, col: int | None = None) -> bool:
    return (_cmd_name_exempt(ctx, scope, name, line, col)
            or _cmd_literal_binding(ctx, scope, name, line, col))
def _cmd_is_literal_value(node: ast.AST | None) -> bool:
    if node is None:
        return False
    if isinstance(node, ast.Constant):
        return True
    if _is_static_transparent_call(node):
        return True
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
        return (_cmd_is_literal_value(node.left)
                and _cmd_is_literal_value(node.right))
    if isinstance(node, ast.JoinedStr):
        return all(
            (isinstance(value, ast.Constant)
             or (isinstance(value, ast.FormattedValue)
                 and value.format_spec is None
                 and _cmd_is_literal_value(value.value)))
            for value in node.values)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return all(_cmd_is_literal_value(elt) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return (all(k is not None and _cmd_is_literal_value(k)
                    for k in node.keys)
                and all(_cmd_is_literal_value(v) for v in node.values))
    return False
def _cmd_augmented_value_exempt(ctx: _CmdScanContext,
                                 node: ast.AST) -> bool:
    if (_cmd_is_literal_value(node)
            or _is_shell_quote_call(node, ctx.tree)
            or _is_scalar_sanitizer_call(node, ctx.tree)):
        return True
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
        return (_cmd_augmented_value_exempt(ctx, node.left)
                and _cmd_augmented_value_exempt(ctx, node.right))
    if isinstance(node, ast.JoinedStr):
        return all(
            isinstance(value, ast.Constant)
            or (isinstance(value, ast.FormattedValue)
                and _cmd_augmented_value_exempt(ctx, value.value))
            for value in node.values)
    return False
def _is_shell_quote_call(node: ast.AST,
                         tree: ast.Module | None = None) -> bool:
    return (isinstance(node, ast.Call)
            and resolve_taint_source(
                node, _CMD_SHELL_QUOTE_CALLS, tree) is not None)
def _cmd_interp_all_exempt(ctx: _CmdScanContext, arg: ast.AST,
                           line: int, scope: str,
                           col: int | None = None) -> bool:
    def prune(call):
        return (_is_static_transparent_call(call)
                or _is_shell_quote_call(call, ctx.tree)
                or _is_scalar_sanitizer_call(call, ctx.tree))
    for sub in _iter_interp_nodes(arg, prune):
        if isinstance(sub, ast.Call):
            return False
        if not isinstance(sub, ast.Name):
            continue
        if not _cmd_component_exempt(ctx, scope, sub.id, line, col):
            return False
    return True
def _cmd_expr_tainted(ctx: _CmdScanContext, expr: ast.AST, line: int,
                      scope: str, col: int | None = None) -> bool:
    if isinstance(expr, ast.Name):
        if _cmd_component_exempt(ctx, scope, expr.id, line, col):
            return False
        return expr.id in _visible_input_taints(ctx, scope, line, col)
    if isinstance(expr, (ast.Starred, ast.Await)):
        return _cmd_expr_tainted(ctx, expr.value, line, scope, col)
    if isinstance(expr, ast.Call):
        if resolve_taint_source(
                expr, TAINT_SOURCE_CALLS, ctx.tree) is not None:
            return True
        if (_is_scalar_sanitizer_call(expr, ctx.tree)
                or _is_shell_quote_call(expr, ctx.tree)):
            return False
        values = [*expr.args, *(kw.value for kw in expr.keywords)]
        if isinstance(expr.func, ast.Attribute):
            values.append(expr.func.value)
        return any(_cmd_expr_tainted(ctx, value, line, scope, col)
                   for value in values)
    if isinstance(expr, (ast.Attribute, ast.Subscript)):
        if resolve_taint_source(
                expr, TAINT_SOURCE_CALLS, ctx.tree) is not None:
            return True
        root = expr
        while isinstance(root, (ast.Attribute, ast.Subscript)):
            root = root.value
        return (isinstance(root, ast.Name)
                and not _cmd_name_exempt(ctx, scope, root.id, line, col)
                and root.id in _visible_input_taints(ctx, scope, line, col))
    if isinstance(expr, (ast.BinOp, ast.JoinedStr, ast.List, ast.Tuple,
                         ast.Set, ast.Dict, ast.BoolOp, ast.IfExp,
                         ast.NamedExpr)):
        return _cmd_composite_tainted(ctx, expr, line, scope, col=col)
    return False
def _cmd_composite_operands(expr: ast.AST):
    if isinstance(expr, ast.BinOp):
        yield from _cmd_composite_operands(expr.left)
        yield from _cmd_composite_operands(expr.right)
        return
    if isinstance(expr, ast.JoinedStr):
        for value in expr.values:
            yield from _cmd_composite_operands(
                value.value if isinstance(value, ast.FormattedValue) else value)
        return
    if isinstance(expr, (ast.List, ast.Tuple, ast.Set)):
        for elt in expr.elts:
            yield from _cmd_composite_operands(elt)
        return
    if isinstance(expr, ast.Dict):
        for key, value in zip(expr.keys, expr.values, strict=True):
            if key is not None:
                yield from _cmd_composite_operands(key)
            yield from _cmd_composite_operands(value)
        return
    if isinstance(expr, ast.BoolOp):
        for value in expr.values:
            yield from _cmd_composite_operands(value)
        return
    if isinstance(expr, ast.IfExp):
        yield from _cmd_composite_operands(expr.body)
        yield from _cmd_composite_operands(expr.orelse)
        return
    if isinstance(expr, ast.NamedExpr):
        yield from _cmd_composite_operands(expr.value)
        return
    yield expr
def _cmd_operand_tainted(ctx: _CmdScanContext, operand: ast.AST, line: int,
                         scope: str, seen: frozenset,
                         col: int | None = None) -> bool:
    if isinstance(operand, ast.Call):
        return not (_is_static_transparent_call(operand)
                    or _is_scalar_sanitizer_call(operand, ctx.tree)
                    or _is_shell_quote_call(operand, ctx.tree))
    if _cmd_expr_tainted(ctx, operand, line, scope, col):
        return True
    if isinstance(operand, (ast.Attribute, ast.Subscript)):
        root = operand
        while isinstance(root, (ast.Attribute, ast.Subscript)):
            root = root.value
        return (isinstance(root, ast.Name)
                and not _cmd_name_exempt(ctx, scope, root.id, line, col))
    if not isinstance(operand, ast.Name) or operand.id in seen:
        return False
    name = operand.id
    if _cmd_component_exempt(ctx, scope, name, line, col):
        return False
    assigned = lookup_name_assignment(
        ctx.tree, name, line, scope=scope, scope_idx=ctx.facts.scope_idx)
    if assigned is None:
        return True
    if isinstance(assigned, (ast.Name, ast.Call, ast.Constant,
                             ast.Attribute, ast.Subscript, ast.BinOp,
                             ast.JoinedStr, ast.List, ast.Tuple, ast.Set,
                             ast.Dict)):
        return _cmd_operand_tainted(
            ctx, assigned, line, scope, seen | {name}, col)
    return True
def _cmd_composite_tainted(ctx: _CmdScanContext, expr: ast.AST, line: int,
                           scope: str, seen: frozenset = _EMPTY_NAME_SET,
                           col: int | None = None) -> bool:
    return any(_cmd_operand_tainted(ctx, operand, line, scope, seen, col)
               for operand in _cmd_composite_operands(expr))
def _cmd_is_list_argv(arg: ast.AST) -> bool:
    if isinstance(arg, (ast.List, ast.Tuple)):
        return True
    if isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Add):
        return (_cmd_is_list_argv(arg.left)
                or _cmd_is_list_argv(arg.right))
    return False
DESER_DANGER_FUNCTIONS: frozenset[str] = frozenset({
    'pickle.load', 'pickle.loads',
    'yaml.load', 'yaml.unsafe_load',
    'marshal.load', 'marshal.loads',
    'dill.load', 'dill.loads',
    'torch.load',
})
_DESER_DATA_KWARGS: dict[str, tuple[str, ...]] = {
    'pickle.dump': ('obj',),
    'pickle.load': ('file',),
    'pickle.loads': ('data',),
    'yaml.load': ('stream',),
    'yaml.unsafe_load': ('stream',),
    'marshal.load': ('file',),
    'marshal.loads': ('bytes',),
    'dill.load': ('file',),
    'dill.loads': ('str',),
    'torch.load': ('f',),
}
_SAFE_ALTERNATIVES = {
    'pickle.load': 'json.load()',
    'pickle.loads': 'json.loads()',
    'yaml.load': 'yaml.safe_load()',
    'yaml.unsafe_load': 'yaml.safe_load()',
    'marshal.load': 'json.load()',
    'marshal.loads': 'json.loads()',
    'dill.load': 'json.load()',
    'dill.loads': 'json.loads()',
}
_SourcePos = tuple[int, int]
_ControlGuard = tuple[tuple[int, str], ...]
_PickleDumpRecord = tuple[_SourcePos, _SourcePos, _ControlGuard, str | None]
_PickleDumpHandles = dict[tuple[str, str], set[_PickleDumpRecord]]
_PICKLE_WRITE_METHODS = frozenset({'write', 'writelines', 'truncate'})
_LOW_LEVEL_WRITE_METHODS = frozenset({'write', 'pwrite', 'writev', 'pwritev'})
_PICKLE_POSITION_METHODS = frozenset({'seek'})
_LOW_LEVEL_POSITION_METHODS = frozenset({'lseek'})
def scan_deserialization(tree: ast.Module, code: str, filepath: str,
                         analyzer: PreciseTaintAnalyzer) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    ctx = _build_scan_context(analyzer, tree, code, filepath)
    nodes = tree_nodes(tree)
    resolver = _StarImportCallResolver(tree, CALL_ALIAS_MODULES["deser"])
    dump_handles: _PickleDumpHandles = {}
    for _n in nodes:
        _dump = _pickle_dump_handle(_n, resolver, ctx)
        if _dump is None:
            continue
        _scope, _handle, _line, _binding, _guard, _dump_path = _dump
        dump_handles.setdefault((_scope, _handle), set()).add(
            (_line, _binding, _guard, _dump_path))
    for node in nodes:
        finding = _deser_scan_node(ctx, node, dump_handles, resolver)
        if finding is not None:
            findings.append(finding)
    return findings
def _node_position(node: ast.AST) -> _SourcePos:
    return node.lineno, getattr(node, 'col_offset', 0) or 0
def _control_guard_chain(ctx: _ScanContext,
                         node: ast.AST) -> _ControlGuard:
    chain: list[tuple[int, str]] = []
    current = node
    parent = ctx.parent_map.get(id(current))
    conditional = (ast.If, ast.Try, getattr(ast, 'TryStar', ast.Try),
                   ast.Match, ast.For, ast.AsyncFor, ast.While,
                   ast.ExceptHandler, ast.match_case)
    while parent is not None:
        if isinstance(parent, conditional):
            region = ''
            for field_name in ('body', 'orelse', 'handlers', 'finalbody', 'cases'):
                children = getattr(parent, field_name, None)
                if (isinstance(children, list)
                        and any(child is current for child in children)):
                    region = field_name
                    break
            chain.append((id(parent), region))
        current = parent
        parent = ctx.parent_map.get(id(current))
    return tuple(reversed(chain))
def _handle_binding_expr(ctx: _ScanContext, name: str,
                         use_node: ast.Call, scope: str) -> ast.AST | None:
    use_pos = _node_position(use_node)
    candidates: list[ast.AST] = []
    assigned = lookup_name_assignment(
        ctx.tree, name, use_node.lineno, scope=scope,
        scope_idx=ctx.facts.scope_idx, use_col=use_node.col_offset)
    if assigned is not None:
        candidates.append(assigned)
    for stmt in tree_nodes(ctx.tree):
        if not isinstance(stmt, (ast.With, ast.AsyncWith)):
            continue
        stmt_scope = ctx.facts.scope_idx.get(id(stmt), "")
        if (stmt_scope != scope
                and not (stmt_scope == ""
                         and ctx.facts.module_visible(scope, name))):
            continue
        for item in stmt.items:
            if not (isinstance(item.optional_vars, ast.Name)
                    and item.optional_vars.id == name):
                continue
            position = _node_position(item.context_expr)
            if position < use_pos:
                candidates.append(item.context_expr)
    return max(candidates, key=_node_position, default=None)


def _handle_binding_pos(ctx: _ScanContext, name: str,
                        use_node: ast.Call, scope: str) -> _SourcePos | None:
    assigned = _handle_binding_expr(ctx, name, use_node, scope)
    return _node_position(assigned) if assigned is not None else None


def _static_open_path(node: ast.AST | None) -> str | None:
    if (not isinstance(node, ast.Call)
            or resolve_call_name(node) not in {
                'open', 'io.open', 'codecs.open'}):
        return None
    path = (node.args[0] if node.args else next(
        (kw.value for kw in node.keywords
         if kw.arg in {'file', 'filename'}), None))
    return _static_path_text(path)


def _handle_static_path(ctx: _ScanContext, name: str,
                        use_node: ast.Call, scope: str) -> str | None:
    assigned = _handle_binding_expr(ctx, name, use_node, scope)
    return _static_open_path(assigned)

def _write_target_static_path(ctx: _ScanContext, target: ast.AST,
                              node: ast.Call, scope: str) -> str | None:
    seen: set[str] = set()
    while True:
        direct_path = _static_open_path(target)
        if direct_path is not None:
            return direct_path
        if isinstance(target, ast.Name):
            handle_path = _handle_static_path(ctx, target.id, node, scope)
            if handle_path is not None:
                return handle_path
            if target.id in seen:
                return None
            seen.add(target.id)
            target = lookup_name_assignment(
                ctx.tree, target.id, node.lineno, scope=scope,
                scope_idx=ctx.facts.scope_idx, use_col=node.col_offset)
            if target is None:
                return None
            continue
        if (isinstance(target, ast.Call)
                and isinstance(target.func, ast.Attribute)
                and target.func.attr == 'fileno'
                and not target.args and not target.keywords):
            target = target.func.value
            continue
        return None

def _open_call_mutates_static_path(node: ast.Call, path: str) -> bool:
    if _static_open_path(node) != path:
        return False
    mode = (node.args[1] if len(node.args) > 1 else next(
        (kw.value for kw in node.keywords if kw.arg == 'mode'), None))
    if mode is None:
        return False
    if not (isinstance(mode, ast.Constant)
            and isinstance(mode.value, str)):
        return True
    return any(flag in mode.value for flag in 'wax+')


def _pickle_dump_handle(
        node: ast.AST, resolver: ImportCallResolver, ctx: _ScanContext
        ) -> tuple[str, str, _SourcePos, _SourcePos, _ControlGuard,
                   str | None] | None:
    if (not isinstance(node, ast.Call)
            or resolver.resolve(
                resolve_call_name(node)) != 'pickle.dump'):
        return None
    payload = _deser_first_arg(node, 'pickle.dump')
    handle = node.args[1] if len(node.args) >= 2 else next(
        (kw.value for kw in node.keywords if kw.arg == 'file'), None)
    if not isinstance(handle, ast.Name) or payload is None:
        return None
    scope = ctx.facts.scope_idx.get(id(node), "")
    if _deser_arg_untrusted(
            payload, _visible_input_taints(
                ctx, scope, node.lineno, node.col_offset), ctx.tree):
        return None
    binding_pos = _handle_binding_pos(ctx, handle.id, node, scope)
    if binding_pos is None:
        return None
    return (scope, handle.id, _node_position(node), binding_pos,
            _control_guard_chain(ctx, node),
            _handle_static_path(ctx, handle.id, node, scope))
def _deser_scan_node(ctx: _ScanContext, node: ast.AST,
                     dump_handles: _PickleDumpHandles,
                     resolver: ImportCallResolver
                     ) -> VulnerabilityFinding | None:
    if not isinstance(node, ast.Call):
        return None
    call_name = resolver.resolve(resolve_call_name(node))
    if call_name not in DESER_DANGER_FUNCTIONS:
        return None
    scope = ctx.facts.scope_idx.get(id(node), "")
    taint = _visible_input_taints(
        ctx, scope, node.lineno, node.col_offset)
    if call_name == 'yaml.load' and yaml_load_is_safe(node, ctx.tree):
        return None
    if _deser_self_managed_pickle(
            ctx, scope, node, call_name, taint, dump_handles):
        return None
    data_arg = _deser_first_arg(node, call_name)
    has_untrusted = _deser_data_arg_untrusted(
        ctx, node, scope, data_arg, taint)
    return _deser_finding(ctx, node, call_name, has_untrusted)
def _deser_self_managed_pickle(ctx: _ScanContext, scope: str,
                               node: ast.Call, call_name: str,
                               taint: frozenset,
                               dump_handles: _PickleDumpHandles) -> bool:
    first = _deser_first_arg(node, call_name)
    if not (call_name == 'pickle.load'
            and isinstance(first, ast.Name) and first.id not in taint):
        return False
    load_pos = _node_position(node)
    load_guard = _control_guard_chain(ctx, node)
    load_path = _handle_static_path(ctx, first.id, node, scope)
    if (load_path is not None and _has_prior_path_dump(
            ctx, dump_handles, load_path, scope, load_pos, load_guard)):
        return True
    binding_pos = _handle_binding_pos(ctx, first.id, node, scope)
    if binding_pos is None:
        return False
    if _has_prior_dump(
            ctx, dump_handles, (scope, first.id), load_pos, binding_pos,
            load_guard):
        return True
    return (ctx.facts.module_visible(scope, first.id)
            and _has_prior_dump(
                ctx, dump_handles, ('', first.id), load_pos, binding_pos,
                load_guard))
def _write_targets_handle(ctx: _ScanContext, handle: str,
                          target: ast.AST, node: ast.Call,
                          scope: str) -> bool:
    seen: set[str] = set()
    while True:
        if isinstance(target, ast.Name):
            if target.id == handle:
                return True
            if target.id in seen:
                return False
            seen.add(target.id)
            target = lookup_name_assignment(
                ctx.tree, target.id, node.lineno, scope=scope,
                scope_idx=ctx.facts.scope_idx, use_col=node.col_offset)
            if target is None:
                return False
            continue
        if (isinstance(target, ast.Call)
                and isinstance(target.func, ast.Attribute)
                and target.func.attr == 'fileno'
                and not target.args and not target.keywords):
            target = target.func.value
            continue
        return False
def _is_zero_position_value(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, int) and node.value == 0
    return (isinstance(node, ast.Attribute) and node.attr == 'SEEK_SET'
            and isinstance(node.value, ast.Name)
            and node.value.id in {'os', 'io'})
def _is_start_rewind(node: ast.Call, offset_index: int) -> bool:
    if len(node.args) > offset_index + 2:
        return False
    allowed_keywords = {'offset', 'whence'} | ({'fd'} if offset_index else set())
    if any(kw.arg not in allowed_keywords for kw in node.keywords):
        return False
    offset = (node.args[offset_index] if len(node.args) > offset_index
              else next((kw.value for kw in node.keywords
                         if kw.arg == 'offset'), None))
    whence = (node.args[offset_index + 1] if len(node.args) > offset_index + 1
              else next((kw.value for kw in node.keywords
                         if kw.arg == 'whence'), None))
    return (_is_zero_position_value(offset)
            and (whence is None or _is_zero_position_value(whence)))
def _handle_has_intervening_mutation(ctx: _ScanContext, handle: str,
                                     binding_pos: _SourcePos,
                                     safe_dump_pos: _SourcePos,
                                     load_pos: _SourcePos) -> bool:
    for node in tree_nodes(ctx.tree):
        if not isinstance(node, ast.Call):
            continue
        position = _node_position(node)
        if not binding_pos < position < load_pos or position == safe_dump_pos:
            continue
        func = node.func
        if isinstance(func, ast.Attribute):
            method = func.attr
        elif isinstance(func, ast.Name):
            method = func.id
        else:
            continue
        targets: list[ast.AST] = []
        if (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and (func.attr in _PICKLE_WRITE_METHODS
                     or (func.attr in _PICKLE_POSITION_METHODS
                         and not _is_start_rewind(node, 0)))):
            targets.append(func.value)
        if method in _LOW_LEVEL_WRITE_METHODS | _LOW_LEVEL_POSITION_METHODS:
            target = (node.args[0] if node.args else next(
                (kw.value for kw in node.keywords if kw.arg == 'fd'), None))
            if (target is not None
                    and (method in _LOW_LEVEL_WRITE_METHODS
                         or not _is_start_rewind(node, 1))):
                targets.append(target)
        if method == 'dump':
            dump_target = (
                node.args[1] if len(node.args) >= 2 else next(
                    (kw.value for kw in node.keywords if kw.arg == 'file'),
                    None))
            if dump_target is not None:
                targets.append(dump_target)
        scope = ctx.facts.scope_idx.get(id(node), "")
        if not any(_write_targets_handle(ctx, handle, target, node, scope)
                   for target in targets):
            continue
        if _handle_binding_pos(ctx, handle, node, scope) == binding_pos:
            return True
    return False
def _path_has_intervening_mutation(ctx: _ScanContext, path: str,
                                   safe_dump_pos: _SourcePos,
                                   load_pos: _SourcePos) -> bool:
    for node in tree_nodes(ctx.tree):
        if not isinstance(node, ast.Call):
            continue
        position = _node_position(node)
        if not safe_dump_pos < position < load_pos:
            continue
        if _open_call_mutates_static_path(node, path):
            return True
        func = node.func
        if isinstance(func, ast.Attribute):
            method = func.attr
        elif isinstance(func, ast.Name):
            method = func.id
        else:
            continue
        targets: list[ast.AST] = []
        if (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and (func.attr in _PICKLE_WRITE_METHODS
                     or (func.attr in _PICKLE_POSITION_METHODS
                         and not _is_start_rewind(node, 0)))):
            targets.append(func.value)
        if method in _LOW_LEVEL_WRITE_METHODS | _LOW_LEVEL_POSITION_METHODS:
            target = (node.args[0] if node.args else next(
                (kw.value for kw in node.keywords if kw.arg == 'fd'), None))
            if (target is not None
                    and (method in _LOW_LEVEL_WRITE_METHODS
                         or not _is_start_rewind(node, 1))):
                targets.append(target)
        if method == 'dump':
            target = (node.args[1] if len(node.args) >= 2 else next(
                (kw.value for kw in node.keywords if kw.arg == 'file'), None))
            if target is not None:
                targets.append(target)
        scope = ctx.facts.scope_idx.get(id(node), "")
        for target in targets:
            if _write_target_static_path(ctx, target, node, scope) == path:
                return True
    return False


def _has_prior_path_dump(ctx: _ScanContext,
                         dump_handles: _PickleDumpHandles,
                         load_path: str, load_scope: str,
                         load_pos: _SourcePos,
                         load_guard: _ControlGuard) -> bool:
    return any(
        dump_path == load_path
        and dump_binding <= dump_pos < load_pos
        and dump_guard == load_guard[:len(dump_guard)]
        and not _path_has_intervening_mutation(
            ctx, load_path, dump_pos, load_pos)
        for (dump_scope, _handle), records in dump_handles.items()
        if dump_scope == load_scope
        for dump_pos, dump_binding, dump_guard, dump_path in records)


def _has_prior_dump(ctx: _ScanContext, dump_handles: _PickleDumpHandles,
                    key: tuple[str, str], load_pos: _SourcePos,
                    binding_pos: _SourcePos,
                    load_guard: _ControlGuard) -> bool:
    handle = key[1]
    return any(
        dump_binding == binding_pos
        and binding_pos <= dump_pos < load_pos
        and dump_guard == load_guard[:len(dump_guard)]
        and not _handle_has_intervening_mutation(
            ctx, handle, binding_pos, dump_pos, load_pos)
        for dump_pos, dump_binding, dump_guard, _dump_path
        in dump_handles.get(key, ())
    )
def _deser_first_arg(node: ast.Call, call_name: str) -> ast.AST | None:
    if node.args:
        return node.args[0]
    names = _DESER_DATA_KWARGS.get(call_name, ())
    for kw in node.keywords:
        if kw.arg in names:
            return kw.value
    return None
def _deser_composite_arg_untrusted(
        arg: ast.AST, taint: frozenset,
        tree: ast.AST | None = None) -> bool:
    for sub in _iter_interp_nodes(arg, tree=tree):
        if sub is arg:
            continue
        if isinstance(sub, ast.Name) and sub.id in taint:
            return True
        if (isinstance(sub, (ast.Call, ast.Attribute, ast.Subscript))
                and resolve_taint_source(
                    sub, TAINT_SOURCE_CALLS, tree) is not None):
            return True
    return False
def _deser_arg_untrusted(
        arg: ast.AST, taint: frozenset,
        tree: ast.AST | None = None) -> bool:
    if isinstance(arg, ast.Name):
        return arg.id in taint
    if resolve_taint_source(arg, TAINT_SOURCE_CALLS, tree) is not None:
        return True
    if isinstance(arg, ast.Constant):
        return False
    return _deser_composite_arg_untrusted(arg, taint, tree)
def _deser_data_arg_untrusted(ctx: _ScanContext, node: ast.Call,
                               scope: str, data_arg: ast.AST | None,
                               taint: frozenset) -> bool:
    if data_arg is None:
        return False
    if _deser_arg_untrusted(data_arg, taint, ctx.tree):
        return True
    if not isinstance(data_arg, ast.Name):
        return False
    assigned = _handle_binding_expr(ctx, data_arg.id, node, scope)
    return (assigned is not None
            and _deser_arg_untrusted(assigned, taint, ctx.tree))


def _deser_finding(ctx: _ScanContext, node: ast.Call, call_name: str,
                   has_untrusted: bool) -> VulnerabilityFinding:
    return build_vulnerability_finding(
        VulnerabilityCategory.DESERIALIZATION,
        code=ctx.code,
        filepath=ctx.filepath,
        line=node.lineno,
        source="untrusted_data" if has_untrusted else "unknown",
        sink=call_name,
        severity="HIGH" if has_untrusted else "MEDIUM",
        confidence=0.9 if has_untrusted else 0.5,
        suggestion=("使用安全替代: "
                    f"{_SAFE_ALTERNATIVES.get(call_name, '安全的序列化方案')}"),
        cwe_id="CWE-502",
    )
_TAINT_SCANNERS = (scan_sql_injection, scan_command_injection,
                   scan_deserialization, scan_path_traversal)
def _iter_scoped_functions(tree: ast.AST) -> list[tuple[str, ast.AST]]:
    found: list[tuple[str, ast.AST]] = []
    stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while stack:
        node, prefix = stack.pop()
        pending: list[tuple[ast.AST, str]] = []
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qualname = f"{prefix}{child.name}"
                found.append((qualname, child))
                pending.append((child, f"{qualname}."))
            elif isinstance(child, ast.ClassDef):
                pending.append((child, f"{prefix}{child.name}."))
            else:
                pending.append((child, prefix))
        stack.extend(reversed(pending))
    counts = Counter(name for name, _ in found)
    return [(f"{name}@{node.lineno}" if counts[name] > 1 else name, node)
            for name, node in found]
class PreciseVulnDetector:
    def __init__(self) -> None:
        self._cfg_builder = CFGBuilder()
        self._du_analyzer = DUChainAnalyzer()
        self.knowledge = get_security_knowledge()
    @staticmethod
    def match_knowledge_patterns(rules: list[dict], node_srcs: list,
                                 filepath: str) -> list[VulnerabilityFinding]:
        rules = _clean_knowledge_rules(rules)
        compiled = _compile_knowledge_patterns(rules)
        emitted: set[tuple[str, int, int]] = set()
        return [
            _knowledge_finding(rule, pattern_name, node, filepath)
            for rule, pattern_name, node in _iter_knowledge_hits(
                rules, node_srcs, compiled, emitted)
        ]
    def cfg_du_report(self, tree: ast.AST) -> tuple[dict[str, int], dict[str, int]]:
        cfg_results: dict[str, int] = {}
        du_results: dict[str, int] = {}
        for qualname, node in _iter_scoped_functions(tree):
            cfg_results[qualname] = len(self._cfg_builder.build(node))
            du_results[qualname] = len(self._du_analyzer.analyze(node))
        return cfg_results, du_results
    def scan(self, tree: ast.Module, code: str,
             filepath: str = _DEFAULT_FILEPATH) -> list[VulnerabilityFinding]:
        filepath = normalize_filepath(filepath)
        _ck = (filepath, _scan_source_digest(code),
               _scan_tree_digest(tree))
        with _SCAN_RESULT_CACHE_LOCK:
            _hit = _SCAN_RESULT_CACHE.get(_ck)
            if _hit is not None:
                return deepcopy(_hit)
        findings: list[VulnerabilityFinding] = []
        analyzer = PreciseTaintAnalyzer()
        for scan in _TAINT_SCANNERS:
            findings.extend(scan(tree, code, filepath, analyzer))
        findings.extend(scan_pattern_channels(tree, code, filepath))
        _sev = Counter(f.severity for f in findings)
        logger.info(
            "[VulnDetector] scan 完成: %s — %d 项发现 (CRITICAL=%d HIGH=%d MEDIUM=%d)",
            filepath or "<code>", len(findings),
            _sev.get("CRITICAL", 0), _sev.get("HIGH", 0), _sev.get("MEDIUM", 0),
        )
        with _SCAN_RESULT_CACHE_LOCK:
            if len(_SCAN_RESULT_CACHE) >= _SCAN_RESULT_CACHE_CAP:
                _SCAN_RESULT_CACHE.clear()
            _SCAN_RESULT_CACHE[_ck] = deepcopy(findings)
        return findings
def _scan_source_digest(code: str) -> str:
    _norm = code.replace("\r\n", "\n").replace("\r", "\n").rstrip("\n")
    return hashlib.sha256(
        _norm.encode("utf-8", "surrogatepass")).hexdigest()
def _scan_tree_digest(tree: ast.Module) -> str:
    dumped = ast.dump(tree, include_attributes=True)
    return hashlib.sha256(
        dumped.encode("utf-8", "surrogatepass")).hexdigest()
_SCAN_RESULT_CACHE: dict[tuple[str, str, str], list] = {}
_SCAN_RESULT_CACHE_LOCK = threading.Lock()
_SCAN_RESULT_CACHE_CAP = 512
_STAR_IMPORT_MEMO: dict[int, tuple[ast.Module, frozenset[str]]] = {}
_STAR_IMPORT_MEMO_LOCK = threading.Lock()
_STAR_IMPORT_MEMO_CAP = 256
def _star_import_modules(tree: ast.Module) -> frozenset[str]:
    with _STAR_IMPORT_MEMO_LOCK:
        hit = _STAR_IMPORT_MEMO.get(id(tree))
        if hit is not None and hit[0] is tree:
            return hit[1]
    mods = frozenset(
        node.module for node in tree_nodes(tree)
        if isinstance(node, ast.ImportFrom) and not node.level and node.module
        and any(alias.name == '*' for alias in node.names))
    with _STAR_IMPORT_MEMO_LOCK:
        if len(_STAR_IMPORT_MEMO) >= _STAR_IMPORT_MEMO_CAP:
            _STAR_IMPORT_MEMO.clear()
        _STAR_IMPORT_MEMO[id(tree)] = (tree, mods)
    return mods
def release_scanner_caches() -> int:
    """释放本模块两级进程级缓存（扫描结果 + 星号导入记忆）。

    返回实际清空的缓存域数（0 表示本就为空）。``PreciseVulnDetector`` 由
    ``EnhancedSecurityDiagnoser`` 持有，E1 诊断器缓存释放钩子经此函数一并
    回收，避免只清 diagnoser 自身缓存而漏掉检测器层。
    """
    released = 0
    with _SCAN_RESULT_CACHE_LOCK:
        if _SCAN_RESULT_CACHE:
            _SCAN_RESULT_CACHE.clear()
            released += 1
    with _STAR_IMPORT_MEMO_LOCK:
        if _STAR_IMPORT_MEMO:
            _STAR_IMPORT_MEMO.clear()
            released += 1
    return released
class _StarImportCallResolver(ImportCallResolver):
    __slots__ = ()
    def _star_bound(self, module: str) -> bool:
        if self._star_modules is None:
            self._star_modules = _star_import_modules(self._tree)
        return module in self._star_modules
def danger_call_match(call_name: str,
                       danger_calls: frozenset[str]) -> bool:
    return (call_name in danger_calls
            or call_name.rsplit(".", 1)[-1] in danger_calls)
_XSS_DANGER_CALLS = frozenset(
    {VULN_RENDER_TEMPLATE_STRING}
    | {member for members in CALL_ALIAS_MODULES["xss"].values()
       for member in members})
_SSTI_ENV_SINK = 'Environment.from_string'
_SSTI_DANGER_CALLS = frozenset({
    VULN_RENDER_TEMPLATE_STRING, 'jinja2.Template',
    _SSTI_ENV_SINK, 'mako.template.Template',
})
_XXE_DANGER_CALLS = frozenset({
    'etree.parse', 'etree.fromstring', 'etree.XMLParser',
    'ElementTree.parse', 'ElementTree.fromstring', 'ElementTree.XMLParser',
    'minidom.parse', 'minidom.parseString',
    'sax.parse', 'sax.parseString',
})
_XXE_PARSER_CONSTRUCTORS = frozenset({
    'etree.XMLParser', 'ElementTree.XMLParser',
})
_XXE_CANONICAL_MODULES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ('lxml.etree', ('parse', 'fromstring', 'XMLParser')),
    ('xml.etree.ElementTree', ('parse', 'fromstring', 'XMLParser')),
    ('xml.dom.minidom', ('parse', 'parseString')),
    ('xml.sax', ('parse', 'parseString')),
)
_LDAP_DANGER_CALLS = frozenset(
    {"ldap3.Connection.search"}
    | {f"ldap.{member}"
       for member in CALL_ALIAS_MODULES["ldap"]["ldap"]})
@dataclass(frozen=True)
class _InjectionProfile:
    category: VulnerabilityCategory
    severity: str
    confidence: float
    suggestion: str
    cwe_id: str
    first_arg_only: bool = False
    positional_arg_indices: tuple[tuple[str, int], ...] = ()
    keyword_args: frozenset[str] = _EMPTY_NAME_SET
    sanitizer_calls: frozenset[str] = _EMPTY_NAME_SET
_XSS_KEYWORD_ARGS: frozenset[str] = frozenset({
    'content', 'source', 's', 'object',
})
_SSTI_KEYWORD_ARGS: frozenset[str] = frozenset({'source', 'text'})
_LDAP_KEYWORD_ARGS: frozenset[str] = frozenset({'filterstr', 'search_filter'})
_XSS_SANITIZER_CALLS = frozenset({
    'html.escape', 'markupsafe.escape', 'bleach.clean',
    'escape', 'conditional_escape',
})
_LDAP_SANITIZER_CALLS = frozenset({
    'ldap.filter.escape_filter_chars',
    'ldap3.utils.conv.escape_filter_chars', 'escape_filter_chars',
})
_XSS_PROFILE = _InjectionProfile(
    category=VulnerabilityCategory.XSS,
    severity="HIGH",
    confidence=0.85,
    suggestion="对用户输入进行 HTML 转义后再输出",
    cwe_id="CWE-79",
    first_arg_only=True,
    keyword_args=_XSS_KEYWORD_ARGS,
    sanitizer_calls=_XSS_SANITIZER_CALLS,
)
_SSTI_PROFILE = _InjectionProfile(
    category=VulnerabilityCategory.SSTI,
    severity="CRITICAL",
    confidence=0.95,
    suggestion="避免将用户输入直接传入模板渲染函数",
    cwe_id="CWE-94",
    first_arg_only=True,
    keyword_args=_SSTI_KEYWORD_ARGS,
)
_LDAP_POSITIONAL_ARG_INDICES = tuple(
    (call_name, 1 if call_name == 'ldap3.Connection.search' else 2)
    for call_name in sorted(_LDAP_DANGER_CALLS)
)
_LDAP_PROFILE = _InjectionProfile(
    category=VulnerabilityCategory.LDAP_INJECTION,
    severity="HIGH",
    confidence=0.85,
    suggestion="对 LDAP 查询参数进行转义",
    cwe_id="CWE-90",
    positional_arg_indices=_LDAP_POSITIONAL_ARG_INDICES,
    keyword_args=_LDAP_KEYWORD_ARGS,
    sanitizer_calls=_LDAP_SANITIZER_CALLS,
)
def _payload_argument_nodes(node: ast.Call,
                            profile: _InjectionProfile,
                            call_name: str,
                            tree: ast.Module) -> tuple[ast.AST, ...]:
    if profile.positional_arg_indices:
        position = next(
            (index for name, index in profile.positional_arg_indices
             if name == call_name), None)
        if (call_name == 'ldap3.Connection.search'
                and _resolve_ldap3_unbound_search(
                    tree, resolve_call_name(node))):
            position = 2
        args = (() if position is None
                else node.args[position:position + 1])
    else:
        args = node.args[:1] if profile.first_arg_only else node.args
    keyword_values = tuple(
        kw.value for kw in node.keywords if kw.arg in profile.keyword_args)
    return (*args, *keyword_values)
def _base_name_in_taint(node: ast.AST, taint: frozenset) -> bool:
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        node = node.value
    return isinstance(node, ast.Name) and node.id in taint
def _iter_payload_concat_parts(arg: ast.AST):
    if isinstance(arg, ast.BinOp):
        yield from _iter_payload_concat_parts(arg.left)
        yield from _iter_payload_concat_parts(arg.right)
        return
    if isinstance(arg, ast.JoinedStr):
        for value in arg.values:
            if isinstance(value, ast.FormattedValue):
                yield from _iter_payload_concat_parts(value.value)
                if value.format_spec is not None:
                    yield from _iter_payload_concat_parts(value.format_spec)
            else:
                yield value
        return
    yield arg
def _is_unsafe_payload(arg: ast.AST,
                       taint: frozenset = _EMPTY_NAME_SET,
                       tree: ast.Module | None = None,
                       sanitizer_calls: frozenset[str] = _EMPTY_NAME_SET) -> bool:
    if resolve_taint_source(arg, TAINT_SOURCE_CALLS, tree) is not None:
        return True
    if _base_name_in_taint(arg, taint):
        return True
    if isinstance(arg, ast.Call) and (
            _is_scalar_sanitizer_call(arg, tree)
            or resolve_taint_source(arg, sanitizer_calls, tree) is not None):
        return False
    if isinstance(arg, ast.Call):
        values = [*arg.args, *(kw.value for kw in arg.keywords)]
        if isinstance(arg.func, ast.Attribute):
            values.append(arg.func.value)
        return any(_is_unsafe_payload(
            value, taint, tree, sanitizer_calls) for value in values)
    if isinstance(arg, (ast.List, ast.Tuple, ast.Set)):
        return any(_is_unsafe_payload(
            value, taint, tree, sanitizer_calls) for value in arg.elts)
    if isinstance(arg, ast.Dict):
        return any(_is_unsafe_payload(
            value, taint, tree, sanitizer_calls)
            for value in (*arg.values,
                          *(key for key in arg.keys if key is not None)))
    if isinstance(arg, (ast.Starred, ast.Await, ast.NamedExpr)):
        return _is_unsafe_payload(arg.value, taint, tree, sanitizer_calls)
    if isinstance(arg, ast.BoolOp):
        return any(_is_unsafe_payload(
            value, taint, tree, sanitizer_calls) for value in arg.values)
    if isinstance(arg, ast.IfExp):
        return (_is_unsafe_payload(arg.body, taint, tree, sanitizer_calls)
                or _is_unsafe_payload(
                    arg.orelse, taint, tree, sanitizer_calls))
    if not isinstance(arg, (ast.BinOp, ast.JoinedStr)):
        return False
    if is_static_literal_expr(arg):
        return False
    return any(
        not (is_static_literal_expr(part)
             or _is_scalar_sanitizer_call(part, tree)
             or resolve_taint_source(
                 part, sanitizer_calls, tree) is not None)
        for part in _iter_payload_concat_parts(arg))
def _scan_dynamic_arg_calls(tree: ast.Module, code: str, filepath: str,
                            danger_calls: frozenset[str],
                            resolve: Callable[[ast.Call], str],
                            profile: _InjectionProfile,
                            analyzer: PreciseTaintAnalyzer | None = None,
                            scope_facts: ScopeFacts | None = None,
                            ) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    ctx = _build_scan_context(
        analyzer or PreciseTaintAnalyzer(), tree, code, filepath,
        facts=scope_facts)
    facts = ctx.facts
    sanitizer_names = set(profile.sanitizer_calls) | set(
        SCALAR_SANITIZER_CALLS)
    shadow = (facts.local_bindings, facts.global_names, facts.class_scopes)
    sanitized_keys = collect_sanitized_keys(
        tree, sanitizer_names, facts.scope_idx, shadow)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        call_name = resolve(node)
        if not danger_call_match(call_name, danger_calls):
            continue
        scope = facts.scope_idx.get(id(node), "")
        taint = _visible_input_taints(
            ctx, scope, node.lineno, node.col_offset)
        payload_args = _payload_argument_nodes(
            node, profile, call_name, tree)
        if not any(_is_unsafe_payload(
                arg, taint, tree, profile.sanitizer_calls)
                for arg in payload_args):
            continue
        active_sanitized_keys = _lambda_sanitized_keys(
            ctx, sanitized_keys, node.lineno, scope)
        if is_sanitized(
                node, tree, scope, active_sanitized_keys, shadow,
                sanitizer_names=sanitizer_names,
                argument_nodes=payload_args):
            continue
        findings.append(build_vulnerability_finding(
            profile.category,
            code=code,
            filepath=filepath,
            line=node.lineno,
            source="user_input",
            sink=call_name,
            severity=profile.severity,
            confidence=profile.confidence,
            suggestion=profile.suggestion,
            cwe_id=profile.cwe_id,
        ))
    return findings
def scan_xss(tree: ast.Module, code: str,
             filepath: str = _DEFAULT_FILEPATH,
             analyzer: PreciseTaintAnalyzer | None = None,
             ) -> list[VulnerabilityFinding]:
    resolver = _StarImportCallResolver(tree, CALL_ALIAS_MODULES["xss"])
    return _scan_dynamic_arg_calls(
        tree, code, filepath, _XSS_DANGER_CALLS,
        lambda node: resolver.resolve(resolve_call_name(node)),
        _XSS_PROFILE, analyzer)
_SSTI_BINDING_TARGETS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ('jinja2', ('Template',)),
    ('mako.template', ('Template',)),
)
_SSTI_ENV_MODULE = 'jinja2'
_SSTI_ENV_MEMBERS: tuple[str, ...] = ('Environment',)
_LDAP3_MODULE = 'ldap3'
_LDAP3_CONNECTION_MEMBERS: tuple[str, ...] = ('Connection',)
_LDAP_INITIALIZE_MEMBERS: tuple[str, ...] = ('initialize',)
_LDAP_INSTANCE_METHODS = frozenset({'search_s', 'search_ext', 'search_ext_s'})
def _resolve_imported_binding(tree: ast.Module, head: str, rest: str,
                              module: str, members: tuple[str, ...]) -> str:
    aliases, from_origins = collect_module_bindings_detailed(
        tree, module, members)
    return origin_from_binding(
        aliases, from_origins, head, rest, module, members,
        star_bound=module in _star_import_modules(tree))
def _constructor_call(tree: ast.Module, node: ast.AST | None,
                      module: str, members: tuple[str, ...]) -> bool:
    if not isinstance(node, ast.Call):
        return False
    call_name = resolve_call_name(node)
    if not call_name:
        return False
    head, _sep, rest = call_name.partition('.')
    return bool(_resolve_imported_binding(
        tree, head, rest, module, members))
def _assignment_target_names(node: ast.AST) -> list[str]:
    if isinstance(node, ast.Assign):
        targets: list[ast.AST] = list(node.targets)
    elif isinstance(node, ast.AnnAssign):
        targets = [node.target]
    else:
        return []
    return [target.id if isinstance(target, ast.Name) else target.attr
            for target in targets
            if isinstance(target, (ast.Name, ast.Attribute))]
def _constructor_binding_names(tree: ast.Module, module: str,
                               members: tuple[str, ...]) -> frozenset[str]:
    names: set[str] = set()
    for node in tree_nodes(tree):
        if (isinstance(node, (ast.Assign, ast.AnnAssign))
                and _constructor_call(tree, node.value, module, members)):
            names.update(_assignment_target_names(node))
    return frozenset(names)
def _class_scope_owner(scope: str, class_scopes: frozenset[str]) -> str:
    owner = ""
    for candidate in class_scopes:
        if ((scope == candidate or scope.startswith(candidate + "."))
                and len(candidate) > len(owner)):
            owner = candidate
    return owner
def _assignment_value_owners(tree: ast.Module) -> dict[int, ast.AST]:
    return {
        id(node.value): node for node in tree_nodes(tree)
        if isinstance(node, (ast.Assign, ast.AnnAssign))
        and node.value is not None
    }
def _latest_attribute_assignment(tree: ast.Module, receiver: ast.Attribute,
                                 call_node: ast.Call, scope: str,
                                 scope_idx: dict,
                                 class_scopes: frozenset[str], *,
                                 before: tuple[int, int] | None = None,
                                 ) -> ast.AST | None:
    receiver_name = dotted_name(receiver)
    if not receiver_name:
        return None
    call_pos = (before if before is not None else
                (call_node.lineno, getattr(call_node, 'col_offset', 0) or 0))
    call_owner = _class_scope_owner(scope, class_scopes)
    latest_pos = (-1, -1)
    latest_value = None
    for node in tree_nodes(tree):
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        if node.value is None:
            continue
        if not any(dotted_name(target) == receiver_name for target in targets):
            continue
        candidate_owner = _class_scope_owner(
            scope_idx.get(id(node), ""), class_scopes)
        if call_owner and candidate_owner and call_owner != candidate_owner:
            continue
        position = (node.lineno, getattr(node, 'col_offset', 0) or 0)
        if latest_pos < position < call_pos:
            latest_pos, latest_value = position, node.value
    return latest_value
def _resolve_name_alias_assignment(
        tree: ast.Module, name: str, node: ast.AST,
        scope: str, scope_idx: dict) -> ast.AST | None:
    seen: set[str] = set()
    current = name
    use_site = node
    while current not in seen:
        seen.add(current)
        assigned = lookup_name_assignment(
            tree, current, use_site.lineno, scope=scope,
            scope_idx=scope_idx,
            use_col=getattr(use_site, 'col_offset', 0) or 0)
        if not isinstance(assigned, ast.Name):
            return assigned
        current = assigned.id
        use_site = assigned
    return None
def _constructed_receiver(tree: ast.Module, receiver: ast.AST,
                          binding_names: frozenset[str], scope_idx: dict,
                          class_scopes: frozenset[str],
                          call_node: ast.Call, module: str,
                          members: tuple[str, ...], parent_map: dict,
                          assignment_owners: dict[int, ast.AST]) -> bool:
    scope = scope_idx.get(id(call_node), "")
    if isinstance(receiver, ast.Call):
        return _constructor_call(tree, receiver, module, members)
    if isinstance(receiver, ast.Name):
        assigned = _resolve_name_alias_assignment(
            tree, receiver.id, call_node, scope, scope_idx)
        seen: set[int] = set()
        while assigned is not None and id(assigned) not in seen:
            if _constructor_call(tree, assigned, module, members):
                return True
            seen.add(id(assigned))
            stmt = assignment_owners.get(id(assigned))
            if (stmt is None or not _statement_is_conditional(
                    tree, stmt, parent_map)):
                return False
            assigned = _resolve_name_alias_assignment(
                tree, receiver.id, stmt, scope, scope_idx)
        return False
    if isinstance(receiver, ast.Attribute):
        if receiver.attr not in binding_names:
            return False
        before = None
        seen: set[int] = set()
        while True:
            assigned = _latest_attribute_assignment(
                tree, receiver, call_node, scope, scope_idx, class_scopes,
                before=before)
            if assigned is None or id(assigned) in seen:
                return False
            if _constructor_call(tree, assigned, module, members):
                return True
            seen.add(id(assigned))
            stmt = assignment_owners.get(id(assigned))
            if (stmt is None or not _statement_is_conditional(
                    tree, stmt, parent_map)):
                return False
            before = (stmt.lineno, stmt.col_offset)
    return False
def _resolve_ssti_env_call(tree: ast.Module, node: ast.Call,
                           env_names: frozenset[str], scope_idx: dict,
                           class_scopes: frozenset[str], parent_map: dict,
                           assignment_owners: dict[int, ast.AST]) -> str:
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'from_string'):
        return ''
    return _SSTI_ENV_SINK if _constructed_receiver(
        tree, func.value, env_names, scope_idx, class_scopes, node,
        _SSTI_ENV_MODULE, _SSTI_ENV_MEMBERS, parent_map,
        assignment_owners) else ''
def _resolve_ssti_qualified_env(tree: ast.Module, call_name: str) -> str:
    suffix = '.from_string'
    if not call_name.endswith(suffix):
        return ''
    receiver = call_name[:-len(suffix)]
    head, _sep, rest = receiver.partition('.')
    if not head:
        return ''
    if _resolve_imported_binding(
            tree, head, rest, _SSTI_ENV_MODULE, _SSTI_ENV_MEMBERS):
        return _SSTI_ENV_SINK
    return ''
def _resolve_ssti_call(tree: ast.Module, node: ast.Call,
                       env_names: frozenset[str], scope_idx: dict,
                       class_scopes: frozenset[str], parent_map: dict,
                       assignment_owners: dict[int, ast.AST]) -> str:
    call_name = resolve_call_name(node)
    env_sink = (_resolve_ssti_env_call(
                    tree, node, env_names, scope_idx, class_scopes,
                    parent_map, assignment_owners)
                or (_resolve_ssti_qualified_env(tree, call_name)
                    if call_name else ''))
    if env_sink:
        return env_sink
    if not call_name:
        return call_name
    head, _sep, rest = call_name.partition('.')
    for module, members in _SSTI_BINDING_TARGETS:
        resolved = _resolve_imported_binding(tree, head, rest, module, members)
        if resolved:
            return resolved
    return call_name
def scan_ssti(tree: ast.Module, code: str,
              filepath: str = _DEFAULT_FILEPATH,
              analyzer: PreciseTaintAnalyzer | None = None,
              ) -> list[VulnerabilityFinding]:
    analyzer = analyzer or PreciseTaintAnalyzer()
    facts = collect_scope_facts(analyzer, tree)
    env_names = _constructor_binding_names(
        tree, _SSTI_ENV_MODULE, _SSTI_ENV_MEMBERS)
    parent_map = build_parent_map(tree)
    assignment_owners = _assignment_value_owners(tree)
    return _scan_dynamic_arg_calls(
        tree, code, filepath, _SSTI_DANGER_CALLS,
        lambda node: _resolve_ssti_call(
            tree, node, env_names, facts.scope_idx, facts.class_scopes,
            parent_map, assignment_owners),
        _SSTI_PROFILE, analyzer, facts)
def _resolve_ldap3_unbound_search(tree: ast.Module,
                                   call_name: str) -> str:
    suffix = '.search'
    if not call_name.endswith(suffix):
        return ''
    receiver = call_name[:-len(suffix)]
    head, _sep, rest = receiver.partition('.')
    if not head:
        return ''
    if _resolve_imported_binding(
            tree, head, rest, _LDAP3_MODULE, _LDAP3_CONNECTION_MEMBERS):
        return 'ldap3.Connection.search'
    return ''
def _resolve_ldap_call(tree: ast.Module, node: ast.Call,
                       resolver: ImportCallResolver,
                       ldap3_names: frozenset[str],
                       ldap_names: frozenset[str], scope_idx: dict,
                       class_scopes: frozenset[str], parent_map: dict,
                       assignment_owners: dict[int, ast.AST]) -> str:
    call_name = resolver.resolve(resolve_call_name(node))
    if call_name in _LDAP_DANGER_CALLS:
        return call_name
    func = node.func
    if not isinstance(func, ast.Attribute):
        return call_name
    if (func.attr == 'search'
            and _resolve_ldap3_unbound_search(tree, call_name)):
        return 'ldap3.Connection.search'
    if (func.attr in _LDAP_INSTANCE_METHODS
            and _constructed_receiver(
                tree, func.value, ldap_names, scope_idx, class_scopes, node,
                'ldap', _LDAP_INITIALIZE_MEMBERS, parent_map,
                assignment_owners)):
        return f'ldap.{func.attr}'
    if func.attr != 'search':
        return call_name
    if _constructed_receiver(
            tree, func.value, ldap3_names, scope_idx, class_scopes, node,
            _LDAP3_MODULE, _LDAP3_CONNECTION_MEMBERS, parent_map,
            assignment_owners):
        return 'ldap3.Connection.search'
    if _constructed_receiver(
            tree, func.value, ldap_names, scope_idx, class_scopes, node,
            'ldap', _LDAP_INITIALIZE_MEMBERS, parent_map, assignment_owners):
        return 'ldap.search'
    return call_name
def scan_ldap_injection(tree: ast.Module, code: str,
                        filepath: str = _DEFAULT_FILEPATH,
                        analyzer: PreciseTaintAnalyzer | None = None,
                        ) -> list[VulnerabilityFinding]:
    analyzer = analyzer or PreciseTaintAnalyzer()
    facts = collect_scope_facts(analyzer, tree)
    resolver = _StarImportCallResolver(tree, CALL_ALIAS_MODULES["ldap"])
    ldap3_names = _constructor_binding_names(
        tree, _LDAP3_MODULE, _LDAP3_CONNECTION_MEMBERS)
    ldap_names = _constructor_binding_names(
        tree, 'ldap', _LDAP_INITIALIZE_MEMBERS)
    parent_map = build_parent_map(tree)
    assignment_owners = _assignment_value_owners(tree)
    return _scan_dynamic_arg_calls(
        tree, code, filepath, _LDAP_DANGER_CALLS,
        lambda node: _resolve_ldap_call(
            tree, node, resolver, ldap3_names, ldap_names,
            facts.scope_idx, facts.class_scopes, parent_map,
            assignment_owners),
        _LDAP_PROFILE, analyzer, facts)
_XXE_PROTECT_KW_VALUES = {
    'resolve_entities': False,
    'forbid_entities': True,
}
_XXE_PARSER_KWNAME = 'parser'
_XXE_PARSER_POSITION = 1
def _xxe_flag_matches(value: Any, expected: bool) -> bool:
    if isinstance(value, bool):
        return value is expected
    if isinstance(value, int):
        return value == (1 if expected else 0)
    return False
def _is_xxe_protect_kw(kw: ast.keyword) -> bool:
    if kw.arg not in _XXE_PROTECT_KW_VALUES:
        return False
    return (isinstance(kw.value, ast.Constant)
            and _xxe_flag_matches(
                kw.value.value, _XXE_PROTECT_KW_VALUES[kw.arg]))
def _is_xxe_parser_constructor(node: ast.AST | None,
                               resolver: ImportCallResolver) -> bool:
    if not isinstance(node, ast.Call):
        return False
    call_name = resolver.resolve(resolve_call_name(node))
    return _xxe_danger_suffix(call_name) in _XXE_PARSER_CONSTRUCTORS
def _xxe_parser_argument(node: ast.Call) -> ast.AST | None:
    for kw in node.keywords:
        if kw.arg == _XXE_PARSER_KWNAME:
            return kw.value
    if len(node.args) > _XXE_PARSER_POSITION:
        return node.args[_XXE_PARSER_POSITION]
    return None
def _xxe_constructor_is_protected(node: ast.AST | None,
                                  resolver: ImportCallResolver) -> bool:
    return (_is_xxe_parser_constructor(node, resolver)
            and any(_is_xxe_protect_kw(kw) for kw in node.keywords))
def _xxe_parser_is_protected(parser: ast.AST | None, tree: ast.Module,
                             node: ast.Call, scope_idx: dict,
                             resolver: ImportCallResolver, parent_map: dict,
                             assignment_owners: dict[int, ast.AST]) -> bool:
    if _is_xxe_parser_constructor(parser, resolver):
        return _xxe_constructor_is_protected(parser, resolver)
    if not isinstance(parser, ast.Name):
        return False
    scope = scope_idx.get(id(node), "")
    assigned = _resolve_name_alias_assignment(
        tree, parser.id, node, scope, scope_idx)
    seen: set[int] = set()
    while assigned is not None and id(assigned) not in seen:
        if not _xxe_constructor_is_protected(assigned, resolver):
            return False
        seen.add(id(assigned))
        stmt = assignment_owners.get(id(assigned))
        if (stmt is None or not _statement_is_conditional(
                tree, stmt, parent_map)):
            return True
        assigned = _resolve_name_alias_assignment(
            tree, parser.id, stmt, scope, scope_idx)
    return False
def _xxe_call_is_protected(tree: ast.Module, node: ast.Call,
                           scope_idx: dict, resolver: ImportCallResolver,
                           parent_map: dict,
                           assignment_owners: dict[int, ast.AST]) -> bool:
    if _is_xxe_parser_constructor(node, resolver):
        return _xxe_constructor_is_protected(node, resolver)
    return _xxe_parser_is_protected(
        _xxe_parser_argument(node), tree, node, scope_idx, resolver,
        parent_map, assignment_owners)
_XXE_MODULE_HEADS = frozenset({"lxml", "xml", "xml.dom", "xml.sax",
                               "xml.etree", "lxml.etree"})
def _xxe_danger_suffix(call_name: str) -> str:
    if call_name in _XXE_DANGER_CALLS:
        return call_name
    parts = call_name.split(".")
    for idx in range(1, len(parts)):
        suffix = ".".join(parts[idx:])
        if (".".join(parts[:idx]) in _XXE_MODULE_HEADS
                and suffix in _XXE_DANGER_CALLS):
            return suffix
    return ""
def _xxe_resolve_call(node: ast.Call,
                      resolver: ImportCallResolver) -> str:
    call_name = resolve_call_name(node)
    if not call_name:
        return ""
    if _xxe_danger_suffix(call_name):
        return call_name
    return resolver.resolve(call_name)
def scan_xxe(tree: ast.Module, code: str,
             filepath: str = _DEFAULT_FILEPATH) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    resolver = _StarImportCallResolver(tree, dict(_XXE_CANONICAL_MODULES))
    scope_idx = build_scope_index(tree)
    parent_map = build_parent_map(tree)
    assignment_owners = _assignment_value_owners(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        call_name = _xxe_resolve_call(node, resolver)
        if not _xxe_danger_suffix(call_name):
            continue
        if _xxe_call_is_protected(
                tree, node, scope_idx, resolver, parent_map,
                assignment_owners):
            continue
        findings.append(build_vulnerability_finding(
            VulnerabilityCategory.XXE,
            code=code,
            filepath=filepath,
            line=node.lineno,
            source="xml_parser",
            sink=call_name,
            severity="HIGH",
            confidence=0.8,
            suggestion="配置 XML 解析器禁用外部实体: resolve_entities=False",
            cwe_id="CWE-611",
        ))
    return findings
_PATTERN_SCANNERS = (
    scan_xss,
    scan_ssti,
    scan_xxe,
    scan_ldap_injection,
    scan_hardcoded_secrets,
)
def scan_pattern_channels(tree: ast.Module, code: str,
                          filepath: str = _DEFAULT_FILEPATH
                          ) -> list[VulnerabilityFinding]:
    findings: list[VulnerabilityFinding] = []
    for scan in _PATTERN_SCANNERS:
        findings.extend(scan(tree, code, filepath))
    return findings

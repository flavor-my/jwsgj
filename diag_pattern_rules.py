from __future__ import annotations

import ast
import bisect
import builtins
import copy
import logging
import os
import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any

from jwsgj.diag_detector_findings import (
    extend_issues,
    normalize_id_set,
    project_pollution_issues,
)
from jwsgj.diag_detectors_registry import run_channel
from jwsgj.diag_guard_injection_enforce import size_gate_issues
from jwsgj.diag_module_surface import static_all_names, static_seq_bindings
from jwsgj.diag_shared_ast_nodes import (
    AST_MATCH_TYPES,
    COMP_SCOPE_NODES,
    TRY_STAR,
    collect_param_names,
    import_alias_bound_names,
    is_dunder_name,
    is_main_check,
    iter_module_level_stmts,
    iter_own_scope,
    iter_params,
    iter_target_bindings,
    module_postpones_annotations,
    parse_ast_safely,
    parse_py_source,
    resolve_call_name,
    split_identifier,
    subtree_node_ids,
)
from jwsgj.diag_shared_ast_views import (
    parent_map,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    byte_col_to_char_col,
    coerce_source_text,
    count_effective_lines,
    extract_code_lines,
    is_consolidated_code,
    is_constant_name,
    leading_quote_states,
    marker_hit,
    scan_line_quote_state,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
    string_token_row_spans,
)
from jwsgj.diag_types_vocab import (
    CAT_MAINTAINABILITY,
    HARD_MAX_FILE_LINES,
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    diag_severity_to_p,
)
from jwsgj.prevention_scope_facts import walk_nodes

_DEFAULT_FILEPATH = ""
_DEFAULT_TREE = None
_DEFAULT_EXCLUDE_RULES = None
_AST_TYPE_ALIAS = getattr(ast, "TypeAlias", ())
__all__ = [
    "FACADE_FILENAMES",
    "AntipatternEngine",
    "DelegationType",
    "PatternLibrary",
    "PatternMatch",
    "PollutionReport",
    "check_D50_facade",
    "check_D51_delegation",
    "check_MP01",
    "check_MP03",
    "check_PF01_pure_forward",
    "detect_assert_security_check",
    "detect_closure_late_binding",
    "detect_global_nonconst",
    "detect_n_plus_one_query",
    "detect_pollution",
    "get_engine",
    "get_pattern_library",
    "pollution_issues",
    "rebuild_antipattern_engine",
    "run_engine_channels",
    "wiring_declarations",
]
logger = logging.getLogger(__name__)
logger.info("diag_pattern_rules 模式与规则投影域已加载: %d 项导出", len(__all__))
class DelegationType(Enum):
    INTERNAL_DELEGATE = auto()
    REGISTRY_LOOKUP = auto()
    FACTORY = auto()
    DEFENSIVE_COPY = auto()
    CROSS_PACKAGE = auto()
    LAZY_INIT = auto()
    TYPE_ADAPTER = auto()
    LOGGING_PROXY = auto()
    VALIDATION_WRAPPER = auto()
    COMPAT_ALIAS = auto()
    SENTINEL = auto()
    CACHE_ACCESS = auto()
    PATH_ADAPTER = auto()
    DICT_DISPATCH = auto()
    SUSPICIOUS = auto()
    UNKNOWN = auto()
FACADE_FILENAMES = frozenset({
    '__init__.py', 'facade.py', '_facade.py', 'bridge.py',
    '_bridge.py', 'adapter.py', '_adapter.py', 'wrapper.py',
    '_wrapper.py', 'reexports.py', '_reexports.py',
    'public_api.py', '_public_api.py',
})
@dataclass(frozen=True)
class _Family:
    category: str
    attr: str
    scanners: tuple[str, ...]
_FAMILIES: dict[str, _Family] = {
    "bugs": _Family("bug", "_bug_patterns", ("_scan_closure_late_binding",)),
    "refactors": _Family("refactor", "_refactor_patterns",
                         ("_scan_global_nonconst",)),
    "performance": _Family("performance", "_perf_patterns",
                           ("_scan_append_loop", "_scan_n_plus_one",
                            "_scan_full_read")),
    "security": _Family("security", "_security_patterns",
                        ("_scan_assert_security",)),
}
_FAMILY_ALIASES: dict[str, str] = {
    **{family: family for family in _FAMILIES},
    **{spec.category: family for family, spec in _FAMILIES.items()},
    **{spec.attr.lstrip("_"): family for family, spec in _FAMILIES.items()},
    "perf": "performance",
}
_FAMILY_SCANNERS: dict[str, tuple[str, ...]] = {
    family: spec.scanners for family, spec in _FAMILIES.items()
}
def _resolve_family(name: Any) -> str | None:
    if not isinstance(name, str):
        return None
    return _FAMILY_ALIASES.get(name.strip().lower())
@dataclass
class PatternMatch:
    pattern_id: str
    pattern_name: str
    category: str
    severity: str
    line: int
    message: str
    fix_suggestion: str
    confidence: float = 0.8
    file: str = _DEFAULT_FILEPATH
    def to_dict(self) -> dict[str, Any]:
        return {
            "rule_id": self.pattern_id,
            "severity": diag_severity_to_p(self.severity),
            "file": self.file,
            "line": self.line,
            "message": self.message,
            "category": self.category,
            "confidence": self.confidence,
            "suggestion": self.fix_suggestion,
            "pattern_name": self.pattern_name,
        }
_BASE_PATTERNS: dict[str, tuple[dict[str, str], ...]] = {
    "bugs": (
        {
            "id": "BUG-018", "name": "闭包晚绑定陷阱",
            "severity": "MEDIUM",
            "description": "lambda 在循环中引用循环变量,执行时使用最终值",
            "fix": "使用默认参数绑定当前值: lambda x=i: ...",
        },
    ),
    "refactors": (
        {
            "id": "REF-012", "name": "global 非常量",
            "severity": "MEDIUM",
            "description": "函数内使用 global 声明非常量变量",
            "fix": "使用返回值或类属性替代 global",
        },
    ),
    "performance": (
        {
            "id": "PERF-003", "name": "列表推导式可优化",
            "severity": "LOW",
            "description": "循环体仅一条 append 调用,可用列表推导式替代显式循环",
            "fix": "使用列表推导式: result = [expr for x in iterable]",
        },
        {
            "id": "PERF-005", "name": "N+1 查询模式",
            "severity": "MEDIUM",
            "description": "循环内执行数据库查询",
            "fix": "使用批量查询或 JOIN 一次性获取",
        },
        {
            "id": "PERF-006", "name": "大文件一次性读取",
            "severity": "LOW",
            "description": "无参数 .read() 全量读取,大文件场景应逐行或分块",
            "fix": "逐行迭代 for line in f 或 f.read(chunk_size) 分块处理",
        },
    ),
    "security": (
        {
            "id": "SEC-008", "name": "assert 用于安全检查",
            "severity": "HIGH",
            "description": "assert 用于权限/安全检查,-O 模式下被移除",
            "fix": "使用显式 if not check: raise SecurityError(...)",
        },
    ),
}
_PATTERN_META: dict[str, dict[str, str]] = {
    pattern["id"]: {
        "name": pattern["name"],
        "severity": pattern["severity"],
        "category": _FAMILIES[family].category,
    }
    for family, patterns in _BASE_PATTERNS.items()
    for pattern in patterns
}
_ASSERT_SECURITY_SEGMENTS = frozenset({
    "permission", "permissions", "permitted",
    "auth", "authn", "authz",
    "authorize", "authorized", "authorization",
    "authenticate", "authenticated", "authentication",
    "authority", "authorities",
    "admin", "admins", "administrator", "administrators",
    "role", "roles",
    "access", "accessed", "accesses",
})
def _expr_security_segments(expr: ast.AST) -> set[str]:
    segs: set[str] = set()
    for node in walk_nodes(expr):
        if isinstance(node, ast.Name):
            segs.update(split_identifier(node.id))
        elif isinstance(node, ast.Attribute):
            segs.update(split_identifier(node.attr))
        elif isinstance(node, ast.Constant) and isinstance(node.value, str):
            segs.update(split_identifier(node.value))
    return segs
_DB_CALL_ATTRS = frozenset({
    "execute", "executemany", "executeMany",
    "query", "fetchone", "fetchall", "fetchmany",
})
_SELF_CLS_NAMES = frozenset({"self", "cls"})
_MP03_EXEMPT_ATTRS = frozenset({"__dict__", "__class__"})
def _comprehension_local_binding(node: ast.AST, func_node: ast.AST,
                                 parents: dict) -> bool:
    cur = parents.get(node)
    while cur is not None and cur is not func_node:
        if isinstance(cur, ast.NamedExpr):
            return False
        if isinstance(cur, COMP_SCOPE_NODES):
            return True
        cur = parents.get(cur)
    return False
def _scope_node_binding_names(node: ast.AST, func_node: ast.AST,
                                parents: dict) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.alias):
        return {node.asname or node.name.split(".")[0]}
    if (isinstance(node, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar))
            and node.name):
        return {node.name}
    if isinstance(node, ast.MatchMapping) and node.rest:
        return {node.rest}
    if (isinstance(node, ast.Name)
            and isinstance(node.ctx, (ast.Store, ast.Del))
            and not _comprehension_local_binding(node, func_node, parents)):
        return {node.id}
    return set()
def _iter_outer_scope_nodes(roots):
    queue = list(roots)
    head = 0
    while head < len(queue):
        child = queue[head]
        head += 1
        yield child
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            children = _definition_time_children(
                child, annotations_deferred=True)
        elif isinstance(child, ast.ClassDef):
            children = [*child.decorator_list, *child.bases, *child.keywords]
        else:
            children = None
        queue.extend(
            ast.iter_child_nodes(child) if children is None else children)
def _func_local_names(func_node: ast.AST, parents: dict) -> set[str]:
    names: set[str] = set(collect_param_names(func_node))
    declared: set[str] = set()
    for node in _iter_outer_scope_nodes(func_node.body):
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            declared.update(node.names)
            continue
        names.update(_scope_node_binding_names(node, func_node, parents))
    return names - declared
def _func_global_names(func_node: ast.AST) -> set[str]:
    return {
        name
        for node in iter_own_scope(func_node, skip_lambda=True)
        if isinstance(node, ast.Global)
        for name in node.names
    }
def _loop_uses_module_binding(scope_node: ast.AST, parents: dict,
                              loop_var: str) -> bool:
    if not isinstance(scope_node, (ast.For, ast.AsyncFor, ast.While)):
        return False
    cur = parents.get(scope_node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return loop_var in _func_global_names(cur)
        if isinstance(cur, (ast.Lambda, ast.ClassDef, *COMP_SCOPE_NODES)):
            return False
        cur = parents.get(cur)
    return True
def _loop_uses_class_binding(scope_node: ast.AST, parents: dict) -> bool:
    if not isinstance(scope_node, (ast.For, ast.AsyncFor, ast.While)):
        return False
    cur = parents.get(scope_node)
    while cur is not None:
        if isinstance(cur, ast.ClassDef):
            return True
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, *COMP_SCOPE_NODES)):
            return False
        cur = parents.get(cur)
    return False
def _enclosing_scope_shadows(anc: ast.AST, loop_var: str,
                             parents: dict, loop_uses_module: bool) -> bool:
    if isinstance(anc, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return (loop_var in _func_local_names(anc, parents)
                or (not loop_uses_module
                    and loop_var in _func_global_names(anc)))
    if isinstance(anc, ast.Lambda):
        return (loop_var in collect_param_names(anc)
                or _lambda_binds_walrus(anc, loop_var))
    return False
def _shadowed_by_enclosing_def(lam: ast.Lambda, scope_node: ast.AST,
                               loop_var: str, parents: dict) -> bool:
    loop_uses_module = _loop_uses_module_binding(
        scope_node, parents, loop_var)
    cur = parents.get(lam)
    while cur is not None and cur is not scope_node:
        if _enclosing_scope_shadows(
                cur, loop_var, parents, loop_uses_module):
            return True
        cur = parents.get(cur)
    return False
def _lambda_binds_walrus(lam: ast.Lambda, var: str) -> bool:
    stack: list[ast.AST] = [lam.body]
    while stack:
        n = stack.pop()
        if isinstance(n, ast.Lambda):
            stack.extend(n.args.defaults)
            stack.extend(d for d in n.args.kw_defaults if d is not None)
            continue
        if (isinstance(n, ast.NamedExpr)
                and isinstance(n.target, ast.Name)
                and n.target.id == var):
            return True
        stack.extend(ast.iter_child_nodes(n))
    return False
def _lambda_body_refs_var(lam: ast.Lambda, var: str) -> bool:
    stack = [lam.body]
    while stack:
        n = stack.pop()
        if (isinstance(n, ast.Name) and n.id == var
                and isinstance(n.ctx, ast.Load)):
            return True
        if isinstance(n, ast.Lambda):
            stack.extend(n.args.defaults)
            stack.extend(d for d in n.args.kw_defaults if d is not None)
            if (var in collect_param_names(n)
                    or _lambda_binds_walrus(n, var)):
                continue
            stack.append(n.body)
            continue
        if isinstance(n, COMP_SCOPE_NODES):
            stack.extend(_comprehension_shadow_roots(n, var))
            continue
        stack.extend(ast.iter_child_nodes(n))
    return False
def _comprehension_shadow_roots(node: ast.AST, var: str) -> tuple:
    if not node.generators:
        return ()
    roots: list[ast.AST] = []
    shadowed = False
    for gen in node.generators:
        roots.append(gen.iter)
        if any(name == var
               for name, _line, _col in iter_target_bindings(gen.target)):
            shadowed = True
            break
        roots.extend(gen.ifs)
    if shadowed:
        return tuple(roots)
    roots.extend(ast.iter_child_nodes(node))
    return tuple(roots)
def _immediate_lambda_body(call: ast.AST) -> ast.AST | None:
    if not isinstance(call, ast.Call):
        return None
    func = call.func
    if isinstance(func, ast.Lambda):
        return func.body
    if (isinstance(func, ast.Attribute) and func.attr == "__call__"
            and isinstance(func.value, ast.Lambda)):
        return func.value.body
    return None
def _lambda_is_immediately_invoked(lam: ast.Lambda, parents: dict) -> bool:
    parent = parents.get(lam)
    if isinstance(parent, ast.Call):
        return _immediate_lambda_body(parent) is lam.body
    if isinstance(parent, ast.Attribute) and parent.value is lam:
        call = parents.get(parent)
        return (isinstance(call, ast.Call)
                and _immediate_lambda_body(call) is lam.body)
    return False
_SYNCHRONOUS_KEY_BUILTINS = frozenset({'sorted', 'min', 'max'})
def _lambda_consumed_in_place(lam: ast.Lambda, parents: dict) -> bool:
    """lambda 是否在当前迭代内被同步消费完毕（不会逃逸到后续迭代）。

    两种形态与 IIFE 同属「创建即消费」：
    - 作为 ``sorted/min/max`` 的 ``key=`` 实参：内置在调用期间逐元素
      同步调用 key，调用返回前 lambda 已用完，不存在延后执行面；
    - 作为 ``for`` 头部 ``iter(callable, sentinel)`` 的 callable：迭代器
      由该 for 语句就地驱动，lambda 在本次外层迭代内被调用。
    """
    parent = parents.get(lam)
    if isinstance(parent, ast.keyword) and parent.arg == 'key':
        call = parents.get(parent)
        return (isinstance(call, ast.Call)
                and isinstance(call.func, ast.Name)
                and call.func.id in _SYNCHRONOUS_KEY_BUILTINS)
    if (isinstance(parent, ast.Call)
            and isinstance(parent.func, ast.Name)
            and parent.func.id == 'iter'
            and len(parent.args) == 2
            and parent.args[0] is lam):
        owner = parents.get(parent)
        return isinstance(owner, ast.For) and owner.iter is parent
    return False
def _lambda_captures_loop_var(lam: ast.Lambda, scope_node: ast.AST,
                               loop_var: str, parents: dict) -> bool:
    if loop_var in collect_param_names(lam):
        return False
    if _lambda_binds_walrus(lam, loop_var):
        return False
    if _shadowed_by_enclosing_def(lam, scope_node, loop_var, parents):
        return False
    return _lambda_body_refs_var(lam, loop_var)
def _loop_binding_roots(node: ast.AST) -> tuple[ast.AST, ...]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return (node.target, *node.body)
    if isinstance(node, ast.While):
        return (node.test, *node.body)
    if isinstance(node, COMP_SCOPE_NODES):
        return (node,)
    return ()
def _loop_binding_names(node: ast.AST, parents: dict) -> list[str]:
    names: list[str] = []
    seen: set[str] = set()
    for child in _iter_outer_scope_nodes(_loop_binding_roots(node)):
        for name in _scope_node_binding_names(child, node, parents):
            if name not in seen:
                seen.add(name)
                names.append(name)
    return names
def _collect_loop_scopes(tree: ast.Module,
                         parents: dict) -> list[tuple[ast.AST, str]]:
    loop_scopes: list[tuple[ast.AST, str]] = []
    for node in tree_nodes(tree):
        if (isinstance(node, (ast.For, ast.AsyncFor, ast.While,
                              *COMP_SCOPE_NODES))
                and not _loop_uses_class_binding(node, parents)):
            loop_scopes.extend(
                (node, name) for name in _loop_binding_names(node, parents))
    return loop_scopes
def _loop_excluded_ids(node: ast.AST) -> set[int] | None:
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        exclude_roots: list[ast.AST] = list(node.orelse)
        if isinstance(node, (ast.For, ast.AsyncFor)):
            exclude_roots.append(node.iter)
    elif isinstance(node, COMP_SCOPE_NODES):
        exclude_roots = [node.generators[0].iter] if node.generators else []
    else:
        return None
    return subtree_node_ids(exclude_roots)
def _late_binding_excluded_ids(node: ast.AST) -> set[int]:
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        excluded_roots = list(node.orelse)
        if isinstance(node, (ast.For, ast.AsyncFor)):
            excluded_roots.append(node.iter)
        return subtree_node_ids(excluded_roots)
    if isinstance(node, COMP_SCOPE_NODES) and node.generators:
        return subtree_node_ids([node.generators[0].iter])
    return set()
def _definition_time_children(node: ast.AST,
                              annotations_deferred: bool = False):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        children = [*node.decorator_list, *node.args.defaults]
        children.extend(d for d in node.args.kw_defaults if d is not None)
        if not annotations_deferred:
            children.extend(
                arg.annotation for arg in iter_params(node.args)
                if arg.annotation is not None)
            if node.returns is not None:
                children.append(node.returns)
        return children
    if isinstance(node, ast.Lambda):
        children = list(node.args.defaults)
        children.extend(d for d in node.args.kw_defaults if d is not None)
        return children
    if isinstance(node, ast.ClassDef):
        return [*node.decorator_list, *node.bases, *node.keywords, *node.body]
    if isinstance(node, _AST_TYPE_ALIAS):
        return ()
    if isinstance(node, ast.AnnAssign) and annotations_deferred:
        children = [node.target]
        if node.value is not None:
            children.append(node.value)
        return children
    return None
def _locally_unexecuted_generator_ids(node: ast.AST) -> set[int]:
    parents = parent_map(node)
    loaded_names = {
        child.id for child in walk_nodes(node)
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load)
    }
    deferred: set[int] = set()
    for child in walk_nodes(node):
        if not isinstance(child, ast.GeneratorExp):
            continue
        parent = parents.get(child)
        if isinstance(parent, ast.Expr):
            deferred.add(id(child))
            continue
        targets: list[ast.AST] = []
        if isinstance(parent, ast.Assign):
            targets = list(parent.targets)
        elif isinstance(parent, (ast.AnnAssign, ast.NamedExpr)):
            targets = [parent.target]
        if (targets and all(isinstance(target, ast.Name) for target in targets)
                and all(target.id not in loaded_names for target in targets)):
            deferred.add(id(child))
    return deferred
def _iter_db_calls_in_loop(node: ast.AST, excluded_ids: set[int],
                           annotations_deferred: bool = False):
    deferred_generator_ids = _locally_unexecuted_generator_ids(node)
    queue = list(ast.iter_child_nodes(node))
    head = 0
    while head < len(queue):
        child = queue[head]
        head += 1
        if id(child) in excluded_ids:
            continue
        if (isinstance(child, ast.Call)
                and isinstance(child.func, ast.Attribute)
                and child.func.attr in _DB_CALL_ATTRS):
            yield child
        immediate_body = _immediate_lambda_body(child)
        if immediate_body is not None:
            queue.append(immediate_body)
        if id(child) in deferred_generator_ids:
            definition_time = ([child.generators[0].iter]
                               if child.generators else [])
        else:
            definition_time = _definition_time_children(
                child, annotations_deferred)
        queue.extend(
            ast.iter_child_nodes(child) if definition_time is None
            else definition_time)
def _match(pattern_id: str, line: int, filepath: str, confidence: float,
          *, message: str, fix_suggestion: str) -> PatternMatch:
    meta = _PATTERN_META[pattern_id]
    return PatternMatch(
        pattern_id=pattern_id,
        pattern_name=meta["name"],
        category=meta["category"],
        severity=meta["severity"],
        line=line,
        message=message,
        fix_suggestion=fix_suggestion,
        confidence=confidence,
        file=filepath,
    )
def _is_unbounded_read_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if not (isinstance(node.func, ast.Attribute) and node.func.attr == "read"):
        return False
    return not (node.args or node.keywords)
def _single_append_call(body: list[ast.stmt]) -> ast.Call | None:
    if len(body) != 1:
        return None
    stmt = body[0]
    if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)):
        return None
    call = stmt.value
    if not (isinstance(call.func, ast.Attribute) and call.func.attr == "append"):
        return None
    return call if isinstance(call.func.value, ast.Name) else None
def _parse_family_tree(code: Any) -> ast.Module | None:
    if not isinstance(code, (str, bytes, bytearray)):
        return None
    text = coerce_source_text(code)
    if not text:
        return None
    return parse_py_source(text)
class PatternLibrary:
    def __init__(self) -> None:
        self._bug_patterns: list[dict] = list(_BASE_PATTERNS["bugs"])
        self._refactor_patterns: list[dict] = list(_BASE_PATTERNS["refactors"])
        self._perf_patterns: list[dict] = list(_BASE_PATTERNS["performance"])
        self._security_patterns: list[dict] = list(_BASE_PATTERNS["security"])
    @property
    def stats(self) -> dict[str, int]:
        counts = {family: len(getattr(self, spec.attr))
                  for family, spec in _FAMILIES.items()}
        counts["total"] = sum(counts.values())
        return counts
    def pattern_count(self, category: str = "") -> int:
        if not category:
            return self.stats["total"]
        family = _resolve_family(category)
        if family is None:
            return 0
        return len(getattr(self, _FAMILIES[family].attr))
    def _run_scanners(self, tree: ast.Module, filepath: str,
                      scanner_names: tuple) -> list[PatternMatch]:
        return [match for name in scanner_names
                for match in getattr(self, name)(tree, filepath)]
    def _scan_family(self, code: str, filepath: str,
                     scanner_names: tuple) -> list[PatternMatch]:
        tree = _parse_family_tree(code)
        if tree is None:
            return []
        return self._run_scanners(tree, filepath, scanner_names)
    def scan_bugs(self, code: str, filepath: str = _DEFAULT_FILEPATH) -> list[PatternMatch]:
        return self._scan_family(code, filepath, _FAMILY_SCANNERS["bugs"])
    def scan_refactors(self, code: str, filepath: str = _DEFAULT_FILEPATH) -> list[PatternMatch]:
        return self._scan_family(code, filepath, _FAMILY_SCANNERS["refactors"])
    def scan_performance(self, code: str, filepath: str = _DEFAULT_FILEPATH) -> list[PatternMatch]:
        return self._scan_family(code, filepath, _FAMILY_SCANNERS["performance"])
    def scan_security(self, code: str, filepath: str = _DEFAULT_FILEPATH) -> list[PatternMatch]:
        return self._scan_family(code, filepath, _FAMILY_SCANNERS["security"])
    def scan_all(self, code: str, filepath: str = _DEFAULT_FILEPATH) -> dict[str, list[PatternMatch]]:
        tree = _parse_family_tree(code)
        if tree is None:
            return {family: [] for family in _FAMILY_SCANNERS}
        return {family: self._run_scanners(tree, filepath, names)
                for family, names in _FAMILY_SCANNERS.items()}
    def _scan_closure_late_binding(
            self, tree: ast.Module, filepath: str) -> list[PatternMatch]:
        _parents = parent_map(tree)
        loop_scopes = _collect_loop_scopes(tree, _parents)
        if not loop_scopes:
            return []
        matches: list[PatternMatch] = []
        reported: set[tuple[int, str]] = set()
        for scope_node, loop_var in loop_scopes:
            matches.extend(self._report_late_binding_in_scope(
                scope_node, loop_var, _parents, reported, filepath))
        return matches
    def _report_late_binding_in_scope(
            self, scope_node: ast.AST, loop_var: str,
            parents: dict, reported: set[tuple[int, str]],
            filepath: str) -> list[PatternMatch]:
        found: list[PatternMatch] = []
        excluded_ids = _late_binding_excluded_ids(scope_node)
        pending = [scope_node]
        head = 0
        while head < len(pending):
            child = pending[head]
            head += 1
            if id(child) in excluded_ids:
                continue
            if (isinstance(child, ast.Lambda)
                    and not (_lambda_is_immediately_invoked(child, parents)
                             or _lambda_consumed_in_place(child, parents))
                    and _lambda_captures_loop_var(
                        child, scope_node, loop_var, parents)):
                _ln = getattr(child, "lineno", 0)
                if (_ln, loop_var) not in reported:
                    reported.add((_ln, loop_var))
                    found.append(_match(
                        "BUG-018", _ln, filepath, 0.85,
                        message=(f"lambda 引用循环变量 '{loop_var}',"
                                 "执行时使用最终值"),
                        fix_suggestion=(f"使用默认参数绑定: lambda "
                                        f"{loop_var}={loop_var}: ...")))
            pending.extend(ast.iter_child_nodes(child))
        return found
    def _scan_global_nonconst(
            self, tree: ast.Module, filepath: str) -> list[PatternMatch]:
        matches: list[PatternMatch] = []
        for node in tree_nodes(tree):
            if not isinstance(node, ast.Global):
                continue
            for name in node.names:
                if not is_constant_name(name.lstrip("_")):
                    matches.append(_match(
                        "REF-012", node.lineno, filepath, 0.75,
                        message=f"global 声明非常量变量 '{name}'",
                        fix_suggestion="使用返回值或类属性替代 global"))
        return matches
    def _scan_n_plus_one(self, tree: ast.Module, filepath: str) -> list[PatternMatch]:
        matches: list[PatternMatch] = []
        reported: set[int] = set()
        annotations_deferred = module_postpones_annotations(tree)
        nodes = list(tree_nodes(tree))
        deferred_generator_ids = {
            generator_id
            for scope in nodes
            if isinstance(scope, (ast.For, ast.AsyncFor, ast.While))
            for generator_id in _locally_unexecuted_generator_ids(scope)
        }
        for node in nodes:
            if id(node) in deferred_generator_ids:
                continue
            excluded_ids = _loop_excluded_ids(node)
            if excluded_ids is None:
                continue
            ordered_calls = sorted(
                _iter_db_calls_in_loop(
                    node, excluded_ids, annotations_deferred),
                key=lambda call: (
                    getattr(call, "lineno", 0),
                    getattr(call, "col_offset", 0)))
            for child in ordered_calls:
                call_line = getattr(child, "lineno", 0)
                if call_line in reported:
                    continue
                reported.add(call_line)
                matches.append(_match(
                    "PERF-005", call_line, filepath, 0.6,
                    message=f"循环内调用 '{child.func.attr}()'"
                            f"(疑似 N+1 查询),建议批量获取",
                    fix_suggestion="使用批量查询或 JOIN 一次性获取"))
                break
        return matches
    def _scan_append_loop(self, tree: ast.Module, filepath: str) -> list[PatternMatch]:
        matches: list[PatternMatch] = []
        for node in tree_nodes(tree):
            if not isinstance(node, (ast.For, ast.AsyncFor)):
                continue
            if node.orelse or _single_append_call(node.body) is None:
                continue
            is_async = isinstance(node, ast.AsyncFor)
            comprehension = "异步列表推导式" if is_async else "列表推导式"
            iteration = "async for" if is_async else "for"
            matches.append(_match(
                "PERF-003", getattr(node, "lineno", 0), filepath, 0.6,
                message=f"循环体仅一条 append 调用,可用{comprehension}替代显式循环",
                fix_suggestion=f"改写为{comprehension}: "
                               f"result = [expr {iteration} x in iterable]。"
                               "若循环体内含多条语句或依赖顺序副作用,"
                               "保持现状不改。"))
        return matches
    def _scan_full_read(self, tree: ast.Module, filepath: str) -> list[PatternMatch]:
        matches: list[PatternMatch] = []
        for node in tree_nodes(tree):
            if not _is_unbounded_read_call(node):
                continue
            matches.append(_match(
                "PERF-006", getattr(node, "lineno", 0), filepath, 0.4,
                message="无参数 .read() 全量读取;若文件较大建议逐行/分块处理",
                fix_suggestion="大文件场景改用逐行迭代 for line in f: 或 "
                               "f.read(chunk_size) 分块处理；小文件或 "
                               "StringIO/响应流等合法全量读取可忽略。"))
        return matches
    def _scan_assert_security(
            self, tree: ast.Module, filepath: str) -> list[PatternMatch]:
        matches: list[PatternMatch] = []
        for node in tree_nodes(tree):
            if not isinstance(node, ast.Assert):
                continue
            if _expr_security_segments(node.test) & _ASSERT_SECURITY_SEGMENTS:
                matches.append(_match(
                    "SEC-008", node.lineno, filepath, 0.6,
                    message="assert 用于权限/安全检查,-O 模式下被移除",
                    fix_suggestion="使用显式 if not check: "
                                   "raise SecurityError(...)"))
        return matches
_pattern_library: PatternLibrary | None = None
def get_pattern_library() -> PatternLibrary:
    global _pattern_library
    if _pattern_library is None:
        _pattern_library = PatternLibrary()
    return _pattern_library
def _make_pattern_detector(detector_name: str, method_name: str, doc: str):
    def _detect(
        source_code: str = "",
        tree: ast.Module | None = _DEFAULT_TREE,
        filepath: str = _DEFAULT_FILEPATH,
        **_kwargs: Any,
    ) -> list[dict[str, Any]]:
        if tree is None:
            text = coerce_source_text(source_code)
            if not text:
                return []
            tree = parse_py_source(text)
            if tree is None:
                return []
        lib = get_pattern_library()
        scanner = getattr(lib, method_name)
        return [m.to_dict() for m in scanner(tree, filepath)]
    _detect.__doc__ = doc
    _detect.__name__ = detector_name
    _detect.__qualname__ = detector_name
    return _detect
detect_closure_late_binding = _make_pattern_detector(
    "detect_closure_late_binding", "_scan_closure_late_binding",
    "PL-01: 闭包晚绑定陷阱检测器（注册表通道，BUG-018）。")
detect_assert_security_check = _make_pattern_detector(
    "detect_assert_security_check", "_scan_assert_security",
    "PL-02: assert 安全检查检测器（注册表通道，SEC-008）。")
detect_global_nonconst = _make_pattern_detector(
    "detect_global_nonconst", "_scan_global_nonconst",
    "PL-03: global 非常量检测器（注册表通道，REF-012）。")
detect_n_plus_one_query = _make_pattern_detector(
    "detect_n_plus_one_query", "_scan_n_plus_one",
    "PL-04: N+1 查询模式检测器（注册表通道，PERF-005）。")
_FILE_LINE_LIMIT = int(HARD_MAX_FILE_LINES)
_MAX_NONCRITICAL_WARNINGS = 8
_MAX_CRITICAL_FULL = 5
_SEVERITY_WEIGHTS = {"CRITICAL": 4, "HIGH": 3, "MEDIUM": 2, "LOW": 1}
_TASK_KEYWORDS = {
    "script": ["脚本", "script", "自动化", "batch"],
    "refactor": ["重构", "refactor", "拆分", "合并"],
    "review": ["审查", "review", "诊断", "diag"],
    "cleanup": ["清理", "cleanup", "删除", "delete"],
    "merge": ["merge", "整合"],
    "fix": ["修复", "fix", "bug", "错误"],
    "security": ["安全", "security", "漏洞", "vulnerability"],
    "performance": ["性能", "performance", "优化", "optimize"],
}
_DOMAIN_FIRST_TASK_TYPES = ("security",)
def _normalize_exclude_rules(exclude_rules: Any) -> frozenset[str] | None:
    normalized = normalize_id_set(exclude_rules)
    return frozenset(normalized) or None
def _is_excluded(rule_id: str, exclude_rules: Any) -> bool:
    if not exclude_rules:
        return False
    return bool(normalize_id_set((rule_id,)) & set(exclude_rules))
def _channel_exclude_set(exclude_rules: Any,
                         canonical_ids: tuple[str, ...]) -> Any:
    if not exclude_rules:
        return exclude_rules
    missing = {rid for rid in canonical_ids
               if rid not in exclude_rules
               and _is_excluded(rid, exclude_rules)}
    return frozenset(set(exclude_rules) | missing) if missing else exclude_rules
class AntipatternEngine:
    def __init__(self) -> None:
        self._rules: list[dict[str, Any]] = []
        self._load_rules()
    def _load_rules(self) -> None:
        if self._rules:
            return
        self._rules = [
            {"id": "A1", "category": "A", "severity": "CRITICAL",
             "title": "禁止 bare except", "description": "except 不指定异常类型会捕获所有异常包括 SystemExit"},
            {"id": "A2", "category": "A", "severity": "CRITICAL",
             "title": "禁止 eval/exec", "description": "eval/exec 存在代码注入风险"},
            {"id": "A3", "category": "A", "severity": "HIGH",
             "title": "禁止 os.system", "description": "os.system 存在命令注入风险，用 subprocess.run"},
            {"id": "A8", "category": "A", "severity": "CRITICAL",
             "title": "修改前备份", "description": "代码修改前必须创建备份"},
            {"id": "A9", "category": "A", "severity": "CRITICAL",
             "title": "验证后交付", "description": "修改后必须验证语法和导入"},
            {"id": "B1", "category": "B", "severity": "HIGH",
             "title": "禁止直接 sqlite3 裸写", "description": "数据库操作必须使用安全接口"},
            {"id": "C1", "category": "C", "severity": "HIGH",
             "title": "函数不超过300行", "description": "过长函数应拆分"},
            {"id": "C2", "category": "C", "severity": "MEDIUM",
             "title": f"文件不超过{_FILE_LINE_LIMIT}行",
             "description": "过大文件应拆分"},
            {"id": "P1", "category": "P", "severity": "CRITICAL",
             "title": "修复后清理 __pycache__", "description": "pyc 缓存会掩盖修复是否生效"},
            {"id": "P2", "category": "P", "severity": "HIGH",
             "title": "编译验证不等于运行验证", "description": "py_compile 仅验证语法不等于运行验证"},
        ]
    def _classify_task(self, user_msg: str) -> str:
        msg_lower = user_msg.lower()
        ordered = tuple(dict.fromkeys(
            (*_DOMAIN_FIRST_TASK_TYPES, *_TASK_KEYWORDS)))
        for task_type in ordered:
            if any(kw in msg_lower for kw in _TASK_KEYWORDS[task_type]):
                return task_type
        return "general"
    def get_warnings(self, user_msg: str) -> dict:
        if not isinstance(user_msg, str):
            user_msg = ""
        task_type = self._classify_task(user_msg)
        final_warnings = _select_warnings(self._rules, task_type)
        return {
            "report_section": _format_warning_section(final_warnings),
            "task_type": task_type,
            "warnings": final_warnings,
        }
    def detect(self, code: Any, tree: Any = _DEFAULT_TREE,
               exclude_rules: Any = _DEFAULT_EXCLUDE_RULES) -> list[dict[str, Any]]:
        text, node, parse_error = _coerce_channel_input(code, tree)
        _excl = _normalize_exclude_rules(exclude_rules)
        _skip_a1 = _is_excluded("A1", _excl)
        _skip_a2 = _is_excluded("A2", _excl)
        _skip_c2 = _is_excluded("C2", _excl)
        if parse_error is not None:
            return [{"rule_id": "SYNTAX", "severity": "CRITICAL",
                     "message": "代码存在语法错误", "line": 0}]
        if node is None:
            return []
        issues = _detect_a1_a2(
            node, _skip_a1, _skip_a2, parse_suppressions(text))
        issues.extend(_check_file_length_issue(text, _skip_c2))
        return issues
def _select_warnings(rules: list[dict], task_type: str) -> list[dict]:
    relevant = [r for r in rules if _is_rule_relevant(r, task_type)]
    relevant.sort(key=lambda r: -_SEVERITY_WEIGHTS.get(r["severity"], 0))
    critical = [
        r for r in relevant if r["severity"] == "CRITICAL"
    ][:_MAX_CRITICAL_FULL]
    others = [
        r for r in relevant if r["severity"] != "CRITICAL"
    ][:_MAX_NONCRITICAL_WARNINGS]
    return critical + others
def _is_rule_relevant(rule: dict, task_type: str) -> bool:
    return (rule["category"] in ("A", "P")
            or (task_type == "security" and rule["category"] == "B")
            or (task_type == "refactor" and rule["category"] == "C"))
def _format_warning_section(final_warnings: list) -> str:
    lines = []
    if final_warnings:
        lines.append("### 反模式预警\n")
        for w in final_warnings:
            lines.append(f"- **[{w['id']}]** {w['title']}: {w['description']}")
        lines.append("")
    return "\n".join(lines)
def _parse_ast(code: str) -> tuple[ast.AST | None, Exception | None]:
    text = coerce_source_text(code)
    if text is None:
        return None, None
    return parse_ast_safely(text)
_EVAL_EXEC_CALL_NAMES = frozenset({
    'eval', 'exec', 'builtins.eval', 'builtins.exec'})
def _is_a2_suppressed(node: ast.Call, suppressions) -> bool:
    return (is_suppressed(suppressions, node.lineno, 'A2')
            or is_suppressed(suppressions, node.lineno, 'code_execution'))
def _is_eval_exec_call(node, suppressions) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    call_name = resolve_call_name(node)
    if call_name not in _EVAL_EXEC_CALL_NAMES:
        return None
    if _is_a2_suppressed(node, suppressions):
        return None
    return call_name
def _is_a1_suppressed(node: ast.ExceptHandler, suppressions) -> bool:
    return (is_suppressed(suppressions, node.lineno, 'A1')
            or is_suppressed(suppressions, node.lineno, 'broad_except'))
def _detect_a1_a2(tree, skip_a1: bool, skip_a2: bool,
                  suppressions) -> list:
    issues: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.ExceptHandler):
            if (node.type is None and not skip_a1
                    and not _is_a1_suppressed(node, suppressions)):
                issues.append({"rule_id": "A1", "severity": "CRITICAL",
                               "message": "bare except: 必须指定异常类型",
                               "line": node.lineno,
                               "rule_family": "broad_except"})
            continue
        if skip_a2:
            continue
        call_name = _is_eval_exec_call(node, suppressions)
        if call_name is None:
            continue
        issues.append({"rule_id": "A2", "severity": "CRITICAL",
                       "message": f"禁止使用 {call_name}()，存在代码注入风险",
                       "line": node.lineno})
    return issues
def _check_file_length_issue(
    code: str, skip_c2: bool
) -> list[dict[str, Any]]:
    effective_lines = count_effective_lines(ast_split_lines(code))
    if (not skip_c2 and effective_lines > _FILE_LINE_LIMIT
            and not is_consolidated_code(code)):
        return [{"rule_id": "C2", "severity": "P3",
                 "message": (f"文件过长 ({effective_lines} 有效行 > "
                             f"{_FILE_LINE_LIMIT} 行限制)"),
                 "line": 1}]
    return []
_engine_instance = AntipatternEngine()
def get_engine() -> AntipatternEngine:
    return _engine_instance
def rebuild_antipattern_engine() -> AntipatternEngine:
    global _engine_instance
    _engine_instance = AntipatternEngine()
    return _engine_instance
def _channel_source_text(code: Any) -> str:
    if isinstance(code, (str, bytes, bytearray)):
        return coerce_source_text(code) or ""
    if (isinstance(code, (list, tuple))
            and all(isinstance(line, str) for line in code)):
        return coerce_source_text(code) or ""
    return ""
def _coerce_channel_input(
        code: Any, tree: Any
) -> tuple[str, ast.AST | None, Exception | None]:
    node = tree if isinstance(tree, ast.AST) else None
    text = _channel_source_text(code)
    if node is None and not text and isinstance(code, ast.AST):
        node = code
    parse_error: Exception | None = None
    if node is None and text:
        node, parse_error = parse_ast_safely(text)
    return text, node, parse_error
def run_engine_channels(code: Any, tree: Any = _DEFAULT_TREE, source_lines: Any = None,
                        filepath: str = _DEFAULT_FILEPATH, exclude_rules: Any = _DEFAULT_EXCLUDE_RULES) -> list:
    _excl = _normalize_exclude_rules(exclude_rules)
    text, node, _ = _coerce_channel_input(code, tree)
    issues: list = []
    extend_issues(issues, run_channel(
        __name__, "size_gate_issues", size_gate_issues, text, tree=node,
        exclude_rules=_channel_exclude_set(_excl, ("SZ-01",)),
        filepath=filepath), filepath)
    extend_issues(issues, run_channel(
        __name__, "AntipatternEngine.detect",
        lambda: get_engine().detect(text, tree=node,
                                    exclude_rules=_excl)), filepath)
    extend_issues(issues, run_channel(
        __name__, "pollution_issues", pollution_issues, text, tree=node,
        exclude_rules=_excl), filepath)
    return issues
_MP01_SAFE_METACLASSES = frozenset({
    'ABCMeta', 'EnumMeta', 'EnumType', 'ProtocolMeta', 'type',
})
def _mp01_metaclass_name(keyword: ast.keyword) -> str | None:
    if isinstance(keyword.value, ast.Name):
        return keyword.value.id
    if isinstance(keyword.value, ast.Attribute):
        return keyword.value.attr
    return None
def _mp01_risky_metaclasses(node: ast.ClassDef) -> list[str]:
    names: list[str] = []
    for keyword in node.keywords:
        if keyword.arg != 'metaclass':
            continue
        mc_name = _mp01_metaclass_name(keyword)
        if mc_name is not None and mc_name not in _MP01_SAFE_METACLASSES:
            names.append(mc_name)
    return names
def _mp01_finding(node: ast.ClassDef, mc_name: str, source: Any,
                  filepath: Any) -> dict:
    return {
        "rule_id": "MP-01", "severity": "P2",
        "dimension": "metaprogramming_safety",
        "file": filepath, "line": node.lineno,
        "title": f"自定义 metaclass: {mc_name}",
        "description": (
            f"类 {node.name} 使用自定义 metaclass {mc_name}, "
            "可能导致实例化行为不可预测、调试困难."
        ),
        "code_snippet": extract_code_lines(source, node.lineno),
        "suggestion": _mp_suggest(
            "确认 metaclass 必要性, 优先使用 __init_subclass__ 替代."),
        "rule_ref": "mp-custom-metaclass",
    }
def _mp_suggest(fix_strategy: str) -> str:
    return ("根因: 代码使用了不规范或有风险的实现方式。该问题属于元编程类别。\n"
            f"修复策略: {fix_strategy}\n"
            "参考标准: PEP 8 / metaclass / descriptor")
def check_MP01(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if not isinstance(tree, ast.AST):
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        for mc_name in _mp01_risky_metaclasses(node):
            issues.append(_mp01_finding(node, mc_name, source, filepath))
    return issues
def _mp03_branch_children(nodes, path):
    return [(child, path) for child in nodes]
def _mp03_comprehension_children(cur, path):
    generators = cur.generators
    if not generators:
        return _mp03_branch_children(ast.iter_child_nodes(cur), path)
    children = [(generators[0].iter, path)]
    branch = path + ((id(cur), 'comp', cur.lineno, cur.col_offset),)
    children.extend(_mp03_branch_children(
        (generators[0].target, *generators[0].ifs), branch))
    current = branch
    for generator in generators[1:]:
        children.append((generator.iter, current))
        current = current + ((id(generator), 'comp_gen'),)
        children.extend(_mp03_branch_children(
            (generator.target, *generator.ifs), current))
    values = ((cur.key, cur.value) if isinstance(cur, ast.DictComp)
              else (cur.elt,))
    children.extend(_mp03_branch_children(values, current))
    return children
def _mp03_frame_children(cur, path, annotations_deferred):
    if isinstance(cur, ast.Call):
        children = _mp03_branch_children(ast.iter_child_nodes(cur), path)
        immediate_body = _immediate_lambda_body(cur)
        if immediate_body is not None:
            children.extend(_mp03_branch_children((immediate_body,), path))
        return children
    if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        children = _definition_time_children(cur, annotations_deferred)
        return _mp03_branch_children(children or (), path)
    if isinstance(cur, ast.ClassDef):
        return (_mp03_branch_children(cur.decorator_list, path)
                + _mp03_branch_children(cur.bases, path)
                + _mp03_branch_children(cur.keywords, path)
                + _mp03_branch_children(cur.body, path))
    if isinstance(cur, COMP_SCOPE_NODES):
        return _mp03_comprehension_children(cur, path)
    if isinstance(cur, ast.If):
        return ([(cur.test, path)]
                + _mp03_branch_children(
                    cur.body, path + ((id(cur), 'if_body'),))
                + _mp03_branch_children(
                    cur.orelse, path + ((id(cur), 'if_else'),)))
    if isinstance(cur, (ast.For, ast.AsyncFor)):
        branch = path + ((id(cur), 'body'),)
        return (_mp03_branch_children((cur.target,), branch)
                + [(cur.iter, path)]
                + _mp03_branch_children(cur.body, branch)
                + _mp03_branch_children(cur.orelse, path + ((id(cur), 'else'),)))
    if isinstance(cur, ast.While):
        return ([(cur.test, path)]
                + _mp03_branch_children(cur.body, path + ((id(cur), 'body'),))
                + _mp03_branch_children(cur.orelse, path + ((id(cur), 'else'),)))
    if isinstance(cur, (ast.Try, TRY_STAR)):
        children = _mp03_branch_children(
            cur.body, path + ((id(cur), 'body'),))
        children.extend(
            (handler, path + ((id(cur), 'handler', index),))
            for index, handler in enumerate(cur.handlers))
        children.extend(_mp03_branch_children(
            cur.orelse, path + ((id(cur), 'body'),)))
        children.extend(_mp03_branch_children(cur.finalbody, path))
        return children
    if isinstance(cur, AST_MATCH_TYPES):
        children = [(cur.subject, path)]
        for index, case in enumerate(cur.cases):
            children.extend(_mp03_branch_children(
                (case,), path + ((id(cur), 'case', index),)))
        return children
    return _mp03_branch_children(ast.iter_child_nodes(cur), path)
def _mp03_frame_walk(stmts, annotations_deferred):
    stack = [(stmt, (), stmt) for stmt in stmts]
    while stack:
        cur, path, owner_stmt = stack.pop()
        yield cur, path, owner_stmt
        stack.extend((child, child_path,
                      child if isinstance(child, ast.stmt) else owner_stmt)
                     for child, child_path in _mp03_frame_children(
                         cur, path, annotations_deferred))
def _mp03_is_assignment_target(child: ast.Attribute,
                               owner_stmt: ast.AST) -> bool:
    if isinstance(owner_stmt, ast.Assign):
        targets = owner_stmt.targets
    elif isinstance(owner_stmt, (ast.AnnAssign, ast.AugAssign)):
        targets = (owner_stmt.target,)
    else:
        return False
    return any(node is child for target in targets
               for node in walk_nodes(target))
def _mp03_write_position(child: ast.Attribute,
                         owner_stmt: ast.AST, path) -> tuple[int, int]:
    for step in reversed(path):
        if len(step) == 4 and step[1] == 'comp':
            return step[2], step[3]
    if _mp03_is_assignment_target(child, owner_stmt):
        return (int(getattr(owner_stmt, 'end_lineno', 0) or child.lineno),
                int(getattr(owner_stmt, 'end_col_offset', 0)
                    or child.col_offset))
    return (child.lineno, child.col_offset)
def _mp03_is_augassign_target(child: ast.Attribute,
                              owner_stmt: ast.AST) -> bool:
    return (isinstance(owner_stmt, ast.AugAssign)
            and owner_stmt.target is child
            and isinstance(child.value, ast.Name)
            and child.value.id == 'self'
            and child.attr not in _MP03_EXEMPT_ATTRS)
def _mp03_self_attr_writes(node, annotations_deferred) -> dict:
    ops = {}
    for child, path, owner_stmt in _mp03_frame_walk(
            node.body, annotations_deferred):
        if not isinstance(child, ast.Attribute):
            continue
        if not isinstance(child.value, ast.Name) or child.value.id != 'self':
            continue
        if not isinstance(child.ctx, (ast.Store, ast.Del)):
            continue
        if (isinstance(owner_stmt, ast.AnnAssign)
                and owner_stmt.value is None
                and owner_stmt.target is child):
            continue
        ops.setdefault(child.attr, []).append(
            (_mp03_write_position(child, owner_stmt, path),
             isinstance(child.ctx, ast.Store), path))
    return ops
def _mp03_is_self_attr_load(child: ast.Attribute) -> bool:
    return (isinstance(child.ctx, ast.Load)
            and isinstance(child.value, ast.Name)
            and child.value.id == 'self'
            and child.attr not in _MP03_EXEMPT_ATTRS)
def _mp03_load_attrs(node: Any, annotations_deferred):
    for child, path, owner_stmt in _mp03_frame_walk(
            node.body, annotations_deferred):
        if not isinstance(child, ast.Attribute):
            continue
        if not (_mp03_is_self_attr_load(child)
                or _mp03_is_augassign_target(child, owner_stmt)):
            continue
        yield child, path
def _mp03_store_guarantees_load(store_path, load_path) -> bool:
    return load_path[:len(store_path)] == store_path
def _mp03_if_else_coverage_pos(ops, load_pos, load_path, match_nodes):
    branches = {}
    node_ids = set()
    for op in ops:
        position, _is_store, path = op
        if (position >= load_pos or len(path) < len(load_path) + 1
                or path[:len(load_path)] != load_path):
            continue
        step = path[len(load_path)]
        if len(step) != 2 or step[1] not in {'if_body', 'if_else'}:
            continue
        node_ids.add(step[0])
        if len(path) == len(load_path) + 1:
            branches.setdefault((step[0], step[1]), []).append(op)
    covered_at = []
    for node_id in node_ids:
        labels = ('if_body', 'if_else')
        branch_ops = {}
        for label in labels:
            key = (node_id, label)
            values = list(branches.get(key, ()))
            branch_path = (*load_path, key)
            for nested_at in (
                    _mp03_if_else_coverage_pos(
                        ops, load_pos, branch_path, match_nodes),
                    _mp03_match_coverage_pos(
                        ops, load_pos, branch_path, match_nodes),
                    _mp03_try_coverage_pos(
                        ops, load_pos, branch_path, match_nodes),
            ):
                if nested_at is not None:
                    values.append((nested_at, True, branch_path))
            branch_ops[key] = values
        if any(not branch_ops[(node_id, label)] for label in labels):
            continue
        final_ops = [max(branch_ops[(node_id, label)], key=lambda op: op[0])
                     for label in labels]
        if not all(op[1] for op in final_ops):
            continue
        later_delete = False
        for label, final_op in zip(labels, final_ops, strict=True):
            branch_path = (*load_path, (node_id, label))
            if any(not is_store
                   and final_op[0] < position < load_pos
                   and path[:len(branch_path)] == branch_path
                   for position, is_store, path in ops):
                later_delete = True
                break
        if not later_delete:
            covered_at.append(max(op[0] for op in final_ops))
    return max(covered_at) if covered_at else None
def _mp03_match_coverage_pos(ops, load_pos, load_path, match_nodes):
    covered_at = []
    for node_id, match in match_nodes.items():
        exhaustive_index = None
        if not isinstance(match, AST_MATCH_TYPES):
            continue
        for index, case in enumerate(match.cases):
            if (case.guard is None
                    and isinstance(case.pattern, ast.MatchAs)
                    and case.pattern.pattern is None):
                exhaustive_index = index
                break
        if exhaustive_index is None:
            continue
        final_ops = []
        for index in range(exhaustive_index + 1):
            branch_path = (*load_path, (node_id, 'case', index))
            branch_ops = [
                op for op in ops
                if (op[0] < load_pos
                    and op[2][:len(branch_path)] == branch_path)
            ]
            if not branch_ops:
                break
            values = [
                op for op in branch_ops
                if len(op[2]) == len(branch_path)
            ]
            for nested_at in (
                    _mp03_if_else_coverage_pos(
                        branch_ops, load_pos, branch_path, match_nodes),
                    _mp03_match_coverage_pos(
                        branch_ops, load_pos, branch_path, match_nodes),
                    _mp03_try_coverage_pos(
                        branch_ops, load_pos, branch_path, match_nodes)):
                if nested_at is not None:
                    values.append((nested_at, True, branch_path))
            if not values:
                break
            final_op = max(values, key=lambda op: op[0])
            if not final_op[1]:
                break
            if any(not is_store
                   and final_op[0] < position < load_pos
                   and path[:len(branch_path)] == branch_path
                   for position, is_store, path in ops):
                break
            final_ops.append(final_op)
        else:
            covered_at.append(max(op[0] for op in final_ops))
    return max(covered_at) if covered_at else None
def _mp03_try_coverage_pos(ops, load_pos, load_path, coverage_nodes):
    covered_at = []
    for node_id, try_node in coverage_nodes.items():
        if not isinstance(try_node, (ast.Try, TRY_STAR)):
            continue
        branch_paths = [(*load_path, (node_id, 'body'))]
        branch_paths.extend(
            (*load_path, (node_id, 'handler', index))
            for index in range(len(try_node.handlers)))
        final_ops = []
        for branch_path in branch_paths:
            branch_ops = [
                op for op in ops
                if (op[0] < load_pos
                    and op[2][:len(branch_path)] == branch_path)
            ]
            if not branch_ops:
                break
            values = [
                op for op in branch_ops
                if len(op[2]) == len(branch_path)
            ]
            for nested_at in (
                    _mp03_if_else_coverage_pos(
                        branch_ops, load_pos, branch_path, coverage_nodes),
                    _mp03_match_coverage_pos(
                        branch_ops, load_pos, branch_path, coverage_nodes),
                    _mp03_try_coverage_pos(
                        branch_ops, load_pos, branch_path, coverage_nodes)):
                if nested_at is not None:
                    values.append((nested_at, True, branch_path))
            if not values:
                break
            final_op = max(values, key=lambda op: op[0])
            if not final_op[1]:
                break
            if any(not is_store
                   and final_op[0] < position < load_pos
                   and path[:len(branch_path)] == branch_path
                   for position, is_store, path in ops):
                break
            final_ops.append(final_op)
        else:
            covered_at.append(max(op[0] for op in final_ops))
    return max(covered_at) if covered_at else None
def _mp03_paths_mutually_exclusive(left, right) -> bool:
    for left_step, right_step in zip(left, right, strict=False):
        if left_step == right_step:
            continue
        if left_step[0] != right_step[0]:
            return False
        labels = {left_step[1], right_step[1]}
        return (labels == {'if_body', 'if_else'}
                or labels == {'case'})
    return False
def _mp03_op_affects_load(op, load_pos, load_path) -> bool:
    position, is_store, path = op
    if position >= load_pos:
        return False
    if is_store:
        return _mp03_store_guarantees_load(path, load_path)
    return not _mp03_paths_mutually_exclusive(path, load_path)
def _mp03_should_report(child: Any, ops: dict, load_path,
                        match_nodes) -> bool:
    load_pos = (child.lineno, child.col_offset)
    attr_ops = ops.get(child.attr, ())
    prior = sorted(
        op for op in attr_ops
        if _mp03_op_affects_load(op, load_pos, load_path))
    coverage = [
        position for position in (
            _mp03_if_else_coverage_pos(
                attr_ops, load_pos, load_path, match_nodes),
            _mp03_match_coverage_pos(
                attr_ops, load_pos, load_path, match_nodes),
            _mp03_try_coverage_pos(
                attr_ops, load_pos, load_path, match_nodes),
        )
        if position is not None
    ]
    if coverage and (not prior or prior[-1][0] <= max(coverage)):
        return False
    return not (prior and prior[-1][1])
def _mp03_finding(child: Any, source: Any, filepath: Any) -> dict:
    return {
        "rule_id": "MP-03", "severity": "P1",
        "dimension": "metaprogramming_safety",
        "file": filepath, "line": child.lineno,
        "title": f"__getattr__ 中 self.{child.attr} 可能触发递归",
        "description": (
            f"__getattr__ 方法内访问 self.{child.attr}, "
            "若该属性不存在将再次触发 __getattr__, 导致 RecursionError."
        ),
        "code_snippet": extract_code_lines(source, child.lineno),
        "suggestion": _mp_suggest("使用 self.__dict__.get(attr) 或 object.__getattribute__ 访问."),
        "rule_ref": "mp-getattr-recursion",
    }
def check_MP03(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if not isinstance(tree, ast.AST):
        return issues
    annotations_deferred = module_postpones_annotations(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name != '__getattr__':
            continue
        ops = _mp03_self_attr_writes(node, annotations_deferred)
        match_nodes = {
            id(child): child for child in walk_nodes(node)
            if isinstance(child, (*AST_MATCH_TYPES, ast.Try, TRY_STAR))
        }
        for child, load_path in _mp03_load_attrs(node, annotations_deferred):
            if not _mp03_should_report(child, ops, load_path, match_nodes):
                continue
            issues.append(_mp03_finding(child, source, filepath))
    return issues
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "diag4_direct": {"MP-03": check_MP03},
            "engine_channels": {
                "ENGINE": (10, run_engine_channels),
            },
            "rule_bindings": {
                "MP01": check_MP01,
                "MP03": check_MP03,
                "PL-01": detect_closure_late_binding,
                "PL-02": detect_assert_security_check,
                "PL-03": detect_global_nonconst,
                "PL-04": detect_n_plus_one_query,
                "PF01": check_PF01_pure_forward,
            },
        },
        "rebuild_hooks": {
            "antipattern_engine": rebuild_antipattern_engine,
        },
    }
_LINE_BOUNDARY = re.compile(r'\r\n|\r|\n')
@dataclass
class PollutionReport:
    is_clean: bool = True
    pollution_score: int = 0
    is_critical: bool = False
    issues: list[dict] = field(default_factory=list)
_POLLUTION_PATTERNS: tuple[tuple[str, str, str, str, str], ...] = (
    ((r'(#\s*TODO\b(?=\s|$|[:：(])|#\s*FIXME\b(?=\s|$|[:：(])'
      r'|#\s*HACK\b(?=\s|$|[:：(])|#\s*XXX\b(?=\s|$|[:：(]))'),
     'P2', '未解决的技术债务标记', 'comment', 'debt'),
    ((r'(#\s*DEPRECATED\b(?=\s|$|[:：(])'
      r'|#\s*deprecated\b(?=\s|$|[:：(]))'),
     'P2', '废弃标记未清理', 'comment', 'deprecated'),
    (r'(#\s*TEMP\b(?=\s|$|[:：(])|#\s*TEMPORARY\b(?=\s|$|[:：(]))',
     'P2', '临时代码标记', 'comment', 'temp'),
    (r'(?<![\w.])print\s*\([^)]*\)', 'P2', '调试 print 语句', 'code', 'print'),
    (r'(#\s*DEBUG\b(?=\s|$|[:：(])|#\s*debug\b(?=\s|$|[:：(]))',
     'P2', '调试代码标记', 'comment', 'debug'),
    (r'(?<![\w.])(breakpoint\s*\([^)]*\))', 'P1', 'breakpoint() 调试断点',
     'code', 'breakpoint'),
    (r'(?<![\w.])(pdb\.set_trace\s*\([^)]*\))', 'P0', 'pdb 调试器调用',
     'code', 'pdb'),
)
_PRINT_SAFE_FUNC_KEYWORDS = (
    'report', 'summary', 'main', 'cli', 'health', 'check',
    'display', 'show', 'dump', 'format', 'render', 'banner',
    'print_', '_print', 'usage', 'help', 'version', 'status',
    'maintain', 'clean', 'monitor', 'watch', 'run_', 'diag',
    'scan', 'notify', 'warn', 'log_', 'info_', 'result_',
    '_out', '_emit', '_puts', 'unified',
)
_PRINT_SAFE_FUNC_NAMES = frozenset({'_p'})
_TEMP_SAFE_PATTERN = re.compile(
    r'临时(?:文件|目录|脚本|产物)|temp(?:orary)? (?:file|directory|script|artifact)')
def _is_temp_safe_line(line_text: str) -> bool:
    return _TEMP_SAFE_PATTERN.search(line_text.casefold()) is not None
def _line_text_at(code_lines: list, line_num: int) -> str:
    if 0 < line_num <= len(code_lines):
        return code_lines[line_num - 1]
    return ""
def _comment_start_col(text: str, lead_state: str = "") -> int:
    return scan_line_quote_state(text, lead_state)[0]
def _hit_in_comment(code_lines: list, line_num: int, col: int,
                    lead_state: str = "") -> bool:
    _csc = _comment_start_col(
        _line_text_at(code_lines, line_num), lead_state)
    return _csc >= 0 and col > _csc
def _is_print_in_safe_context(node, parent_map):
    current = node
    func_def = None
    in_main_block = False
    while current in parent_map:
        parent = parent_map[current]
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_def = parent
            break
        if isinstance(parent, ast.If) and is_main_check(parent.test):
            in_main_block = True
        current = parent
    if in_main_block:
        return True
    if func_def is not None:
        func_name = func_def.name.lower()
        if (func_name in _PRINT_SAFE_FUNC_NAMES
                or any(kw in func_name for kw in _PRINT_SAFE_FUNC_KEYWORDS)):
            return True
    if not node.args and not node.keywords:
        return True
    return func_def is None
_PREFIX_KW_RE = re.compile(r'\b(?:def|class)\s*$')
_DEF_KEYWORD_LOOKBACK = 12
def _norm_span_cols(node, lines: list | None) -> tuple[int, int]:
    _sc, _ec = node.col_offset, node.end_col_offset
    if lines is not None:
        _li = node.lineno - 1
        if _li < len(lines):
            _sc = byte_col_to_char_col(lines[_li], _sc)
        _eli = node.end_lineno - 1
        if _eli < len(lines):
            _ec = byte_col_to_char_col(lines[_eli], _ec)
    return _sc, _ec
def _build_string_literal_spans(tree, code: str | None = None):
    spans = []
    if tree is None:
        return spans
    _lines = ast_split_lines(code) if code is not None else None
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes))
                and hasattr(node, 'lineno') and hasattr(node, 'end_lineno')):
            _sc, _ec = _norm_span_cols(node, _lines)
            spans.append((node.lineno, _sc,
                          node.end_lineno, _ec))
    return spans
def _build_span_index(spans) -> dict[int, list]:
    index: dict[int, list] = {}
    for sl, sc, el, ec in spans:
        for ln in range(sl, el + 1):
            index.setdefault(ln, []).append((sl, sc, el, ec))
    return index
def _offset_in_spans(line: int, col: int, span_index: dict) -> bool:
    for sl, sc, el, ec in span_index.get(line, ()):
        if (line, col) >= (sl, sc) and (line, col) < (el, ec):
            return True
    return False
@dataclass(frozen=True)
class _PolAstCtx:
    span_index: dict[int, list]
    print_safe_lines: set
def _token_span_index(code: str) -> dict[int, list]:
    spans = string_token_row_spans(code)
    if not spans:
        return {}
    index: dict[int, list] = {}
    for line, pairs in spans.items():
        for start, stop in pairs:
            if stop > start:
                index.setdefault(line, []).append((line, start, line, stop))
    return index
def _empty_pol_ast_ctx(code: str | None = None) -> _PolAstCtx:
    return _PolAstCtx(
        span_index=_token_span_index(code) if code else {},
        print_safe_lines=set())
def _collect_ast_pol_ctx(tree, code: str) -> _PolAstCtx:
    _parent_map = parent_map(tree)
    _print_safe_lines: set = set()
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name) and node.func.id == 'print'
                and _is_print_in_safe_context(node, _parent_map)
                and hasattr(node, 'lineno')):
            _print_safe_lines.add(node.lineno)
    return _PolAstCtx(
        span_index=_build_span_index(_build_string_literal_spans(tree, code)),
        print_safe_lines=_print_safe_lines)
@dataclass(frozen=True)
class _Pol01Context:
    code: str
    code_lines: list[str]
    line_starts: list[int]
    lead_states: list[str]
    ast: _PolAstCtx
def _lead_state_at(ctx: _Pol01Context, line_num: int) -> str:
    if 0 < line_num <= len(ctx.lead_states):
        return ctx.lead_states[line_num - 1]
    return ""
def _pol01_issue(line_num: int, severity: str, desc: str,
                 matched: str) -> dict:
    return {
        'rule_id': 'POL-01',
        'line': line_num,
        'severity': severity,
        'description': desc,
        'match': matched[:80],
    }
def _pol01_comment_line_hits(ctx: _Pol01Context, marker_pat: str,
                             severity: str, desc: str, key: str,
                             index: int) -> list[dict]:
    _text = ctx.code_lines[index]
    _line_no = index + 1
    _csc = _comment_start_col(_text, _lead_state_at(ctx, _line_no))
    if _csc < 0:
        return []
    issues: list[dict] = []
    for match in re.finditer(marker_pat, _text[_csc:]):
        _col = _csc + match.start()
        if _offset_in_spans(_line_no, _col, ctx.ast.span_index):
            continue
        if key == 'temp' and _is_temp_safe_line(_text):
            continue
        issues.append(_pol01_issue(_line_no, severity, desc, match.group()))
    return issues
def _pol01_comment_family_scan(ctx: _Pol01Context, pattern: str,
                               severity: str, desc: str,
                               key: str) -> list[dict]:
    issues: list[dict] = []
    for _li in range(len(ctx.code_lines)):
        issues.extend(_pol01_comment_line_hits(
            ctx, pattern, severity, desc, key, _li))
    return issues
def _pol01_match_position(line_starts: list,
                          offset: int) -> tuple[int, int]:
    if not line_starts:
        return 1, 0
    line_num = bisect.bisect_right(line_starts, offset)
    return line_num, offset - line_starts[line_num - 1]
def _is_attribute_access(code: str, offset: int) -> bool:
    cursor = offset
    while cursor > 0 and code[cursor - 1].isspace():
        cursor -= 1
    return cursor > 0 and code[cursor - 1] == "."
def _pol01_code_hit_exempt(ctx: _Pol01Context, key: str,
                           line_num: int, col: int, offset: int) -> bool:
    if _offset_in_spans(line_num, col, ctx.ast.span_index):
        return True
    if (key in ("print", "breakpoint", "pdb")
            and _is_attribute_access(ctx.code, offset)):
        return True
    if _PREFIX_KW_RE.search(
            ctx.code[max(0, offset - _DEF_KEYWORD_LOOKBACK):offset]):
        return True
    if key == 'print' and line_num in ctx.ast.print_safe_lines:
        return True
    if _hit_in_comment(ctx.code_lines, line_num, col,
                       _lead_state_at(ctx, line_num)):
        return True
    return (key == 'temp'
            and _is_temp_safe_line(_line_text_at(ctx.code_lines, line_num)))
def _pol01_code_family_scan(ctx: _Pol01Context, pattern: str,
                            severity: str, desc: str,
                            key: str) -> list[dict]:
    issues: list[dict] = []
    for match in re.finditer(pattern, ctx.code):
        _off = match.start()
        line_num, _col = _pol01_match_position(ctx.line_starts, _off)
        if _pol01_code_hit_exempt(ctx, key, line_num, _col, _off):
            continue
        issues.append(_pol01_issue(line_num, severity, desc, match.group()))
    return issues
def _pol02_scan_ast(tree) -> list[dict]:
    issues: list[dict] = []
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ExceptHandler) and node.type is None
                and node.body
                and all(_is_noop_stmt(stmt) for stmt in node.body)):
            issues.append({
                'rule_id': 'POL-02',
                'line': node.lineno,
                'severity': 'P2',
                'description': 'bare except: pass (静默吞异常)',
            })
    return issues
def _pol01_scan_all(code: str, ast_ctx: _PolAstCtx) -> list[dict]:
    _code_lines = ast_split_lines(code)
    ctx = _Pol01Context(
        code=code,
        code_lines=_code_lines,
        line_starts=[0] + [m.end() for m in _LINE_BOUNDARY.finditer(code)],
        lead_states=leading_quote_states(_code_lines),
        ast=ast_ctx,
    )
    issues: list[dict] = []
    for pattern, severity, desc, kind, key in _POLLUTION_PATTERNS:
        if kind == "comment":
            issues.extend(_pol01_comment_family_scan(
                ctx, pattern, severity, desc, key))
        else:
            issues.extend(_pol01_code_family_scan(
                ctx, pattern, severity, desc, key))
    return issues
_SEVERITY_SCORES = {'P0': 10, 'P1': 5}
_SEVERITY_SCORE_DEFAULT = 1
def _compute_pollution_score(issues: list[dict]) -> int:
    return sum(
        _SEVERITY_SCORES.get(issue['severity'], _SEVERITY_SCORE_DEFAULT)
        for issue in issues
    )
def _pollution_detect_issues(code: Any, tree: Any,
                             skip_pollution_01: bool,
                             skip_pollution_02: bool
                             ) -> list[dict[str, Any]] | None:
    text, node, parse_error = _coerce_channel_input(code, tree)
    if node is None:
        if not text:
            return None
        if parse_error is not None:
            logger.warning("AST解析失败，跳过AST级检测",
                           exc_info=parse_error)
    issues: list[dict[str, Any]] = []
    ast_ctx = (_collect_ast_pol_ctx(node, text) if node is not None
               else _empty_pol_ast_ctx(text))
    if text and not is_consolidated_code(text) and not skip_pollution_01:
        issues.extend(_pol01_scan_all(text, ast_ctx))
    if node is not None and not skip_pollution_02:
        issues.extend(_pol02_scan_ast(node))
    return issues
def detect_pollution(code: Any, tree: Any = _DEFAULT_TREE,
                     *, skip_pollution_01: bool = False,
                     skip_pollution_02: bool = False) -> PollutionReport:
    issues = _pollution_detect_issues(code, tree,
                                      skip_pollution_01, skip_pollution_02)
    if issues is None:
        return PollutionReport()
    report = PollutionReport()
    report.is_critical = any(i['severity'] == 'P0' for i in issues)
    report.pollution_score = _compute_pollution_score(issues)
    report.issues = issues
    report.is_clean = len(issues) == 0
    return report
def pollution_issues(code: Any, tree: Any = _DEFAULT_TREE,
                     exclude_rules: Any = _DEFAULT_EXCLUDE_RULES) -> list:
    _excl = _normalize_exclude_rules(exclude_rules)
    report = detect_pollution(
        code, tree=tree,
        skip_pollution_01=_is_excluded("POL-01", _excl),
        skip_pollution_02=_is_excluded("POL-02", _excl))
    return project_pollution_issues(report)
_FACTORY_PREFIXES = ('create_', 'make_', 'build_', 'new_', 'from_', 'load_', 'parse_')
def _has_factory_prefix(name: str) -> bool:
    return name.startswith(_FACTORY_PREFIXES)
def _has_path_conversion(body: list[ast.stmt]) -> bool:
    for stmt in body:
        for node in walk_nodes(stmt):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            if isinstance(func, ast.Name) and func.id == 'Path':
                return True
            if isinstance(func, ast.Attribute) and func.attr == 'Path':
                return True
    return False
def _is_cache_or_singleton_call(call_node: ast.Call) -> bool:
    return (isinstance(call_node.func, ast.Attribute)
            and call_node.func.attr in ('get', 'copy', 'items', 'keys', 'values')
            and isinstance(call_node.func.value, ast.Name)
            and call_node.func.value.id.startswith('_'))
def _is_dict_dispatch_callee(func: ast.AST) -> bool:
    if isinstance(func, ast.Subscript):
        return True
    return (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Subscript))
def _is_noop_stmt(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.Pass)
            or (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)))
def _effective_body(func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[ast.stmt]:
    return [stmt for stmt in func_node.body if not _is_noop_stmt(stmt)]
def _iter_function_nodes(tree: ast.AST):
    for node in tree_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node
def _param_names(func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[str]:
    return [p.arg for p in iter_params(func_node.args)]
def _resolve_tree(code: str | ast.AST | None, tree: ast.AST | None) -> ast.AST | None:
    if isinstance(tree, ast.AST):
        return tree
    if isinstance(code, ast.AST):
        return code
    if not isinstance(code, str):
        return None
    resolved, error = _parse_ast(code)
    if error is not None:
        logger.warning(MSG_SYNTAX_ERROR_SKIP)
    return resolved
def _is_facade_file(filepath: str) -> bool:
    fname = os.path.basename(filepath or "").lower()
    return fname in FACADE_FILENAMES
_TYPE_ALIAS_NAMES = frozenset({
    'TypeVar', 'TypeAlias', 'TypeAliasType', 'NewType',
    'Generic', 'Protocol', 'ABC', 'ABCMeta',
    'Any', 'Union', 'Optional', 'Literal', 'Final',
    'ClassVar', 'TypedDict', 'NamedTuple',
})
def _is_type_alias(node: ast.Assign | ast.AnnAssign) -> bool:
    if isinstance(node, ast.AnnAssign):
        annotation = node.annotation
        if (isinstance(annotation, ast.Name) and annotation.id == 'TypeAlias'):
            return True
        if (isinstance(annotation, ast.Attribute)
                and annotation.attr == 'TypeAlias'):
            return True
    value = node.value
    if isinstance(value, ast.Name):
        return value.id in _TYPE_ALIAS_NAMES
    if isinstance(value, ast.Attribute):
        return value.attr in _TYPE_ALIAS_NAMES
    return False
def _is_constant_assignment(node: ast.Assign | ast.AnnAssign) -> bool:
    if isinstance(node.value, ast.Constant):
        return True
    if isinstance(node.value, (ast.List, ast.Tuple, ast.Set)):
        return all(isinstance(e, ast.Constant) for e in node.value.elts)
    if isinstance(node.value, ast.Dict):
        return all(
            isinstance(k, ast.Constant) and isinstance(v, ast.Constant)
            for k, v in zip(node.value.keys, node.value.values, strict=True)
        )
    return False
_PROTO_CONVERTERS = frozenset({'asdict', 'astuple'})
_TYPE_CONVERTERS = frozenset({
    'str', 'int', 'float', 'bool', 'bytes', 'list', 'tuple', 'set',
    'dict', 'frozenset', 'repr', 'ascii', 'format', 'chr', 'ord',
    'enumerate', 'zip', 'map', 'filter',
    'json.dumps', 'json.loads',
})
def _type_converter_name(call: ast.AST) -> str | None:
    if isinstance(call, ast.Name):
        return call.id if call.id in _TYPE_CONVERTERS else None
    if isinstance(call, ast.Attribute) and isinstance(call.value, ast.Name):
        if call.value.id == 'builtins':
            return call.attr if call.attr in _TYPE_CONVERTERS else None
        dotted = f'{call.value.id}.{call.attr}'
        return dotted if dotted in _TYPE_CONVERTERS else None
    return None
def _seg_root_set(name: str) -> set[str]:
    words: set[str] = set()
    for seg in split_identifier(name):
        word = seg[:-1] if len(seg) > 3 and seg.endswith('s') else seg
        words.add(word)
    return words
def _attr_root_is_object(func: ast.Attribute) -> bool:
    root = func
    while isinstance(root, ast.Attribute):
        root = root.value
    if isinstance(root, ast.Call):
        return True
    if isinstance(root, ast.Name):
        return (root.id in _SELF_CLS_NAMES
                or root.id[:1].isupper()
                or root.id.startswith('_'))
    return False
def _call_shape_exempt(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                      call: ast.AST) -> bool:
    if func_node.decorator_list:
        return True
    if isinstance(call, ast.Name):
        return call.id[:1].isupper()
    if isinstance(call, ast.Attribute):
        return _attr_root_is_object(call)
    return False
def _private_impl_exempt(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                        ret_val: ast.Call, callee: str) -> bool:
    if not callee.startswith('_'):
        return False
    if ret_val.keywords:
        return True
    return len(_param_names(func_node)) > len(ret_val.args)
def _naming_exempt(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                  callee: str) -> bool:
    if func_node.name.startswith('_'):
        return True
    if callee in _PROTO_CONVERTERS or func_node.name.startswith('to_'):
        return True
    return bool(_seg_root_set(func_node.name) & _seg_root_set(callee))
def _is_private_seam_callee(func: ast.AST) -> bool:
    if isinstance(func, ast.Name):
        return func.id.startswith('_')
    if isinstance(func, ast.Attribute):
        base: ast.AST = func.value
        while isinstance(base, ast.Attribute):
            base = base.value
        if isinstance(base, ast.Name):
            if base.id in _SELF_CLS_NAMES:
                return False
            return base.id.startswith('_') or base.id.isupper()
    return False
def _thin_wrapper_semantic_exempt(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                                  ret_val: ast.Call) -> bool:
    call = ret_val.func
    if ast.get_docstring(func_node):
        return True
    if _is_private_seam_callee(call):
        return True
    if _call_shape_exempt(func_node, call):
        return True
    if _type_converter_name(call) is not None:
        return True
    if isinstance(call, ast.Name):
        callee = call.id
    elif isinstance(call, ast.Attribute):
        callee = call.attr
    else:
        return False
    return (_private_impl_exempt(func_node, ret_val, callee)
            or _naming_exempt(func_node, callee))
def _thin_reexport_callee(target: ast.AST, value: ast.AST) -> str | None:
    if not isinstance(target, ast.Name):
        return None
    if isinstance(value, ast.Name):
        return value.id
    parts: list[str] = []
    current = value
    while isinstance(current, ast.Attribute):
        parts.append(current.attr)
        current = current.value
    if isinstance(current, ast.Name) and parts:
        return ".".join((current.id, *reversed(parts)))
    return None
def _import_binding_names(node: ast.AST) -> list[str]:
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return sorted(import_alias_bound_names(node))
    return []
def _collect_imported_names(tree: ast.AST, *,
                           include_modules: bool = True,
                           module_level: bool = False) -> set[str]:
    imported_names: set[str] = set()
    nodes = iter_module_level_stmts(tree) if module_level else tree_nodes(tree)
    for node in nodes:
        if not include_modules and isinstance(node, ast.Import):
            continue
        imported_names.update(_import_binding_names(node))
    return imported_names
@dataclass(frozen=True)
class _ModuleIndex:
    imported_names: frozenset[str]
    module_def_names: frozenset[str]
def _module_def_names(tree: ast.AST) -> frozenset[str]:
    return frozenset(
        node.name for node in iter_module_level_stmts(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)))
def _build_index(tree: ast.AST) -> _ModuleIndex:
    return _ModuleIndex(
        imported_names=frozenset(_collect_imported_names(
            tree, include_modules=False, module_level=True)),
        module_def_names=_module_def_names(tree),
    )
def _as_module_index(source: ast.AST | _ModuleIndex) -> _ModuleIndex:
    return source if isinstance(source, _ModuleIndex) else _build_index(source)
def _name_binding_forms(node: ast.AST) -> list[tuple[ast.Name, ast.AST]]:
    if isinstance(node, ast.Assign):
        return [(t, node.value) for t in node.targets
                if isinstance(t, ast.Name)]
    if isinstance(node, ast.AnnAssign):
        if node.value is not None and isinstance(node.target, ast.Name):
            return [(node.target, node.value)]
        return []
    if (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)
            and isinstance(node.target, ast.Name)):
        return [(node.target, node.value)]
    return []
def _iter_all_assignment_nodes(tree: ast.AST):
    for node in iter_module_level_stmts(tree):
        for target, value in _name_binding_forms(node):
            yield target, value, node.lineno, node.col_offset
_TYPE_SUSPICIOUS = DelegationType.SUSPICIOUS.name
_TYPE_THIN_WRAPPER = "THIN_WRAPPER"
_TYPE_THIN_REEXPORT = "THIN_REEXPORT"
_TYPE_ALL_REEXPORT = "ALL_REEXPORT"
def _d50_issue(filepath: str, line: int, col_offset: int,
               **fields) -> dict[str, Any]:
    issue = {
        "id": "D50",
        "severity": "P3",
        "dimension": CAT_MAINTAINABILITY,
        "file": filepath,
        "line": line,
        "col_offset": col_offset,
    }
    issue.update(fields)
    return issue
def _detect_all_reexports(tree: ast.AST, filepath: str,
                          scan: _FacadeScan) -> list[dict[str, Any]]:
    issues = []
    for target, value, lineno, col_offset in _iter_all_assignment_nodes(tree):
        if target.id != '__all__':
            continue
        names = static_all_names(value, scan.seq_bindings).names
        if not names:
            continue
        reexported = [n for n in names if n in scan.reexport_roots]
        if len(reexported) > 20:
            issues.append(_d50_issue(
                filepath, lineno, col_offset,
                message=(f"__all__ 重导出 {len(reexported)} 个 import 引入符号: "
                         f"{', '.join(reexported[:5])}..."),
                suggestion="检查 __all__ 中是否有可内联或移除的冗余重导出",
                facade_type=_TYPE_ALL_REEXPORT,
                exported_names=reexported,
                count=len(reexported),
            ))
    return issues
def _is_thin_wrapper(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                    effective: list[ast.stmt]) -> bool:
    ret_val = _returned_call(effective)
    if ret_val is None:
        return False
    call = _collect_passthrough_call(
        ret_val, func_node.args.vararg, func_node.args.kwarg)
    return (call is not None
            and _passthrough_signature_matches(call, func_node))
def _iter_module_bindings(tree: ast.AST):
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.AugAssign):
            continue
        if isinstance(node, ast.Assign) and len(node.targets) != 1:
            continue
        for target, value in _name_binding_forms(node):
            yield node, target, value
@dataclass(frozen=True)
class _FacadeScan:
    seq_bindings: dict[str, ast.AST]
    imported_names: frozenset[str]
    local_def_names: frozenset[str]
    public_names: frozenset[str]
    main_guard_ids: frozenset[int]
    @property
    def reexport_roots(self) -> frozenset[str]:
        return self.imported_names - self.local_def_names
def _build_facade_scan(tree: ast.AST) -> _FacadeScan:
    seq_bindings = static_seq_bindings(tree)
    public: set[str] = set()
    for target, value, _lineno, _col in _iter_all_assignment_nodes(tree):
        if target.id == "__all__":
            public.update(static_all_names(value, seq_bindings).names)
    return _FacadeScan(
        seq_bindings=seq_bindings,
        imported_names=frozenset(
            _collect_imported_names(tree, module_level=True)),
        local_def_names=_module_def_names(tree),
        public_names=frozenset(public),
        main_guard_ids=frozenset(_main_guard_node_ids(tree)),
    )
def _main_guard_node_ids(tree: ast.AST) -> set[int]:
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.If) and is_main_check(node.test):
            ids.update(id(child) for child in walk_nodes(node))
    return ids
def _scan_reexport_assignments(tree, filepath,
                               scan: _FacadeScan) -> list[dict[str, Any]]:
    issues = []
    roots = scan.reexport_roots
    for node, _target, _value in _iter_module_bindings(tree):
        if id(node) in scan.main_guard_ids:
            continue
        if _target.id in scan.public_names:
            continue
        if _is_constant_assignment(node) or _is_type_alias(node):
            continue
        reexport_target = _thin_reexport_callee(_target, _value)
        if reexport_target is None:
            continue
        root = reexport_target.split(".", 1)[0]
        if (root not in roots
                or hasattr(builtins, root)
                or _is_exempt_reexport(_target.id, reexport_target)):
            continue
        target_name = _target.id
        issues.append(_d50_issue(
            filepath, node.lineno, node.col_offset,
            message=f"重导出门面: {target_name} = {reexport_target}",
            suggestion=(f"考虑让调用方直接导入 {reexport_target}，"
                        "或保留作为语义别名"),
            facade_type=_TYPE_THIN_REEXPORT,
            source_name=target_name,
            target_name=reexport_target,
        ))
    return issues
def _is_exempt_reexport(target_name: str, reexport_target: str) -> bool:
    if target_name == reexport_target:
        return True
    if target_name.lstrip('_') == reexport_target.lstrip('_'):
        return True
    if target_name.startswith('_'):
        return True
    return is_constant_name(target_name)
def _thin_wrapper_effective_body(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[ast.stmt] | None:
    effective = _effective_body(node)
    if (is_dunder_name(node.name)
            or _has_factory_prefix(node.name)
            or _has_path_conversion(effective)):
        return None
    return effective if _is_thin_wrapper(node, effective) else None
def _scan_thin_wrappers(tree, filepath):
    issues = []
    for node in _iter_function_nodes(tree):
        effective = _thin_wrapper_effective_body(node)
        if effective is None:
            continue
        issue = _classify_thin_wrapper(node, effective, filepath)
        if issue is not None:
            issues.append(issue)
    return issues
def _classify_thin_wrapper(node: ast.FunctionDef | ast.AsyncFunctionDef,
                           effective: list[ast.stmt],
                           filepath: str) -> dict[str, Any] | None:
    ret_val = _returned_call(effective)
    if ret_val is None or _is_dict_dispatch_callee(ret_val.func):
        return None
    if _thin_wrapper_semantic_exempt(node, ret_val):
        return None
    if isinstance(ret_val.func, ast.Name):
        delegates_to = ret_val.func.id
    elif isinstance(ret_val.func, ast.Attribute):
        delegates_to = ret_val.func.attr
    else:
        delegates_to = "?"
    return _d50_issue(
        filepath, node.lineno, node.col_offset,
        message=f"薄包装器: {node.name}() → {delegates_to}()",
        suggestion="考虑内联或使用 functools.wraps 保留元数据",
        facade_type=_TYPE_THIN_WRAPPER,
        function=node.name,
        delegates_to=delegates_to,
    )
def _facade_tree(code: str | ast.AST | None, tree: ast.AST | None,
                 filepath: str) -> ast.AST | None:
    resolved = _resolve_tree(code, tree)
    if resolved is None or _is_facade_file(filepath):
        return None
    return resolved
def check_D50_facade(code: str | ast.AST | None, filepath: str = _DEFAULT_FILEPATH,
                     tree: ast.AST | None = _DEFAULT_TREE) -> list[dict[str, Any]]:
    tree = _facade_tree(code, tree, filepath)
    if tree is None:
        return []
    scan = _build_facade_scan(tree)
    issues = []
    issues.extend(_scan_reexport_assignments(tree, filepath, scan))
    issues.extend(_detect_all_reexports(tree, filepath, scan))
    issues.extend(_scan_thin_wrappers(tree, filepath))
    if issues:
        logger.info("[D50] 门面检测命中: %s ×%d (%s)",
                  filepath or "<inline>", len(issues),
                  ", ".join(sorted({str(i.get("facade_type", "?"))
                                    for i in issues})))
    return issues
_TRANSPARENT_DECORATORS = frozenset({'property', 'staticmethod', 'classmethod'})
def _decorator_label(decorator: ast.AST) -> str | None:
    if isinstance(decorator, ast.Name):
        return decorator.id
    if isinstance(decorator, ast.Attribute):
        return decorator.attr
    return None
_COPY_MARKERS = (
    'copy(', 'deepcopy(', '[:]', '.copy()',
    'dict(', 'list(', 'set(', 'tuple(', 'frozenset(',
)
_REGISTRY_MARKERS = (
    'get_registry', 'registry.get', 'Registry()', '_registry.get',
    'lookup(', 'resolve(', 'find_by_', 'get_by_',
)
_LOG_MARKERS = ('logger.', 'logging.', 'warnings.warn', 'print(')
_VALIDATION_MARKERS = ('isinstance(', 'issubclass(', 'hasattr(', 'callable(')
def _try_unparse(node: ast.AST) -> str | None:
    try:
        return ast.unparse(node)
    except Exception as e:  # noqa: BLE001
        logger.warning('[Delegation] unparse 失败: %s', e)
        return None
def _blank_string_constants_seq(items: list) -> list:
    """对列表内每个 AST 元素做置空，**没有变化时返回原列表**。"""
    replaced: dict[int, ast.AST] = {}
    for position, item in enumerate(items):
        if not isinstance(item, ast.AST):
            continue
        blanked = _blank_string_constants(item)
        if blanked is not item:
            replaced[position] = blanked
    if not replaced:
        return items
    out = list(items)
    for position, blanked in replaced.items():
        out[position] = blanked
    return out
def _blank_string_constants(node: ast.AST) -> ast.AST:
    """把字符串/字节常量替换为空串，返回**结构共享**的等价副本。

    原实现 ``_TextConstantBlanker().visit(copy.deepcopy(stmt))`` 先整棵
    ``deepcopy`` 再原地改写。AST 的 ``deepcopy`` 走 ``__reduce_ex__`` 路径，
    单节点成本约为普通属性遍历的 8~10 倍；而外层函数体里嵌套着下一层
    ``def``，每一层都会把内层整棵子树重新拷贝一遍，总开销退化为
    O(作用域 x 深度)。

    本实现只重建**从根到字符串常量所在位置**的路径，其余子树直接共享原
    节点。因为 ``ast.unparse`` 是只读的，结构共享不产生任何可观察差异：
    对同一棵树，输出文本与「全量 deepcopy + 全量变换」逐字符相同。
    """
    if isinstance(node, ast.Constant):
        if isinstance(node.value, (str, bytes)):
            return ast.copy_location(ast.Constant(value=''), node)
        return node
    replaced: dict[str, Any] = {}
    for field_name, value in ast.iter_fields(node):
        if isinstance(value, ast.AST):
            blanked = _blank_string_constants(value)
        elif isinstance(value, list):
            blanked = _blank_string_constants_seq(value)
        else:
            continue
        if blanked is not value:
            replaced[field_name] = blanked
    if not replaced:
        return node
    clone = copy.copy(node)
    for field_name, blanked in replaced.items():
        setattr(clone, field_name, blanked)
    return clone
_STMT_SOURCE_MEMO: dict[int, tuple[ast.AST, str]] = {}
_STMT_SOURCE_MEMO_MAX = 4096
def _stmt_source(stmt: ast.AST) -> str:
    """返回语句的源码文本（字符串常量已置空）。

    置空与 unparse 合并为**单次**遍历（``_blank_string_constants`` 无变化
    时返回原节点），并按语句节点身份记忆化——同一语句被多个检测器反复
    取证时只算一次。
    """
    key = id(stmt)
    hit = _STMT_SOURCE_MEMO.get(key)
    if hit is not None and hit[0] is stmt:
        return hit[1]
    try:
        blanked = _blank_string_constants(stmt)
    except PARSE_DEGRADE_EXC as e:
        logger.warning('[Delegation] 语句拷贝失败，证据面退回原树: %s', e)
        blanked = stmt
    source = _try_unparse(blanked) or ''
    if len(_STMT_SOURCE_MEMO) >= _STMT_SOURCE_MEMO_MAX:
        _STMT_SOURCE_MEMO.clear()
    _STMT_SOURCE_MEMO[key] = (stmt, source)
    return source
def _is_deprecated_alias_name(name: str) -> bool:
    name_lower = name.lower()
    return (name.startswith('_')
            or 'legacy' in name_lower
            or 'old' in split_identifier(name)
            or 'compat' in name_lower
            or 'deprecated' in name_lower)
def _check_compat_alias(name: str, effective: list) -> tuple[DelegationType, str] | None:
    if _is_deprecated_alias_name(name) and len(effective) <= 2:
        return (DelegationType.COMPAT_ALIAS, f'兼容性别名: {name} → 可能是旧API委托')
    return None
def _has_conditional_delegation(root: ast.AST) -> bool:
    return any(
        isinstance(inner, ast.Return) and inner.value is not None
        and isinstance(inner.value, ast.Call)
        for inner in walk_nodes(root)
    )
def _detect_lazy_init(name: str, stmt_sources: list) -> tuple[DelegationType, str] | None:
    has_global = False
    has_is_none = False
    for _stmt, source in stmt_sources:
        if marker_hit(source, 'global '):
            has_global = True
        if marker_hit(source, ' is None'):
            has_is_none = True
    if has_global and has_is_none:
        return (DelegationType.LAZY_INIT, f'懒初始化获取器: {name} 使用 global + None 检查模式')
    return None
def _detect_marker_delegation(
        name: str, stmt_sources: list, markers: tuple[str, ...],
        dtype: DelegationType, message: str,
) -> tuple[DelegationType, str] | None:
    for _stmt, source in stmt_sources:
        hit = any(marker_hit(source, marker) for marker in markers)
        if hit:
            return dtype, message.format(name=name)
    return None
_MARKER_DELEGATIONS: tuple[tuple[tuple[str, ...], DelegationType, str], ...] = (
    (_COPY_MARKERS, DelegationType.DEFENSIVE_COPY,
     '防御性拷贝: {name} 包含 copy/deepcopy 操作'),
    (_REGISTRY_MARKERS, DelegationType.REGISTRY_LOOKUP,
     '注册表查找: {name} 使用注册表/查找模式'),
    (_LOG_MARKERS + ('log.', '_log.'), DelegationType.LOGGING_PROXY,
     '日志代理: {name} 包含日志记录操作'),
)
def _validation_evidence(stmt: ast.stmt) -> str | None:
    if isinstance(stmt, ast.Raise):
        return 'raise'
    if isinstance(stmt, ast.Assert):
        return 'assert'
    return None
def _has_type_check(source: str) -> bool:
    return any(marker_hit(source, marker) for marker in _VALIDATION_MARKERS)
def _detect_validation_wrapper(name: str, func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                               stmt_sources: list) -> tuple[DelegationType, str] | None:
    for stmt, source in stmt_sources:
        evidence = _validation_evidence(stmt)
        if evidence is not None:
            return (DelegationType.VALIDATION_WRAPPER,
                    f'校验包装器: {name} 包含 {evidence} 语句（参数校验）')
        if _has_type_check(source) and _has_conditional_delegation(func_node):
            return (DelegationType.VALIDATION_WRAPPER, f'校验包装器: {name} 包含条件检查后委托')
        if marker_hit(source, 'if ') and _has_conditional_delegation(stmt):
            return (DelegationType.VALIDATION_WRAPPER, f'校验包装器: {name} 包含条件检查后委托')
    return None
def _detect_body_patterns(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                         name: str,
                         effective: list[ast.stmt]
                         ) -> tuple[DelegationType, str] | None:
    stmt_sources = [(stmt, _stmt_source(stmt)) for stmt in effective]
    result = _detect_lazy_init(name, stmt_sources)
    if result is not None:
        return result
    for markers, dtype, template in _MARKER_DELEGATIONS:
        result = _detect_marker_delegation(
            name, stmt_sources, markers, dtype, template)
        if result is not None:
            return result
    result = _detect_validation_wrapper(name, func_node, stmt_sources)
    if result is not None:
        return result
    if _has_path_conversion(effective):
        return (DelegationType.PATH_ADAPTER, f'Path标准化适配器: {name} 包含 Path() 类型转换')
    return None
def _return_call(stmt: ast.stmt) -> ast.Call | None:
    if isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Call):
        return stmt.value
    return None
def _uppercase_callee_name(func: ast.AST) -> str | None:
    if isinstance(func, ast.Name) and func.id[:1].isupper():
        return func.id
    if isinstance(func, ast.Attribute) and func.attr[:1].isupper():
        return func.attr
    return None
def _detect_factory_pattern(name: str, effective: list) -> tuple[DelegationType, str] | None:
    if not _has_factory_prefix(name):
        return None
    for stmt in effective:
        call = _return_call(stmt)
        if call is None:
            continue
        callee_name = _uppercase_callee_name(call.func)
        if callee_name is not None:
            return (DelegationType.FACTORY, f'工厂函数: {name} → {callee_name}()')
    return None
def _detect_cross_package(name: str, ret_val: ast.AST | None,
                         index: _ModuleIndex) -> tuple[DelegationType, str] | None:
    if ret_val is None or not isinstance(ret_val, ast.Call):
        return None
    if isinstance(ret_val.func, ast.Attribute):
        root: ast.AST = ret_val.func
        while isinstance(root, ast.Attribute):
            root = root.value
        if isinstance(root, ast.Name) and (
                root.id in _SELF_CLS_NAMES or root.id.startswith('_')):
            return None
        callee = _try_unparse(ret_val.func) or '?'
        return (DelegationType.CROSS_PACKAGE, f'跨包委托: {name} → {callee}()')
    if (isinstance(ret_val.func, ast.Name)
            and ret_val.func.id in index.imported_names):
        return (DelegationType.CROSS_PACKAGE, f'跨包委托: {name} → {ret_val.func.id}() (imported)')
    return None
def _detect_type_adapter(name: str, ret_val: ast.AST | None) -> tuple[DelegationType, str] | None:
    if not isinstance(ret_val, ast.Call):
        return None
    converter = _type_converter_name(ret_val.func)
    if converter is None:
        return None
    return (DelegationType.TYPE_ADAPTER, f'类型适配器: {name} → {converter}()')
def _is_empty_literal(ret_val: ast.AST) -> bool:
    if isinstance(ret_val, ast.Constant):
        return ret_val.value is None
    if isinstance(ret_val, (ast.List, ast.Tuple, ast.Set)):
        return not ret_val.elts
    if isinstance(ret_val, ast.Dict):
        return not ret_val.keys
    return False
def _detect_sentinel(name: str, ret_val: ast.AST | None,
                    func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[DelegationType, str] | None:
    if (func_node.args.vararg is not None
            and func_node.args.kwarg is not None
            and ret_val is not None
            and _is_empty_literal(ret_val)):
        return (DelegationType.SENTINEL, f'统一哨兵: {name}(*args,**kwargs)→固定返回值 (替代分散桩函数)')
    return None
def _detect_cache_access(name: str, ret_val: ast.AST | None) -> tuple[DelegationType, str] | None:
    if ret_val is not None and isinstance(ret_val, ast.Call) and _is_cache_or_singleton_call(ret_val):
        obj_name = ret_val.func.value.id
        return (DelegationType.CACHE_ACCESS, f'缓存/单例访问: {name} → {obj_name}.{ret_val.func.attr}()')
    return None
def _detect_dict_dispatch(name: str, ret_val: ast.AST | None) -> tuple[DelegationType, str] | None:
    if ret_val is None or not isinstance(ret_val, ast.Call):
        return None
    if not _is_dict_dispatch_callee(ret_val.func):
        return None
    style = '下标访问' if isinstance(ret_val.func, ast.Subscript) else '注册表查找'
    return (DelegationType.DICT_DISPATCH, f'字典分发架构: {name} 使用注册表{style}')
def _detect_internal_delegate(name: str, ret_val: ast.AST | None,
                             index: _ModuleIndex) -> tuple[DelegationType, str] | None:
    if ret_val is None or not isinstance(ret_val, ast.Call):
        return None
    func = ret_val.func
    if isinstance(func, ast.Name) and func.id in index.module_def_names:
        return (DelegationType.INTERNAL_DELEGATE, f'内部委托: {name} → {func.id}() (同模块)')
    if (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id in _SELF_CLS_NAMES):
        return (DelegationType.INTERNAL_DELEGATE,
                f'实例方法委托: {name} → {func.value.id}.{func.attr}()')
    return None
@dataclass(frozen=True)
class _PassthroughCall:
    positional: tuple[str, ...]
    keywords: tuple[tuple[str, str], ...]
    vararg: str | None
    kwarg: str | None
def _collect_passthrough_positional(
        args: list[ast.expr], vararg: ast.arg | None
) -> tuple[list[str], str | None] | None:
    positional: list[str] = []
    forwarded_vararg: str | None = None
    for arg in args:
        if isinstance(arg, ast.Name):
            if forwarded_vararg is not None:
                return None
            positional.append(arg.id)
        elif (isinstance(arg, ast.Starred) and isinstance(arg.value, ast.Name)
              and vararg is not None and arg.value.id == vararg.arg
              and forwarded_vararg is None):
            forwarded_vararg = arg.value.id
        else:
            return None
    return positional, forwarded_vararg
def _collect_passthrough_keywords(
        keywords: list[ast.keyword], kwarg: ast.arg | None
) -> tuple[list[tuple[str, str]], str | None] | None:
    named: list[tuple[str, str]] = []
    forwarded_kwarg: str | None = None
    for keyword in keywords:
        if not isinstance(keyword.value, ast.Name):
            return None
        if keyword.arg is not None:
            named.append((keyword.arg, keyword.value.id))
        elif (kwarg is not None and keyword.value.id == kwarg.arg
              and forwarded_kwarg is None):
            forwarded_kwarg = keyword.value.id
        else:
            return None
    return named, forwarded_kwarg
def _collect_passthrough_call(
        ret_val: ast.Call,
        vararg: ast.arg | None,
        kwarg: ast.arg | None) -> _PassthroughCall | None:
    positional = _collect_passthrough_positional(ret_val.args, vararg)
    keywords = _collect_passthrough_keywords(ret_val.keywords, kwarg)
    if positional is None or keywords is None:
        return None
    args, forwarded_vararg = positional
    named, forwarded_kwarg = keywords
    return _PassthroughCall(tuple(args), tuple(named),
                            forwarded_vararg, forwarded_kwarg)
def _callee_display(func: ast.AST) -> str:
    if isinstance(func, ast.Name):
        return func.id
    return _try_unparse(func) or '?'
def _passthrough_keywords_match(
        call: _PassthroughCall, remaining: list[str]) -> bool:
    keyword_values = [value for _key, value in call.keywords]
    if len(keyword_values) != len(remaining) or set(keyword_values) != set(remaining):
        return False
    same_name = all(key == value for key, value in call.keywords)
    return same_name or keyword_values == remaining
def _passthrough_signature_matches(
        call: _PassthroughCall,
        func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    if (func_node.args.defaults
            or any(default is not None
                   for default in func_node.args.kw_defaults)):
        return False
    func_args = _param_names(func_node)
    positional = list(call.positional)
    positional_params = [*func_node.args.posonlyargs, *func_node.args.args]
    positional_names = [param.arg for param in positional_params]
    if (len(positional) < len(func_node.args.posonlyargs)
            or positional != positional_names[:len(positional)]):
        return False
    if any(key in func_args and key != value
           for key, value in call.keywords):
        return False
    if not _passthrough_keywords_match(call, func_args[len(positional):]):
        return False
    vararg = func_node.args.vararg
    kwarg = func_node.args.kwarg
    expected_vararg = vararg.arg if vararg is not None else None
    expected_kwarg = kwarg.arg if kwarg is not None else None
    return call.vararg == expected_vararg and call.kwarg == expected_kwarg
def _detect_suspicious(name: str, ret_val: ast.AST | None,
                       func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[DelegationType, str] | None:
    if not isinstance(ret_val, ast.Call):
        return None
    if ast.get_docstring(func_node):
        return None
    if func_node.decorator_list:
        return None
    if _is_private_seam_callee(ret_val.func):
        return None
    call = _collect_passthrough_call(
        ret_val, func_node.args.vararg, func_node.args.kwarg)
    if call is None or not _passthrough_signature_matches(call, func_node):
        return None
    delegates_to = _callee_display(ret_val.func)
    return (DelegationType.SUSPICIOUS,
            (f'可疑纯透传委托: {name} → {delegates_to}()  '
             '(无变换、无校验、无副作用)'))
def _build_suspicious_issue(node: ast.FunctionDef | ast.AsyncFunctionDef,
                           reason: str,
                           filepath: str,
                           ret_val: ast.AST | None) -> dict[str, Any]:
    delegates_to = (_callee_display(ret_val.func)
                    if isinstance(ret_val, ast.Call) else '?')
    return {
        'id': 'D51', 'severity': 'P2', 'dimension': CAT_MAINTAINABILITY,
        'file': filepath, 'line': node.lineno, 'col_offset': node.col_offset,
        'message': f'可疑委托: {node.name}() → {delegates_to}()  ({reason})',
        'suggestion': '考虑内联调用方直接调用目标函数，或添加文档说明委托的架构原因',
        'function': node.name, 'delegates_to': delegates_to,
        'delegation_type': DelegationType.SUSPICIOUS.name, 'reason': reason,
    }
def _sole_return_value(effective: list[ast.stmt]) -> ast.AST | None:
    if len(effective) != 1 or not isinstance(effective[0], ast.Return):
        return None
    value = effective[0].value
    while isinstance(value, (ast.Await, ast.YieldFrom)):
        value = value.value
    return value
def _returned_call(effective: list[ast.stmt]) -> ast.Call | None:
    value = _sole_return_value(effective)
    return value if isinstance(value, ast.Call) else None
def _detect_return_patterns(name: str, effective: list,
                            func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                            index: _ModuleIndex) -> tuple[DelegationType, str] | None:
    result = _detect_factory_pattern(name, effective)
    if result is not None:
        return result
    ret_val = _sole_return_value(effective)
    for detector, ctx in (
            (_detect_cache_access, ()),
            (_detect_type_adapter, ()),
            (_detect_dict_dispatch, ()),
            (_detect_cross_package, (index,)),
            (_detect_sentinel, (func_node,)),
            (_detect_internal_delegate, (index,)),
            (_detect_suspicious, (func_node,)),
    ):
        result = detector(name, ret_val, *ctx)
        if result is not None:
            return result
    return None
def _classify_delegation(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                        source: ast.AST | _ModuleIndex,
                        effective: list[ast.stmt]
                        ) -> tuple[DelegationType, str]:
    index = _as_module_index(source)
    name = func_node.name
    for decorator in func_node.decorator_list:
        decorator_name = _decorator_label(decorator)
        if decorator_name in _TRANSPARENT_DECORATORS:
            return (DelegationType.INTERNAL_DELEGATE,
                    f'装饰器方法: {name} 使用@{decorator_name},豁免委托检测')
    result = _check_compat_alias(name, effective)
    if result:
        return result
    result = _detect_body_patterns(func_node, name, effective)
    if result:
        return result
    result = _detect_return_patterns(name, effective, func_node, index)
    if result:
        return result
    return (DelegationType.UNKNOWN, '无法分类（非简单委托模式）')
def _iter_delegation_candidates(tree: ast.AST):
    for node in _iter_function_nodes(tree):
        if is_dunder_name(node.name):
            continue
        effective = _effective_body(node)
        if effective:
            yield node, effective
def check_D51_delegation(code: str | ast.AST | None, filepath: str = _DEFAULT_FILEPATH,
                         tree: ast.AST | None = _DEFAULT_TREE) -> list[dict[str, Any]]:
    tree = _facade_tree(code, tree, filepath)
    if tree is None:
        return []
    issues = []
    index = _build_index(tree)
    for node, effective in _iter_delegation_candidates(tree):
        dtype, reason = _classify_delegation(node, index, effective)
        if dtype == DelegationType.SUSPICIOUS:
            issues.append(_build_suspicious_issue(
                node, reason, filepath, _sole_return_value(effective)))
    if issues:
        logger.info("[D51] 可疑委托命中: %s ×%d",
                  filepath or "<inline>", len(issues))
    return issues
_PF01_TYPE_RANK = {
    _TYPE_SUSPICIOUS: 0,
    _TYPE_THIN_WRAPPER: 1,
    _TYPE_THIN_REEXPORT: 2,
    _TYPE_ALL_REEXPORT: 3,
}
_PF01_SEVERITY = {
    _TYPE_SUSPICIOUS: "P2",
    _TYPE_THIN_WRAPPER: "P3",
    _TYPE_THIN_REEXPORT: "P3",
    _TYPE_ALL_REEXPORT: "P3",
}
def _pf01_type_of(item: dict) -> str:
    if item.get("delegation_type") == _TYPE_SUSPICIOUS:
        return _TYPE_SUSPICIOUS
    facade = str(item.get("facade_type") or "")
    if facade in _PF01_TYPE_RANK:
        return facade
    return _TYPE_THIN_WRAPPER
def _pf01_key(item: dict) -> tuple[int, str]:
    name = item.get("function") or item.get("source_name") or ""
    return int(item.get("line") or 0), str(name)
def _pf01_issue(item: dict) -> dict:
    dtype = _pf01_type_of(item)
    return {
        "id": "PF01",
        "rule_id": "PF01",
        "severity": _PF01_SEVERITY[dtype],
        "dimension": CAT_MAINTAINABILITY,
        "file": item.get("file", ""),
        "line": item.get("line", 0),
        "col_offset": item.get("col_offset", 0),
        "message": item.get("message", ""),
        "suggestion": item.get("suggestion", ""),
        "delegation_type": dtype,
        "function": item.get("function", ""),
        "delegates_to": (item.get("delegates_to")
                         or item.get("target_name") or ""),
        "source_rule": item.get("id", ""),
        "suppress_aliases": ("D50", "D51", "O04"),
    }
def check_PF01_pure_forward(code: str | ast.AST | None, filepath: str = _DEFAULT_FILEPATH,
                            tree: ast.AST | None = _DEFAULT_TREE) -> list[dict[str, Any]]:
    tree = _facade_tree(code, tree, filepath)
    if tree is None:
        return []
    merged: dict[tuple[int, str], list[dict]] = {}
    for item in check_D51_delegation(code, filepath, tree=tree):
        merged.setdefault(_pf01_key(item), []).append(item)
    for item in check_D50_facade(code, filepath, tree=tree):
        merged.setdefault(_pf01_key(item), []).append(item)
    issues = [
        _pf01_issue(min(items, key=lambda x: _PF01_TYPE_RANK[_pf01_type_of(x)]))
        for items in merged.values()
    ]
    issues.sort(key=lambda i: (i["line"], i["col_offset"]))
    if issues:
        logger.info("[PF01] 纯转发层命中: %s ×%d",
                  filepath or "<inline>", len(issues))
    return issues

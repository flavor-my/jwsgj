from __future__ import annotations

import ast
import io
import logging
import os
import pathlib
import re
import threading
import time
import tokenize
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any

from jwsgj.diag_shared_ast_bindings import (
    ScanContext,
    ScopeNameResolver,
    scope_key,
)
from jwsgj.diag_shared_ast_nodes import (
    _protocol_member_ids,
    ast_name,
    coerce_str,
    has_abstractmethod_decorator,
    is_placeholder_stmt,
)
from jwsgj.diag_shared_ast_views import (
    parent_map,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    decode_source_bytes,
    leading_quote_states,
    line_num_fast,
    line_start_offset,
    parse_or_none,
    parse_with_compile,
    read_source_interpreter_encoding,
    read_source_with_fingerprint,
    scan_line_quote_state,
)
from jwsgj.diag_shared_source_core import (
    parse_py_file as _parse_py_file,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
)
from jwsgj.diag_symbol_surface import (
    HallucinationFinding,
    detect_hallucinated_api,
    detect_hallucinated_import,
    is_dynamic_callback,
    is_private_name,
    star_import_exports,
)
from jwsgj.diag_testing_test_index import iter_collectable_test_functions
from jwsgj.diag_types_normalize import (
    is_finite_num,
    signal_bool,
    strip_bom,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_FINDING_CONFIDENCE,
    FUNC_CLAIM_RE,
    HALLUCINATION_RULE_IDS,
    LINE_CLAIM_RE,
    NORM_INDEX,
    ORDINAL_FUNC_RE,
    ORDINAL_LINE_RE,
    ORDINAL_PASS_RE,
    PARSE_DEGRADE_EXC,
    PASS_CLAIM_RE,
    PASS_SUFFIX_CLAIM_RE,
    SANDBOX_REFLECTION_FUNCS,
    HallucinationType,
    NormRule,
    NormSeverity,
    NormViolation,
    claim_number,
    first_quantity_claim,
)
from jwsgj.log_config import (
    log_swallowed,
    write_module_run,
)
from jwsgj.prevention_scope_facts import (
    is_irrefutable_pattern,
    walk_nodes,
)
from jwsgj.runtime_scope import (
    collect_scan_py_files,
    iter_diagnosis_scan_targets,
)

__all__ = [
    'HallucinationDetector',
    'HallucinationScanResult',
    'NormEngine',
    'boost_known_pattern_confidence',
    'check_hallucination_norms',
    'check_memory_ast_verified',
    'check_process_norms',
    'claim_norm_violations',
    'detect_ai_slop',
    'detect_context_contradiction',
    'detect_hallucinated_exception',
    'detect_memory_hallucination',
    'detect_new_p0_api_calls',
    'detect_sandbox_reflection',
    'detect_test_illusion',
    'escape_chain_reflect_arg',
    'get_norm_engine',
    'is_exec_escape_context',
    'mk_violation',
    'produce_cv_findings',
    'scan_code_violations',
    'scan_hallucinations',
    'verify_api_existence',
    'verify_code_against_norms',
    'verify_memory_against_norms',
]
logger = logging.getLogger(__name__)
_POISON_CONFIDENCE = 0.6
_DEFAULT_FILE_PATH = ""
_DEFAULT_MAX_VIOLATIONS = 3
_EMPTY_RULE_IDS: frozenset[str] = frozenset()
_TRY_NODE_TYPES = (ast.Try, getattr(ast, "TryStar", ast.Try))
def _real_body_stmts(body: list[ast.stmt]) -> list[ast.stmt]:
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[1:]
    return body
def _placeholder_body_stmt(body: list[ast.stmt]) -> ast.stmt | None:
    real_stmts = _real_body_stmts(body)
    if len(real_stmts) == 1 and is_placeholder_stmt(real_stmts[0]):
        return real_stmts[0]
    if not real_stmts and body:
        return body[0]
    return None
def _placeholder_label(stmt: ast.AST) -> str:
    if isinstance(stmt, ast.Pass):
        return "pass"
    if (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and isinstance(stmt.value.value, str)):
        return "docstring"
    return "..."
def _normalized_source(source_code: Any) -> str | None:
    if isinstance(source_code, (bytes, bytearray)):
        return decode_source_bytes(bytes(source_code))
    if not isinstance(source_code, str):
        return None
    return strip_bom(source_code)
def mk_violation(
    rule_id: str,
    detail: str,
    suggestion: str = "",
    file_path: str = _DEFAULT_FILE_PATH,
    line_num: int = 0,
    severity: str | None = None,
    description: str | None = None,
) -> NormViolation:
    rule_id = coerce_str(rule_id)
    detail = coerce_str(detail)
    suggestion = coerce_str(suggestion)
    file_path = coerce_str(file_path)
    severity = coerce_str(severity)
    description = coerce_str(description)
    norm = NORM_INDEX.get(rule_id)
    if norm is None:
        category = "U"
        severity = severity or NormSeverity.P1.value
        name = "未知铁律"
        description = description or (
            "规则元数据缺失：rule_id 不在 24 铁律 SSOT（HALLUCINATION_NORMS）中")
    else:
        category = norm.category.value
        severity = severity or norm.severity.value
        name = norm.name
        description = description or norm.description
    return NormViolation(
        rule_id=rule_id or "<unknown>",
        category=category,
        severity=severity,
        name=name,
        description=description,
        detail=detail,
        file_path=file_path,
        line_num=line_num,
        suggestion=suggestion,
    )
_DONE_MARKER_CN = ("已完成", "已实现", "已通过", "已修复")
_DONE_MARKER_EN = ("implemented", "completed", "resolved", "fixed", "done")
_NOT_DONE_PREFIX_GUARD = (
    r"(?i:(?<!not )(?<!never )(?<!not yet )"
    r"(?<!not fully )(?<!not completely ))"
)
_DONE_MARKER_PASS = _NOT_DONE_PREFIX_GUARD + r'(?i:PASSED|PASS)'
_DONE_MARKER_PATTERN = (
    "|".join(_DONE_MARKER_CN)
    + r"|(?<![0-9_a-zA-Z])" + _NOT_DONE_PREFIX_GUARD
    + r"(?i:" + "|".join(_DONE_MARKER_EN) + r")(?![0-9_a-zA-Z])"
    + rf"|(?<![_a-zA-Z]){_DONE_MARKER_PASS}(?![_a-zA-Z])"
)
_DONE_CLAIM_RE = re.compile(rf'(?:{_DONE_MARKER_PATTERN})')
_PLAN_CLAIM_RE = re.compile(
    r'(?:TODO|计划|待实现|将要|'
    r'(?i:(?<![a-z])(?:planned|to be implemented|wip|pending|'
    r'will (?:implement|add|fix))(?![a-z])))')
_CROSS_LANG_ATTR_MAP: dict[str, str] = {
    "length": "len(x)",
    "size": "len(x)",
    "push": ".append(x)",
    "startsWith": ".startswith(...)",
    "endsWith": ".endswith(...)",
    "toLowerCase": ".lower()",
    "toUpperCase": ".upper()",
    "charAt": "s[i]",
    "indexOf": ".find(...)/.index(...)",
    "substring": "s[a:b]",
    "isEmpty": "len(x) == 0",
    "containsKey": "key in d",
    "getOrDefault": "d.get(k, default)",
    "hashCode": "hash(...)",
    "equals": "== 比较",
    "toString": "str(...)",
    "trim": ".strip()",
    "replaceAll": ".replace(...)",
    "getSize": "len(...)",
    "parseInt": "int(...)",
}
_ATTR_HALLUCINATION_MODULES: dict[str, set[str]] = {}
_ATTR_HALLUCINATION_NORMED: dict[str, set[str]] = {}
def _norm_attr_name(name: str) -> str:
    return name.replace('_', '').casefold()
def _norm_attr_names(names: set[str]) -> set[str]:
    return {_norm_attr_name(name) for name in names
            if not name.startswith('_')}
def _attr_hallucination_method_sets() -> dict[str, set[str]]:
    if not _ATTR_HALLUCINATION_MODULES:
        modules = {
            "os.path": set(dir(os.path)),
            "pathlib.Path": set(dir(pathlib.Path)),
        }
        _ATTR_HALLUCINATION_NORMED.update(
            {k: _norm_attr_names(v) for k, v in modules.items()})
        _ATTR_HALLUCINATION_MODULES.update(modules)
    return _ATTR_HALLUCINATION_MODULES
def _levenshtein_le_1(a: str, b: str) -> bool:
    if abs(len(a) - len(b)) > 1:
        return False
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1] <= 1
def _is_resolvable_name(ctx: ScanContext, node: ast.Name,
                        resolver: ScopeNameResolver) -> bool:
    return node.id in ctx.builtins_ or resolver.is_bound(node)
def _g1_bare_name_violation(call_name: str, node: ast.Call,
                            ctx: ScanContext,
                            resolver: ScopeNameResolver) -> NormViolation | None:
    if _is_resolvable_name(ctx, node.func, resolver):
        return None
    if ctx.star_import_modules:
        return None
    if is_private_name(call_name):
        return mk_violation(
            "G1",
            detail=f"调用未定义的函数 '{call_name}'（_前缀私有名，可能为幻觉API）",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion=f"搜索相似函数名或添加导入: from module import {call_name}",
        )
    if (not call_name[0].isupper() and len(call_name) > 4
            and not is_dynamic_callback(call_name)):
        return mk_violation(
            "G1", severity="P1",
            detail=f"调用未定义的函数 '{call_name}'，可能为幻觉API",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion=f"验证 '{call_name}' 是否已定义/导入，或来自父类/装饰器/动态注入",
        )
    return None
def _g1_attr_base_violation(node: ast.Call,
                            ctx: ScanContext,
                            resolver: ScopeNameResolver) -> NormViolation | None:
    call_name = node.func.value.id
    if _is_resolvable_name(ctx, node.func.value, resolver):
        return None
    if ctx.star_import_modules:
        return None
    if is_private_name(call_name):
        return mk_violation(
            "G1",
            detail=f"调用 '{call_name}' 的基对象可能未定义（_前缀私有名）",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion=f"验证 '{call_name}' 是否在当前模块中定义或正确导入",
        )
    return None
def _import_path_at(ctx: ScanContext, node: ast.Name) -> str | None:
    resolver = ctx._scope_names
    if resolver is None:
        return ctx.alias_paths.get(node.id)
    return resolver.import_path(node)
def _module_path_at(ctx: ScanContext, node: ast.Name) -> str | None:
    import_path = _import_path_at(ctx, node)
    if import_path is not None:
        return import_path
    resolver = ctx._scope_names
    if resolver is not None and resolver.is_bound(node):
        return None
    return ctx.alias_paths.get(node.id, node.id)
def _dotted_import_path(node: ast.AST, ctx: ScanContext) -> str | None:
    parts: list[str] = []
    cur = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if not isinstance(cur, ast.Name):
        return None
    root = _import_path_at(ctx, cur)
    if root is None:
        return None
    parts.append(root)
    return ".".join(reversed(parts))
def _check_hallucinated_api_ctx(
    ctx: ScanContext, resolver: ScopeNameResolver,
) -> list[NormViolation]:
    violations: list[NormViolation] = []
    for node in ctx.all_calls:
        if isinstance(node.func, ast.Name):
            violation = _g1_bare_name_violation(node.func.id, node, ctx, resolver)
        elif isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
            violation = _g1_attr_base_violation(node, ctx, resolver)
        else:
            continue
        if violation is not None:
            violations.append(violation)
    return violations
def _g1_normalized_hit(mod_path: str, attr: str, mset: set[str],
                       normed_set: set[str], node: ast.Call,
                       ctx: ScanContext) -> NormViolation | None:
    norm_attr = _norm_attr_name(attr)
    if norm_attr not in normed_set:
        return None
    right = next((m for m in sorted(mset)
                  if not m.startswith('_') and _norm_attr_name(m) == norm_attr),
                 None)
    if right is None:
        return None
    return mk_violation(
        "G1", description="属性调用疑似标准库方法名形态错误",
        detail=f'{mod_path}.{attr} 不存在，正确写法是 .{right}()',
        file_path=ctx.file_path, line_num=node.lineno,
        suggestion=f'改为 {mod_path}.{right}(...)',
    )
def _g1_near_miss_hit(mod_path: str, attr: str, mset: set[str],
                      node: ast.Call,
                      ctx: ScanContext) -> NormViolation | None:
    if len(attr) < 4:
        return None
    near = next((m for m in sorted(mset)
                 if m != attr and _levenshtein_le_1(attr, m)), None)
    if not near:
        return None
    return mk_violation(
        "G1", description="属性调用与标准库方法拼写近似，疑似幻觉API",
        detail=f'{mod_path}.{attr} 不存在，最接近的是 .{near}',
        file_path=ctx.file_path, line_num=node.lineno,
        suggestion=f'确认并改为 {mod_path}.{near}(...)',
    )
def _bound_attribute_names(tree: ast.AST | None) -> set[str]:
    if tree is None:
        return set()
    return {
        node.attr for node in walk_nodes(tree)
        if isinstance(node, ast.Attribute)
        and isinstance(node.ctx, (ast.Store, ast.Del))}
def _attr_call_channel(ctx: ScanContext,
                       reported_call_func_ids: set[int],
                       bound_attrs: set[str]) -> list[NormViolation]:
    methods = _attr_hallucination_method_sets()
    normed = _ATTR_HALLUCINATION_NORMED
    violations: list[NormViolation] = []
    for node in ctx.all_calls:
        func = node.func
        if not isinstance(func, ast.Attribute):
            continue
        attr = func.attr
        mod_path = _resolve_attr_base(func, ctx, methods)
        violation = None
        if mod_path in methods:
            mset = methods[mod_path]
            if attr in mset:
                continue
            violation = (_g1_normalized_hit(mod_path, attr, mset,
                                            normed[mod_path], node, ctx)
                         or _g1_near_miss_hit(mod_path, attr, mset, node, ctx))
        elif (attr in _CROSS_LANG_ATTR_MAP and attr not in ctx.defined
              and attr not in bound_attrs):
            violation = mk_violation(
                "G1", severity="P1",
                description="疑似跨语言（JS/Java）习惯方法名直译，Python 无此方法",
                detail=f'.{attr} 应使用 Python 惯用写法: {_CROSS_LANG_ATTR_MAP[attr]}',
                file_path=ctx.file_path, line_num=node.lineno,
                suggestion=f'改用 {_CROSS_LANG_ATTR_MAP[attr]}',
            )
        if violation is not None:
            reported_call_func_ids.add(id(func))
            violations.append(violation)
    return violations
def _attr_access_channel(ctx: ScanContext,
                         reported_call_func_ids: set[int],
                         bound_attrs: set[str]) -> list[NormViolation]:
    violations: list[NormViolation] = []
    for node in ctx.attribute_nodes:
        if id(node) in reported_call_func_ids:
            continue
        if (node.attr != "length" or node.attr in ctx.defined
                or node.attr in bound_attrs
                or not isinstance(node.ctx, ast.Load)):
            continue
        violations.append(mk_violation(
            "G1", severity="P1",
            description="疑似跨语言（JS/Java）习惯属性名直译，Python 无此属性",
            detail=".length 应使用 Python 惯用写法: len(x)",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion="改用 len(x)",
        ))
    return violations
def _check_attr_hallucination_ctx(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    reported_call_func_ids: set[int] = set()
    bound_attrs = _bound_attribute_names(ctx.tree)
    violations.extend(_attr_call_channel(
        ctx, reported_call_func_ids, bound_attrs))
    violations.extend(_attr_access_channel(
        ctx, reported_call_func_ids, bound_attrs))
    return violations
def _resolve_ctor_base(value_call: ast.Call, ctx: ScanContext,
                       methods: dict[str, set[str]]) -> str | None:
    f = value_call.func
    if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
        mod = _module_path_at(ctx, f.value)
        if mod is None:
            return None
        cand = f"{mod}.{f.attr}"
        return cand if cand in methods else None
    if isinstance(f, ast.Name):
        mod = _import_path_at(ctx, f)
        if mod:
            return mod if mod in methods else None
    return None
def _resolve_attr_base(func: ast.Attribute, ctx: ScanContext,
                       methods: dict[str, set[str]]) -> str | None:
    v = func.value
    if isinstance(v, ast.Call):
        return _resolve_ctor_base(v, ctx, methods)
    parts: list[str] = []
    cur = v
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        root = _module_path_at(ctx, cur)
        if root is None:
            return None
        parts.append(root)
        path = ".".join(reversed(parts))
        return path if path in methods else None
    return None
def _check_except_pass_ctx(ctx: ScanContext,
                           comments: _CommentContext,
                           ) -> list[NormViolation]:
    violations: list[NormViolation] = []
    for node in ctx.except_handlers:
        stmt = _placeholder_body_stmt(node.body)
        if stmt is None:
            continue
        if (comments.is_suppressed(node.lineno)
                or comments.is_suppressed(stmt.lineno)):
            continue
        if comments.has_rationale(node):
            continue
        prefix = ("bare except" if node.type is None
                  else f"except {ast.unparse(node.type)}")
        form = _placeholder_label(stmt)
        violations.append(mk_violation(
            "G2",
            detail=f"{prefix}: {form} — 静默吞掉异常，可能隐藏幻觉错误",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion="改为: except SpecificError as e: logger.warning(f'...: {e}')",
        ))
    return violations
def _star_import_export_evidence(
    modules: list[str],
) -> tuple[set[str], bool]:
    exported: set[str] = set()
    unresolved = False
    for source in modules:
        level = len(source) - len(source.lstrip("."))
        exports = star_import_exports(source[level:], level)
        if exports is None:
            unresolved = True
        else:
            exported.update(exports)
    return exported, unresolved
def _check_star_import_underscore_ctx(
    ctx: ScanContext, resolver: ScopeNameResolver,
) -> list[NormViolation]:
    violations: list[NormViolation] = []
    if not ctx.star_import_modules:
        return violations
    first_use = _g3_first_underscore_uses(ctx, resolver)
    if not first_use:
        return violations
    exported, unresolved = _star_import_export_evidence(ctx.star_import_modules)
    for name, line in first_use.items():
        if unresolved or name in exported:
            continue
        violations.append(mk_violation(
            "G3",
            detail=f"使用 '{name}' 但星号导入模块的已解析导出面不包含该名称 (模块: {', '.join(ctx.star_import_modules)})",
            file_path=ctx.file_path, line_num=line,
            suggestion=f"改为显式导入: from {ctx.star_import_modules[0]} import {name}",
        ))
    return violations
def _g3_first_underscore_uses(
    ctx: ScanContext, resolver: ScopeNameResolver,
) -> dict[str, int]:
    first_use: dict[str, int] = {}
    for node in ctx.name_nodes:
        if not isinstance(node.ctx, ast.Load) or not is_private_name(node.id):
            continue
        if _is_resolvable_name(ctx, node, resolver):
            continue
        prev = first_use.get(node.id)
        if prev is None or node.lineno < prev:
            first_use[node.id] = node.lineno
    return first_use
_STRING_REFLECT_FUNCS = frozenset({"getattr", "setattr"})
_ESCAPE_CHAIN_MARKERS = ("__subclasses__", "__bases__", "__mro__")
def _h08_called_name(node: ast.Call,
                     ctx: ScanContext | None = None) -> str | None:
    func = node.func
    if isinstance(func, ast.Name):
        if ctx is None:
            return func.id
        alias_path = _import_path_at(ctx, func)
        if alias_path is not None:
            return (alias_path.removeprefix("builtins.")
                    if alias_path.startswith("builtins.") else None)
        resolver = ctx._scope_names
        if resolver is not None and resolver.is_bound(func):
            return None
        return func.id
    if (ctx is not None and isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and _import_path_at(ctx, func.value) == "builtins"):
        return func.attr
    return None
def escape_chain_reflect_arg(node: ast.Call,
                             ctx: ScanContext | None = None) -> str | None:
    if _h08_called_name(node, ctx) not in _STRING_REFLECT_FUNCS:
        return None
    second_arg = (node.args[1] if len(node.args) >= 2 else next(
        (keyword.value for keyword in node.keywords if keyword.arg == "name"),
        None))
    if not (isinstance(second_arg, ast.Constant)
            and isinstance(second_arg.value, str)):
        return None
    value = second_arg.value
    return value if any(m in value for m in _ESCAPE_CHAIN_MARKERS) else None
def is_exec_escape_context(ctx: ScanContext, line: int | ast.AST,
                            cache: dict[int, bool] | None = None) -> bool:
    cache_key = id(line) if isinstance(line, ast.AST) else line
    if cache is not None:
        cached = cache.get(cache_key)
        if cached is not None:
            return cached
    owner = (ctx.enclosing_exec_scope(line) if isinstance(line, ast.AST)
             else ctx.innermost_func_owner(line))
    result = scope_key(owner) in ctx.exec_scope_keys
    if cache is not None:
        cache[cache_key] = result
    return result
def _h08_call_findings(all_calls: list[ast.Call],
                       is_escape_context: Callable[[ast.AST], bool],
                       file_path: str,
                       ctx: ScanContext | None = None) -> list[HallucinationFinding]:
    out = []
    for node in all_calls:
        if not is_escape_context(node):
            continue
        called = _h08_called_name(node, ctx)
        dangerous_arg = escape_chain_reflect_arg(node, ctx)
        if dangerous_arg is not None:
            out.append(_h08_string_reflect_finding(
                node, called, dangerous_arg, file_path))
        elif called in SANDBOX_REFLECTION_FUNCS:
            out.append(_h08_reflect_name_finding(node, called, file_path))
    return out
def _h08_subclasses_attr_findings(all_attributes: list[ast.Attribute],
                                  is_escape_context: Callable[[ast.AST], bool],
                                  file_path: str) -> list[HallucinationFinding]:
    return [_h08_subclasses_attr_finding(node, file_path)
            for node in all_attributes
            if node.attr == "__subclasses__"
            and is_escape_context(node)]
def _norms_finding(rule_id: str, htype: str, *, severity: str, title: str,
                   description: str, confidence: float, suggestion: str,
                   evidence: str, file_path: str,
                   line: int = 0) -> HallucinationFinding:
    return HallucinationFinding(
        rule_id=rule_id, hallucination_type=htype, severity=severity,
        title=title, description=description, file_path=file_path,
        line_num=line, confidence=confidence, suggestion=suggestion,
        evidence=evidence)
def _h08_reflect_name_finding(node: ast.Call, func_name: str,
                              file_path: str) -> HallucinationFinding:
    return _norms_finding(
        "H08", HallucinationType.SECURITY.value, severity="P0",
        title=f"沙箱反射链: exec/eval 上下文中使用 '{func_name}' 可导致逃逸",
        description=f"反射函数 '{func_name}' 在exec/eval上下文中可通过 __subclasses__ 链逃逸沙箱。",
        confidence=0.85,
        suggestion=f"在沙箱代码中移除 {func_name} 调用，使用AST拦截替代",
        evidence=(f"ast.Call func=Name('{func_name}') at line {node.lineno}, "
                  "in_exec_context=True"),
        line=node.lineno,
        file_path=file_path,
    )
def _h08_subclasses_attr_finding(node: ast.Attribute, file_path: str) -> HallucinationFinding:
    return _norms_finding(
        "H08", HallucinationType.SECURITY.value, severity="P0",
        title="沙箱反射链: 使用 __subclasses__ 可逃逸沙箱",
        description="__subclasses__ 链是已知的沙箱逃逸路径。",
        confidence=0.95,
        suggestion="移除 __subclasses__ 调用，使用白名单替代",
        evidence=f"ast.Attribute(attr='__subclasses__') at line {node.lineno}",
        line=node.lineno,
        file_path=file_path,
    )
def _h08_string_reflect_finding(node: ast.Call, func_name: str,
                                dangerous_arg: str,
                                file_path: str) -> HallucinationFinding:
    return _norms_finding(
        "H08", HallucinationType.SECURITY.value, severity="P0",
        title=f"沙箱反射链: {func_name}() 使用 '{dangerous_arg}' 可逃逸沙箱",
        description=(f"通过 {func_name}() 传递 '{dangerous_arg}' 字符串是"
                     "已知的沙箱逃逸路径。"),
        confidence=0.9,
        suggestion=f"移除 {func_name}() 中的 '{dangerous_arg}' 参数",
        evidence=(f"ast.Call(func=Name('{func_name}'), "
                  f"{'args[1]' if len(node.args) >= 2 else 'keyword name'}="
                  f"Constant('{dangerous_arg}')) at line {node.lineno}"),
        line=node.lineno,
        file_path=file_path,
    )
def _prepare_detection(
    source_code: Any, file_path: Any, _tree: ast.AST | None,
) -> tuple[str, str, ast.AST] | None:
    normalized = _normalized_source(source_code)
    if normalized is None:
        return None
    tree = parse_or_none(normalized, _tree)
    if tree is None:
        return None
    return normalized, coerce_str(file_path), tree
def detect_sandbox_reflection(
    source_code: str,
    file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    prepared = _prepare_detection(source_code, file_path, _tree)
    if prepared is None:
        return []
    source_code, file_path, tree = prepared
    ctx = ScanContext(source_code, file_path, _tree=tree)
    if not ctx.exec_scope_keys:
        return []
    _escape_by_node: dict[int, bool] = {}
    def _is_escape_context(node: ast.AST) -> bool:
        return is_exec_escape_context(ctx, node, _escape_by_node)
    findings: list[HallucinationFinding] = []
    findings.extend(_h08_call_findings(ctx.all_calls, _is_escape_context,
                                       file_path, ctx))
    findings.extend(_h08_subclasses_attr_findings(ctx.attribute_nodes,
                                                  _is_escape_context, file_path))
    return findings
def _g7_reflection_call_violations(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    escape_cache: dict[int, bool] = {}
    for node in ctx.all_calls:
        func_name = _h08_called_name(node, ctx)
        if func_name not in SANDBOX_REFLECTION_FUNCS:
            continue
        if not is_exec_escape_context(ctx, node, escape_cache):
            continue
        dangerous_arg = escape_chain_reflect_arg(node, ctx)
        if dangerous_arg is not None:
            violations.append(mk_violation(
                "G7",
                detail=(f"{func_name}() 使用 '{dangerous_arg}' 字符串访问逃逸链，"
                        "可绕过属性限制取得危险对象"),
                file_path=ctx.file_path, line_num=node.lineno,
                suggestion=(f"移除 {func_name}() 中的 '{dangerous_arg}' 参数，"
                            "改用静态属性访问或白名单校验"),
            ))
            continue
        violations.append(mk_violation(
            "G7",
            detail=f"反射函数 '{func_name}' 在exec/eval上下文中可通过 __subclasses__ 链逃逸沙箱",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion=f"移除 {func_name} 调用，使用AST拦截替代",
        ))
    return violations
def _g7_subclasses_violations(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    for node in ctx.attribute_nodes:
        if node.attr != "__subclasses__":
            continue
        if not is_exec_escape_context(ctx, node):
            continue
        violations.append(mk_violation(
            "G7", description="__subclasses__链是已知的沙箱逃逸路径",
            detail="__subclasses__ 可遍历所有子类获取危险对象，即使移除__import__仍可逃逸",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion="移除 __subclasses__ 调用，使用白名单替代",
        ))
    return violations
def _check_sandbox_reflection_ctx(ctx: ScanContext) -> list[NormViolation]:
    if not ctx.exec_scope_keys:
        return []
    violations = _g7_reflection_call_violations(ctx)
    violations.extend(_g7_subclasses_violations(ctx))
    return violations
def _compile_failure_violation(ctx: ScanContext) -> NormViolation | None:
    if ctx.compile_ok:
        return None
    e = ctx.compile_error
    _emsg = getattr(e, "msg", None) or str(e)
    _eline = getattr(e, "lineno", None) or 0
    return mk_violation(
        "V1",
        detail=f"compile失败: {_emsg} (行 {_eline})",
        file_path=ctx.file_path, line_num=_eline,
    )
def _check_compile_ctx(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    compile_violation = _compile_failure_violation(ctx)
    if compile_violation is not None:
        violations.append(compile_violation)
    for line_no, call_name in ctx.bare_ast_parse_calls:
        alias_note = "" if call_name == "ast.parse" else f"（别名 {call_name}）"
        violations.append(mk_violation(
            "V1",
            detail=(f"检测到裸 ast.parse() 调用(行{line_no})用于语法验证"
                    f"{alias_note}，应使用 compile(src, name, 'exec')"),
            file_path=ctx.file_path, line_num=line_no,
            suggestion="将 ast.parse(source) 替换为 compile(source, name, 'exec')，或使用 parse_with_compile",
        ))
    return violations
def _check_ai_slop_ctx(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    collectable_tests = _collectable_test_nodes(ctx.tree)
    protocol_members = (_protocol_member_ids(ctx.tree)
                        if isinstance(ctx.tree, ast.Module) else set())
    for node in ctx.pass_only_funcs:
        if id(node) in protocol_members:
            continue
        if node in collectable_tests:
            continue
        if _docstring_declares_noop(node.body):
            continue
        violations.append(mk_violation(
            "G6",
            detail=f"函数 '{node.name}' 仅含占位语句（pass/...），可能为AI Slop",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion="实现函数逻辑或标记为abstract/TODO",
        ))
    return violations
def _is_verification_callsite(node: ast.Call) -> bool:
    if isinstance(node.func, ast.Name):
        name = node.func.id
        return (name in ("compile", "raises", "main")
                or (name.startswith("assert") and len(name) > len("assert")))
    if not isinstance(node.func, ast.Attribute):
        return False
    if node.func.attr.startswith("assert"):
        return True
    return (node.func.attr in ("raises", "main")
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in ("pytest", "unittest"))
def _g4_has_verification(ctx: ScanContext) -> bool:
    has_assert_stmt = (ctx.tree is not None and any(
        isinstance(node, ast.Assert) for node in walk_nodes(ctx.tree)))
    return has_assert_stmt or any(
        _is_verification_callsite(node) for node in ctx.all_calls)
def _check_non_executable_ctx(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    func_count = len(ctx.all_funcs)
    if not func_count:
        return violations
    if ctx.all_declarations:
        return violations
    if not _g4_has_verification(ctx) and not ctx.has_main_guard:
        violations.append(mk_violation(
            "G4",
            detail=f"文件定义了{func_count}个函数但无测试/assert/main守卫，代码可能未经验证",
            file_path=ctx.file_path, line_num=1,
            suggestion="添加测试函数(test_xxx)或if __name__=='__main__'执行入口或assert验证",
        ))
    return violations
_V3_EXCLUDED_NAMES = frozenset({
    "__init__", "__main__", "main", "setUp", "tearDown",
    "setUpClass", "tearDownClass", "setUpModule", "tearDownModule",
    "setup_module", "teardown_module", "setup_function", "teardown_function",
})
def _v3_is_reportable_top_level(ctx: ScanContext,
                                node: ast.FunctionDef | ast.AsyncFunctionDef,
                                declarations: set[str]) -> bool:
    name = node.name
    if name in _V3_EXCLUDED_NAMES or name.startswith(("_", "test_")):
        return False
    if ctx.referenced_outside_own_scope(node):
        return False
    if name in declarations:
        return False
    return not node.decorator_list
def _check_verify_caller_ctx(ctx: ScanContext) -> list[NormViolation]:
    violations: list[NormViolation] = []
    if ctx.tree is None:
        return violations
    for node in ctx.tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not _v3_is_reportable_top_level(ctx, node, ctx.all_declarations):
            continue
        violations.append(mk_violation(
            "V3",
            detail=f"顶层函数 '{node.name}' 定义但未被调用且未在 __all__ 声明",
            file_path=ctx.file_path, line_num=node.lineno,
            suggestion=f"验证 '{node.name}' 是否被外部模块调用（可加入 __all__ 声明）或删除",
        ))
    return violations
def _claim_memory_rule_id(done_markers: list[str], has_code: bool) -> str:
    return "M4" if has_code and not done_markers else "M1"
def _memory_norm_violations(
    claim: str, code_source: str | bytes, file_path: str,
    *, _tree: ast.AST | None = None,
) -> list[NormViolation]:
    claim_text = coerce_str(claim)
    if not claim_text:
        return []
    normalized_code = _normalized_source(code_source)
    done_markers = _DONE_CLAIM_RE.findall(claim_text)
    if done_markers:
        if normalized_code:
            parsed_tree, tree_error = _h07_resolve_tree(normalized_code, _tree)
            if tree_error is None:
                _tree = parsed_tree
        if not normalized_code or (
                isinstance(_tree, ast.Module) and not _tree.body):
            return [mk_violation(
                "M1",
                detail=f"声明中包含完成态标记({', '.join(done_markers[:3])})但未提供code_source进行AST验证",
                file_path=file_path,
                suggestion="记录'已实现'前必须执行ast.walk/compile验证，并传入code_source供M1检查",
            )]
    rule_id = _claim_memory_rule_id(done_markers, bool(normalized_code))
    findings = detect_memory_hallucination(
        claim_text, normalized_code if normalized_code is not None else "",
        file_path, _tree=_tree)
    return [
        mk_violation(
            rule_id if f.rule_id == "H07" else f.rule_id,
            detail=f.title or f.description,
            suggestion=f.suggestion,
            file_path=f.file_path or file_path,
            line_num=f.line_num,
            severity=f.severity,
        )
        for f in findings
    ]
def check_memory_ast_verified(
    claim_text: str = "", code_source: str | bytes = "",
    file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
) -> NormViolation | None:
    violations = _memory_norm_violations(
        claim_text, code_source, file_path, _tree=_tree)
    return violations[0] if violations else None
def _extract_comment_hits(source_code: str) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source_code).readline):
            if tok.type == tokenize.COMMENT:
                row, col = tok.start
                if row > 0:
                    hits.append(
                        (line_start_offset(source_code, row) + col, tok.string))
        return hits
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as _e:
        log_swallowed(__name__, _e,
                       context='_extract_comment_hits:tokenize')
        return hits
def _claim_span_to_line_end(src: str, start: int) -> tuple[int, int]:
    ends = [i for i in (src.find("\n", start), src.find("\r", start)) if i >= 0]
    return (start, min(ends) if ends else len(src))
def _span_hit(start: int, end: int, spans: list[tuple[int, int]]) -> bool:
    return start >= 0 and any(s < end and start < e for s, e in spans)
def _claim_comment_parts(comment_hits: list[tuple[int, str]],
                         mask_spans: list[tuple[int, int]]) -> list[str]:
    return [text for start, text in comment_hits
            if not _span_hit(start, start + 1, mask_spans)]
def _claim_docstring_parts(
    source_code: str, docstrings: list[tuple[str, int]] | None,
    mask_spans: list[tuple[int, int]],
    literals: dict[tuple[str, int], tuple[int, str]] | None = None,
) -> list[str]:
    parts: list[str] = []
    for doc_text, doc_line in (docstrings or []):
        if not doc_text:
            continue
        literal = (literals or {}).get((doc_text, doc_line))
        if literal is not None:
            rel, raw_literal = literal
            rel_end = rel + len(raw_literal)
        else:
            rel = _locate_docstring(source_code, doc_text, doc_line)
            rel_end = rel + len(doc_text)
        if _span_hit(rel, rel_end, mask_spans):
            continue
        if rel < 0 and _docstring_claim_marker(doc_text):
            continue
        parts.append(doc_text)
    return parts
def _locate_docstring(source_code: str, doc_text: str, doc_line: int) -> int:
    return source_code.find(doc_text, line_start_offset(source_code, doc_line))
def _docstring_literals(
    source_code: str, tree: ast.AST | None,
) -> dict[tuple[str, int], tuple[int, str]]:
    if not isinstance(tree, ast.AST):
        return {}
    literals: dict[tuple[str, int], tuple[int, str]] = {}
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Expr)
                and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str)):
            continue
        raw = ast.get_source_segment(source_code, node.value)
        if not raw:
            continue
        line = getattr(node.value, "lineno", 0) or 0
        start = source_code.find(raw, line_start_offset(source_code, line))
        if start >= 0:
            literals[(node.value.value, line)] = (start, raw)
    return literals
def _extract_claim_text(source_code: str,
                        docstrings: list[tuple[str, int]] | None,
                        mask_spans: list[tuple[int, int]],
                        comment_hits: list[tuple[int, str]] | None = None,
                        literals: dict[tuple[str, int], tuple[int, str]] | None = None,
                        ) -> str:
    if comment_hits is None:
        comment_hits = _extract_comment_hits(source_code)
    parts = _claim_comment_parts(comment_hits, mask_spans)
    parts.extend(_claim_docstring_parts(
        source_code, docstrings, mask_spans, literals=literals))
    return "\n".join(parts)
_COMMENT_CLAIM_PATTERN = rf'(?:{_DONE_MARKER_PATTERN})'
def _comment_claim_finds(
        source_code: str,
        comment_hits: list[tuple[int, str]] | None = None,
) -> list[tuple[int, str]]:
    if comment_hits is None:
        comment_hits = _extract_comment_hits(source_code)
    findings: list[tuple[int, str]] = []
    for comment_start, comment_text in comment_hits:
        body = comment_text[1:].lstrip()
        content_offset = len(comment_text) - len(body)
        match = next(
            (matched for pattern in (_COMMENT_CLAIM_PATTERN,
                                     *_G5_CLAIM_PATTERNS)
             if (matched := re.match(pattern, body)) is not None),
            None)
        if match is not None:
            findings.append((
                comment_start + content_offset + match.start(),
                comment_text[:content_offset + match.end()],
            ))
    return findings
_G5_CLAIM_PATTERNS = (
    rf'本(?:模块|文件|类|函数)[^。\n]{{0,30}}(?:{_DONE_MARKER_PATTERN})',
    rf'(?:{_DONE_MARKER_PATTERN})\s*\d+\s*(?:个|项|条|处|测试)',
    rf'(?<![_a-zA-Z])\d+\s*(?:个)?\s*{_DONE_MARKER_PASS}(?![_a-zA-Z])',
    rf'(?<![_a-zA-Z]){_DONE_MARKER_PASS}(?![_a-zA-Z])\s*\d+',
    (r'(?i:this|the)\s+(?:module|file|class|function)\s+'
     r'[^.\n]{0,40}?\b' + _NOT_DONE_PREFIX_GUARD
     + r'(?:implements|implemented|completes|completed)\b'),
    (r'(?i)\b' + _NOT_DONE_PREFIX_GUARD
     + r'(?:implemented|completed|verified|passed)\s+'
     r'\d+\s*(?:items?|tests?|cases?|functions?)\b'),
    r'(?i)\b\d+\s*(?:tests?|cases?)\s+passed\b',
)
def _docstring_claim_marker(doc_text: str) -> re.Match[str] | None:
    m = None
    for pat in _G5_CLAIM_PATTERNS:
        m = re.search(pat, doc_text)
        if m:
            break
    return m
def _g5_docstring_channel(
    source_code: str, file_path: str,
    docstrings: list[tuple[str, int]] | None,
    spans: list[tuple[int, int]],
    literals: dict[tuple[str, int], tuple[int, str]] | None = None,
) -> list[NormViolation]:
    violations: list[NormViolation] = []
    for doc_text, doc_line in (docstrings or []):
        if not doc_text:
            continue
        m = _docstring_claim_marker(doc_text)
        if not m:
            continue
        inner_line = doc_text[:m.start()].count('\n')
        line_num = doc_line + inner_line
        literal = (literals or {}).get((doc_text, doc_line))
        raw_match = None
        if literal is not None:
            rel, raw_literal = literal
            raw_match = next(
                (match for pattern in _G5_CLAIM_PATTERNS
                 if (match := re.search(pattern, raw_literal)) is not None),
                None)
            if raw_match is not None:
                line_num = doc_line + raw_literal[:raw_match.start()].count('\n')
                spans.append(_claim_span_to_line_end(
                    source_code, rel + raw_match.start()))
            else:
                spans.append((rel, rel + len(raw_literal)))
        else:
            rel = _locate_docstring(source_code, doc_text, doc_line)
        if literal is None and rel >= 0:
            spans.append(
                _claim_span_to_line_end(source_code, rel + m.start()))
        violations.append(mk_violation(
            "G5",
            detail=f"docstring中的完成声明无执行证据: {m.group()[:40]}",
            file_path=file_path, line_num=line_num,
            suggestion="添加ast.walk验证或pytest执行证据后再声明'已完成'",
        ))
    return violations
def _check_unverified_claim(source_code: str, file_path: str = _DEFAULT_FILE_PATH,
                             docstrings: list[tuple[str, int]] | None = None,
                             comment_hits: list[tuple[int, str]] | None = None,
                             literals: dict[tuple[str, int], tuple[int, str]] | None = None,
                             ) -> tuple[list[NormViolation], list[tuple[int, int]]]:
    violations: list[NormViolation] = []
    spans: list[tuple[int, int]] = []
    for hit_start, hit_text in _comment_claim_finds(source_code, comment_hits):
        line_num = line_num_fast(source_code, hit_start)
        spans.append(_claim_span_to_line_end(source_code, hit_start))
        violations.append(mk_violation(
            "G5",
            detail=f"已实现声明无执行证据: {hit_text[:60]}",
            file_path=file_path, line_num=line_num,
            suggestion="添加ast.walk验证或pytest执行证据后再声明'已完成'",
        ))
    violations.extend(_g5_docstring_channel(
        source_code, file_path, docstrings, spans, literals=literals))
    return violations, spans
def scan_code_violations(ctx: ScanContext,
                         source_code: str) -> list[NormViolation]:
    violations: list[NormViolation] = []
    resolver = ScopeNameResolver(
        source_code, ctx.file_path, ctx.tree,
        ctx.defined | ctx.imported | ctx.builtins_)
    violations.extend(_check_hallucinated_api_ctx(ctx, resolver))
    violations.extend(_check_attr_hallucination_ctx(ctx))
    comments = _comment_scan(source_code)
    violations.extend(_check_except_pass_ctx(ctx, comments))
    violations.extend(_check_star_import_underscore_ctx(ctx, resolver))
    violations.extend(_check_sandbox_reflection_ctx(ctx))
    violations.extend(_check_compile_ctx(ctx))
    comment_hits = _extract_comment_hits(source_code)
    docstring_literals = _docstring_literals(source_code, ctx.tree)
    g5_violations, g5_spans = _check_unverified_claim(
        source_code, ctx.file_path, docstrings=ctx.docstrings,
        comment_hits=comment_hits, literals=docstring_literals)
    violations.extend(g5_violations)
    violations.extend(_check_ai_slop_ctx(ctx))
    violations.extend(_check_non_executable_ctx(ctx))
    violations.extend(_check_verify_caller_ctx(ctx))
    memory_violation = check_memory_ast_verified(
        _extract_claim_text(source_code, ctx.docstrings, g5_spans,
                            comment_hits=comment_hits,
                            literals=docstring_literals),
        source_code, ctx.file_path, _tree=ctx.tree)
    if memory_violation:
        violations.append(memory_violation)
    return violations
def verify_memory_against_norms(
    claim: str, code_source: str | bytes, file_path: str = _DEFAULT_FILE_PATH
) -> dict[str, Any]:
    claim = coerce_str(claim)
    violations = _memory_norm_violations(claim, code_source, file_path)
    return {
        "status": "ok" if not violations else "violations",
        "violations": [
            {key: value for key, value in v.as_dict().items()
             if key != "description"}
            for v in violations
        ],
        "claim": claim,
    }
def _claim_state_markers(claim_text: str) -> tuple[list[str], list[str]]:
    return (_PLAN_CLAIM_RE.findall(claim_text),
            _DONE_CLAIM_RE.findall(claim_text))
def _check_claim_text_norms(
    claim_text: str, file_path: str = _DEFAULT_FILE_PATH,
) -> list[NormViolation]:
    violations: list[NormViolation] = []
    claim_text = coerce_str(claim_text)
    if not claim_text:
        return violations
    plan_markers, done_markers = _claim_state_markers(claim_text)
    if plan_markers and done_markers:
        violations.append(mk_violation(
            "M2",
            detail="声明中同时包含计划态和完成态标记，可能混淆",
            file_path=file_path,
            suggestion="明确区分: 计划态用TODO标记，完成态含可验证量化指标",
        ))
    if not re.search(r'\d+', claim_text):
        violations.append(mk_violation(
            "M3",
            detail="声明中无量化的校验锚点(数字指标)",
            file_path=file_path,
            suggestion="在summary中加入行数/函数数/PASS数等可验证的量化指标",
        ))
    return violations
def claim_norm_violations(claim_text: str, code_source: str,
                           file_path: str) -> list[NormViolation]:
    violations = list(_memory_norm_violations(
        claim_text, code_source, file_path))
    violations.extend(_check_claim_text_norms(claim_text, file_path))
    return violations
def _build_test_result_norm_index(test_results) -> dict[str, dict[str, Any]]:
    norm_index: dict[str, dict[str, Any]] = {}
    if test_results:
        for _k, _v in test_results.items():
            if isinstance(_k, str):
                norm_index[os.path.normcase(os.path.normpath(_k))] = _v
    return norm_index
def _lookup_test_result(test_results, norm_index, py_file: str):
    if not test_results:
        return None
    if py_file in test_results:
        return test_results[py_file]
    return norm_index.get(os.path.normcase(os.path.normpath(py_file)))
def _read_scan_source(file_path: str, started: float) -> str | None:
    source_code, _ = read_source_with_fingerprint(file_path)
    if source_code is not None:
        return source_code
    logger.warning("无法读取文件 %s", file_path)
    write_module_run(
        "hallucination_norms", "scan_file",
        outcome="read_failed",
        duration_ms=(time.monotonic() - started) * 1000.0)
    return None
def _parse_scan_tree(source_code: str, file_path: str,
                     started: float) -> ast.AST | None:
    try:
        return parse_with_compile(source_code, file_path or "<scan>")
    except PARSE_DEGRADE_EXC as e:
        logger.warning("scan 预解析失败(语法错误/超深嵌套)，跳过全部检测器: %s", e)
        write_module_run(
            "hallucination_norms", "scan_file",
            outcome="parse_failed",
            duration_ms=(time.monotonic() - started) * 1000.0)
        return None
_HALLU_STACK_EXHAUSTED = object()
_SUPPRESS_MARK_RE = re.compile(r"#\s*(?:noqa|nosec)\b", re.IGNORECASE)
_FINDING_TEXT_LIMIT = 120
_H04_EVIDENCE_MAX_ITEMS = 4
_H04_NON_CONCRETE_TYPES = frozenset({"unknown", "None"})
@dataclass(frozen=True)
class _DeletionEvidenceSpec:
    rule_id: str
    hallucination_type: str
    label: str
    obj_desc: str
    suggestion: str
_H05_DELETION_SPEC = _DeletionEvidenceSpec(
    "H05", HallucinationType.AI_SLOP.value, "AI Slop", "函数",
    suggestion="删除该函数")
_H06_DELETION_SPEC = _DeletionEvidenceSpec(
    "H06", HallucinationType.TEST_ILLUSION.value, "测试幻觉", "测试函数",
    suggestion="重写该测试以验证被测函数的真实行为，或删除无效测试")
def _deletion_evidence_findings(
    test_result: dict[str, Any] | None,
    spec: _DeletionEvidenceSpec,
    file_path: str = _DEFAULT_FILE_PATH,
    *,
    eligible_names: set[str] | frozenset[str],
) -> list[HallucinationFinding]:
    findings: list[HallucinationFinding] = []
    if not (test_result and isinstance(test_result, dict)):
        return findings
    for func_name, result in test_result.items():
        if func_name not in eligible_names:
            continue
        if (isinstance(result, dict)
                and signal_bool(result.get("tests_passed_after_deletion", False))):
            findings.append(HallucinationFinding(
                rule_id=spec.rule_id,
                hallucination_type=spec.hallucination_type,
                severity="P1",
                title=(f"{spec.label}: 删除{spec.obj_desc} '{func_name}'"
                       " 后测试仍全部通过"),
                description=(f"删除{spec.obj_desc} '{func_name}' 后测试套件全部通过，"
                             "说明其无实质功能/验证价值。"),
                file_path=file_path,
                line_num=0,
                confidence=0.95,
                suggestion=spec.suggestion,
                evidence=f"Deletion test: tests_passed_after_deletion=True for '{func_name}'",
            ))
    return findings
def _repr_limited(value: Any) -> str:
    try:
        text = ast.unparse(value) if isinstance(value, ast.AST) else repr(value)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_repr_limited:Exc')
        text = "<unparse-failed>"
    if len(text) > _FINDING_TEXT_LIMIT:
        text = text[:_FINDING_TEXT_LIMIT] + "...<截断>"
    return text
_BROAD_EXCEPT_PATHS = frozenset({
    "Exception", "BaseException",
    "builtins.Exception", "builtins.BaseException",
})
def _is_broad_except_handler(
    handler: ast.ExceptHandler, ctx: ScanContext | None = None,
) -> bool:
    if handler.type is None:
        return True
    _t = handler.type
    _elts = _t.elts if isinstance(_t, ast.Tuple) else [_t]
    for _e in _elts:
        _type_src = ast.unparse(_e)
        if _type_src in _BROAD_EXCEPT_PATHS:
            return True
        if (ctx is not None
                and _dotted_import_path(_e, ctx) in _BROAD_EXCEPT_PATHS):
            return True
    return False
_LOG_METHOD_NAMES = frozenset({
    'warning', 'error', 'debug', 'info', 'critical', 'exception', 'log', 'msg',
})
_LOGGER_GETTER_NAMES = frozenset({'getLogger'})
_LOG_BASE_WORDS = frozenset({'log', 'logger', 'logging'})
def _has_logger_semantic_name(name: str) -> bool:
    if not name:
        return False
    words = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", name).lower().split("_")
    return any(word in _LOG_BASE_WORDS for word in words)
def _is_logger_receiver(base: ast.AST) -> bool:
    if isinstance(base, ast.Call):
        return ast_name(base.func) in _LOGGER_GETTER_NAMES
    return _has_logger_semantic_name(ast_name(base))
def _is_logging_call(node) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if isinstance(node.func, ast.Name):
        return node.func.id == 'print'
    return (isinstance(node.func, ast.Attribute)
            and node.func.attr in _LOG_METHOD_NAMES
            and _is_logger_receiver(node.func.value))
_NESTED_SCOPE_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
)
_H03_NESTED_SCOPE_NODES = (ast.ExceptHandler, *_NESTED_SCOPE_NODES)
def _walk_own_scope(body: list[ast.stmt],
                    nested: tuple[type[ast.AST], ...]):
    stack = list(reversed(body))
    while stack:
        node = stack.pop()
        if isinstance(node, nested):
            continue
        yield node
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _h03_nonempty_literal_iter(node: ast.expr) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return bool(node.elts) and all(
            not isinstance(elt, ast.Starred) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return bool(node.keys) and all(key is not None for key in node.keys)
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))
def _h03_loop_entry_facts(stmt: ast.stmt) -> tuple[bool, bool]:
    """返回 (循环体可能一次都不执行, 循环可能正常耗尽)。

    ``while True:`` 必然进入循环体且只能经 break/return/raise 离开；
    非空字面量可迭代对象的 for 必然至少执行一次。
    """
    if isinstance(stmt, ast.While):
        constant_true = (isinstance(stmt.test, ast.Constant)
                         and bool(stmt.test.value))
        return not constant_true, not constant_true
    return not _h03_nonempty_literal_iter(stmt.iter), True
def _h03_scan_logging(
    body: list[ast.stmt], states: frozenset[bool],
    unlogged: list[ast.Return],
    breaks: set[frozenset[bool]] | None = None,
    continues: set[frozenset[bool]] | None = None,
) -> frozenset[bool]:
    for stmt in body:
        if not states:
            break
        if isinstance(stmt, ast.Return):
            if states != {True}:
                unlogged.append(stmt)
            states = frozenset()
            continue
        if isinstance(stmt, ast.Raise):
            states = frozenset()
            continue
        if isinstance(stmt, (ast.Break, ast.Continue)):
            # break 把「跳出时的日志状态」带到所属循环的出口；continue 结束
            # 本轮后直接回到循环的取下一条目/条件判断：若此后循环正常耗尽，
            # 出口状态就是 continue 处的状态，故同样收集到 continues，由所属
            # 循环在「可能正常耗尽」时并入出口；循环体扫描本身到此为止。
            if isinstance(stmt, ast.Break) and breaks is not None:
                breaks.add(states)
            if isinstance(stmt, ast.Continue) and continues is not None:
                continues.add(states)
            states = frozenset()
            continue
        if isinstance(stmt, ast.Expr) and _is_logging_call(stmt.value):
            states = frozenset({True})
            continue
        if isinstance(stmt, ast.If):
            states = (_h03_scan_logging(stmt.body, states, unlogged, breaks,
                                        continues)
                      | _h03_scan_logging(stmt.orelse, states, unlogged,
                                          breaks, continues))
        elif isinstance(stmt, (ast.With, ast.AsyncWith)):
            states = _h03_scan_logging(stmt.body, states, unlogged, breaks,
                                       continues)
        elif isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            # 循环出口 = 正常耗尽（含 else）状态 ∪ 各 break/continue 处状态；
            # 只有循环体可能一次都不执行时才保留循环前状态，只有循环可能
            # 正常耗尽时才保留循环体出口与 continue 处状态。一律并入循环前
            # 状态会把「必然执行且已记日志的循环」之后的 return 误判成未记
            # 日志降级。
            may_skip, may_exhaust = _h03_loop_entry_facts(stmt)
            loop_breaks: set[frozenset[bool]] = set()
            loop_continues: set[frozenset[bool]] = set()
            body_exit = _h03_scan_logging(
                stmt.body, states, unlogged, loop_breaks, loop_continues)
            entry = states if may_skip else frozenset()
            normal_exit = (entry | body_exit) if may_exhaust else frozenset()
            if may_exhaust:
                for continue_states in loop_continues:
                    normal_exit = normal_exit | continue_states
            states = normal_exit | _h03_scan_logging(
                stmt.orelse, normal_exit, unlogged, breaks, continues)
            for break_states in loop_breaks:
                states = states | break_states
        elif isinstance(stmt, _TRY_NODE_TYPES):
            normal_exit = _h03_scan_logging(
                stmt.orelse,
                _h03_scan_logging(stmt.body, states, unlogged, breaks,
                                  continues),
                unlogged, breaks, continues)
            for _except_clause in stmt.handlers:
                normal_exit |= _h03_scan_logging(
                    _except_clause.body, states, [], breaks, continues)
            states = (_h03_scan_logging(
                stmt.finalbody, states | normal_exit, unlogged, breaks,
                continues)
                if stmt.finalbody else normal_exit)
        elif isinstance(stmt, ast.Match):
            matched_exit = frozenset()
            exhaustive = False
            for case in stmt.cases:
                matched_exit |= _h03_scan_logging(
                    case.body, states, unlogged, breaks, continues)
                if case.guard is None and is_irrefutable_pattern(case.pattern):
                    exhaustive = True
            # 穷尽 match（无守卫的不可反驳模式）必经某一分支，不保留 match 前状态；
            # 非穷尽 match 可无分支命中直落，须并入 match 前状态。
            states = matched_exit if exhaustive else states | matched_exit
        elif isinstance(stmt, _NESTED_SCOPE_NODES):
            continue
    return states
def _h03_unlogged_returns(handler: ast.ExceptHandler) -> list[ast.Return]:
    unlogged: list[ast.Return] = []
    _h03_scan_logging(handler.body, frozenset({False}), unlogged)
    return unlogged
def _h03_finally_logged_returns(tree: ast.AST) -> set[ast.Return]:
    logged_finally = {
        node for node in walk_nodes(tree)
        if isinstance(node, _TRY_NODE_TYPES)
        and _h03_scan_logging(node.finalbody, frozenset({False}), []) == {True}
    }
    protected: set[ast.Return] = set()
    if not logged_finally:
        return protected
    parents = parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Return):
            continue
        cur: ast.AST = node
        while True:
            parent = parents.get(cur)
            if parent is None or isinstance(parent, _NESTED_SCOPE_NODES):
                break
            if parent in logged_finally:
                in_finalbody = any(cur is stmt for stmt in parent.finalbody)
                if not in_finalbody:
                    protected.add(node)
                    break
            cur = parent
    return protected
_EMPTY_COLLECTION_CTORS = frozenset({"set", "list", "dict", "tuple", "frozenset"})
def _is_empty_collection_expr(ret: ast.expr) -> bool:
    if isinstance(ret, (ast.List, ast.Tuple, ast.Set)):
        return not ret.elts
    if isinstance(ret, ast.Dict):
        return not ret.keys
    return (isinstance(ret, ast.Call) and isinstance(ret.func, ast.Name)
            and ret.func.id in _EMPTY_COLLECTION_CTORS
            and not ret.args and not ret.keywords)
_COMMENT_PRAGMA_RE = re.compile(
    r"#\s*(?:noqa|nosec|type\s*:|pragma\s*:|pyright\s*:|mypy\s*:|isort\s*:|ruff\s*:|fmt\s*:)",
    re.IGNORECASE)
@dataclass(frozen=True)
class _CommentContext:
    lines: list[str]
    suppressed: set[int]
    spans: dict[int, list[tuple[int, int]]] | None
    def is_suppressed(self, line: int) -> bool:
        return line in self.suppressed
    def has_rationale(self, handler: ast.ExceptHandler) -> bool:
        if not self.lines:
            return False
        check_lines = {handler.lineno}
        for stmt in handler.body:
            if is_placeholder_stmt(stmt):
                check_lines.update(range(handler.lineno, stmt.lineno + 1))
        for ln in check_lines:
            if not 0 < ln <= len(self.lines):
                continue
            line = self.lines[ln - 1]
            if self.spans is None:
                idx = line.find("#")
                if idx >= 0 and _COMMENT_PRAGMA_RE.match(line, idx) is None:
                    return True
                continue
            if any(_COMMENT_PRAGMA_RE.match(line, start) is None
                   for start, _end in self.spans.get(ln, [])):
                return True
        return False
def _comment_suppression_lines(
        src_lines: list[str],
        spans: dict[int, list[tuple[int, int]]] | None) -> set[int]:
    if spans is not None:
        return {
            ln for ln, items in spans.items()
            if any(_SUPPRESS_MARK_RE.search(src_lines[ln - 1][s:e])
                   for s, e in items)
        }
    suppressed: set[int] = set()
    states = leading_quote_states(src_lines)
    for ln, line in enumerate(src_lines, start=1):
        start, _state = scan_line_quote_state(line, states[ln - 1])
        if start >= 0 and _SUPPRESS_MARK_RE.search(line[start:]):
            suppressed.add(ln)
    return suppressed
def _comment_scan(source_code: str) -> _CommentContext:
    try:
        src_lines = ast_split_lines(source_code)
        spans = comment_only_spans("\n".join(src_lines))
        return _CommentContext(
            lines=src_lines,
            suppressed=_comment_suppression_lines(src_lines, spans),
            spans=spans,
        )
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_comment_scan:Exc')
        return _CommentContext(lines=[], suppressed=set(), spans=None)
def _h03_is_log_fallback_guard(
        handler: ast.ExceptHandler,
        handler_parents: dict[ast.ExceptHandler, ast.Try | ast.TryStar],
) -> bool:
    parent_try = handler_parents.get(handler)
    if parent_try is None:
        return False
    return _h03_body_all_logging(parent_try.body)
def _h03_handler_parents(tree: ast.AST) -> dict:
    parents = {}
    for _n in walk_nodes(tree):
        if isinstance(_n, _TRY_NODE_TYPES):
            for _h in _n.handlers:
                parents[_h] = _n
    return parents
def _h03_body_all_logging(body) -> bool:
    return bool(body) and all(
        isinstance(s, ast.Expr) and _is_logging_call(s.value) for s in body)
def _h03_is_placeholder_capture(node: ast.ExceptHandler,
                                comments: _CommentContext,
                                ctx: ScanContext) -> bool:
    if not _is_broad_except_handler(node, ctx):
        return False
    placeholder = _placeholder_body_stmt(node.body)
    if placeholder is None:
        return False
    return not (comments.is_suppressed(node.lineno)
                or comments.is_suppressed(placeholder.lineno))
def _h03_placeholder_finding(node: ast.ExceptHandler,
                             file_path: str) -> HallucinationFinding:
    prefix = ("bare except" if node.type is None
              else f"except {ast.unparse(node.type)}")
    placeholder = _placeholder_label(_placeholder_body_stmt(node.body))
    return HallucinationFinding(
        rule_id="H03",
        hallucination_type=HallucinationType.LOGIC.value,
        severity="P0",
        title=f"幻觉异常吞没: {prefix}: {placeholder}",
        description="except 宽泛捕获搭配占位体(pass/...)会静默吞掉幻觉导致的NameError/ImportError，使幻觉不可见。必须精确捕获+日志记录或向上传播。",
        file_path=file_path,
        line_num=node.lineno,
        confidence=0.9,
        suggestion="改为: except SpecificError as e: logger.warning(f'desc: {e}')",
        evidence=f"ExceptHandler at line {node.lineno}, body={placeholder}",
    )
def _h03_degrade_finding(stmt: ast.Return,
                         file_path: str) -> HallucinationFinding:
    return HallucinationFinding(
        rule_id="H03",
        hallucination_type=HallucinationType.LOGIC.value,
        severity="P1",
        title="幻觉异常降级: except块返回空值",
        description="异常降级返回空值(空列表/空字典/空元组)会导致数据静默丢失。应返回原始输入或安全默认值。",
        file_path=file_path,
        line_num=stmt.lineno,
        confidence=0.8,
        suggestion="返回原始输入或安全默认值，而非空集合",
        evidence=f"Return empty collection at line {stmt.lineno} in ExceptHandler",
    )
def _h03_empty_return_findings(node: ast.ExceptHandler,
                               comments: _CommentContext,
                               file_path: str,
                               ctx: ScanContext,
                               finally_logged: set[ast.Return]) -> list:
    if comments.is_suppressed(node.lineno):
        return []
    if not _is_broad_except_handler(node, ctx):
        return []
    if comments.has_rationale(node):
        return []
    findings: list[HallucinationFinding] = []
    for stmt in _h03_unlogged_returns(node):
        if stmt in finally_logged:
            continue
        if stmt.value and _is_empty_collection_expr(stmt.value):
            if comments.is_suppressed(stmt.lineno):
                continue
            findings.append(_h03_degrade_finding(stmt, file_path))
    return findings
def detect_hallucinated_exception(
    source_code: str,
    file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    prepared = _prepare_detection(source_code, file_path, _tree)
    if prepared is None:
        return []
    source_code, file_path, tree = prepared
    findings: list[HallucinationFinding] = []
    ctx = ScanContext(source_code, file_path, _tree=tree)
    comments = _comment_scan(source_code)
    _handler_parents = _h03_handler_parents(tree)
    finally_logged = _h03_finally_logged_returns(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ExceptHandler):
            continue
        if _h03_is_placeholder_capture(node, comments, ctx):
            if comments.has_rationale(node):
                continue
            if _h03_is_log_fallback_guard(node, _handler_parents):
                continue
            findings.append(_h03_placeholder_finding(node, file_path))
        findings.extend(_h03_empty_return_findings(
            node, comments, file_path, ctx, finally_logged))
    return findings
def _h04_record_walrus(var_assignments: dict, value: ast.AST, scope) -> None:
    queue: list[tuple[ast.AST, tuple]] = [(value, scope)]
    head = 0
    while head < len(queue):
        cur, key = queue[head]
        head += 1
        if isinstance(cur, ast.Lambda):
            for _d in (list(cur.args.defaults)
                       + [d for d in cur.args.kw_defaults
                          if d is not None]):
                queue.append((_d, key))
            queue.append((cur.body, (type(cur).__name__, cur.lineno,
                                      cur.col_offset)))
            continue
        if isinstance(cur, ast.NamedExpr) and isinstance(cur.target, ast.Name):
            var_assignments.setdefault((cur.target.id, key), []).append(
                (cur.lineno, _infer_value_type(cur.value)))
        queue.extend((ch, key) for ch in ast.iter_child_nodes(cur))
_H04_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef,
                       ast.ClassDef, ast.Lambda)
def _h04_outer_expressions(child: ast.AST) -> list[ast.expr]:
    expressions: list[ast.expr] = []
    args = getattr(child, "args", None)
    if args is not None:
        expressions.extend(args.defaults)
        expressions.extend(d for d in args.kw_defaults if d is not None)
    expressions.extend(getattr(child, "decorator_list", ()) or ())
    expressions.extend(getattr(child, "bases", ()) or ())
    expressions.extend(
        keyword.value for keyword in getattr(child, "keywords", ()) or ())
    returns = getattr(child, "returns", None)
    if returns is not None:
        expressions.append(returns)
    return expressions
def _h04_boundary_kids(var_assignments: dict, child, cur_key) -> list | None:
    if not isinstance(child, _H04_SCOPE_NODES):
        return None
    for expression in _h04_outer_expressions(child):
        _h04_record_walrus(var_assignments, expression, cur_key)
    if isinstance(child, ast.Lambda):
        return [child.body]
    return list(child.body)
def _h04_register_target_value(var_assignments: dict, target,
                               lineno: int, value: ast.AST, scope) -> None:
    if isinstance(target, ast.Name):
        var_assignments.setdefault((target.id, scope), []).append(
            (lineno, _infer_value_type(value)))
        return
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return
    if len(target.elts) != len(value.elts):
        return
    if any(isinstance(elt, ast.Starred)
           for elt in (*target.elts, *value.elts)):
        return
    for sub_target, sub_value in zip(target.elts, value.elts, strict=True):
        _h04_register_target_value(
            var_assignments, sub_target, lineno, sub_value, scope)
def _h04_handle_assignment_family(var_assignments: dict, child, cur_key) -> bool:
    if isinstance(child, ast.Assign):
        for target in child.targets:
            _h04_register_target_value(var_assignments, target,
                                         child.lineno, child.value, cur_key)
        _h04_record_walrus(var_assignments, child.value, cur_key)
    elif isinstance(child, ast.AnnAssign):
        if child.value is not None:
            _h04_register_target_value(var_assignments, child.target,
                                         child.lineno, child.value, cur_key)
            _h04_record_walrus(var_assignments, child.value, cur_key)
    elif isinstance(child, (ast.AugAssign, ast.NamedExpr)):
        _h04_register_target_value(var_assignments, child.target,
                                     child.lineno, child.value, cur_key)
        _h04_record_walrus(var_assignments, child.value, cur_key)
    else:
        return False
    return True
def _h04_collect_scope(var_assignments: dict, node, scope) -> None:
    stack = [(iter(ast.iter_child_nodes(node)), scope)]
    while stack:
        child_iter, cur_key = stack[-1]
        child = next(child_iter, _HALLU_STACK_EXHAUSTED)
        if child is _HALLU_STACK_EXHAUSTED:
            stack.pop()
            continue
        _kids = _h04_boundary_kids(var_assignments, child, cur_key)
        if _kids is not None:
            stack.append((iter(_kids),
                          (type(child).__name__, child.lineno,
                           child.col_offset)))
        elif not _h04_handle_assignment_family(var_assignments, child,
                                               cur_key):
            stack.append((iter(ast.iter_child_nodes(child)), cur_key))
def _h04_concrete_type(vtype: str) -> str | None:
    if not vtype or vtype in _H04_NON_CONCRETE_TYPES:
        return None
    if vtype.startswith('Call('):
        return None
    return vtype
def _h04_concrete_types(assignments: list) -> set[str]:
    return {concrete for _line, vtype in assignments
            if (concrete := _h04_concrete_type(vtype)) is not None}
def _h04_conflict_line(assignments: list) -> int:
    base_type: str | None = None
    for line, vtype in assignments:
        concrete = _h04_concrete_type(vtype)
        if concrete is None:
            continue
        if base_type is None:
            base_type = concrete
        elif concrete != base_type:
            return line
    return assignments[0][0]
def _h04_evidence(assignments: list) -> str:
    shown = assignments[:_H04_EVIDENCE_MAX_ITEMS]
    evidence = f"Assignments: {shown}"
    if len(assignments) > len(shown):
        evidence += f" (+{len(assignments) - len(shown)} more)"
    return evidence
def _h04_contradiction_findings(var_assignments: dict, file_path: str) -> list:
    findings: list[HallucinationFinding] = []
    for (var_name, _scope), assignments in var_assignments.items():
        if len(assignments) < 2:
            continue
        concrete_types = _h04_concrete_types(assignments)
        if len(concrete_types) < 2:
            continue
        findings.append(HallucinationFinding(
            rule_id="H04",
            hallucination_type=HallucinationType.MAPPING.value,
            severity="P3",
            title=f"上下文矛盾: 变量 '{var_name}' 被赋值为多种具体类型",
            description=(f"变量 '{var_name}' 在文件中被赋值为不同具体类型: "
                         f"{sorted(concrete_types)}。Python动态类型允许此模式, "
                         "但可能为上下文遗忘幻觉。"),
            file_path=file_path,
            line_num=_h04_conflict_line(assignments),
            confidence=0.3,
            suggestion="检查变量类型是否一致，或使用不同的变量名",
            evidence=_h04_evidence(assignments),
        ))
    return findings
def detect_context_contradiction(
    source_code: str,
    file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    prepared = _prepare_detection(source_code, file_path, _tree)
    if prepared is None:
        return []
    _source_code, file_path, tree = prepared
    var_assignments: dict[tuple, list[tuple[int, str]]] = {}
    _h04_collect_scope(var_assignments, tree, ("module", 0))
    return _h04_contradiction_findings(var_assignments, file_path)
def _constant_value_type(node: ast.Constant) -> str | None:
    if isinstance(node.value, bool):
        return "bool"
    if isinstance(node.value, str):
        return "str"
    if isinstance(node.value, (bytes, bytearray)):
        return "bytes"
    if isinstance(node.value, (int, float, complex)):
        return "number"
    if node.value is None:
        return "None"
    return None
def _is_always_truthy_literal(expr: ast.expr) -> bool:
    if isinstance(expr, (ast.List, ast.Set, ast.Tuple)):
        return any(not isinstance(elt, ast.Starred) for elt in expr.elts)
    if isinstance(expr, ast.Dict):
        return any(key is not None for key in expr.keys)
    return False
_VALUE_TYPE_BY_AST_NODE = {
    ast.List: "list",
    ast.Dict: "dict",
    ast.Tuple: "tuple",
    ast.Set: "set",
}
_UNARY_NUMERIC_OPS = (ast.USub, ast.UAdd, ast.Invert)
def _infer_value_type(node: ast.expr) -> str:
    if isinstance(node, ast.UnaryOp):
        if not isinstance(node.op, _UNARY_NUMERIC_OPS):
            return "unknown"
        operand = node.operand
        while (isinstance(operand, ast.UnaryOp)
               and isinstance(operand.op, _UNARY_NUMERIC_OPS)):
            operand = operand.operand
        if (isinstance(operand, ast.Constant)
                and _constant_value_type(operand) == "number"):
            return "number"
        return "unknown"
    if isinstance(node, ast.Constant):
        return _constant_value_type(node) or "unknown"
    value_type = _VALUE_TYPE_BY_AST_NODE.get(type(node))
    if value_type is not None:
        return value_type
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        return f"Call({node.func.id})"
    return "unknown"
def _classify_body(body: list) -> tuple[str, ast.AST | None]:
    real_stmts = _real_body_stmts(body)
    if not real_stmts:
        return "docstring_only", None
    if len(real_stmts) == 1 and is_placeholder_stmt(real_stmts[0]):
        return "placeholder", real_stmts[0]
    return "real", None
_H05_NOOP_DOC_MARKERS = (
    '空操作', '空实现', '有意为空', '占位', '无实际效果',
    'no-op', 'placeholder', '接口占位', '接口定义', '接口声明', '协议桩')
def _has_overload_decorator(node: ast.AST) -> bool:
    for deco in getattr(node, "decorator_list", ()):
        target = deco.func if isinstance(deco, ast.Call) else deco
        if isinstance(target, ast.Name) and target.id == "overload":
            return True
        if isinstance(target, ast.Attribute) and target.attr == "overload":
            return True
    return False
def _h05_is_exempt(node: ast.AST, body: list) -> bool:
    return (has_abstractmethod_decorator(node)
            or _has_overload_decorator(node)
            or _docstring_declares_noop(body))
def _docstring_declares_noop(body: list) -> bool:
    if not (isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return False
    doc = body[0].value.value.casefold()
    return any(marker in doc for marker in _H05_NOOP_DOC_MARKERS)
def _h05_pattern_finding(node: ast.AST, file_path: str,
                         placeholder_stmt: ast.AST | None) -> HallucinationFinding:
    if placeholder_stmt is None:
        shape, desc_tail, confidence, evidence_body = (
            "仅有docstring无实质功能",
            "仅包含docstring，无任何可执行语句",
            0.6,
            "docstring only",
        )
    else:
        label = _placeholder_label(placeholder_stmt)
        shape, desc_tail, confidence, evidence_body = (
            f"仅含{label}",
            f"仅包含 {label} 占位语句",
            0.7,
            label,
        )
    return _norms_finding(
        "H05", HallucinationType.AI_SLOP.value, severity="P2",
        title=f"AI Slop: 函数 '{node.name}' {shape}",
        description=f"函数 '{node.name}' 体{desc_tail}。可能为AI灌水代码。",
        confidence=confidence, suggestion="实现函数体或删除该函数",
        evidence=f"FunctionDef '{node.name}' at line {node.lineno}, body={evidence_body}",
        file_path=file_path, line=node.lineno)
def detect_ai_slop(
    source_code: str,
    file_path: str = _DEFAULT_FILE_PATH,
    test_result: dict[str, Any] | None = None,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    prepared = _prepare_detection(source_code, file_path, _tree)
    if prepared is None:
        return []
    _source_code, file_path, tree = prepared
    findings: list[HallucinationFinding] = []
    collectable_tests = _collectable_test_nodes(tree)
    protocol_members = (_protocol_member_ids(tree)
                        if isinstance(tree, ast.Module) else set())
    all_function_names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        all_function_names.add(node.name)
        if id(node) in protocol_members:
            continue
        if node in collectable_tests:
            continue
        body = node.body
        if not body:
            continue
        if _h05_is_exempt(node, body):
            continue
        body_kind, placeholder = _classify_body(body)
        if body_kind == "docstring_only":
            findings.append(_h05_pattern_finding(node, file_path, None))
        elif body_kind == "placeholder":
            findings.append(_h05_pattern_finding(node, file_path, placeholder))
    test_names = {node.name for node in collectable_tests}
    findings.extend(_deletion_evidence_findings(
        test_result, _H05_DELETION_SPEC, file_path,
        eligible_names=all_function_names - test_names))
    return findings
def detect_test_illusion(
    source_code: str,
    file_path: str = _DEFAULT_FILE_PATH,
    test_result: dict[str, Any] | None = None,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    prepared = _prepare_detection(source_code, file_path, _tree)
    if prepared is None:
        return []
    _source_code, file_path, tree = prepared
    findings: list[HallucinationFinding] = []
    collectable_tests = _collectable_test_nodes(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node not in collectable_tests:
            continue
        body_kind, placeholder = _classify_body(node.body)
        if body_kind in ("docstring_only", "placeholder"):
            findings.append(_h06_empty_body_finding(node, file_path, placeholder))
            continue
        findings.extend(_h06_constant_assert_findings(node, file_path))
    findings.extend(_deletion_evidence_findings(
        test_result, _H06_DELETION_SPEC, file_path,
        eligible_names={node.name for node in collectable_tests}))
    return findings
def _h06_empty_body_finding(node, file_path: str,
                            placeholder: ast.AST | None) -> HallucinationFinding:
    if placeholder is None:
        shape, desc_tail, confidence, suggestion, evidence_body = (
            "仅有docstring无断言",
            "仅包含docstring，无任何断言",
            0.85,
            "添加有意义的断言以验证被测函数的行为",
            "docstring only",
        )
    else:
        label = _placeholder_label(placeholder)
        shape, desc_tail, confidence, suggestion, evidence_body = (
            f"仅含{label}",
            f"仅包含 {label} 占位语句",
            0.9,
            "实现有意义的测试逻辑",
            label,
        )
    return _norms_finding(
        "H06", HallucinationType.TEST_ILLUSION.value, severity="P1",
        title=f"测试幻觉: '{node.name}' {shape}",
        description=f"测试函数 '{node.name}' 体{desc_tail}。测试永远通过。",
        confidence=confidence, suggestion=suggestion,
        evidence=f"FunctionDef '{node.name}' at line {node.lineno}, body={evidence_body}",
        file_path=file_path, line=node.lineno)
def _is_expected_exception_context(expr: ast.AST) -> bool:
    if not isinstance(expr, ast.Call):
        return False
    func = expr.func
    if isinstance(func, ast.Attribute):
        return func.attr in ("raises", "assertRaises", "assertRaisesRegex")
    return isinstance(func, ast.Name) and func.id in ("raises", "assertRaises")
def _assert_in_expected_exception(node: ast.AST, root: ast.AST,
                                  parents: dict) -> bool:
    cur = node
    while cur is not root:
        parent = parents.get(cur)
        if parent is None:
            return False
        if isinstance(parent, _NESTED_SCOPE_NODES):
            return False
        if (isinstance(parent, (ast.With, ast.AsyncWith))
                and any(_is_expected_exception_context(item.context_expr)
                        for item in parent.items)):
            return True
        cur = parent
    return False
def _h06_constant_assert_findings(node, file_path: str) -> list:
    findings: list[HallucinationFinding] = []
    parents = parent_map(node)
    for stmt in _walk_own_scope(node.body, _NESTED_SCOPE_NODES):
        if not isinstance(stmt, ast.Assert):
            continue
        if _assert_in_expected_exception(stmt, node, parents):
            continue
        test = stmt.test
        is_constant = isinstance(test, ast.Constant)
        if not (is_constant or _is_empty_collection_expr(test)
                or _is_always_truthy_literal(test)):
            continue
        shown = (_repr_limited(test.value) if is_constant
                 else _repr_limited(ast.unparse(test)))
        findings.append(HallucinationFinding(
            rule_id="H06",
            hallucination_type=HallucinationType.TEST_ILLUSION.value,
            severity="P1",
            title=f"测试幻觉: '{node.name}' 包含恒真/恒假断言",
            description=(f"assert {_repr_limited(test)} — 断言常量值/空集合，"
                         "测试无实际验证意义。"),
            file_path=file_path,
            line_num=stmt.lineno,
            confidence=0.8,
            suggestion="替换为对被测函数返回值的断言",
            evidence=(f"Assert at line {stmt.lineno}, "
                      f"test={shown}"),
        ))
    return findings
def _h07_resolve_tree(code_source: str, _tree: ast.AST | None) -> tuple[ast.AST | None, Exception | None]:
    if isinstance(_tree, ast.AST):
        return _tree, None
    try:
        return parse_with_compile(code_source), None
    except PARSE_DEGRADE_EXC as e:
        logger.warning("detect_memory_hallucination: 语法错误: %s", e)
        return None, e
_H07_LINE_DEVIATION_RATIO = 0.2
_H07_LINE_DEVIATION_FLOOR = 5
def _h07_line_claim_finding(claimed: int, actual: int, file_path: str) -> HallucinationFinding | None:
    tolerance = max(actual * _H07_LINE_DEVIATION_RATIO, _H07_LINE_DEVIATION_FLOOR)
    if abs(claimed - actual) <= tolerance:
        return None
    return _norms_finding(
        "H07", HallucinationType.MEMORY.value, severity="P0",
        title=f"记忆幻觉: 声称 {claimed} 行，实际 {actual} 行",
        description="记忆声明与代码实际状态不符。偏差超过20%。",
        confidence=0.95,
        suggestion=f"修正记忆中的行数: {claimed} → {actual}",
        evidence=f"claim={claimed}行, actual={actual}行",
        file_path=file_path,
    )
def _h07_func_claim_finding(
    claimed: int, tree: ast.AST, file_path: str,
) -> HallucinationFinding | None:
    actual = sum(
        1 for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    )
    if claimed == actual:
        return None
    return _norms_finding(
        "H07", HallucinationType.MEMORY.value, severity="P0",
        title=f"记忆幻觉: 声称 {claimed} 个函数，AST验证 {actual} 个",
        description="记忆声明与代码实际状态不符。",
        confidence=0.95,
        suggestion=f"修正记忆中的函数数: {claimed} → {actual}",
        evidence=f"claim={claimed}函数, actual(ast.walk)={actual}函数",
        file_path=file_path,
    )
def _collectable_test_nodes(tree: ast.AST) -> frozenset[ast.AST]:
    return frozenset(iter_collectable_test_functions(tree))
def _h07_pass_claim_finding(
    claimed: int, tree: ast.AST, file_path: str,
) -> HallucinationFinding | None:
    actual_test_funcs = len(_collectable_test_nodes(tree))
    if (claimed > 0 and actual_test_funcs == 0) or (
            actual_test_funcs > 0 and claimed > actual_test_funcs * 2):
        return _h07_test_count_finding(claimed, actual_test_funcs, file_path)
    return None
def _h07_syntax_error_finding(
    claimed: int, tree_error: Exception, file_path: str,
    *, claim_label: str = "PASS",
) -> HallucinationFinding:
    return _norms_finding(
        "H07", HallucinationType.MEMORY.value, severity="P0",
        title=(f"记忆幻觉: 声称 {claimed} {claim_label}，"
               f"但代码存在语法错误: {tree_error}"),
        description="记忆声明中的量化指标无法通过 AST 验证，代码编译失败。",
        confidence=0.95,
        suggestion=f"修正代码语法错误后再声称 {claimed} {claim_label}",
        evidence=f"claim={claimed}{claim_label}, SyntaxError={tree_error}",
        file_path=file_path,
    )
def _h07_test_count_finding(claimed: int, actual_test_funcs: int,
                            file_path: str) -> HallucinationFinding:
    none_collectable = actual_test_funcs == 0
    return _norms_finding(
        "H07", HallucinationType.MEMORY.value,
        severity="P0" if none_collectable else "P1",
        title=(f"记忆幻觉: 声称 {claimed} PASS，但未找到可收集的测试函数"
               if none_collectable else
               f"记忆幻觉: 声称 {claimed} PASS，但仅有 {actual_test_funcs} 个测试函数"),
        description=("记忆声明中的PASS数与代码实际测试函数数量不符。"
                     if none_collectable else
                     "记忆声明中的PASS数远超代码实际测试函数数量。"),
        confidence=0.9 if none_collectable else 0.8,
        suggestion=(f"修正记忆中的PASS声明: {claimed} PASS → 实际{actual_test_funcs}个测试函数"
                    if none_collectable else
                    f"核实PASS数: 声称{claimed} vs 实际{actual_test_funcs}个测试函数"),
        evidence=f"claim={claimed}PASS, actual_test_funcs={actual_test_funcs}",
        file_path=file_path,
    )
def detect_memory_hallucination(
    claim: str,
    code_source: str,
    file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    findings: list[HallucinationFinding] = []
    normalized_code = _normalized_source(code_source)
    if normalized_code is None:
        return findings
    claim = coerce_str(claim)
    code_source = normalized_code
    file_path = coerce_str(file_path)
    plan_markers, done_markers = _claim_state_markers(claim)
    if plan_markers and not done_markers:
        return findings
    line_match = first_quantity_claim(claim, LINE_CLAIM_RE, ORDINAL_LINE_RE)
    func_match = first_quantity_claim(claim, FUNC_CLAIM_RE, ORDINAL_FUNC_RE)
    pass_match = (first_quantity_claim(claim, PASS_CLAIM_RE, ORDINAL_PASS_RE)
                  or first_quantity_claim(claim, PASS_SUFFIX_CLAIM_RE,
                                          ORDINAL_PASS_RE))
    if not (done_markers or line_match or func_match or pass_match):
        return findings
    tree, tree_error = _h07_resolve_tree(code_source, _tree)
    if tree_error is not None:
        syntax_claim = next(
            ((match, label) for match, label in (
                (line_match, "行"), (func_match, "个函数"), (pass_match, "PASS"),
            ) if match is not None),
            None)
        if syntax_claim is not None:
            match, label = syntax_claim
            return [_h07_syntax_error_finding(
                claim_number(match), tree_error, file_path, claim_label=label)]
        return [_norms_finding(
            "H07", HallucinationType.MEMORY.value, severity="P0",
            title=("记忆幻觉: 完成声明无法通过 AST 验证，"
                   f"代码存在语法错误: {tree_error}"),
            description="完成声明中的代码状态无法通过 AST 验证，代码编译失败。",
            confidence=0.95,
            suggestion="修正代码语法错误后再声明已完成",
            evidence=f"completion_claim=True, SyntaxError={tree_error}",
            file_path=file_path,
        )]
    line_finding = (
        _h07_line_claim_finding(
            claim_number(line_match), len(code_source.splitlines()), file_path)
        if line_match is not None else None)
    func_finding = (_h07_func_claim_finding(
        claim_number(func_match), tree, file_path)
        if func_match is not None else None)
    pass_finding = (_h07_pass_claim_finding(
        claim_number(pass_match), tree, file_path)
        if pass_match is not None else None)
    findings.extend(
        finding for finding in (line_finding, func_finding, pass_finding)
        if finding is not None)
    return findings
@dataclass(frozen=True)
class _DetectorSpec:
    rule_id: str
    run: Callable[..., list[HallucinationFinding]]
    accepts_test_result: bool = False
_DETECTOR_SPECS: tuple[_DetectorSpec, ...] = (
    _DetectorSpec("H01", detect_hallucinated_api),
    _DetectorSpec("H02", detect_hallucinated_import),
    _DetectorSpec("H03", detect_hallucinated_exception),
    _DetectorSpec("H04", detect_context_contradiction),
    _DetectorSpec("H05", detect_ai_slop, accepts_test_result=True),
    _DetectorSpec("H06", detect_test_illusion, accepts_test_result=True),
    _DetectorSpec("H08", detect_sandbox_reflection),
)
class HallucinationDetector:
    def __init__(self):
        self._detectors = {spec.rule_id: spec.run for spec in _DETECTOR_SPECS}
        self._test_result_rules = frozenset(
            spec.rule_id for spec in _DETECTOR_SPECS
            if spec.accepts_test_result)
    def _run_detectors(
        self, source_code: str, file_path: str, tree: ast.AST,
        test_result: dict[str, Any] | None,
    ) -> list[HallucinationFinding]:
        all_findings: list[HallucinationFinding] = []
        for rule_id, rule in self._detectors.items():
            if test_result and rule_id in self._test_result_rules:
                findings = rule(source_code, file_path, test_result,
                                _tree=tree)
            else:
                findings = rule(source_code, file_path, _tree=tree)
            all_findings.extend(findings)
        return all_findings
    def scan_file(
        self, file_path: str, source_code: str | None = None,
        test_result: dict[str, Any] | None = None,
        _tree: ast.AST | None = None,
    ) -> list[HallucinationFinding]:
        file_path = coerce_str(file_path)
        _t0 = time.monotonic()
        if source_code is None:
            source_code = _read_scan_source(file_path, _t0)
        else:
            source_code = _normalized_source(source_code)
        if source_code is None:
            return []
        tree = _tree if _tree is not None else _parse_scan_tree(
            source_code, file_path, _t0)
        if tree is None:
            return []
        all_findings = self._run_detectors(source_code, file_path,
                                          tree, test_result)
        write_module_run(
            "hallucination_norms", "scan_file",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            findings=len(all_findings), rules=len(self._detectors))
        return all_findings
    def scan_directory(
        self, dir_path: str, pattern: str = "*.py",
        test_results: dict[str, dict[str, Any]] | None = None,
    ) -> dict[str, list[HallucinationFinding]]:
        _norm_index = _build_test_result_norm_index(test_results)
        _t0 = time.monotonic()
        _scanned = 0
        results: dict[str, list[HallucinationFinding]] = {}
        for py_file in iter_diagnosis_scan_targets(dir_path, pattern):
            test_result = _lookup_test_result(test_results, _norm_index,
                                              py_file)
            findings = self.scan_file(py_file, test_result=test_result)
            _scanned += 1
            if findings:
                results[py_file] = findings
        write_module_run(
            "hallucination_norms", "scan_directory",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            files=_scanned, files_with_findings=len(results),
            findings=sum(len(v) for v in results.values()))
        return results
@dataclass
class HallucinationScanResult:
    file_path: str
    norm_violations: list[dict[str, Any]] = field(default_factory=list)
    hallucination_findings: list[dict[str, Any]] = field(default_factory=list)
    blocked: bool = False
def scan_hallucinations(
    file_path: str,
    source_code: str | None = None,
    check_norms: bool = True,
    check_findings: bool = True,
) -> HallucinationScanResult:
    file_path = coerce_str(file_path)
    if source_code is not None:
        source_code = _normalized_source(source_code)
    else:
        source_code = _read_source_text(file_path, "scan_hallucinations")[0]
    if source_code is None:
        return HallucinationScanResult(file_path=file_path, blocked=True)
    result = HallucinationScanResult(file_path=file_path)
    if not (check_norms or check_findings):
        return result
    parse_error: Exception | None = None
    try:
        shared_tree = parse_with_compile(source_code, file_path or "<scan>")
    except PARSE_DEGRADE_EXC as e:
        logger.debug("共享 AST 预解析失败(语法错误,由各层自行报告): %s", e)
        shared_tree = None
        parse_error = e
    if check_norms:
        norm_result = verify_code_against_norms(source_code, file_path, _tree=shared_tree)
        result.norm_violations = norm_result.get("violations", [])
        result.blocked = norm_result.get("status") == "blocked"
    if check_findings:
        if shared_tree is None:
            result.blocked = True
            logger.warning("幻觉发现扫描无法解析 %s，按未知结果阻断: %s",
                           file_path, parse_error)
        else:
            try:
                findings = HallucinationDetector().scan_file(
                    file_path, source_code=source_code, _tree=shared_tree)
            except Exception as e:
                result.blocked = True
                logger.warning("幻觉发现扫描失败 %s，按未知结果阻断: %s",
                               file_path, e, exc_info=True)
            else:
                result.hallucination_findings = [
                    _finding_to_dict(f) for f in findings]
    return result
def _read_source_text(file_path: str,
                      purpose: str) -> tuple[str | None, Exception | None]:
    try:
        return read_source_interpreter_encoding(file_path), None
    except (OSError, LookupError, *PARSE_DEGRADE_EXC) as e:
        logger.warning("%s 读取源码失败: %s: %s", purpose, file_path, e)
        return None, e
def _finding_to_dict(finding: Any) -> dict[str, Any]:
    return {
        "rule_id": finding.rule_id,
        "hallucination_type": finding.hallucination_type,
        "severity": finding.severity,
        "title": finding.title,
        "description": finding.description,
        "file_path": finding.file_path,
        "line_num": finding.line_num,
        "confidence": finding.confidence,
        "suggestion": finding.suggestion,
        "evidence": finding.evidence,
    }
def _is_poison_confidence(val: Any) -> bool:
    return not (is_finite_num(val) and 0.0 <= val <= 1.0)
def _boosted_confidence(value: float, *, boost: bool) -> float:
    return min(0.99, (value + 0.1) if boost else value)
def _output_confidence(confidence: Any, rule_id: str = "",
                       known_rule_ids: set[str] | frozenset[str] = _EMPTY_RULE_IDS) -> float:
    if _is_poison_confidence(confidence):
        return _POISON_CONFIDENCE
    return _boosted_confidence(
        confidence, boost=bool(rule_id and rule_id in known_rule_ids))
def boost_known_pattern_confidence(
    all_findings: list[dict[str, Any]],
    known_rule_ids: set[str] | frozenset[str],
) -> None:
    try:
        if not known_rule_ids:
            return
        boosted_count = sum(
            1 for finding in all_findings
            if _boost_one_finding(finding, known_rule_ids))
        if boosted_count:
            logger.info("已知模式增强: %s条finding置信度提升", boosted_count)
    except Exception as e:
        logger.warning("已知模式增强失败(非阻断): %s", e, exc_info=True)
def _boost_one_finding(finding: dict[str, Any], known_rule_ids) -> bool:
    if not isinstance(finding, dict):
        return False
    rule_id = finding.get("rule_id", "")
    if not isinstance(rule_id, str) or rule_id not in known_rule_ids:
        return False
    if "_known_pattern_boosted" in finding:
        return False
    _conf = finding.get("confidence", DEFAULT_FINDING_CONFIDENCE)
    if _is_poison_confidence(_conf):
        finding["confidence"] = _POISON_CONFIDENCE
        finding["_known_pattern_boosted"] = False
        return False
    finding["confidence"] = _boosted_confidence(_conf, boost=True)
    finding["_known_pattern_boosted"] = True
    return True
def _cv_finding_entry(hf: Any, rel_path: str,
                      known_rule_ids: set[str]) -> dict[str, Any]:
    rule_id = getattr(hf, "rule_id", "H00")
    raw_confidence = getattr(hf, "confidence", _POISON_CONFIDENCE)
    boosted = (bool(rule_id and rule_id in known_rule_ids)
               and not _is_poison_confidence(raw_confidence))
    return {
        "file": rel_path,
        "line": getattr(hf, "line_num", 0),
        "rule_id": rule_id,
        "rule_family": HALLUCINATION_RULE_IDS.get(rule_id, "hallucination_general"),
        "severity": getattr(hf, "severity", "P2"),
        "message": getattr(hf, "description", getattr(hf, "title", "")),
        "confidence": _output_confidence(
            raw_confidence, rule_id, known_rule_ids),
        "_known_pattern_boosted": boosted,
        "_source_method": "A2",
        "evidence": getattr(hf, "evidence", ""),
        "hallucination_type": getattr(hf, "hallucination_type", ""),
    }
def produce_cv_findings(
    skill_dir: str,
    include_file: Any = None,
    *,
    known_rule_ids: set[str] | frozenset[str] = _EMPTY_RULE_IDS,
) -> list[dict[str, Any]]:
    scan_root = _cv_scan_root(skill_dir)
    detector = HallucinationDetector()
    py_files = collect_scan_py_files(skill_dir, include_file=include_file)
    findings: list[dict[str, Any]] = []
    for fpath_file in sorted(py_files):
        findings.extend(
            _scan_file_to_cv_entries(fpath_file, scan_root, detector,
                                     known_rule_ids))
    logger.info("[H1] 幻觉检测CV findings: %d 条", len(findings))
    return findings
def _cv_scan_root(skill_dir: Any) -> str:
    raw = (os.fsdecode(os.fspath(skill_dir))
           if isinstance(skill_dir, (str, os.PathLike)) else "")
    if not raw:
        return ""
    path = os.path.abspath(raw)
    return os.path.dirname(path) if os.path.isfile(path) else path
def _scan_file_to_cv_entries(fpath_file: str, skill_dir: str,
                             detector: HallucinationDetector,
                             known_rule_ids: set[str]) -> list[dict[str, Any]]:
    try:
        _src, _tree = _parse_py_file(fpath_file, quiet=True)
        if _src is None:
            return []
        if not _borrow_compile_check(_tree, fpath_file):
            return []
        file_findings = detector.scan_file(
            fpath_file, source_code=_src, _tree=_tree)
        rel_path = os.path.relpath(fpath_file, skill_dir)
        return [_cv_finding_entry(hf, rel_path, known_rule_ids)
                for hf in file_findings]
    except Exception as e:
        logger.warning("幻觉扫描失败 %s: %s", fpath_file, e, exc_info=True)
        return []
def _borrow_compile_check(_tree, fpath_file: str) -> bool:
    if _tree is None:
        logger.debug("CV findings 共享 AST 缺失(文件不可解析)，跳过: %s", fpath_file)
        return False
    try:
        compile(_tree, fpath_file, "exec")
        return True
    except PARSE_DEGRADE_EXC as e:
        logger.debug("CV findings 借树 compile 验证失败(跳过): %s: %s",
                     fpath_file, e)
        return False
def verify_api_existence(file_path: str) -> list[dict[str, Any]]:
    src, read_err = _read_source_text(file_path, "verify_api_existence")
    if src is None:
        raise RuntimeError(
            f"API存在性校验读取源码失败({file_path}): {read_err}") from read_err
    try:
        tree = parse_with_compile(src, file_path)
    except PARSE_DEGRADE_EXC as exc:
        raise RuntimeError(
            f"API存在性校验解析源码失败({file_path}): {exc}") from exc
    return [_api_missing_entry(hf, file_path)
            for hf in detect_hallucinated_api(src, file_path, _tree=tree)]
def _api_name_of(hf: Any) -> str:
    return getattr(hf, "api_name", "") or getattr(hf, "title", "")
def _api_signature(hf: Any) -> tuple[str, str]:
    return _api_name_of(hf), str(getattr(hf, "severity", "")).upper()
def detect_new_p0_api_calls(original_source: str, fixed_source: str,
                            filepath: str = _DEFAULT_FILE_PATH, *,
                            tree: ast.AST | None = None
                            ) -> list[tuple[str, str]]:
    if not isinstance(fixed_source, str):
        raise TypeError(
            f"fixed_source 应为源码全文 str，实际为 {type(fixed_source).__name__}")
    if tree is not None and not isinstance(tree, ast.AST):
        raise TypeError(f"tree 应为 ast.AST，实际为 {type(tree).__name__}")
    fixed_source = strip_bom(fixed_source)
    try:
        fixed_tree = (tree if tree is not None else parse_with_compile(
            fixed_source, filepath or "<fixed>"))
    except PARSE_DEGRADE_EXC as exc:
        raise RuntimeError(
            f"修复后源码解析失败，无法执行新增API核验: {exc}") from exc
    old_source = strip_bom(coerce_str(original_source))
    old_findings = (detect_hallucinated_api(old_source, filepath)
                    if old_source else [])
    new_findings = detect_hallucinated_api(
        fixed_source, filepath, _tree=fixed_tree)
    old_counts = Counter(_api_signature(hf) for hf in old_findings)
    hits: list[tuple[str, str]] = []
    for hf in new_findings:
        sig = _api_signature(hf)
        if old_counts[sig] > 0:
            old_counts[sig] -= 1
            continue
        if sig[1] == "P0":
            hits.append(sig)
    return hits
def _api_missing_entry(hf: Any, file_path: str) -> dict[str, Any]:
    api_name = _api_name_of(hf)
    return {
        "file": file_path,
        "line": getattr(hf, "line_num", 0),
        "rule_id": "H01",
        "rule_family": HALLUCINATION_RULE_IDS["H01"],
        "severity": getattr(hf, "severity", "") or "P1",
        "message": f"可能不存在的API调用: {api_name}",
        "confidence": _output_confidence(
            getattr(hf, "confidence", _POISON_CONFIDENCE)),
        "_source_method": "H1_API",
        "api_name": api_name,
    }
def _coerce_int(value: Any, *, minimum: int) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        return max(minimum, int(value))
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='_coerce_int')
        return None
_FILE_MODIFY_OPS = ("modify", "fix", "refactor", "security_modify")
_PROCESS_FLOW_GATE_SPECS: tuple[
    tuple[str, Callable[[str, dict[str, Any]], bool], str, str], ...
] = (
    ("V2",
     lambda op, ctx: op in ("verify_imports", "verify_compile", "full_audit")
     and not ctx.get("pycache_cleaned"),
     "验证操作前未声明已清除__pycache__，pyc缓存可能掩盖导入链断裂",
     "验证前清除 __pycache__/字节码缓存（缓存会掩盖导入链断裂）"),
    ("V4",
     lambda op, _ctx: op == "batch_fix",
     "检测到批量修复操作，违反逐文件验证原则",
     "改为逐文件修复+验证，每个文件compile通过后再继续下一个"),
    ("V5",
     lambda op, ctx: op in _FILE_MODIFY_OPS
     and not ctx.get("backup_exists"),
     "文件修改前未声明已创建备份，违反可回滚要求",
     "修改前创建可回滚备份，落在会话工作空间的临时区（不得落到技能根或其他非工作空间位置）"),
    ("V6",
     lambda op, ctx: op == "delete"
     and not ctx.get("function_migrated"),
     "删除操作前未声明已验证功能迁移",
     "删除前先用ast.walk+grep验证被删代码的功能在其他地方实现"),
    ("R1",
     lambda op, ctx: op in _FILE_MODIFY_OPS
     and not ctx.get("baseline_compared"),
     "修改后未声明已进行基线对比",
     "修改后重新运行诊断，对比修改前后的findings"),
    ("R2",
     lambda op, ctx: op in _FILE_MODIFY_OPS
     and (ctx.get("test_passed") is False
          and not ctx.get("rolled_back")),
     "验证失败但未声明已执行回滚",
     "验证失败时从会话工作空间的备份区恢复原文件"),
)
_COLLAB_GATE_SPECS = (
    ("C1",
     lambda op, ctx: op == "code_generation"
     and ctx.get("human_review_required") is False,
     "代码生成操作显式标记为无需人类审查",
     "标记所有AI生成代码为'待审查'状态"),
    ("C2",
     lambda op, ctx: op in ("delete", "security_modify", "data_operation")
     and not ctx.get("human_confirmed"),
     "关键路径操作未声明已获人工确认",
     "执行前请求人工确认"),
    ("C3",
     lambda op, ctx: op == "code_generation"
     and not ctx.get("ai_confidence", ""),
     "代码生成操作未标注AI置信度",
     "为每段生成代码标注置信度: 高/中/低"),
    ("C4",
     lambda op, ctx: op == "code_generation"
     and not ctx.get("has_negative_constraint"),
     "代码生成上下文未声明包含负面约束（禁止项）",
     "在代码生成前先声明禁止行为: '不要使用eval/不要删除文件/不要修改系统配置'"),
)
_GATE_BOOL_DEFAULTS: dict[str, bool] = {
    "pycache_cleaned": False, "backup_exists": False,
    "function_migrated": False, "baseline_compared": False,
    "test_passed": True, "rolled_back": False,
    "human_review_required": True, "human_confirmed": False,
    "has_negative_constraint": False,
}
_TRUE_TEXTS = frozenset({
    "true", "1", "yes", "y", "on", "ok", "success",
    "done", "completed", "complete", "passed",
})
_FALSE_TEXTS = frozenset({"false", "0", "no", "n", "off", "fail", "failed", ""})
def _gate_bool(value: Any, default: bool) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    if isinstance(value, str):
        text = value.strip().lower()
        if text in _TRUE_TEXTS:
            return True
        if text in _FALSE_TEXTS:
            return False
        logger.debug("门禁布尔值无法识别，回落默认值 %s: %r", default, value)
        return default
    if is_finite_num(value):
        return value != 0
    return default
def _normalize_gate_bools(context: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(context)
    for key, default in _GATE_BOOL_DEFAULTS.items():
        normalized[key] = _gate_bool(normalized.get(key), default)
    return normalized
def _spec_violations(specs, operation: str, context: dict[str, Any],
                     file_path: str) -> list[NormViolation]:
    context = (_normalize_gate_bools(context)
               if isinstance(context, dict) else {})
    return [
        mk_violation(rule_id, detail=detail, file_path=file_path,
                     suggestion=suggestion)
        for rule_id, gate, detail, suggestion in specs
        if gate(operation, context)
    ]
def _resolve_r3_max_violations(context: dict[str, Any]) -> int:
    parsed = _coerce_int(
        context.get("max_violations", _DEFAULT_MAX_VIOLATIONS), minimum=1)
    return _DEFAULT_MAX_VIOLATIONS if parsed is None else parsed
def _count_by_attr(items, attr: str, default: str = "") -> dict[str, int]:
    counts: dict[str, int] = {}
    for item in items:
        key = getattr(item, attr, default)
        counts[key] = counts.get(key, 0) + 1
    return counts
class NormEngine:
    def __init__(self):
        self._norms: dict[str, NormRule] = NORM_INDEX
        self._custom_check_fns: dict[str, Callable] = {}
        self._violations: list[NormViolation] = []
        self._p0_count: int = 0
        self._blocked: bool = False
        self._max_violations: int = _DEFAULT_MAX_VIOLATIONS
    def register_check_fn(self, rule_id: str,
                          fn: Callable[..., NormViolation | None]) -> None:
        if rule_id not in self._norms:
            raise ValueError(f"未知铁律ID: {rule_id}")
        self._custom_check_fns[rule_id] = fn
    def check(self, rule_id: str, *args: Any,
              **kwargs: Any) -> NormViolation | None:
        if rule_id not in self._norms:
            raise ValueError(f"未知铁律ID: {rule_id}")
        fn = self._custom_check_fns.get(rule_id)
        if fn is None:
            return None
        failure_detail = ""
        try:
            result = fn(*args, **kwargs)
        except Exception as exc:
            failure_detail = (
                f"自定义检查执行异常({type(exc).__name__}): {exc}；"
                "未获得检查结论，按铁律违反处理")
            logger.warning("铁律 %s %s", rule_id, failure_detail, exc_info=True)
        else:
            if isinstance(result, NormViolation):
                self._record_violation(result)
                return result
            if result is None:
                return None
            failure_detail = (
                "自定义检查返回非 NormViolation 结果 "
                f"({type(result).__name__}): {result!r}；按铁律违反处理")
            logger.warning("铁律 %s %s", rule_id, failure_detail)
        violation = mk_violation(
            rule_id, detail=failure_detail, severity="P0",
            suggestion="修复自定义检查实现并重新执行，不得把异常或非法返回当作未命中")
        self._record_violation(violation)
        return violation
    def _preset_session(self, session_p0: int | None) -> None:
        if session_p0 is None:
            return
        self._p0_count = session_p0
        if session_p0 >= self._max_violations:
            self._blocked = True
    def check_process(self, context: dict[str, Any]) -> list[NormViolation]:
        self.reset()
        if not isinstance(context, dict):
            context = {}
        violations: list[NormViolation] = []
        operation = coerce_str(context.get("operation", ""))
        file_path = coerce_str(context.get("file_path", ""))
        claim_text = coerce_str(context.get("claim_text"))
        code_source = context.get("code_source", "")
        self._max_violations = _resolve_r3_max_violations(context)
        session_p0 = _coerce_int(context.get("session_p0_count"), minimum=0)
        self._preset_session(session_p0)
        violations.extend(_spec_violations(
            _PROCESS_FLOW_GATE_SPECS, operation, context, file_path))
        violations.extend(
            claim_norm_violations(claim_text, code_source, file_path))
        violations.extend(_spec_violations(
            _COLLAB_GATE_SPECS, operation, context, file_path))
        for violation in violations:
            self._record_violation(violation)
        self._append_r3_if_blocked(violations, file_path)
        return violations
    def check_code(self, source_code: str, file_path: str = _DEFAULT_FILE_PATH,
                   _tree: ast.AST | None = None,
                   session_p0_count: int | None = None) -> list[NormViolation]:
        self.reset()
        session_p0 = _coerce_int(session_p0_count, minimum=0)
        self._preset_session(session_p0)
        normalized_source = _normalized_source(source_code)
        source_code = normalized_source if normalized_source is not None else ""
        file_path = coerce_str(file_path)
        ctx = ScanContext(source_code, file_path, _tree=_tree)
        violations = scan_code_violations(ctx, source_code)
        for violation in violations:
            self._record_violation(violation)
        self._append_r3_if_blocked(violations, file_path)
        return violations
    def _append_r3_if_blocked(
        self, violations: list[NormViolation], file_path: str,
    ) -> None:
        if self.is_blocked and all(v.rule_id != "R3" for v in violations):
            r3 = mk_violation(
                "R3",
                detail=f"会话累计 {self._p0_count} 次 P0 铁律违反，触发 R3 会话阻断",
                file_path=file_path,
                suggestion="回顾并修复本次会话所有 P0 违规后再继续")
            violations.append(r3)
            self._violations.append(r3)
    def _record_violation(self, violation: NormViolation) -> None:
        self._violations.append(violation)
        if (violation.severity == NormSeverity.P0.value
                and violation.rule_id != "R3"):
            self._p0_count += 1
            logger.warning(
                f"[铁律违反-{violation.rule_id}] {violation.name}: "
                f"{violation.detail} (文件: {violation.file_path}:{violation.line_num})"
            )
        if not self._blocked and self._p0_count >= self._max_violations:
            self._blocked = True
            logger.error(
                f"[会话阻断] 累计 {self._p0_count} 次 P0 铁律违反，触发 R3 阻断"
            )
    @property
    def is_blocked(self) -> bool:
        return self._blocked
    @property
    def violations(self) -> list[NormViolation]:
        return list(self._violations)
    @property
    def violation_summary(self) -> dict[str, Any]:
        return {
            "total": len(self._violations),
            "by_category": _count_by_attr(self._violations, "category"),
            "by_severity": _count_by_attr(self._violations, "severity"),
            "blocked": self._blocked,
            "p0_count": self._p0_count,
        }
    def reset(self) -> None:
        self._violations.clear()
        self._p0_count = 0
        self._blocked = False
        self._max_violations = _DEFAULT_MAX_VIOLATIONS
_engine = NormEngine()
_ENGINE_LOCK = threading.RLock()
def get_norm_engine() -> NormEngine:
    return _engine
def check_hallucination_norms(
    source_code: str, file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
    session_p0_count: int | None = None,
) -> list[NormViolation]:
    engine = get_norm_engine()
    with _ENGINE_LOCK:
        return engine.check_code(source_code, file_path, _tree=_tree,
                                 session_p0_count=session_p0_count)
def _verdict_envelope(violations: list[NormViolation]) -> dict[str, Any]:
    engine = get_norm_engine()
    return {
        "status": ("blocked" if engine.is_blocked
                   else ("ok" if not violations else "violations")),
        "violations": [v.as_dict() for v in violations],
        "summary": engine.violation_summary,
    }
def check_process_norms(context: dict) -> dict[str, Any]:
    with _ENGINE_LOCK:
        violations = get_norm_engine().check_process(context)
        return _verdict_envelope(violations)
def verify_code_against_norms(
    source_code: str, file_path: str = _DEFAULT_FILE_PATH,
    _tree: ast.AST | None = None,
    session_p0_count: int | None = None,
) -> dict[str, Any]:
    with _ENGINE_LOCK:
        violations = check_hallucination_norms(
            source_code, file_path, _tree=_tree,
            session_p0_count=session_p0_count)
        return _verdict_envelope(violations)

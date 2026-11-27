from __future__ import annotations

import ast
import importlib.util
import os
import re
import sys
from collections.abc import Iterator
from dataclasses import dataclass
from importlib.machinery import PathFinder
from importlib.metadata import packages_distributions
from pathlib import Path
from typing import Any, NamedTuple

from jwsgj.diag_dependency_core import (
    build_symbol_universe,
    import_target_exists,
    namespace_has_symbol,
    relative_target_dir,
    resolve_import_symbol,
)
from jwsgj.diag_module_surface import (
    _extract_all,
    dynamic_module_binding_names,
    iter_match_capture_names,
    iter_module_level_nodes_tc,
    iter_target_py_files,
    iter_walrus_expr_bindings,
    layout_of,
    relative_import_base,
    resolve_namespace_dir,
    strip_root_prefix,
)
from jwsgj.diag_shared_ast_bindings import ScopeNameResolver
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    TRY_STAR,
    coerce_str,
    collect_param_names,
    is_type_checking_guard,
    iter_unpack_target_names,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_source_core import (
    parse_or_none,
    parse_with_compile,
    read_source_auto,
)
from jwsgj.diag_types_defs import (
    PreCheckItem,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    SEVERITY_BLOCKING,
    SEVERITY_WARNING,
    HallucinationType,
    register_review_provider,
)
from jwsgj.log_config import (
    Stopwatch,
    get_module_logger,
    log_swallowed,
    write_module_run,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    infer_project_root,
)
from jwsgj.runtime_scope import (
    PACKAGE_NAME,
    import_key,
    normalize_skill_dir,
)
from jwsgj.shared_cache import SharedCache, get_warmed_cache
from jwsgj.skill_profile import detect_layout, python_import_roots

logger = get_module_logger(__name__)
MIN_PYTHON: tuple[int, int] = (3, 10)
_DEFAULT_FILEPATH = ""
_DEFAULT_PACKAGE = ""
__all__ = [
    "DEP_MODULE_MAP",
    "MIN_PYTHON",
    "TOOLCHAIN_PACKAGES",
    "BrokenImport",
    "BrokenImportFixer",
    "HallucinationFinding",
    "detect_hallucinated_api",
    "detect_hallucinated_import",
    "detect_hallucinated_module",
    "ground_code_symbols",
    "importer_module_file_exists",
    "is_dynamic_callback",
    "is_private_name",
    "module_findable",
    "module_resolvable",
    "normalize_max_findings",
    "normalize_pkg_key",
    "pip_pkg_to_module",
    "preflight_symbol_check",
    "quick_scan_broken_imports",
    "scan_broken_imports",
    "spec_exists",
    "star_import_exports",
]
logger.info("diag_symbol_surface 已加载: %d 项导出", len(__all__))
_SOURCE_ROOT_SUBDIRS = ("scripts", "src", "lib")
def _importer_anchor_candidates(start: str, root: str) -> list[str]:
    anchors: list[str] = []
    within_root = True
    if root:
        try:
            normalized_root = os.path.normcase(root)
            within_root = (os.path.commonpath(
                [os.path.normcase(start), normalized_root]) == normalized_root)
        except (ValueError, OSError):  # jwsgj:silent-ok
            within_root = False
    if within_root:
        cur = start
        for _ in range(12):
            anchors.append(cur)
            if os.path.normcase(cur) == os.path.normcase(root):
                break
            parent = os.path.dirname(cur)
            if parent == cur:
                break
            cur = parent
    if root and os.path.isdir(root):
        anchors.append(root)
        anchors.extend(python_import_roots(root, layout=layout_of(root)))
    return anchors
def _module_exists_from_anchor(anchor: str, module_name: str) -> bool:
    relative_path = module_name.replace(".", os.sep)
    if import_target_exists(os.path.join(anchor, relative_path)):
        return True
    return any(
        import_target_exists(os.path.join(anchor, sub, relative_path))
        for sub in _SOURCE_ROOT_SUBDIRS)
def importer_module_file_exists(module_name: str, project_dir: str,
                                file_path: str) -> bool:
    module_name = coerce_str(module_name).strip()
    project_dir = coerce_str(project_dir)
    file_path = coerce_str(file_path)
    if not module_name or not file_path:
        return False
    start = os.path.dirname(os.path.abspath(file_path))
    root = (os.path.abspath(project_dir) if project_dir
            else infer_project_root(file_path))
    return any(
        _module_exists_from_anchor(anchor, module_name)
        for anchor in _importer_anchor_candidates(start, root))
def module_findable(module_name: str) -> bool:
    _name = coerce_str(module_name).strip()
    if not _name:
        return False
    if sys.modules.get(_name) is not None:
        return True
    return _probe_spec(_name) is not False
def module_resolvable(module_name: str, project_dir: str,
                      file_path: str = _DEFAULT_FILEPATH) -> bool:
    _name = coerce_str(module_name).strip()
    project_dir = coerce_str(project_dir)
    file_path = coerce_str(file_path)
    if not _name:
        return False
    if sys.modules.get(_name) is not None:
        return True
    if project_dir and import_target_exists(os.path.join(
            project_dir, _name.replace(".", os.sep))):
        return True
    if project_dir and not file_path and any(
            _module_exists_from_anchor(import_root, _name)
            for import_root in python_import_roots(
                    project_dir, layout=layout_of(project_dir))):
        return True
    if importer_module_file_exists(_name, project_dir, file_path):
        return True
    return module_findable(_name)
def star_import_exports(module_name: str, level: int = 0) -> set[str] | None:
    if level > 0 or not module_name:
        return None
    try:
        mod = importlib.import_module(module_name)  # lazy-by-design
    except (Exception, SystemExit) as _e:  # noqa: BLE001
        logger.debug('静默降级[star_import_exports:Exc]: %s: %s',
                     type(_e).__name__, _e)
        return None
    exported = getattr(mod, "__all__", None)
    if (exported is not None
            and not isinstance(exported, (str, bytes, bytearray))
            and hasattr(exported, "__iter__")):
        return {name for name in exported if isinstance(name, str)}
    return {name for name in dir(mod) if not name.startswith("_")}
@dataclass
class HallucinationFinding:
    rule_id: str
    hallucination_type: str
    severity: str
    title: str
    description: str
    file_path: str
    line_num: int
    confidence: float = 0.8
    suggestion: str = ""
    evidence: str = ""
    is_hallucination: bool = True
    api_name: str = ""
_DYNAMIC_CALL_WHITELIST: frozenset = frozenset({
    "register", "handle", "handler", "callback", "on_", "setup", "teardown",
    "factory", "create", "build", "make", "init", "start", "stop", "run",
    "main", "entry", "dispatch", "process", "load", "save", "read", "write",
    "get_", "set_", "is_", "has_", "to_", "from_", "apply", "validate",
    "verify", "check", "do_", "run_", "emit", "notify", "trigger",
})
_DYNAMIC_CALL_PREFIXES: frozenset = frozenset(
    p for p in _DYNAMIC_CALL_WHITELIST if p.endswith("_")
)
def is_private_name(name: str) -> bool:
    text = coerce_str(name)
    return text.startswith("_") and not text.startswith("__")
def is_dynamic_callback(name: str) -> bool:
    text = coerce_str(name)
    if not text:
        return False
    if text in _DYNAMIC_CALL_WHITELIST:
        return True
    return any(text.startswith(p) for p in _DYNAMIC_CALL_PREFIXES)
@dataclass
class _ScopeNames:
    defined: set[str]
    imported: set[str]
    calls: list[ast.Call]
def _sn_handle_func_def(
        node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
        names: _ScopeNames) -> None:
    names.defined.add(node.name)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        names.defined |= collect_param_names(node)
def _sn_handle_lambda(node: ast.Lambda, names: _ScopeNames) -> None:
    names.defined |= collect_param_names(node)
def _sn_handle_assign(node: ast.Assign, names: _ScopeNames) -> None:
    for target in node.targets:
        names.defined.update(iter_unpack_target_names(target))
def _sn_handle_ann_assign(node: ast.AnnAssign, names: _ScopeNames) -> None:
    if node.value is not None:
        names.defined.update(iter_unpack_target_names(node.target))
def _sn_handle_with(node: ast.With | ast.AsyncWith,
                    names: _ScopeNames) -> None:
    for item in node.items:
        if item.optional_vars is not None:
            names.defined.update(iter_unpack_target_names(item.optional_vars))
def _sn_handle_except(node: ast.ExceptHandler, names: _ScopeNames) -> None:
    if node.name:
        names.defined.add(node.name)
def _sn_handle_iter_target(
        node: ast.For | ast.AsyncFor | ast.comprehension | ast.NamedExpr,
        names: _ScopeNames) -> None:
    names.defined.update(iter_unpack_target_names(node.target))
def _sn_handle_import(node: ast.Import, names: _ScopeNames) -> None:
    for alias in node.names:
        names.imported.add(alias.asname or alias.name.split(".")[0])
def _sn_handle_import_from(node: ast.ImportFrom, names: _ScopeNames) -> None:
    for alias in node.names:
        if alias.name != "*":
            names.imported.add(alias.asname or alias.name)
def _sn_handle_match_capture(
        node: ast.MatchAs | ast.MatchStar | ast.MatchMapping,
        names: _ScopeNames) -> None:
    match_name = getattr(node, "name", None) or getattr(node, "rest", None)
    if match_name:
        names.defined.add(match_name)
def _sn_handle_type_alias(node, names: _ScopeNames) -> None:
    names.defined.add(node.name.id)
_TYPE_ALIAS = getattr(ast, "TypeAlias", None)
_SCOPE_COLLECT_DISPATCH: dict[type, Any] = {
    ast.FunctionDef: _sn_handle_func_def,
    ast.AsyncFunctionDef: _sn_handle_func_def,
    ast.ClassDef: _sn_handle_func_def,
    ast.Lambda: _sn_handle_lambda,
    ast.Assign: _sn_handle_assign,
    ast.AnnAssign: _sn_handle_ann_assign,
    ast.With: _sn_handle_with,
    ast.AsyncWith: _sn_handle_with,
    ast.ExceptHandler: _sn_handle_except,
    ast.For: _sn_handle_iter_target,
    ast.AsyncFor: _sn_handle_iter_target,
    ast.comprehension: _sn_handle_iter_target,
    ast.NamedExpr: _sn_handle_iter_target,
    ast.Import: _sn_handle_import,
    ast.ImportFrom: _sn_handle_import_from,
    ast.MatchAs: _sn_handle_match_capture,
    ast.MatchStar: _sn_handle_match_capture,
    ast.MatchMapping: _sn_handle_match_capture,
}
if _TYPE_ALIAS is not None:
    _SCOPE_COLLECT_DISPATCH[_TYPE_ALIAS] = _sn_handle_type_alias
def _collect_scope_names(tree: ast.AST) -> tuple[set[str], set[str], list[ast.Call]]:
    names = _ScopeNames(defined=set(), imported=set(), calls=[])
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            names.calls.append(node)
            continue
        handler = _SCOPE_COLLECT_DISPATCH.get(type(node))
        if handler is not None:
            handler(node, names)
    names.calls.sort(key=lambda call: (call.lineno, call.col_offset))
    return names.defined, names.imported, names.calls
def _h01_finding(node: ast.Call, api_name: str, file_path: str, *,
                 severity: str, title: str, description: str,
                 confidence: float, suggestion: str,
                 subject: str) -> HallucinationFinding:
    return HallucinationFinding(
        rule_id="H01",
        hallucination_type=HallucinationType.NAMING.value,
        severity=severity,
        title=title,
        description=description,
        file_path=file_path,
        line_num=node.lineno,
        confidence=confidence,
        suggestion=suggestion,
        evidence=f"ast.Call at line {node.lineno}, {subject}",
        api_name=api_name,
    )
def _h01_name_call_finding(node: ast.Call, call_name: str,
                           file_path: str) -> HallucinationFinding | None:
    subject = f"func=Name('{call_name}')"
    if is_private_name(call_name):
        return _h01_finding(
            node, call_name, file_path,
            severity="P0",
            title=f"幻觉API: 调用未定义的函数 '{call_name}'",
            description=(f"函数 '{call_name}' 不在当前模块定义、导入链或内置"
                         "函数中。_前缀私有名不会被 from X import * 导入。"),
            confidence=0.9,
            suggestion=f"搜索相似函数名或添加导入: from module import {call_name}",
            subject=subject)
    if not call_name[0].isupper() and len(call_name) > 4 and not is_dynamic_callback(call_name):
        return _h01_finding(
            node, call_name, file_path,
            severity="P1",
            title=f"疑似幻觉API: 函数 '{call_name}' 未在当前作用域中定义",
            description=f"函数 '{call_name}' 不在当前模块定义、导入链或内置函数中。",
            confidence=0.5,
            suggestion=f"验证 '{call_name}' 是否在父类、装饰器或动态注入中定义",
            subject=subject)
    return None
def _h01_attr_call_finding(node: ast.Call, obj_name: str,
                           file_path: str) -> HallucinationFinding | None:
    if not is_private_name(obj_name):
        return None
    return _h01_finding(
        node, obj_name, file_path,
        severity="P0",
        title=f"幻觉API: 对象 '{obj_name}' 可能未定义",
        description=(f"对象 '{obj_name}' (_前缀私有名) 不在当前模块定义或"
                     "导入链中。可能为幻觉变量。"),
        confidence=0.85,
        suggestion=f"验证 '{obj_name}' 是否在当前作用域中定义",
        subject=f"func=Attribute(value=Name('{obj_name}'))")
def _resolve_star_exports(
        star_imports: list[tuple[str, int, int]]) -> tuple[set[str], bool]:
    exported: set[str] = set()
    unresolved = False
    for mod, _line, level in star_imports:
        exports = star_import_exports(mod, level)
        if exports is None:
            unresolved = True
        else:
            exported |= exports
    return exported, unresolved
def _merge_available_names(available_names: Any,
                           defined_names: set[str]) -> None:
    if not available_names:
        return
    if isinstance(available_names, (str, bytes, bytearray)):
        _single = coerce_str(available_names)
        if _single:
            defined_names.add(_single)
        return
    if not hasattr(available_names, "__iter__"):
        return
    for _name in available_names:
        _coerced = coerce_str(_name)
        if _coerced:
            defined_names.add(_coerced)
def _h01_name_call_check(
    node: ast.Call, resolver: ScopeNameResolver,
    external_names: set[str], builtin_names: frozenset[str],
    file_path: str,
) -> HallucinationFinding | None:
    call_name = node.func.id
    if (call_name in external_names or call_name in builtin_names
            or resolver.is_bound(node.func)):
        return None
    return _h01_name_call_finding(node, call_name, file_path)
def _h01_attr_call_check(
    node: ast.Call, resolver: ScopeNameResolver,
    external_names: set[str], file_path: str,
) -> HallucinationFinding | None:
    obj_name = node.func.value.id
    if obj_name in external_names or resolver.is_bound(node.func.value):
        return None
    return _h01_attr_call_finding(node, obj_name, file_path)
def _h01_call_check(
    node: ast.Call, resolver: ScopeNameResolver,
    external_names: set[str], builtin_names: frozenset[str],
    star_unresolved: bool, file_path: str,
) -> HallucinationFinding | None:
    if star_unresolved:
        return None
    if isinstance(node.func, ast.Name):
        return _h01_name_call_check(
            node, resolver, external_names, builtin_names, file_path)
    if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
        return _h01_attr_call_check(node, resolver, external_names, file_path)
    return None
def detect_hallucinated_api(
    source_code: str,
    file_path: str = _DEFAULT_FILEPATH,
    available_names: set[str] | None = None,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    file_path = coerce_str(file_path)
    tree = parse_or_none(source_code, _tree)
    if tree is None:
        return []
    findings: list[HallucinationFinding] = []
    defined_names, imported_names, all_calls = _collect_scope_names(tree)
    star_exports, _star_unresolved = _resolve_star_exports(
        _collect_star_imports(tree))
    external_names = set(star_exports)
    _merge_available_names(available_names, external_names)
    resolver = ScopeNameResolver(
        source_code, file_path, tree,
        defined_names | imported_names | external_names | set(BUILTIN_NAMES))
    for node in all_calls:
        finding = _h01_call_check(
            node, resolver, external_names, BUILTIN_NAMES,
            _star_unresolved, file_path)
        if finding is not None:
            findings.append(finding)
    return findings
def _api_existence_prechecks(
        code_content: str,
        filename: str = _DEFAULT_FILEPATH) -> list[PreCheckItem]:
    items: list[PreCheckItem] = []
    if not isinstance(code_content, str) or not code_content.strip():
        return items
    for hf in detect_hallucinated_api(code_content, filename or ""):
        items.append(PreCheckItem(
            category="api_existence",
            severity=SEVERITY_BLOCKING if hf.severity == "P0" else SEVERITY_WARNING,
            description=f"{hf.title} (confidence={hf.confidence})",
            suggestion=hf.suggestion,
            source="hallucination_prevention",
            applicable_to=filename or "code",
            rule_id=hf.rule_id,
            locator=f"{filename or 'code'}:{hf.line_num}",
            confidence=hf.confidence,
            evidence_type="ast",
        ))
    return items
register_review_provider("precreation_api_prechecks", _api_existence_prechecks)
def _format_star_import(module: str, level: int) -> str:
    if level <= 0:
        return module
    return "." * level + (module or "")
def _h02_finding(name: str, line: int, sources: list[str], import_line: int,
                 file_path: str) -> HallucinationFinding:
    joined = " / ".join(f"from {src} import *" for src in sources)
    suggestion = ("添加显式导入: " + " 或 ".join(
        f"from {src} import {name}" for src in sources))
    return HallucinationFinding(
        rule_id="H02",
        hallucination_type=HallucinationType.RESOURCE.value,
        severity="P0",
        title=f"幻觉导入: '{name}' 不会被 {joined} 导入",
        description=(f"import * 默认不绑定 _ 前缀名（源有 __all__ "
                      f"时以 __all__ 为准，该名不在其中）。"
                      f"'{name}' 需要显式导入。"),
        file_path=file_path,
        line_num=line,
        confidence=0.95,
        suggestion=suggestion,
        evidence=(f"{joined} at line {import_line}, "
                  f"usage at line {line}"),
        api_name=name,
    )
def _collect_star_imports(tree: ast.AST) -> list[tuple[str, int, int]]:
    return [
        (node.module or "", node.lineno, node.level or 0)
        for node, import_invisible in iter_module_level_nodes_tc(tree)
        if not import_invisible and isinstance(node, ast.ImportFrom)
        for alias in node.names if alias.name == "*"
    ]
_IMPLICIT_FILE_MODULE_GLOBALS = frozenset({
    "__annotations__", "__builtins__", "__cached__", "__dict__",
    "__file__", "__path__",
})
def _is_star_private_name(name: str) -> bool:
    return (name.startswith("_") and name not in BUILTIN_NAMES
            and name not in _IMPLICIT_FILE_MODULE_GLOBALS)
def _collect_underscore_usage(
        tree: ast.AST, resolver: ScopeNameResolver) -> dict[str, int]:
    underscore_names_used: dict[str, int] = {}
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and _is_star_private_name(node.id)
                and not resolver.is_bound(node)):
            underscore_names_used[node.id] = min(
                node.lineno, underscore_names_used.get(node.id, node.lineno))
    return underscore_names_used
def detect_hallucinated_import(
    source_code: str,
    file_path: str = _DEFAULT_FILEPATH,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    file_path = coerce_str(file_path)
    tree = parse_or_none(source_code, _tree)
    if tree is None:
        return []
    findings: list[HallucinationFinding] = []
    star_imports = _collect_star_imports(tree)
    if not star_imports:
        return findings
    defined_names, imported_names, _calls = _collect_scope_names(tree)
    resolver = ScopeNameResolver(
        source_code, file_path, tree, defined_names | imported_names)
    underscore_names_used = _collect_underscore_usage(tree, resolver)
    star_exports, unresolved = _resolve_star_exports(star_imports)
    sources = [_format_star_import(mod, level)
               for mod, _line, level in star_imports]
    first_line = star_imports[0][1]
    for name, line in sorted(underscore_names_used.items(),
                             key=lambda kv: (kv[1], kv[0])):
        if name in star_exports or unresolved:
            continue
        findings.append(_h02_finding(name, line, sources, first_line,
                                     file_path))
    return findings
_TRY_STMTS = (ast.Try, TRY_STAR)
_IMPORT_GUARD_EXC_NAMES = frozenset({
    "ImportError", "ModuleNotFoundError", "Exception", "BaseException"})
def _iter_guard_body_stmts(body: list[ast.stmt]) -> Iterator[ast.stmt]:
    stack = list(body)
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _except_type_names(node: ast.AST | None) -> list[str]:
    if isinstance(node, ast.Name):
        return [node.id]
    if isinstance(node, ast.Attribute):
        return [node.attr]
    if isinstance(node, ast.Tuple):
        names: list[str] = []
        for elt in node.elts:
            names.extend(_except_type_names(elt))
        return names
    return []
def _is_try_import_guard(node: ast.AST) -> bool:
    if not isinstance(node, _TRY_STMTS):
        return False
    for handler in node.handlers:
        if handler.type is None:
            return True
        if any(n in _IMPORT_GUARD_EXC_NAMES for n in _except_type_names(handler.type)):
            return True
    return False
def _is_type_checking_if(node: ast.AST, typing_aliases: set[str],
                         type_checking_names: set[str]) -> bool:
    return (isinstance(node, ast.If)
            and is_type_checking_guard(
                node.test, typing_aliases, type_checking_names))
def _mark_guarded_imports(body: list[ast.stmt],
                        guarded: set[tuple[int, int]]) -> None:
    for sub in _iter_guard_body_stmts(body):
        if isinstance(sub, (ast.Import, ast.ImportFrom)):
            guarded.add((sub.lineno, sub.col_offset))


def _env_condition_operand(node: ast.AST) -> tuple[str, Any] | None:
    """识别 sys.platform / sys.version_info / os.name 比较的左操作数。"""
    if not isinstance(node, ast.Attribute) or not isinstance(
            node.value, ast.Name):
        return None
    owner, attr = node.value.id, node.attr
    if owner == "sys" and attr in ("platform", "version_info"):
        return f"sys.{attr}", getattr(sys, attr)
    if owner == "os" and attr == "name":
        return "os.name", os.name
    return None


def _env_constant(node: ast.AST, root: str) -> tuple[bool, Any]:
    """按操作数类型归一右操作数字面量；无法静态确认时返回 (False, None)。"""
    if root == "sys.version_info":
        if (isinstance(node, ast.Tuple)
                and all(isinstance(elt, ast.Constant)
                        and isinstance(elt.value, int)
                        and not isinstance(elt.value, bool)
                        for elt in node.elts)):
            return True, tuple(elt.value for elt in node.elts)
        return False, None
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return True, node.value
    if (isinstance(node, ast.Tuple)
            and all(isinstance(elt, ast.Constant)
                    and isinstance(elt.value, str) for elt in node.elts)):
        return True, tuple(elt.value for elt in node.elts)
    return False, None


def _env_conditional_dead_branch(test: ast.AST) -> str | None:
    """按当前解释器求值环境条件比较，返回不会执行的分支名（body/orelse）。

    平台/版本条件下的导入只在对应环境执行，与 TYPE_CHECKING 守卫同理：
    当前环境不会走到的分支不是断裂导入。
    """
    if not isinstance(test, ast.Compare) or len(test.ops) != 1:
        return None
    operand = _env_condition_operand(test.left)
    if operand is None:
        return None
    root, current = operand
    known, expected = _env_constant(test.comparators[0], root)
    if not known:
        return None
    op = test.ops[0]
    try:
        if isinstance(op, ast.Eq):
            live = current == expected
        elif isinstance(op, ast.NotEq):
            live = current != expected
        elif isinstance(op, ast.Lt):
            live = current < expected
        elif isinstance(op, ast.LtE):
            live = current <= expected
        elif isinstance(op, ast.Gt):
            live = current > expected
        elif isinstance(op, ast.GtE):
            live = current >= expected
        elif isinstance(op, ast.In):
            live = current in expected
        elif isinstance(op, ast.NotIn):
            live = current not in expected
        else:
            return None
    except TypeError:
        return None
    return "orelse" if live else "body"


def _collect_guarded_module_import_pos(tree: ast.AST) -> set[tuple[int, int]]:
    guarded: set[tuple[int, int]] = set()
    typing_aliases = typing_guard_aliases(tree)
    type_checking_names = typing_type_checking_names(tree)
    for node in walk_nodes(tree):
        if _is_try_import_guard(node):
            # try 主体与 except 处理器体内的导入同属导入守卫链（tomllib → tomli
            # 这类 fallback 只在当前环境缺失时才执行），不能按断裂导入上报
            _mark_guarded_imports(node.body, guarded)
            for handler in node.handlers:
                _mark_guarded_imports(handler.body, guarded)
            continue
        if _is_type_checking_if(node, typing_aliases, type_checking_names):
            _mark_guarded_imports(node.body, guarded)
            continue
        if isinstance(node, ast.If):
            dead_branch = _env_conditional_dead_branch(node.test)
            if dead_branch is not None:
                _mark_guarded_imports(getattr(node, dead_branch), guarded)
    return guarded
def _import_module_names(node: ast.Import | ast.ImportFrom) -> list[str]:
    if isinstance(node, ast.ImportFrom):
        if node.level > 0 or not node.module:
            return []
        return [node.module]
    return [alias.name for alias in node.names if alias.name != "*"]
def _collect_module_candidates(tree: ast.AST,
                               guarded: set[tuple[int, int]],
                               package: str) -> dict[str, int]:
    candidates: dict[str, int] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        if (node.lineno, node.col_offset) in guarded:
            continue
        if isinstance(node, ast.ImportFrom) and node.level > 0:
            resolved = _resolve_import_target(node, package)
            module_names = [resolved] if resolved else []
        else:
            module_names = _import_module_names(node)
        for module_name in module_names:
            _prev = candidates.get(module_name)
            if _prev is None or node.lineno < _prev:
                candidates[module_name] = node.lineno
    return candidates
def _h09_unresolvable_finding(module_name: str, line: int,
                              file_path: str) -> HallucinationFinding:
    _top = module_name.split(".", maxsplit=1)[0]
    return HallucinationFinding(
        rule_id="H09",
        hallucination_type=HallucinationType.RESOURCE.value,
        severity="P1",
        title=f"幻觉模块: '{module_name}' 无法解析",
        description=(f"模块 '{module_name}' 未安装或拼写错误，也可能"
                      "是尚未创建的项目内部模块；运行时导入将抛"
                      " ImportError/ModuleNotFoundError。"),
        file_path=file_path,
        line_num=line,
        confidence=0.6,
        suggestion=(f"检查 '{module_name}' 拼写或安装依赖"
                    f"（pip install {_top}）；项目内部模块请确认"
                    "对应文件已创建"),
        evidence=(f"import of '{module_name}' at line {line}: "
                   "sys.modules/find_spec/项目目录均未命中"),
        api_name=module_name,
    )
def detect_hallucinated_module(
    source_code: str,
    file_path: str = _DEFAULT_FILEPATH,
    *,
    project_dir: str = "",
    package: str = _DEFAULT_PACKAGE,
    _tree: ast.AST | None = None,
) -> list[HallucinationFinding]:
    file_path = coerce_str(file_path)
    project_dir = coerce_str(project_dir).strip()
    package = coerce_str(package).strip()
    tree = parse_or_none(source_code, _tree)
    if tree is None:
        return []
    findings: list[HallucinationFinding] = []
    guarded = _collect_guarded_module_import_pos(tree)
    candidates = _collect_module_candidates(tree, guarded, package)
    for module_name, line in sorted(candidates.items(), key=lambda kv: kv[1]):
        if module_resolvable(module_name, project_dir, file_path):
            continue
        findings.append(_h09_unresolvable_finding(module_name, line, file_path))
    return findings
class _UniverseView(NamedTuple):
    modules: dict
    unparsed: set[str]
    status: str
class _ImportFace(NamedTuple):
    exact_target: str
    reported_target: str
    legal: set[str]
    all_list: list | None
def _parent_module_candidates(dotted: str) -> Iterator[str]:
    parts = dotted.split(".")
    for cut in range(len(parts) - 1, 0, -1):
        yield ".".join(parts[:cut])
def _resolve_import_target(node: ast.ImportFrom, package: str) -> str | None:
    if node.level == 0:
        return node.module or None
    base = _relative_base(package, node.level)
    if base is None:
        return None
    return f"{base}.{node.module}" if node.module else base
def _relative_base(package: str, level: int) -> str | None:
    if not isinstance(package, str) or not package:
        return None
    parts = package.split(".")
    cut = len(parts) - (level - 1)
    return ".".join(parts[:cut]) if cut > 0 else None
def _match_universe_module(target: str, modules: dict) -> str | None:
    if target in modules:
        return target
    candidates = _parent_module_candidates(target)
    return next((c for c in candidates if c in modules), None)
def _submodule_names(prefix: str, modules: dict,
                     unparsed: set[str]) -> set[str]:
    head = prefix + "."
    names: set[str] = set()
    for name_src in (modules, unparsed):
        names.update(key[len(head):].split(".")[0]
                     for key in name_src if key.startswith(head))
    return names
def _legal_import_face(exact_target: str, modules: dict,
                       unparsed: set[str]) -> set[str]:
    info = modules[exact_target]
    all_list = info.get("all")
    legal = set(info["symbols"])
    if all_list and info.get("star_reexport"):
        legal.update(all_list)
    legal.update(_submodule_names(exact_target, modules, unparsed))
    return legal
def _unknown_symbol_detail(exact_target: str, reported_target: str,
                          name: str, all_list: list | None) -> str:
    if reported_target == exact_target:
        base = f"模块 {exact_target} 不存在符号 {name}"
    else:
        base = (f"导入源 {reported_target} 未提供符号 {name}"
                f"（仅核对目标下已发现子模块，不继承父模块 {exact_target} 的符号）")
    return base + (f"（__all__={sorted(all_list)}）" if all_list else "")
def _unknown_symbol_findings(node: ast.ImportFrom, exact_target: str,
                             reported_target: str, legal: set[str],
                             all_list: list | None) -> Iterator[dict[str, Any]]:
    for alias in node.names:
        if alias.name == "*":
            continue
        if alias.name not in legal:
            yield {
                "kind": "unknown_symbol",
                "line": node.lineno,
                "name": alias.name,
                "module": exact_target,
                "detail": _unknown_symbol_detail(
                    exact_target, reported_target, alias.name, all_list),
            }
def _normalize_universe_package_names(project_dir: str, modules: dict,
                                      unparsed: set[str]) -> tuple[dict, set[str]]:
    layout = detect_layout(project_dir)
    if not layout.is_package:
        return modules, unparsed
    try:
        relative_root = Path(layout.package_root).relative_to(Path(layout.root))
    except (OSError, ValueError):  # jwsgj:silent-ok
        return modules, unparsed
    source_prefix = ".".join(relative_root.parts)
    import_prefix = ".".join(relative_root.parent.parts)
    import_prefix_dot = f"{import_prefix}." if import_prefix else ""
    package_name = layout.package_name
    package_root_key = os.path.normcase(os.path.realpath(layout.package_root))
    import_root_keys = {
        os.path.normcase(os.path.realpath(path))
        for path in python_import_roots(project_dir, layout=layout)
    }
    source_root_is_import_root = package_root_key in import_root_keys
    def _import_name(name: str) -> str:
        if not isinstance(name, str) or not name:
            return ""
        if source_prefix and source_root_is_import_root:
            if name == source_prefix:
                return ""
            prefix = source_prefix + "."
            if name.startswith(prefix):
                return name[len(prefix):]
        if not source_prefix:
            return (package_name if name == "__root__"
                    else f"{package_name}.{name}")
        if name == source_prefix:
            return package_name
        prefix = source_prefix + "."
        if name.startswith(prefix):
            return f"{package_name}.{name[len(prefix):]}"
        if not import_prefix:
            return name
        if name.startswith(import_prefix_dot):
            return name[len(import_prefix_dot):]
        return ""
    return (
        {import_name: entry for name, entry in modules.items()
         if (import_name := _import_name(name))},
        {import_name for name in unparsed
         if (import_name := _import_name(name))},
    )
def _load_universe(project_dir: str) -> _UniverseView:
    universe = build_symbol_universe(project_dir)
    udata = universe.get("data", {})
    modules, unparsed = _normalize_universe_package_names(
        project_dir, udata.get("modules", {}),
        set(udata.get("unparsed_modules") or []))
    return _UniverseView(
        modules, unparsed, universe.get("status", "ok"))
def _symbol_result(status: str, findings: list[dict], modules_scanned: int,
                   message: str) -> dict:
    return {
        "status": status,
        "data": {
            "ok": status != "error" and not findings,
            "findings": findings,
            "modules_scanned": modules_scanned,
        },
        "message": message,
    }
def _skip_result(modules: dict, status: str) -> dict:
    return _symbol_result("ok" if modules else status, [], len(modules),
                          "空代码或无模块可对照，跳过符号 grounding")
def _syntax_error_result(error: Exception, modules: dict) -> dict:
    finding = {"kind": "syntax_error", "line": getattr(error, "lineno", 0),
               "name": "", "module": "", "detail": str(error)}
    return _symbol_result("error", [finding], len(modules),
                          f"代码片段语法错误: {error}")
def _import_face(node: ast.ImportFrom, package: str, modules: dict,
                 unparsed: set[str]) -> _ImportFace | None:
    target = _resolve_import_target(node, package)
    if not target or target in unparsed:
        return None
    exact_target = _match_universe_module(target, modules)
    if exact_target is None:
        return None
    if exact_target != target and any(
            candidate in unparsed
            for candidate in _parent_module_candidates(target)):
        return None
    if exact_target == target:
        if modules[exact_target].get("export_open"):
            return None
        legal = _legal_import_face(exact_target, modules, unparsed)
        return _ImportFace(exact_target, target, legal,
                           modules[target].get("all"))
    legal = _submodule_names(target, modules, unparsed)
    return _ImportFace(exact_target, target, legal, None)
_DEFAULT_MAX_FINDINGS = 100
def normalize_max_findings(value: object) -> int:
    if isinstance(value, bool):
        return _DEFAULT_MAX_FINDINGS
    try:
        limit = int(value)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError) as _swallow_e:
        log_swallowed(
            __name__, _swallow_e,
            context=f"normalize_max_findings:{type(_swallow_e).__name__}")
        return _DEFAULT_MAX_FINDINGS
    return max(0, limit)
def _finding_order_key(finding: dict) -> int:
    return finding["line"]
def _collect_import_findings(tree: ast.AST, package: str, modules: dict,
                             unparsed: set[str],
                             max_findings: int) -> list[dict]:
    findings: list[dict] = []
    guarded = _collect_guarded_module_import_pos(tree)
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.ImportFrom)
                or (node.lineno, node.col_offset) in guarded):
            continue
        face = _import_face(node, package, modules, unparsed)
        if face is None:
            continue
        findings.extend(_unknown_symbol_findings(
            node, face.exact_target, face.reported_target,
            face.legal, face.all_list))
    findings.sort(key=_finding_order_key)
    return findings[:max_findings]
def ground_code_symbols(
    code: str,
    project_dir: str,
    *,
    package: str = _DEFAULT_PACKAGE,
    max_findings: int = _DEFAULT_MAX_FINDINGS,
) -> dict:
    project_dir = coerce_str(project_dir).strip()
    view = _load_universe(project_dir)
    modules, unparsed = view.modules, view.unparsed
    if not (isinstance(code, str) and code.strip()) or not modules:
        return _skip_result(modules, view.status)
    try:
        tree = parse_with_compile(code, "<symbol_grounding>")
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[symbol_grounding] 代码片段语法错误: %s", e)
        return _syntax_error_result(e, modules)
    findings = _collect_import_findings(
        tree, package, modules, unparsed, normalize_max_findings(max_findings))
    return _symbol_result(
        "ok", findings, len(modules),
        f"发现 {len(findings)} 条符号幻觉" if findings else "符号 grounding 通过")
def preflight_symbol_check(
        code: str, project_dir: str,
        *, package: str = _DEFAULT_PACKAGE) -> dict:
    result = ground_code_symbols(code, project_dir, package=package)
    if result.get("status") == "error" and not result.get("data", {}).get(
            "findings"):
        return _symbol_result("ok", [], 0,
                              "符号 grounding 环境不可用，降级跳过")
    return result
_STDLIB_MODULE_NAMES = getattr(sys, "stdlib_module_names", frozenset())
def _is_stdlib_module(module_name: str) -> bool:
    return module_name.split(".", maxsplit=1)[0] in _STDLIB_MODULE_NAMES
class _FuzzyNeedle(NamedTuple):
    name: str
    parts: tuple[str, ...]
    chars: set[str]
    char_threshold: int
def _parts_overlap(parts: list[str], needle: _FuzzyNeedle) -> tuple[bool, int]:
    common = len(set(parts) & set(needle.parts))
    hit = (common >= 2
           or (common >= 1 and parts[0] == needle.parts[0]
               and parts[-1] == needle.parts[-1]))
    return hit, common
def _fuzzy_score(name: str, needle: _FuzzyNeedle) -> int:
    if needle.name in name or name in needle.name:
        return 100
    hit, common_parts = _parts_overlap(name.split('.'), needle)
    if hit:
        return 50 + common_parts * 5
    common_chars = len(needle.chars & set(name))
    return common_chars if common_chars >= needle.char_threshold else 0
def _load_scan_tree(
        py_file: Path, cache: SharedCache | None) -> tuple[ast.AST | None, str]:
    if cache is not None:
        _src, tree = cache.get_source_and_ast(str(py_file))
        if tree is not None:
            return tree, ""
        logger.warning("[BrokenImportScan] 跳过 %s: 源码不可解析", py_file.name)
        return None, "源码不可解析（缓存通道）"
    try:
        content = read_source_auto(py_file)
        return compile(content, str(py_file), 'exec', ast.PyCF_ONLY_AST), ""
    except (OSError, *PARSE_DEGRADE_EXC) as e:
        logger.warning("[BrokenImportScan] 跳过 %s: %s", py_file.name, e)
        return None, f"{type(e).__name__}: {e}"
@dataclass
class BrokenImport:
    file_path: str
    line_no: int
    import_stmt: str
    target_module: str
    is_relative: bool = False
    expected_path: str = ""
    exists: bool = False
    suggestion: str = ""
    severity: str = "MEDIUM"
@dataclass(frozen=True)
class _BrokenImportEvidence:
    import_stmt: str
    target_module: str | None
    expected_path: str
    exists: bool
    suggestion: str
    severity: str
    is_relative: bool
@dataclass(frozen=True)
class _SymbolResolutionTarget:
    expected_path: str
    target_file: Path | None = None
    symbol_root: Path | None = None
    is_relative: bool = False
def _probe_spec(import_name: str) -> bool | None:
    try:
        return importlib.util.find_spec(import_name) is not None
    except (ImportError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f"_probe_spec:{type(_e).__name__}")
        return False
    except (Exception, SystemExit) as exc:  # noqa: BLE001
        logger.warning("find_spec 探测异常，结论不确定: %s (%s)",
                       import_name, exc)
        return None
def _index_keys(rel_path: Path) -> tuple[str, ...]:
    parts = list(rel_path.parts)
    fname = parts[-1]
    stem = fname[:-3] if fname.lower().endswith('.py') else fname
    is_facade = fname.lower() == '__init__.py'
    if is_facade:
        module_name = '.'.join(parts[:-1]) if len(parts) > 1 else ''
    else:
        module_name = '.'.join(parts[:-1] + [stem])
    return (module_name,) if module_name else ()
def _path_within_root(root: Path, path: Path) -> Path | None:
    candidate = Path(os.path.abspath(str(path)))
    root_abs = Path(os.path.abspath(str(root)))
    real_root = os.path.realpath(str(root_abs))
    real_candidate = os.path.realpath(str(candidate))
    try:
        relative = os.path.relpath(real_candidate, real_root)
    except (OSError, ValueError):
        return None
    if relative == os.pardir or relative.startswith(os.pardir + os.sep):
        return None
    return root_abs if relative == os.curdir else root_abs / relative
def _is_script_import_context(py_file: Path) -> bool:
    return not (py_file.parent / '__init__.py').is_file()
class _ModuleIndex:
    def __init__(self, project_root: Path) -> None:
        self.project_root = project_root
        layout = detect_layout(str(project_root))
        package_root = (Path(layout.package_root) if layout.package_root
                        else project_root)
        mapped_source_root = _path_within_root(project_root, package_root)
        if mapped_source_root is None:
            logger.warning(
                "[BrokenImportScan] 包根越出项目根，回退项目根: %s", package_root)
        self.source_root = mapped_source_root or project_root
        self.package_name = layout.package_name
        self._import_roots = python_import_roots(
            str(project_root), layout=layout)
        self.entries: dict[str, str] = {}
    def _target_roots(self, module_name: str) -> tuple[Path, ...]:
        if os.path.normcase(str(self.source_root)) == os.path.normcase(
                str(self.project_root)):
            return (self.source_root,)
        top = module_name.split('.', 1)[0]
        package_names = {import_key(self.package_name),
                         import_key(self.project_root.name)}
        if (top and (self.source_root / '__init__.py').is_file()
                and import_key(self.source_root.name) == import_key(
                    self.package_name) and import_key(top) not in package_names):
            import_root = self.source_root.parent
            if import_root == self.project_root:
                return (self.project_root,)
            return (import_root, self.project_root)
        return (self.source_root, self.project_root)
    def _search_roots(self, py_file: Path) -> list[str]:
        roots = list(self._import_roots)
        if _is_script_import_context(py_file):
            roots.insert(0, str(py_file.parent))
        return list(dict.fromkeys(roots))
    def _relative_absolute_name(
            self, py_file: Path, module_name: str, level: int) -> str | None:
        rel_dir = relative_import_base(py_file, level, self.project_root)
        if rel_dir is None:
            return None
        for root_text in self._import_roots:
            try:
                relative = rel_dir.relative_to(Path(root_text))
            except ValueError:
                continue
            parts = ([] if str(relative) == os.curdir
                     else list(relative.parts))
            if not all(part.isidentifier() for part in parts):
                continue
            if module_name:
                parts.extend(module_name.split('.'))
            return '.'.join(parts) if parts else None
        return None
    def _nonpackage_parent_in_roots(
            self, module_name: str, roots: list[str]) -> str | None:
        if sys.modules.get(module_name) is not None:
            return None
        parts = module_name.split('.')
        if len(parts) < 2 or not all(part.isidentifier() for part in parts):
            return None
        spec = PathFinder.find_spec(parts[0], roots)
        for depth in range(1, len(parts)):
            if spec is None:
                return None
            locations = spec.submodule_search_locations
            if locations is None:
                origin = spec.origin
                if origin and (not origin.lower().endswith('.py')
                               or resolve_import_symbol(
                                   self.project_root, Path(origin), '__path__')):
                    return None
                return '.'.join(parts[:depth])
            spec = PathFinder.find_spec(parts[depth], list(locations))
        return None
    def nonpackage_parent(
            self, py_file: Path, module_name: str, level: int = 0) -> str | None:
        if level > 0:
            absolute_name = self._relative_absolute_name(
                py_file, module_name, level)
            if absolute_name is None:
                return None
            return self._nonpackage_parent_in_roots(
                absolute_name, list(self._import_roots))
        return self._nonpackage_parent_in_roots(
            module_name, self._search_roots(py_file))
    def _package_first_candidates(
            self, parts: list[str], module_name: str) -> list[Path]:
        candidates: list[Path] = []
        for root in self._target_roots(module_name):
            base = root.joinpath(*parts)
            module_file = (base if base.suffix == '.py'
                           else base.with_suffix('.py'))
            candidates.extend((base / '__init__.py', module_file))
        return candidates
    def build(self) -> None:
        self.entries.clear()
        for py_file in iter_target_py_files(
                self.project_root, include_tests=False):
            rel = str(py_file.relative_to(self.project_root))
            keys: list[str] = []
            try:
                module_rel = py_file.relative_to(self.source_root)
            except ValueError:  # jwsgj:silent-ok
                module_rel = None
            if module_rel is not None:
                keys.extend(self._import_keys(module_rel))
            for key in _index_keys(Path(rel)):
                if key not in keys:
                    keys.append(key)
            for key in keys:
                self.entries[key] = rel
    def _import_keys(self, module_rel: Path) -> tuple[str, ...]:
        keys = _index_keys(module_rel)
        if not keys or not self.package_name:
            return keys
        if os.path.normcase(str(self.source_root)) == os.path.normcase(
                str(self.project_root)):
            return keys
        return tuple(f"{self.package_name}.{key}" for key in keys)
    def _rel_to_root(self, cand: Path) -> str | None:
        mapped = _path_within_root(self.project_root, cand)
        if mapped is None:
            return None
        try:
            return str(mapped.relative_to(self.project_root))
        except ValueError as _e:
            log_swallowed(
                __name__, _e,
                context=f"_ModuleIndex._rel_to_root:{type(_e).__name__}")
            return None
    def resolve_target_path(self, py_file: Path, node: ast.ImportFrom) -> tuple[str | None, bool]:
        if node.level > 0:
            return self._resolve_relative_target(py_file, node)
        if _is_script_import_context(py_file):
            expected, is_relative = self._resolve_script_dir_target(py_file, node)
            if expected is not None:
                return expected, is_relative
        return self._resolve_absolute_target(node)
    def _resolve_script_dir_target(
            self, py_file: Path,
            node: ast.ImportFrom) -> tuple[str | None, bool]:
        if node.module is None:
            return None, False
        base = py_file.parent.joinpath(*node.module.split('.'))
        for cand in (base / '__init__.py', base.with_suffix('.py')):
            if cand.exists():
                return self._rel_to_root(cand), False
        return None, False
    def _resolve_relative_target(self, py_file: Path,
                                node: ast.ImportFrom) -> tuple[str | None, bool]:
        rel_dir = relative_import_base(py_file, node.level, self.project_root)
        if rel_dir is None:
            return None, True
        src_path = (rel_dir / node.module.replace('.', '/')
                    if node.module else rel_dir / '__init__.py')
        candidates: list[Path] = []
        if src_path.suffix != '.py':
            candidates.append(src_path / '__init__.py')
            candidates.append(src_path.with_suffix('.py'))
        else:
            candidates.append(src_path)
        for cand in candidates:
            if cand.exists():
                return self._rel_to_root(cand), True
        return None, True
    def _resolve_absolute_target(self, node: ast.ImportFrom) -> tuple[str | None, bool]:
        if node.module is None:
            return None, False
        parts = strip_root_prefix(self.project_root, node.module)
        if not parts:
            root_init = self.source_root / '__init__.py'
            if root_init.exists():
                return self._rel_to_root(root_init), False
            return None, False
        for cand in self._package_first_candidates(parts, node.module):
            if cand.exists():
                return self._rel_to_root(cand), False
        return None, False
    def module_target_paths(
            self, parts: list[str], module_name: str) -> list[Path]:
        paths = self._package_first_candidates(parts, module_name)
        for root in self._target_roots(module_name):
            paths.append(root.joinpath(*parts))
        return paths
    def resolve_cross_skill_root(self, module_name: str):
        top = module_name.split(".", 1)[0]
        own_names = {import_key(self.project_root.name),
                     import_key(self.package_name)}
        if top in own_names:
            return None
        parent = self.project_root.parent
        sibling = parent / top
        if sibling.is_dir():
            return sibling
        try:
            return next(
                candidate for candidate in sorted(parent.iterdir())
                if candidate.is_dir() and import_key(candidate.name) == top)
        except StopIteration:
            return None
        except OSError as exc:
            log_swallowed(
                __name__, exc,
                context=(f"_ModuleIndex.resolve_cross_skill_root:"
                         f"{type(exc).__name__}"))
            return None
    def cross_skill_target_exists(self, module_name: str) -> bool:
        cross_root = self.resolve_cross_skill_root(module_name)
        if cross_root is None:
            return False
        rest = module_name.split(".")[1:]
        if not rest:
            return cross_root.is_dir()
        target = cross_root / "/".join(rest)
        return (target.with_suffix(".py").exists()
                or (target / "__init__.py").exists()
                or target.is_dir())
    def resolve_scan_targets(self, filepath: str | None) -> list[Path]:
        if not filepath:
            return list(iter_target_py_files(
                self.project_root, include_tests=False))
        cand = Path(filepath)
        if not cand.is_absolute():
            cand = self.project_root / cand
        mapped = _path_within_root(self.project_root, cand)
        if mapped is None:
            logger.warning(
                "[BrokenImportScan] 跳过项目根之外的扫描目标: %s", cand)
            return []
        if mapped.is_dir():
            return list(iter_target_py_files(mapped, include_tests=False))
        if not mapped.is_file():
            raise FileNotFoundError(f"扫描目标不存在或不是文件: {mapped}")
        return [mapped]
    def fuzzy_match(self, target_name: str) -> list[str]:
        needle = _FuzzyNeedle(
            name=target_name,
            parts=tuple(target_name.split('.')),
            chars=set(target_name),
            char_threshold=max(3, len(target_name) // 2),
        )
        scored: list[tuple[int, int, str, str]] = []
        for name, path in self.entries.items():
            score = _fuzzy_score(name, needle)
            if score > 0:
                scored.append((score, len(needle.chars & set(name)), name, path))
        scored.sort(key=lambda x: (-x[0], -x[1], x[2]))
        return [f"{name} ({path})" for _, _, name, path in scored[:5]]
def _require_project_root(project_root: Any, who: str) -> Path:
    root_text = coerce_str(project_root).strip()
    if not root_text:
        raise ValueError(
            f"{who}: 项目根不能为空（空根会静默落到进程 cwd）")
    resolved = Path(normalize_skill_dir(os.path.expanduser(root_text)))
    if not resolved.is_dir():
        raise FileNotFoundError(f"{who}: 项目根不存在: {resolved}")
    return resolved
class BrokenImportFixer:
    def __init__(self, project_root: str) -> None:
        self.project_root = _require_project_root(
            project_root, "BrokenImportFixer")
        self.broken_imports: list[BrokenImport] = []
        self.skipped_files: list[dict[str, str]] = []
        self._index = _ModuleIndex(self.project_root)
        self._cache: SharedCache | None = None
    def scan(self, filepath: str | None = None,
             cache: SharedCache | None = None) -> BrokenImportFixer:
        self._index.build()
        self.broken_imports.clear()
        self.skipped_files.clear()
        self._cache = cache
        for py_file in self._index.resolve_scan_targets(filepath):
            tree, reason = _load_scan_tree(py_file, self._cache)
            if tree is None:
                self.skipped_files.append({
                    "file": str(py_file.relative_to(self.project_root)),
                    "reason": reason,
                })
                continue
            self._check_tree(py_file, tree)
        self.broken_imports.sort(key=lambda item: (item.file_path, item.line_no))
        return self
    def _check_tree(self, py_file: Path, tree: ast.AST) -> None:
        guarded = _collect_guarded_module_import_pos(tree)
        for node in walk_nodes(tree):
            if (isinstance(node, (ast.ImportFrom, ast.Import))
                    and (node.lineno, node.col_offset) in guarded):
                continue
            if isinstance(node, ast.ImportFrom):
                self._check_import_from(py_file, node, tree)
            elif isinstance(node, ast.Import):
                self._check_import(py_file, node)
    def _emit_broken(self, py_file: Path, node: ast.AST,
                     evidence: _BrokenImportEvidence) -> None:
        self.broken_imports.append(BrokenImport(
            file_path=str(py_file.relative_to(self.project_root)),
            line_no=node.lineno,
            **vars(evidence),
        ))
    def _check_import_from(self, py_file: Path, node: ast.ImportFrom,
                           source_tree: ast.AST | None = None) -> None:
        if node.module is None:
            self._check_relative_bare_imports(
                py_file, node, source_tree=source_tree)
            return
        if (node.level == 0 and _is_stdlib_module(node.module)
                and module_findable(node.module)):
            return
        nonpackage = self._index.nonpackage_parent(
            py_file, node.module, node.level)
        if nonpackage is not None:
            self._emit_nonpackage_parent(
                py_file, node, node.module, nonpackage)
            return
        expected_path, is_relative = self._index.resolve_target_path(py_file, node)
        if expected_path is not None:
            self._check_symbol_resolution(
                py_file, node, _SymbolResolutionTarget(
                    expected_path, is_relative=is_relative),
                source_tree=source_tree)
            return
        self._check_unresolved_from_import(
            py_file, node, is_relative=is_relative)
    def _emit_out_of_root(self, py_file: Path, node: ast.AST, *,
                          import_stmt: str, target_module: str) -> None:
        self._emit_broken(
            py_file, node, _BrokenImportEvidence(
                import_stmt=import_stmt, target_module=target_module,
                is_relative=True, expected_path="OUT OF PROJECT ROOT",
                exists=False, severity="HIGH",
                suggestion="相对导入越过项目根，运行时必然报"
                           " beyond top-level package"))
    def _emit_unresolved_module(self, py_file: Path, node: ast.AST, *,
                                import_stmt: str, target_module: str) -> None:
        suggestions = self._index.fuzzy_match(target_module)
        self._emit_broken(
            py_file, node, _BrokenImportEvidence(
                import_stmt=import_stmt, target_module=target_module,
                expected_path="NOT FOUND", exists=False, severity="HIGH",
                is_relative=False,
                suggestion=('; '.join(suggestions) if suggestions else "无匹配")))
    def _emit_nonpackage_parent(
            self, py_file: Path, node: ast.AST, target_module: str,
            parent: str) -> None:
        is_relative = isinstance(node, ast.ImportFrom) and node.level > 0
        dots = '.' * node.level if isinstance(node, ast.ImportFrom) else ''
        self._emit_broken(
            py_file, node, _BrokenImportEvidence(
                import_stmt=f"from {dots}{target_module} import ..."
                if isinstance(node, ast.ImportFrom)
                else f"import {target_module}",
                target_module=target_module,
                expected_path=f"NOT A PACKAGE: {parent}",
                exists=False, severity="HIGH", is_relative=is_relative,
                suggestion=(f"父级模块 {parent} 不是包，不能导入其子模块；"
                            "请移除同名模块/包冲突或改为有效的包导入")))
    def _check_unresolved_from_import(self, py_file: Path,
                                   node: ast.ImportFrom, *,
                                   is_relative: bool) -> None:
        if is_relative:
            self._check_unresolved_relative(py_file, node)
            return
        if module_findable(node.module):
            return
        if _is_script_import_context(py_file):
            script_ns_dir = resolve_namespace_dir(py_file.parent, node.module)
            if script_ns_dir is not None:
                self._check_ns_import_fallback(py_file, node, script_ns_dir)
                return
        ns_dir = resolve_namespace_dir(self.project_root, node.module)
        if ns_dir is not None:
            self._check_ns_import_fallback(py_file, node, ns_dir)
            return
        cross_root = self._index.resolve_cross_skill_root(node.module)
        if cross_root is not None:
            self._check_cross_skill_imports(py_file, node, cross_root)
            return
        self._emit_unresolved_module(
            py_file, node, import_stmt=f"from {node.module} import ...",
            target_module=node.module)
    def _check_ns_import_fallback(self, py_file: Path,
                                   node: ast.ImportFrom,
                                   ns_dir: Path,
                                   is_relative: bool = False) -> None:
        module_name = node.module or ns_dir.name
        dots = '.' * node.level if is_relative else ''
        for alias in node.names:
            if alias.name == "*":
                continue
            if namespace_has_symbol(ns_dir, alias.name):
                continue
            self._emit_broken(
                py_file, node, _BrokenImportEvidence(
                    import_stmt=f"from {dots}{node.module or ''} import {alias.name}",
                    target_module=module_name,
                    expected_path=f"NOT FOUND (namespace: {module_name})",
                    exists=False, severity="MEDIUM", is_relative=is_relative,
                    suggestion=(f"{alias.name} 既非 {module_name} 的子模块"
                                "也非其子包（namespace 形态不可解析）")))
    def _check_cross_skill_imports(self, py_file: Path, node: ast.ImportFrom,
                                  cross_root: Path) -> None:
        rest = node.module.split(".")[1:]
        target = cross_root / "/".join(rest) if rest else cross_root
        candidates = ((target / "__init__.py",) if not rest
                      else (target / "__init__.py",
                            target.with_suffix(".py")))
        for cand in candidates:
            if cand.exists():
                self._check_symbol_resolution(
                    py_file, node, _SymbolResolutionTarget(
                        expected_path="cross-skill: " + node.module,
                        target_file=cand, symbol_root=cross_root))
                return
        if self._report_cross_skill_ns_fallback(
                py_file, node, target, rest, cross_root):
            return
        self._emit_broken(
            py_file, node, _BrokenImportEvidence(
                import_stmt=f"from {node.module} import ...",
                target_module=node.module,
                expected_path=f"NOT FOUND (cross-skill: {cross_root.name})",
                exists=False, severity="HIGH", is_relative=False,
                suggestion=f"兄弟技能 {cross_root.name} 中不存在模块 {node.module}"))
    def _report_cross_skill_ns_fallback(self, py_file: Path,
                                      node: ast.ImportFrom, target: Path,
                                      rest: list[str],
                                      cross_root: Path) -> bool:
        if not rest:
            self._report_missing_ns_symbols(
                py_file, node, cross_root,
                owner_desc=f"兄弟技能包根 {cross_root.name} ")
            return True
        if target.is_dir():
            self._report_missing_ns_symbols(
                py_file, node, target,
                owner_desc=(f"命名空间目录 {node.module}（兄弟技能 "
                            f"{cross_root.name}）"))
            return True
        return False
    def _report_missing_ns_symbols(self, py_file: Path,
                                   node: ast.ImportFrom,
                                   base_dir: Path, owner_desc: str) -> None:
        missing = [
            a.name for a in node.names
            if a.name != "*" and not namespace_has_symbol(base_dir, a.name)]
        if not missing:
            return
        self._emit_broken(
            py_file, node, _BrokenImportEvidence(
                import_stmt=f"from {node.module} import ...",
                target_module=node.module,
                expected_path=f"NOT FOUND (cross-skill-namespace: {node.module})",
                exists=False, severity="HIGH", is_relative=False,
                suggestion=(owner_desc + "中不存在子模块/子包: "
                            + ", ".join(missing))))
    def _check_unresolved_relative(self, py_file: Path,
                                   node: ast.ImportFrom) -> None:
        target_dir = relative_target_dir(
            str(py_file), node.level, str(self.project_root))
        dots = '.' * node.level
        if target_dir is None:
            self._emit_out_of_root(
                py_file, node,
                import_stmt=f"from {dots}{node.module} import ...",
                target_module=node.module)
            return
        target = Path(target_dir) / node.module.replace('.', '/')
        if target.is_dir():
            self._check_ns_import_fallback(
                py_file, node, target, is_relative=True)
            return
        suggestions = self._index.fuzzy_match(node.module)
        self._emit_broken(
            py_file, node, _BrokenImportEvidence(
                import_stmt=f"from {dots}{node.module} import ...",
                target_module=node.module, is_relative=True,
                expected_path=str(target), exists=False, severity="HIGH",
                suggestion=('; '.join(suggestions)
                            if suggestions else "无匹配")))
    def _check_relative_bare_imports(
            self, py_file: Path, node: ast.ImportFrom,
            source_tree: ast.AST | None = None) -> None:
        target_dir = relative_target_dir(
            str(py_file), node.level, str(self.project_root))
        if target_dir is None:
            self._emit_out_of_root(
                py_file, node,
                import_stmt=f"from {'.' * node.level} import ...",
                target_module="")
            return
        rel_dir = Path(target_dir)
        init = rel_dir / '__init__.py'
        if not init.exists():
            self._check_ns_import_fallback(
                py_file, node, rel_dir, is_relative=True)
            return
        try:
            expected = str(init.relative_to(self.project_root))
        except ValueError as _e:
            log_swallowed(
                __name__, _e,
                context=("_check_relative_bare_imports:"
                         f"{type(_e).__name__}"))
            expected = str(init)
        for alias in node.names:
            if alias.name == '*':
                continue
            if self._symbol_resolvable(
                    py_file, init, alias.name, source_tree=source_tree,
                    source_node=node):
                continue
            self._emit_broken(
                py_file, node, _BrokenImportEvidence(
                    import_stmt=f"from {'.' * node.level} import {alias.name}",
                    target_module=rel_dir.name, is_relative=True,
                    expected_path=expected,
                    exists=True,
                    severity="MEDIUM",
                    suggestion=(f"符号 {alias.name} 不存在于包 {rel_dir.name}"
                                "（已迁移/改名？）")))
    def _check_symbol_resolution(
            self, py_file: Path, node: ast.ImportFrom,
            target: _SymbolResolutionTarget,
            source_tree: ast.AST | None = None) -> None:
        resolved_file = (target.target_file if target.target_file is not None
                         else self.project_root / target.expected_path)
        root = target.symbol_root or self.project_root
        expected_path = target.expected_path
        module_repr = f"{'.' * node.level}{node.module or ''}"
        for alias in node.names:
            if alias.name == "*":
                continue
            symbol = alias.name
            if self._symbol_resolvable(
                    py_file, resolved_file, symbol,
                    symbol_root=root, source_tree=source_tree,
                    source_node=node):
                continue
            self._emit_broken(
                py_file, node, _BrokenImportEvidence(
                    import_stmt=f"from {module_repr} import {symbol}",
                    target_module=node.module, is_relative=target.is_relative,
                    expected_path=expected_path,
                    exists=True,
                    severity="MEDIUM",
                    suggestion=f"符号 {symbol} 不存在于 {expected_path}（已迁移/改名？）"))
    def _symbol_resolvable(
            self, py_file: Path, module_file: Path, symbol: str, *,
            symbol_root: Path | None = None,
            source_tree: ast.AST | None = None,
            source_node: ast.ImportFrom | None = None) -> bool:
        resolved = Path(os.path.abspath(str(module_file)))
        if _same_file_path(resolved, py_file):
            if (resolved.name == "__init__.py"
                    and namespace_has_symbol(resolved.parent, symbol)):
                return True
            return self._self_module_symbol_resolvable(
                py_file, symbol, source_tree, source_node)
        return resolve_import_symbol(
            symbol_root or self.project_root, resolved, symbol,
            cache=self._cache)
    def _star_import_binds_symbol(
            self, py_file: Path, node: ast.ImportFrom, symbol: str) -> bool:
        target_path, _relative = self._index.resolve_target_path(
            py_file, node)
        if target_path is None:
            return True
        module_file = self.project_root / target_path
        tree, _reason = _load_scan_tree(module_file, self._cache)
        if tree is None:
            return True
        all_surface = _extract_all(tree)
        allow_package_member = False
        allow_getattr = False
        if all_surface is not None:
            allow_getattr = True
            if not all_surface.complete:
                return True
            if symbol not in all_surface.names:
                return False
            allow_package_member = True
        elif symbol.startswith("_"):
            return False
        resolved = resolve_import_symbol(
            self.project_root, module_file, symbol, cache=self._cache,
            _allow_package_member=allow_package_member,
            _allow_getattr=allow_getattr)
        if not resolved or symbol != "__getattr__":
            return resolved
        getattr_bound = False
        for statement, import_invisible in iter_module_level_nodes_tc(
                tree, include_class_body=False):
            if import_invisible:
                continue
            getattr_state = _module_statement_getattr_state(statement)
            if getattr_state is not None:
                getattr_bound = getattr_state
        return getattr_bound
    def _self_module_symbol_resolvable(
            self, py_file: Path, symbol: str,
            source_tree: ast.AST | None,
            source_node: ast.ImportFrom | None = None) -> bool:
        tree = source_tree
        if tree is None:
            tree, _reason = _load_scan_tree(py_file, self._cache)
        if tree is None:
            return True
        module_nodes = [
            node for node, import_invisible in iter_module_level_nodes_tc(
                tree, include_class_body=False)
            if not import_invisible
        ]
        class_boundary, exception_aliases = _self_import_execution_context(
            tree, source_node)
        symbol_bound = symbol in exception_aliases
        getattr_bound = False
        for node in module_nodes:
            if node is source_node or node is class_boundary:
                break
            if isinstance(node, ast.ImportFrom):
                target_path, _relative = self._index.resolve_target_path(
                    py_file, node)
                is_self = (target_path is not None and _same_file_path(
                    self.project_root / target_path, py_file))
                if is_self:
                    continue
            is_star_import = (
                isinstance(node, ast.ImportFrom)
                and any(alias.name == "*" for alias in node.names))
            getattr_state = _module_statement_getattr_state(node)
            if is_star_import:
                getattr_state = self._star_import_binds_symbol(
                    py_file, node, "__getattr__")
            if getattr_state is not None:
                getattr_bound = getattr_state
            if isinstance(node, ast.ImportFrom):
                star_bound = (
                    is_star_import
                    and self._star_import_binds_symbol(py_file, node, symbol))
                if (star_bound or any(
                        (alias.asname or alias.name) == symbol
                        for alias in node.names)):
                    symbol_bound = True
                continue
            if _module_statement_deletes_symbol(node, symbol):
                symbol_bound = False
            elif _module_statement_binds_symbol(node, symbol):
                symbol_bound = True
        return symbol_bound or getattr_bound
    def _plain_import_resolvable(self, module_name: str,
                                 py_file: Path | None = None) -> bool:
        parts = strip_root_prefix(self.project_root, module_name)
        if not parts:
            return True
        if any(p.exists() for p in self._index.module_target_paths(
                parts, module_name)):
            return True
        if (py_file is not None
                and _is_script_import_context(py_file)):
            local = py_file.parent.joinpath(*module_name.split('.'))
            if (local.with_suffix('.py').exists()
                    or (local / '__init__.py').exists() or local.is_dir()):
                return True
        return (self._index.cross_skill_target_exists(module_name)
                or module_findable(module_name))
    def _check_import(self, py_file: Path, node: ast.Import) -> None:
        for alias in node.names:
            if _is_stdlib_module(alias.name) and module_findable(alias.name):
                continue
            nonpackage = self._index.nonpackage_parent(py_file, alias.name)
            if nonpackage is not None:
                self._emit_nonpackage_parent(
                    py_file, node, alias.name, nonpackage)
                continue
            if self._plain_import_resolvable(alias.name, py_file):
                continue
            self._emit_unresolved_module(
                py_file, node, import_stmt=f"import {alias.name}",
                target_module=alias.name)
    def report(self) -> str:
        entries = self.broken_imports
        skipped = list(self.skipped_files)
        if not entries and not skipped:
            return ("# BrokenImportScan 报告\n\n"
                    "未发现断裂导入，所有模块引用有效。\n")
        if not entries:
            return ("# BrokenImportScan 报告\n\n未发现断裂导入；但 "
                    f"{len(skipped)} 个文件因源码不可解析被跳过，"
                    "结论不完整。\n" + _render_skipped_section(skipped))
        counts = _severity_counts(entries)
        lines = [
            "# BrokenImportScan 报告", "",
            f"扫描结果: {len(entries)} 处断裂导入",
            f"  HIGH: {counts.get('HIGH', 0)}",
            f"  MEDIUM: {counts.get('MEDIUM', 0)}",
            "", "## 断裂导入详情", "",
            "| 文件 | 行 | 导入语句 | 预期路径 | 建议 |",
            "|------|-----|----------|----------|------|",
        ]
        for item in entries:
            lines.append(
                f"| {item.file_path} | {item.line_no} | `{item.import_stmt}` | "
                f"{item.expected_path} | {item.suggestion[:80]} |")
        if skipped:
            lines.extend(("", _render_skipped_section(skipped)))
        return "\n".join(lines)
    def get_impact_analysis(self) -> dict:
        impacted_files: dict[str, list[str]] = {}
        for item in self.broken_imports:
            impacted_files.setdefault(
                item.target_module or item.import_stmt, []).append(item.file_path)
        return {
            "total_broken": len(self.broken_imports),
            "unique_targets": len(impacted_files),
            "impacted_files": {
                key: list(dict.fromkeys(paths))
                for key, paths in impacted_files.items()},
            "high_severity": _severity_counts(
                self.broken_imports).get("HIGH", 0),
        }
    def to_dict(self) -> dict:
        entries = self.broken_imports
        skipped = list(self.skipped_files)
        return {
            "status": "partial" if skipped else "ok",
            "project_root": str(self.project_root),
            "total_broken": len(entries),
            "total_skipped": len(skipped),
            "skipped_files": skipped,
            "impact": self.get_impact_analysis(),
            "broken_imports": [
                {
                    "file": item.file_path, "line": item.line_no,
                    "import_stmt": item.import_stmt,
                    "target_module": item.target_module,
                    "severity": item.severity, "suggestion": item.suggestion,
                    "expected_path": item.expected_path, "exists": item.exists,
                    "is_relative": item.is_relative,
                }
                for item in entries
            ],
        }
def _same_file_path(left: Path, right: Path) -> bool:
    return (os.path.normcase(os.path.realpath(str(left)))
            == os.path.normcase(os.path.realpath(str(right))))
def _self_import_execution_context(
        tree: ast.AST, source_node: ast.ImportFrom | None,
) -> tuple[ast.ClassDef | None, set[str]]:
    if source_node is None:
        return None, set()
    parents = {
        child: parent
        for parent in walk_nodes(tree)
        for child in ast.iter_child_nodes(parent)
    }
    class_boundary = None
    exception_aliases: set[str] = set()
    current: ast.AST = source_node
    while current in parents:
        parent = parents[current]
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda)):
            return None, set()
        if isinstance(parent, ast.ClassDef):
            class_boundary = parent
            exception_aliases.clear()
        elif isinstance(parent, ast.ExceptHandler) and parent.name:
            exception_aliases.add(parent.name)
        current = parent
    return class_boundary, exception_aliases
def _module_statement_deletes_symbol(node: ast.AST, symbol: str) -> bool:
    return (isinstance(node, ast.Delete)
            and any(symbol in iter_unpack_target_names(target)
                    for target in node.targets))
def _module_statement_binds_symbol(node: ast.AST, symbol: str) -> bool:
    if symbol in iter_walrus_expr_bindings(node):
        return True
    # 与 diag_dependency_core._statement_binds_symbol 同口径：``globals()['x'] = v``
    # / ``globals().update({...})`` 运行期真实绑定模块属性，须按已绑定处理。
    if symbol in dynamic_module_binding_names(node):
        return True
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return node.name == symbol
    if isinstance(node, ast.Assign):
        return any(symbol in iter_unpack_target_names(target)
                   for target in node.targets)
    if isinstance(node, ast.AnnAssign):
        return (node.value is not None
                and symbol in iter_unpack_target_names(node.target))
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return symbol in iter_unpack_target_names(node.target)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return any(item.optional_vars is not None
                   and symbol in iter_unpack_target_names(item.optional_vars)
                   for item in node.items)
    if isinstance(node, ast.Import):
        return any((alias.asname or alias.name.split(".")[0]) == symbol
                   for alias in node.names)
    if isinstance(node, ast.ImportFrom):
        return any(alias.name == "*" or (alias.asname or alias.name) == symbol
                   for alias in node.names)
    if isinstance(node, ast.Match):
        return any(symbol in iter_match_capture_names(case.pattern)
                   for case in node.cases)
    if _TYPE_ALIAS is not None and isinstance(node, _TYPE_ALIAS):
        return isinstance(node.name, ast.Name) and node.name.id == symbol
    return False
def _module_getattr_accepts_name(
        node: ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda) -> bool:
    args = node.args
    positional = [*args.posonlyargs, *args.args]
    required_positional = len(positional) - len(args.defaults)
    accepts_one_positional = bool(positional or args.vararg)
    has_required_keyword_only = any(
        default is None for default in args.kw_defaults)
    return (accepts_one_positional and required_positional <= 1
            and not has_required_keyword_only)
def _module_statement_getattr_state(node: ast.AST) -> bool | None:
    if _module_statement_deletes_symbol(node, "__getattr__"):
        return False
    if not _module_statement_binds_symbol(node, "__getattr__"):
        return None
    if _TYPE_ALIAS is not None and isinstance(node, _TYPE_ALIAS):
        return False
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return _module_getattr_accepts_name(node)
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        simple_names = all(isinstance(target, ast.Name) for target in targets)
        if simple_names and isinstance(node.value, ast.Lambda):
            return _module_getattr_accepts_name(node.value)
        if simple_names and isinstance(node.value, (
                ast.Constant, ast.JoinedStr, ast.List, ast.Tuple,
                ast.Set, ast.Dict)):
            return False
    return True
def _severity_counts(entries: list[BrokenImport]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for b in entries:
        counts[b.severity] = counts.get(b.severity, 0) + 1
    return counts
def _render_skipped_section(skipped: list[dict[str, str]]) -> str:
    lines = [f"## 跳过文件（{len(skipped)}）", ""]
    lines.extend(
        f"- {item.get('file', '')}: {item.get('reason', '')}"
        for item in skipped)
    return "\n".join(lines)
def _scanned_fixer(project_root: str) -> tuple[str, BrokenImportFixer]:
    root = str(_require_project_root(project_root, "scan_broken_imports"))
    cache = get_warmed_cache(root)
    fixer = BrokenImportFixer(root)
    fixer.scan(cache=cache)
    return root, fixer
def scan_broken_imports(project_root: str) -> dict:
    _watch = Stopwatch()
    try:
        project_root, fixer = _scanned_fixer(project_root)
        result = fixer.to_dict()
        result["ai_execution"] = {
            "next_action": "review_and_fix_broken_imports",
            "instruction": (
                "逐项审核 broken_imports 的 suggestion；审核通过后按建议修正对应"
                "导入语句（改名/补符号/改路径），随后调用 "
                f"{PACKAGE_NAME}.diag_symbol_surface.scan_broken_imports"
                f"(project_root={project_root!r}) 复扫，直至 total_broken 归零"
            ),
        }
    except Exception:
        write_module_run(
            "diag_symbol_surface", "scan_broken_imports",
            outcome="error",
            duration_ms=_watch.elapsed_ms(),
            error="scan_failed_fail_fast",
        )
        raise
    logger.info(
        "scan_broken_imports 完成: project=%s, 断裂导入=%d 处 (HIGH=%d), "
        "跳过=%d, 波及目标模块=%d 个",
        project_root, result["total_broken"],
        result["impact"]["high_severity"], result["total_skipped"],
        result["impact"]["unique_targets"],
    )
    write_module_run(
        "diag_symbol_surface", "scan_broken_imports",
        duration_ms=_watch.elapsed_ms(),
        total_broken=result["total_broken"],
        high=result["impact"]["high_severity"],
        medium=result["total_broken"] - result["impact"]["high_severity"],
        skipped=result["total_skipped"],
        unique_targets=result["impact"]["unique_targets"],
    )
    return result
def quick_scan_broken_imports(project_root: str) -> str:
    _watch = Stopwatch()
    try:
        project_root, fixer = _scanned_fixer(project_root)
    except Exception:
        write_module_run(
            "diag_symbol_surface", "quick_scan_broken_imports",
            outcome="error",
            duration_ms=_watch.elapsed_ms(),
            error="scan_failed_fail_fast",
        )
        raise
    counts = _severity_counts(fixer.broken_imports)
    logger.info(
        "quick_scan_broken_imports 完成: project=%s, 断裂导入=%d 处 "
        "(HIGH=%d, MEDIUM=%d)",
        project_root, len(fixer.broken_imports),
        counts.get("HIGH", 0), counts.get("MEDIUM", 0),
    )
    write_module_run(
        "diag_symbol_surface", "quick_scan_broken_imports",
        duration_ms=_watch.elapsed_ms(),
        total_broken=len(fixer.broken_imports),
        high=counts.get("HIGH", 0),
        medium=counts.get("MEDIUM", 0),
    )
    return fixer.report()
DEP_MODULE_MAP: dict[str, str] = {
    "PyYAML": "yaml",
    "z3-solver": "z3",
    "pytest": "pytest",
    "coverage": "coverage",
    "psutil": "psutil",
    **({"tomli": "tomli"} if sys.version_info < (3, 11) else {}),
}
TOOLCHAIN_PACKAGES: dict[str, str] = {
    "xdist": "pytest-xdist",
    "pytest_rerunfailures": "pytest-rerunfailures",
}
def spec_exists(import_name: str) -> bool:
    if import_name in sys.modules:
        return sys.modules[import_name] is not None
    return _probe_spec(import_name) is True
def normalize_pkg_key(name: str) -> str:
    text = coerce_str(name).strip()
    if not text:
        return ""
    return re.sub(r"[-_.]+", "-", text).lower()
_DIST_MODULE_MAP_CACHE: dict[str, str] | None = None
def _is_pseudo_module_name(module: str) -> bool:
    return not module or module.startswith("_") or module.lower().endswith("__mypyc")
def _module_pick_key(module: str, dist_key: str) -> tuple[bool, bool, bool, int, str]:
    normalized = normalize_pkg_key(module)
    return (normalized != dist_key,
            normalized not in dist_key and dist_key not in normalized,
            module != module.lower(),
            module.count("."), module)
def _distribution_module_map(*, refresh: bool = False) -> dict[str, str]:
    global _DIST_MODULE_MAP_CACHE
    if _DIST_MODULE_MAP_CACHE is not None and not refresh:
        return _DIST_MODULE_MAP_CACHE
    mapping: dict[str, str] = {}
    try:
        installed = packages_distributions()
    except (OSError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f"_distribution_module_map:{type(_e).__name__}")
        if refresh and _DIST_MODULE_MAP_CACHE is not None:
            return _DIST_MODULE_MAP_CACHE
        installed = {}
    for module, dists in installed.items():
        if _is_pseudo_module_name(module):
            continue
        for dist in dists:
            key = normalize_pkg_key(dist)
            current = mapping.get(key)
            if current is None or (_module_pick_key(module, key)
                                   < _module_pick_key(current, key)):
                mapping[key] = module
    _DIST_MODULE_MAP_CACHE = mapping
    return mapping
def pip_pkg_to_module(pkg: str) -> str | None:
    if not isinstance(pkg, str):
        return None
    name = pkg.strip()
    if not name:
        return None
    key = normalize_pkg_key(name)
    for package, module in DEP_MODULE_MAP.items():
        if normalize_pkg_key(package) == key:
            return module
    for module, package in TOOLCHAIN_PACKAGES.items():
        if normalize_pkg_key(package) == key:
            return module
    had_snapshot = _DIST_MODULE_MAP_CACHE is not None
    resolved = _distribution_module_map().get(key)
    if resolved is None and had_snapshot:
        resolved = _distribution_module_map(refresh=True).get(key)
    if resolved is not None:
        return resolved
    if "-" in name or "." in name:
        return None
    return name

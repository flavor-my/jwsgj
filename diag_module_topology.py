from __future__ import annotations

__all__ = [
    "BOUNDARY_RULE_IDS",
    "MODULE_LAYER_MAP",
    "TOPOLOGY_INFRA_MODULES",
    "UNREGISTERED_BY_DESIGN",
    "BoundaryReport",
    "BoundaryViolation",
    "ModuleRecord",
    "ModuleTopology",
    "apply_layer_suggestions",
    "build_layer_suggestions",
    "build_module_topology",
    "capture_governance_metrics",
    "check_source_boundary",
    "classify_skill_type",
    "clear_topology_cache",
    "derive_infra_modules",
    "detect_skill_type",
    "format_violation_key",
    "has_layer_registry_surface",
    "import_in_degrees",
    "infer_layer_map",
    "is_registry_host",
    "iter_py_files",
    "load_authoritative_layer_map",
    "rewrite_mapping_table",
    "scan_boundary_imports",
    "skill_type_name",
    "summarize_boundary_scan",
    "target_infra_modules",
    "target_layer_map",
]
import ast
import io
import json
import logging
import os
import re
import tokenize
from collections.abc import Iterable
from dataclasses import dataclass, field
from functools import partial
from typing import Any, NamedTuple

from jwsgj.diag_guard_io import (
    archive_backup,
    atomic_write_text,
    split_tokenizer_lines,
)
from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.diag_merge_safety import (
    build_normalized_import_graph,
    find_graph_cycles,
)
from jwsgj.diag_merge_safety import (
    tarjan_scc as _graph_scc,
)
from jwsgj.diag_shared_ast_bindings import (
    exec_scope_declarations,
)
from jwsgj.diag_shared_ast_nodes import (
    assign_targets_value,
    cyclomatic_complexity,
    direct_class_methods,
    is_main_check,
    iter_module_level_stmts,
    iter_own_scope,
    main_guard_branch,
    module_postpones_annotations,
    str_constant_value,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_surface import (
    collect_all_export_names,
    is_all_target,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    files_fingerprint,
    iter_file_trees,
    parse_py_file,
    read_source,
    read_source_auto,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    collect_py_files,
    collect_python_files,
    is_test_file_path,
)
from jwsgj.skill_profile import (
    LEGACY_DECLARATION_MODULE,
    PROFILE_FILENAME,
    SkillProfileError,
    detect_layout,
    load_declared_profile,
    resolve_skill_profile,
    self_skill_root,
)

logger = logging.getLogger(__name__)
_DEFAULT_INCLUDE_TESTS = False
_DEFAULT_EXCLUDED_MODULES = frozenset()
def _path_text(value: Any) -> str:
    try:
        text = os.fspath(value)
    except TypeError:
        return ""
    if isinstance(text, bytes):
        text = os.fsdecode(text)
    return text if isinstance(text, str) and text.strip() else ""
def _count_class_methods(tree: ast.Module) -> int:
    return sum(len(direct_class_methods(node))
               for node in iter_module_level_stmts(tree)
               if isinstance(node, ast.ClassDef))
def _file_export_summary(tree: ast.Module) -> tuple[bool, int]:
    declared = _declared_exports(tree)
    if declared is not None:
        return True, len(declared)
    has_all = False
    api_count = 0
    for node in iter_module_level_stmts(tree):
        _is_all, _all_names = collect_all_export_names(node)
        if _is_all:
            has_all = True
            api_count += len(_all_names)
    return has_all, api_count
def _analyze_file_for_skill_type(tree: ast.Module) -> tuple[bool, bool, int, int, int]:
    file_has_main = False
    class_count = 0
    func_count = 0
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.If) and _main_guard_polarity(node.test) is True:
            file_has_main = True
        if isinstance(node, ast.ClassDef):
            class_count += 1
            func_count += len(direct_class_methods(node))
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_count += 1
    file_has_all, api_count = _file_export_summary(tree)
    return file_has_main, file_has_all, api_count, class_count, func_count
_THIN_INIT_MAX_LINES = 80
def _check_init_is_thin(skill_dir: str, ctx: Any) -> bool:
    package_root = detect_layout(skill_dir).package_root or skill_dir
    init_path = os.path.join(package_root, "__init__.py")
    if not os.path.isfile(init_path):
        return False
    init_content = read_source(init_path, ctx)
    if init_content is None:
        return False
    return count_lines(init_content) < _THIN_INIT_MAX_LINES
def _file_references_skill(fpath: str, pattern: re.Pattern,
                           ctx: Any) -> bool:
    src = read_source(fpath, ctx)
    return src is not None and bool(pattern.search(src))
def _count_referencing_py_files(dir_path: str, pattern: re.Pattern,
                                ctx: Any) -> int:
    try:
        py_files = collect_py_files(dir_path)
    except (OSError, ValueError) as exc:
        logger.debug("[HealthReport] 引用方目录枚举失败 %s: %s", dir_path, exc)
        return 0
    return sum(
        1 for rel in py_files
        if _file_references_skill(os.path.join(dir_path, rel), pattern, ctx)
    )
def _is_skill_root(path: str) -> bool:
    return os.path.isfile(os.path.join(path, "SKILL.md"))
def _check_cross_referenced(skill_dir: str, ctx: Any) -> int:
    root = os.path.abspath(skill_dir)
    if not _is_skill_root(root):
        return 0
    skills_root = os.path.dirname(root)
    if not os.path.isdir(skills_root):
        return 0
    skill_name = os.path.basename(root)
    package_name = detect_layout(root).package_name
    identities = {skill_name}
    if package_name:
        identities.add(package_name)
    _consumer_pat = re.compile(
        r"\b(?:" + "|".join(re.escape(name) for name in sorted(identities)) + r")\b")
    consumer_count = 0
    try:
        for other_skill in os.listdir(skills_root):
            if other_skill == skill_name or other_skill.startswith("."):
                continue
            other_dir = os.path.join(skills_root, other_skill)
            if not os.path.isdir(other_dir) or not _is_skill_root(other_dir):
                continue
            consumer_count += _count_referencing_py_files(
                other_dir, _consumer_pat, ctx)
    except OSError as e:
        logger.debug("[HealthReport] 跨技能引用检测失败: %s", e)
    return consumer_count
def classify_skill_type(
    real_cli_count: int,
    api_count: int,
    is_cross_referenced: bool,
    init_is_thin: bool,
    total_modules: int,
    is_class_heavy: bool,
) -> tuple[str, str]:
    if real_cli_count >= 3 and not is_cross_referenced:
        return "cli", "low"
    if real_cli_count >= 1:
        return ("hybrid", "normal") if api_count > 20 else ("cli", "normal")
    if _has_high_library_signal(
            api_count, init_is_thin, total_modules,
            is_cross_referenced, is_class_heavy):
        return "library", "high"
    if api_count > 10 and total_modules >= 5:
        return "library", "normal"
    return "hybrid", "normal"
def _has_high_library_signal(api_count: int, init_is_thin: bool,
                             total_modules: int, is_cross_referenced: bool,
                             is_class_heavy: bool) -> bool:
    return ((init_is_thin and total_modules >= 10 and api_count > 20)
            or api_count > 50 or is_cross_referenced
            or (is_class_heavy and api_count > 10))
def detect_skill_type(skill_dir: str, ctx: Any = None) -> dict:
    root = _path_text(skill_dir)
    if not root:
        raise ValueError("detect_skill_type: skill_dir 不能为空")
    py_files = [f for f in collect_py_files(root, ctx)
                if not is_test_file_path(f)]
    cli_count = 0
    real_cli_count = 0
    api_count = 0
    class_count = 0
    func_count = 0
    class_method_count = 0
    for _, tree in iter_file_trees(
            [os.path.join(root, f) for f in py_files], ctx):
        file_has_main, file_has_all, file_api, file_cls, file_func = (
            _analyze_file_for_skill_type(tree)
        )
        api_count += file_api
        class_count += file_cls
        func_count += file_func
        class_method_count += _count_class_methods(tree)
        if file_has_main:
            cli_count += 1
            if not file_has_all:
                real_cli_count += 1
    init_is_thin = _check_init_is_thin(root, ctx)
    cross_ref_count = _check_cross_referenced(root, ctx)
    is_cross_referenced = cross_ref_count > 0
    total_modules = len(py_files)
    class_method_ratio = class_method_count / max(class_count, 1)
    is_class_heavy = class_count > 10 and class_method_ratio > 3.0
    skill_type, orphan_tolerance = classify_skill_type(
        real_cli_count,
        api_count,
        is_cross_referenced,
        init_is_thin,
        total_modules,
        is_class_heavy,
    )
    return {
        "type": skill_type,
        "orphan_tolerance": orphan_tolerance,
        "cli_entries": cli_count,
        "real_cli_entries": real_cli_count,
        "api_exports": api_count,
        "thin_init": init_is_thin,
        "class_count": class_count,
        "class_method_count": class_method_count,
        "func_count": func_count,
        "cross_referenced": is_cross_referenced,
        "cross_referenced_count": cross_ref_count,
    }
def skill_type_name(report: dict) -> str:
    if not isinstance(report, dict):
        return "unknown"
    st = report.get("skill_type")
    if isinstance(st, dict):
        inner = st.get("type", "unknown")
        return inner if isinstance(inner, str) and inner else "unknown"
    if isinstance(st, str):
        return st or "unknown"
    direct = report.get("type")
    if isinstance(direct, str):
        return direct or "unknown"
    return "unknown"
BOUNDARY_RULE_IDS: tuple[str, ...] = (
    "GOV-B01",
    "GOV-B02",
    "GOV-B03",
    "GOV-B04",
)
_RULE_KIND: dict[str, str] = {
    "GOV-B01": "deep_path_import",
    "GOV-B02": "internal_symbol_import",
    "GOV-B03": "undeclared_submodule_access",
    "GOV-B04": "star_import",
}
_RULE_MESSAGES: dict[str, str] = {
    "GOV-B01": "跨包深层路径导入 {target}：须经目标包统一出入口（from {entry} import ...）",
    "GOV-B02": "导入内部符号 {target}.{symbol}：该符号未在目标模块 __all__ 白名单登记",
    "GOV-B03": "经包入口访问未登记子模块 {target}：须在包 __init__.py 的 __all__ 显式登记",
    "GOV-B04": "星号导入 {target}.*：绕过公共 API 白名单，须改为显式符号导入",
}
_MAX_CACHE_ENTRIES = 4
@dataclass(frozen=True)
class ImportRef:
    line: int
    is_from: bool
    level: int
    module: str
    names: tuple[str, ...]
    type_only: bool = False
@dataclass(frozen=True)
class ModuleRecord:
    dotted: str
    path: str
    package: str
    depth: int
    is_package: bool
    exports: frozenset[str]
    has_all: bool
    imports: tuple[ImportRef, ...] = ()
    exports_complete: bool = True
@dataclass
class ModuleTopology:
    root_dir: str
    root_package: str
    flat_layout: bool = False
    modules: dict[str, ModuleRecord] = field(default_factory=dict)
    packages: frozenset[str] = frozenset()
    scanned_files: int = 0
    parse_errors: tuple[str, ...] = ()
    composition_imports: dict[str, frozenset[str]] = field(default_factory=dict)
    skill_root: str = ""
    def resolve(self, dotted: str) -> ModuleRecord | None:
        return self.modules.get(dotted)
    def is_public(self, dotted: str, symbol: str) -> bool:
        record = self.modules.get(dotted)
        if record is None:
            return False
        return symbol in record.exports
@dataclass(frozen=True)
class BoundaryViolation:
    rule_id: str
    file: str
    line: int
    module: str
    target: str
    symbol: str = ""
    type_only: bool = False
    entry: str = ""
    @property
    def kind(self) -> str:
        return _RULE_KIND.get(self.rule_id, "unknown")
    @property
    def message(self) -> str:
        template = _RULE_MESSAGES.get(self.rule_id, "{target}")
        entry = (self.entry
                 or ".".join(self.target.split(".")[:-1])
                 or self.target)
        return template.format(
            target=self.target, symbol=self.symbol, entry=entry)
    def key(self) -> str:
        return format_violation_key(self)
    def as_dict(self) -> dict[str, Any]:
        return {
            "rule_id": self.rule_id,
            "kind": self.kind,
            "file": self.file,
            "line": self.line,
            "target": self.target,
            "symbol": self.symbol,
            "type_only": self.type_only,
            "message": self.message,
        }
@dataclass(frozen=True)
class BoundaryReport:
    root_dir: str
    root_package: str
    scanned_files: int
    violations: tuple[BoundaryViolation, ...] = ()
    parse_errors: tuple[str, ...] = ()
    @property
    def counts(self) -> dict[str, int]:
        result = dict.fromkeys(BOUNDARY_RULE_IDS, 0)
        for item in self.violations:
            result[item.rule_id] = result.get(item.rule_id, 0) + 1
        return result
    @property
    def total(self) -> int:
        return len(self.violations)
    def keys(self) -> tuple[str, ...]:
        return tuple(sorted(item.key() for item in self.violations))
def format_violation_key(violation: BoundaryViolation) -> str:
    flag = "T" if violation.type_only else "R"
    return "|".join((
        violation.rule_id,
        violation.file.replace(os.sep, "/"),
        str(violation.line),
        violation.target,
        violation.symbol,
        flag,
    ))
def iter_py_files(
        root_dir: str, include_tests: bool = _DEFAULT_INCLUDE_TESTS) -> list[str]:
    try:
        return collect_python_files(root_dir, include_tests=include_tests)
    except (OSError, TypeError, ValueError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='iter_py_files:collect')
        return []
def _path_within(path: str, root: str) -> bool:
    try:
        rel = os.path.relpath(
            os.path.normcase(os.path.abspath(path)),
            os.path.normcase(os.path.abspath(root)))
    except ValueError:
        return False
    return not (rel == os.pardir or rel.startswith(os.pardir + os.sep))
_TOPO_CACHE: dict[tuple, ModuleTopology] = {}
def clear_topology_cache() -> int:
    count = len(_TOPO_CACHE)
    _TOPO_CACHE.clear()
    return count
def _literal_name_list(node: ast.AST | None) -> tuple[str, ...] | None:
    if isinstance(node, (ast.List, ast.Tuple)):
        names: list[str] = []
        for item in node.elts:
            if isinstance(item, ast.Constant) and isinstance(item.value, str):
                names.append(item.value)
            else:
                return None
        return tuple(names)
    return None
_TypeCheckScope = tuple[frozenset[str], frozenset[str], bool]
def _type_checking_scope(tree: ast.Module) -> _TypeCheckScope:
    return (frozenset(typing_type_checking_names(tree)),
            frozenset(typing_guard_aliases(tree)),
            not module_postpones_annotations(tree, require_absolute=True))
def _type_checking_lines(tree: ast.Module) -> set[int]:
    lines: set[int] = set()
    scope = _type_checking_scope(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        polarity = _type_checking_polarity(node.test, scope)
        if polarity is None:
            continue
        type_branches = node.body if polarity is False else node.orelse
        for branch in type_branches:
            for child in walk_nodes(branch):
                if isinstance(child, (ast.Import, ast.ImportFrom)):
                    lines.add(getattr(child, "lineno", 0))
    return lines
def _import_refs(tree: ast.Module) -> tuple[ImportRef, ...]:
    type_lines = _type_checking_lines(tree)
    refs: list[ImportRef] = []
    for node in walk_nodes(tree):
        lineno = getattr(node, "lineno", 0)
        type_only = lineno in type_lines
        if isinstance(node, ast.ImportFrom):
            refs.append(ImportRef(
                line=lineno, is_from=True, level=int(node.level or 0),
                module=node.module or "",
                names=tuple(alias.name for alias in node.names if alias.name),
                type_only=type_only))
        elif isinstance(node, ast.Import):
            refs.extend(
                ImportRef(
                    line=lineno, is_from=False, level=0,
                    module=alias.name, names=(), type_only=type_only)
                for alias in node.names if alias.name
            )
    return tuple(refs)
_ALL_CONTENT_MUTATION_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear",
})
_ALL_READONLY_METHODS = frozenset({
    "copy", "count", "index", "sort", "reverse",
})
_ALL_ADD = "add"
_ALL_REMOVE = "remove"
_ALL_CLEAR = "clear"
def _all_mutation(
    node: ast.AST,
) -> tuple[bool, str | None, tuple[str, ...] | None]:
    if isinstance(node, ast.AugAssign) and is_all_target(node.target):
        if not isinstance(node.op, ast.Add):
            return True, None, None
        return True, _ALL_ADD, _literal_name_list(node.value)
    if not isinstance(node, ast.Expr) or not isinstance(node.value, ast.Call):
        return False, None, None
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
            and is_all_target(func.value)):
        return False, None, None
    if func.attr not in _ALL_CONTENT_MUTATION_METHODS:
        return False, None, None
    if func.attr == "clear":
        return (True, _ALL_CLEAR, None) if not call.args and not call.keywords \
            else (True, None, None)
    if call.keywords:
        return True, None, None
    if func.attr == "extend":
        if len(call.args) != 1:
            return True, None, None
        return True, _ALL_ADD, _literal_name_list(call.args[0])
    if func.attr == "append":
        name = str_constant_value(call.args[0]) if len(call.args) == 1 else None
        return (True, _ALL_ADD, (name,)) if name is not None else (True, None, None)
    if func.attr == "insert":
        name = str_constant_value(call.args[1]) if len(call.args) == 2 else None
        return (True, _ALL_ADD, (name,)) if name is not None else (True, None, None)
    if func.attr == "remove":
        name = str_constant_value(call.args[0]) if len(call.args) == 1 else None
        return ((True, _ALL_REMOVE, (name,)) if name is not None
                else (True, None, None))
    return True, None, None
_EXPORT_ABSENT: Any = object()
_EXPORT_UNKNOWN: Any = object()
_EXPORT_STATE_LIMIT = 16
def _definition_time_expressions(
        node: ast.AST, scope: _TypeCheckScope | None) -> list[ast.AST]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        expressions: list[ast.AST] = [
            *getattr(node, "decorator_list", ()),
            *node.args.defaults,
            *(value for value in node.args.kw_defaults if value is not None),
        ]
        if scope is None or scope[2]:
            args = node.args
            arguments = (
                *args.posonlyargs, *args.args, *args.kwonlyargs,
                args.vararg, args.kwarg,
            )
            expressions.extend(
                arg.annotation for arg in arguments
                if arg is not None and arg.annotation is not None)
            returns = getattr(node, "returns", None)
            if returns is not None:
                expressions.append(returns)
        return expressions
    if isinstance(node, ast.ClassDef):
        return [
            *node.decorator_list, *node.bases,
            *(keyword.value for keyword in node.keywords),
        ]
    return []
def _mutates_all(node: ast.AST, scope: _TypeCheckScope | None = None) -> bool:
    if isinstance(node, ast.AnnAssign):
        expressions: list[ast.AST] = []
        if scope is None or scope[2]:
            expressions.append(node.annotation)
        if node.value is not None:
            expressions.extend((node.target, node.value))
        return any(_mutates_all(child, scope) for child in expressions)
    if isinstance(node, ast.Import):
        return any(
            (alias.asname or alias.name.split(".", 1)[0]) == "__all__"
            for alias in node.names)
    if isinstance(node, ast.ImportFrom):
        return any(
            (alias.asname or alias.name) == "__all__"
            for alias in node.names)
    if isinstance(node, ast.ExceptHandler) and node.name == "__all__":
        return True
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.Lambda, ast.ClassDef)):
        return any(
            _mutates_all(child, scope)
            for child in _definition_time_expressions(node, scope))
    if isinstance(node, ast.Name) and node.id == "__all__":
        return isinstance(node.ctx, (ast.Store, ast.Del))
    if (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == "__all__"
            and isinstance(node.ctx, (ast.Store, ast.Del))):
        return True
    if (isinstance(node, ast.Subscript)
            and isinstance(node.value, ast.Name)
            and node.value.id == "__all__"
            and isinstance(node.ctx, (ast.Store, ast.Del))):
        return True
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == "__all__"
            and node.func.attr not in _ALL_READONLY_METHODS):
        return True
    if isinstance(node, ast.Match) and any(
            "__all__" in _pattern_bound_names(case.pattern)
            for case in node.cases):
        return True
    return any(_mutates_all(child, scope)
               for child in ast.iter_child_nodes(node))
def _merge_export_states(states: Iterable[Any]) -> list[Any]:
    merged: list[Any] = []
    for state in states:
        if state is _EXPORT_UNKNOWN:
            return [_EXPORT_UNKNOWN]
        if not any(state == known for known in merged):
            merged.append(state)
    return merged or [_EXPORT_UNKNOWN]
def _main_guard_polarity(test: ast.AST) -> bool | None:
    branch = main_guard_branch(test)
    if branch is not None:
        return branch
    return True if is_main_check(test) else None
def _constant_condition_truth(test: ast.AST) -> bool | None:
    return bool(test.value) if isinstance(test, ast.Constant) else None
def _import_time_branch(node: ast.If) -> list[ast.stmt]:
    return node.orelse if _main_guard_polarity(node.test) else node.body
def _export_state_after_if(
        node: ast.If, state: Any,
        scope: _TypeCheckScope | None) -> list[Any]:
    if _mutates_all(node.test, scope):
        return [_EXPORT_UNKNOWN]
    constant = _constant_condition_truth(node.test)
    if constant is not None:
        return _export_states(
            node.body if constant else node.orelse, state, scope)
    if _main_guard_polarity(node.test) is not None:
        return _export_states(_import_time_branch(node), state, scope)
    polarity = _type_checking_polarity(node.test, scope)
    if polarity is True:
        return _export_states(node.body, state, scope)
    if polarity is False:
        return _export_states(node.orelse, state, scope)
    touches = any(_mutates_all(stmt, scope) for stmt in node.body) or any(
        _mutates_all(stmt, scope) for stmt in node.orelse)
    if not touches:
        return [state]
    return _merge_export_states(
        _export_states(node.body, state, scope)
        + _export_states(node.orelse, state, scope))
def _statement_binds_class_all(node: ast.stmt) -> bool:
    probe = ast.Module(body=[node], type_ignores=[])
    local, _global_names = exec_scope_declarations(probe)
    return "__all__" in local
def _class_body_export_states(
        node: ast.ClassDef, state: Any,
        scope: _TypeCheckScope | None) -> list[Any]:
    local, global_names = exec_scope_declarations(node)
    if "__all__" in global_names or "__all__" not in local:
        return _export_states(node.body, state, scope)
    prefix: list[ast.stmt] = []
    for statement in node.body:
        if _statement_binds_class_all(statement):
            break
        prefix.append(statement)
    return _export_states(prefix, state, scope)
def _export_state_after(
        node: ast.stmt, state: Any,
        scope: _TypeCheckScope | None) -> list[Any]:
    normalized = assign_targets_value(node)
    if normalized is not None and any(
            is_all_target(target) for target in normalized[0]):
        names = _literal_name_list(normalized[1])
        return [_EXPORT_UNKNOWN if names is None else list(names)]
    if isinstance(node, ast.Delete) and any(
            isinstance(target, ast.Name) and is_all_target(target)
            for target in node.targets):
        return [_EXPORT_ABSENT]
    touches_all, operation, names = _all_mutation(node)
    if touches_all:
        if not isinstance(state, list):
            return [_EXPORT_UNKNOWN]
        if operation == _ALL_CLEAR:
            return [[]]
        if operation == _ALL_ADD:
            return ([state + list(names)] if names is not None
                    else [_EXPORT_UNKNOWN])
        if names is None:
            return [_EXPORT_UNKNOWN]
        if operation == _ALL_REMOVE:
            updated = list(state)
            for name in names:
                if name in updated:
                    updated.remove(name)
            return [updated]
        return [_EXPORT_UNKNOWN]
    if isinstance(node, ast.If):
        return _export_state_after_if(node, state, scope)
    if isinstance(node, ast.ClassDef):
        if _mutates_all(node, scope):
            return [_EXPORT_UNKNOWN]
        return _class_body_export_states(node, state, scope)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return [_EXPORT_UNKNOWN] if _mutates_all(node, scope) else [state]
    if _mutates_all(node, scope):
        return [_EXPORT_UNKNOWN]
    return [state]
def _export_states(body: Iterable[ast.stmt], entry: Any,
                   scope: _TypeCheckScope | None) -> list[Any]:
    states = [entry]
    for node in body:
        next_states: list[Any] = []
        for state in states:
            next_states.extend(_export_state_after(node, state, scope))
        states = _merge_export_states(next_states)
        if len(states) > _EXPORT_STATE_LIMIT:
            return [_EXPORT_UNKNOWN]
    return states
def _declared_exports(
        tree: ast.Module, states: list[Any] | None = None
) -> tuple[str, ...] | None:
    if states is None:
        states = _export_states(
            tree.body, _EXPORT_ABSENT, _type_checking_scope(tree))
    if any(state is _EXPORT_UNKNOWN for state in states):
        return ()
    if any(state is _EXPORT_ABSENT for state in states):
        return None
    merged: list[str] = []
    for state in states:
        for name in state:
            if name not in merged:
                merged.append(name)
    return tuple(merged)
def _imported_public_names(node: ast.AST) -> set[str]:
    names: set[str] = set()
    if isinstance(node, ast.Import):
        for alias in node.names:
            top = alias.name.split(".", 1)[0]
            names.add(alias.asname or top)
        return names
    if not isinstance(node, ast.ImportFrom):
        return names
    for alias in node.names:
        if alias.name != "*":
            names.add(alias.asname or alias.name)
    return names
_TRY_STATEMENTS: tuple[type[ast.stmt], ...] = tuple(
    node for node in (ast.Try, getattr(ast, "TryStar", None))
    if node is not None)
_TYPE_ALIAS = getattr(ast, "TypeAlias", None)
def _pattern_bound_names(pattern: ast.AST | None) -> set[str]:
    if pattern is None:
        return set()
    if isinstance(pattern, ast.MatchStar):
        return {pattern.name} if pattern.name else set()
    if isinstance(pattern, ast.MatchAs):
        names = {pattern.name} if pattern.name else set()
        names.update(_pattern_bound_names(pattern.pattern))
        return names
    if isinstance(pattern, ast.MatchMapping):
        names = {pattern.rest} if pattern.rest else set()
        for sub in pattern.patterns:
            names.update(_pattern_bound_names(sub))
        return names
    names: set[str] = set()
    for attr in ("patterns", "kwd_patterns"):
        for sub in getattr(pattern, attr, ()) or ():
            names.update(_pattern_bound_names(sub))
    inner = getattr(pattern, "pattern", None)
    if isinstance(inner, ast.AST):
        names.update(_pattern_bound_names(inner))
    return names
def _walrus_bindings(node: ast.AST | None) -> set[str]:
    if node is None:
        return set()
    names: set[str] = set()
    stack = [node]
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef)):
            stack.extend(_definition_time_expressions(current, None))
            continue
        if (isinstance(current, ast.NamedExpr)
                and isinstance(current.target, ast.Name)):
            names.add(current.target.id)
        stack.extend(ast.iter_child_nodes(current))
    return names
def _type_checking_polarity(
        test: ast.expr,
        scope: _TypeCheckScope | None) -> bool | None:
    if scope is None:
        names, aliases = frozenset(), frozenset()
    else:
        names, aliases, _ = scope
    if isinstance(test, ast.Name):
        return False if test.id in names else None
    if isinstance(test, ast.Attribute):
        is_typing_attr = (
            test.attr == "TYPE_CHECKING"
            and isinstance(test.value, ast.Name)
            and test.value.id in aliases)
        return False if is_typing_attr else None
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        inner = _type_checking_polarity(test.operand, scope)
        return None if inner is None else not inner
    return None
def _assignment_target_names(target: ast.AST) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, (ast.Tuple, ast.List)):
        names: set[str] = set()
        for element in target.elts:
            names.update(_assignment_target_names(element))
        return names
    if isinstance(target, ast.Starred):
        return _assignment_target_names(target.value)
    return set()
def _collect_public_definitions(
        body: Iterable[ast.stmt], names: set[str],
        scope: _TypeCheckScope | None, conditional: bool = False) -> None:
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            names.add(node.name)
            names.update(_walrus_bindings(node))
            continue
        if _TYPE_ALIAS is not None and isinstance(node, _TYPE_ALIAS):
            names.add(node.name.id)
            continue
        if isinstance(node, ast.Assign):
            for target in node.targets:
                names.update(_assignment_target_names(target))
            names.update(_walrus_bindings(node.value))
            continue
        if isinstance(node, ast.AnnAssign):
            if node.value is not None and isinstance(node.target, ast.Name):
                names.add(node.target.id)
            names.update(_walrus_bindings(node.annotation))
            names.update(_walrus_bindings(node.value))
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names.update(_imported_public_names(node))
            continue
        if isinstance(node, ast.Delete):
            if not conditional:
                for target in node.targets:
                    names.difference_update(_assignment_target_names(target))
            continue
        if isinstance(node, ast.If):
            names.update(_walrus_bindings(node.test))
            constant = _constant_condition_truth(node.test)
            if constant is not None:
                _collect_public_definitions(
                    node.body if constant else node.orelse,
                    names, scope, conditional=conditional)
                continue
            if _main_guard_polarity(node.test) is not None:
                _collect_public_definitions(
                    _import_time_branch(node), names, scope,
                    conditional=conditional)
                continue
            polarity = _type_checking_polarity(node.test, scope)
            if polarity is False:
                _collect_public_definitions(
                    node.orelse, names, scope, conditional=conditional)
            elif polarity is True:
                _collect_public_definitions(
                    node.body, names, scope, conditional=conditional)
            else:
                _collect_public_definitions(
                    node.body, names, scope, conditional=True)
                _collect_public_definitions(
                    node.orelse, names, scope, conditional=True)
            continue
        if isinstance(node, _TRY_STATEMENTS):
            for block in (node.body, node.orelse):
                _collect_public_definitions(
                    block, names, scope, conditional=True)
            for handler in node.handlers:
                _collect_public_definitions(
                    handler.body, names, scope, conditional=True)
            _collect_public_definitions(
                node.finalbody, names, scope, conditional=conditional)
            continue
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                names.update(_walrus_bindings(item.context_expr))
                if item.optional_vars is not None:
                    names.update(
                        _assignment_target_names(item.optional_vars))
            _collect_public_definitions(
                node.body, names, scope, conditional=True)
            continue
        if isinstance(node, ast.Match):
            names.update(_walrus_bindings(node.subject))
            for case in node.cases:
                names.update(_pattern_bound_names(case.pattern))
                names.update(_walrus_bindings(case.guard))
                _collect_public_definitions(
                    case.body, names, scope, conditional=True)
            continue
        if isinstance(node, (ast.For, ast.AsyncFor)):
            names.update(_assignment_target_names(node.target))
            names.update(_walrus_bindings(node.iter))
            _collect_public_definitions(
                node.body, names, scope, conditional=True)
            _collect_public_definitions(
                node.orelse, names, scope, conditional=True)
            continue
        if isinstance(node, ast.While):
            names.update(_walrus_bindings(node.test))
            _collect_public_definitions(
                node.body, names, scope, conditional=True)
            _collect_public_definitions(
                node.orelse, names, scope, conditional=True)
            continue
        names.update(_walrus_bindings(node))
def _public_definitions(tree: ast.Module) -> frozenset[str]:
    names: set[str] = set()
    _collect_public_definitions(
        tree.body, names, _type_checking_scope(tree))
    return frozenset(name for name in names if not name.startswith("_"))
def _module_exports(
        tree: ast.Module,
) -> tuple[frozenset[str], bool, bool]:
    states = _export_states(
        tree.body, _EXPORT_ABSENT, _type_checking_scope(tree))
    declared = _declared_exports(tree, states)
    if declared is not None:
        complete = not any(state is _EXPORT_UNKNOWN for state in states)
        return frozenset(declared), True, complete
    return _public_definitions(tree), False, True
def _dotted_for(path: str, root_dir: str, root_package: str,
                flat_layout: bool = False) -> tuple[str, bool]:
    rel = os.path.relpath(path, root_dir)
    parts = os.path.splitext(rel)[0].split(os.sep)
    is_package = parts[-1] == "__init__"
    if is_package:
        parts = parts[:-1]
    prefix = [] if flat_layout else [root_package]
    dotted_parts = prefix + [p for p in parts if p]
    return ".".join(dotted_parts), is_package
def _module_identity(dotted: str, is_package: bool) -> tuple[str, int]:
    parent = dotted.rsplit(".", 1)[0] if "." in dotted else ""
    rel_depth = dotted.count(".")
    depth = rel_depth if is_package else max(rel_depth - 1, 0)
    return parent, depth
def build_module_topology(
        root_dir: str,
        include_tests: bool = _DEFAULT_INCLUDE_TESTS) -> ModuleTopology:
    root_text = _path_text(root_dir)
    if not root_text:
        raise ValueError("build_module_topology: root_dir 不能为空")
    # detect_layout 返回的 package_root 是 realpath：技能根经符号链接访问时（本包
    # 部署即 target_skills/jwsgj → user_skills/jwsgj），若 root 保持未解析路径，
    # 全部文件会被判为 analysis_root 之外而按扁平布局命名（丢根包前缀、根入口
    # 点名为空），边界扫描与层级建议随访问路径不同而不同。
    root = os.path.normpath(os.path.realpath(os.path.abspath(root_text)))
    if not os.path.isdir(root):
        if os.path.exists(root):
            raise NotADirectoryError(
                f"build_module_topology: root_dir 不是目录: {root}")
        raise FileNotFoundError(
            f"build_module_topology: root_dir 不存在: {root}")
    layout = detect_layout(root)
    analysis_root = os.path.normpath(os.path.abspath(
        layout.package_root or root))
    files = iter_py_files(root, include_tests)
    root_package = layout.package_name or os.path.basename(analysis_root) or "root"
    flat_layout = not os.path.isfile(os.path.join(analysis_root, "__init__.py"))
    cache_key = (root, analysis_root, root_package, flat_layout,
                 bool(include_tests), files_fingerprint(files))
    cached = _TOPO_CACHE.get(cache_key)
    if cached is not None:
        return cached
    modules: dict[str, ModuleRecord] = {}
    packages: set[str] = set() if flat_layout else {root_package}
    parse_errors: list[str] = []
    for path in files:
        tree = parse_py_file(path, quiet=True)[1]
        if tree is None:
            parse_errors.append(path)
            continue
        if _path_within(path, analysis_root):
            dotted, is_package = _dotted_for(
                path, analysis_root, root_package, flat_layout)
        else:
            dotted, is_package = _dotted_for(path, root, root_package, True)
        parent, depth = _module_identity(dotted, is_package)
        exports, has_all, exports_complete = _module_exports(tree)
        if dotted in modules:
            logger.warning(
                "[Topology] 模块名冲突 %s: %s 覆盖 %s",
                dotted, path, modules[dotted].path)
        modules[dotted] = ModuleRecord(
            dotted=dotted, path=path, package=parent, depth=depth,
            is_package=is_package, exports=exports, has_all=has_all,
            imports=_import_refs(tree), exports_complete=exports_complete)
        if is_package:
            packages.add(dotted)
    composition_imports = {}
    if not flat_layout:
        root_tree = parse_py_file(os.path.join(analysis_root, "__init__.py"), quiet=True)[1]
        composition_imports = _composition_contract_from_tree(root_tree)
    topology = ModuleTopology(
        root_dir=analysis_root, root_package=root_package, skill_root=root,
        flat_layout=flat_layout, modules=modules, packages=frozenset(packages),
        scanned_files=len(files), parse_errors=tuple(parse_errors),
        composition_imports=composition_imports)
    if len(_TOPO_CACHE) >= _MAX_CACHE_ENTRIES:
        _TOPO_CACHE.clear()
    _TOPO_CACHE[cache_key] = topology
    return topology
def _resolve_relative(importer_pkg: str, level: int, module: str | None) -> str:
    parts = [p for p in importer_pkg.split(".") if p]
    up = max(level - 1, 0)
    if up >= len(parts) and up > 0:
        return ""
    base_parts = parts[:len(parts) - up] if up else parts
    base = ".".join(base_parts)
    if module:
        return f"{base}.{module}" if base else module
    return base
def _is_deep_target(
        target: ModuleRecord, importer: ModuleRecord,
        topology: ModuleTopology) -> bool:
    if target.dotted == importer.dotted:
        return False
    if target.dotted == importer.package:
        return False
    if target.package == importer.package:
        return False
    if importer.is_package and target.package == importer.dotted:
        return False
    if topology.flat_layout:
        return target.package != ""
    if target.dotted == topology.root_package:
        return False
    return target.package != topology.root_package
def _collect_violations(
        refs: tuple[ImportRef, ...], importer: ModuleRecord,
        topology: ModuleTopology) -> list[BoundaryViolation]:
    violations: list[BoundaryViolation] = []
    for ref in refs:
        if ref.is_from:
            violations.extend(_from_import_violations(ref, importer, topology))
        else:
            violations.extend(_plain_import_violations(ref, importer, topology))
    return violations
def _resolve_from_base(ref: ImportRef, importer: ModuleRecord) -> str:
    if not ref.level:
        return ref.module
    base_pkg = importer.dotted if importer.is_package else importer.package
    return _resolve_relative(base_pkg, ref.level, ref.module)
_COMPOSITION_CONTRACT_NAME = "__composition_imports__"
def _literal_str_sequence(node: ast.AST | None) -> tuple[str, ...] | None:
    if not isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return None
    names: list[str] = []
    for item in node.elts:
        if not (isinstance(item, ast.Constant) and isinstance(item.value, str)):
            return None
        names.append(item.value)
    return tuple(names)
def _composition_contract_from_tree(
        tree: ast.Module | None) -> dict[str, frozenset[str]]:
    if tree is None:
        return {}
    declarations = [
        node for node in tree.body
        if _declares_table(node, _COMPOSITION_CONTRACT_NAME)
    ]
    if len(declarations) != 1:
        if declarations:
            logger.warning("[Topology] %s 重复声明，按未声明处理",
                           _COMPOSITION_CONTRACT_NAME)
        return {}
    for node in declarations:
        targets = (node.targets if isinstance(node, ast.Assign)
                   else [node.target] if isinstance(node, ast.AnnAssign)
                   else [])
        if not any(isinstance(target, ast.Name)
                   and target.id == _COMPOSITION_CONTRACT_NAME
                   for target in targets):
            continue
        mapping = node.value
        if not isinstance(mapping, ast.Dict):
            logger.warning("[Topology] %s 非字面量映射，按未声明处理",
                           _COMPOSITION_CONTRACT_NAME)
            return {}
        declared: dict[str, frozenset[str]] = {}
        for key, value in zip(mapping.keys, mapping.values, strict=True):
            names = _literal_str_sequence(value)
            if not (isinstance(key, ast.Constant)
                    and isinstance(key.value, str)) or names is None:
                logger.warning("[Topology] %s 条目不可静态定论，按未声明处理",
                               _COMPOSITION_CONTRACT_NAME)
                return {}
            declared[key.value] = frozenset(names)
        return declared
    return {}
def _is_surface_composition_symbol(
        importer: ModuleRecord, parent: ModuleRecord, symbol: str,
        topology: ModuleTopology) -> bool:
    if not importer.is_package or importer.dotted != topology.root_package:
        return False
    if parent.package != topology.root_package:
        return False
    parent_name = parent.dotted.rsplit('.', 1)[-1]
    return symbol in topology.composition_imports.get(parent_name, frozenset())
def _symbol_violations(
        ref: ImportRef, importer: ModuleRecord, topology: ModuleTopology,
        base: str, parent: ModuleRecord,
        symbol: str) -> list[BoundaryViolation]:
    sub_record = topology.resolve(f"{base}.{symbol}")
    if sub_record is not None and symbol not in parent.exports:
        # 子模块经 ``base`` 入口到达：导入路径是否「深层」取决于 ``base`` 本身，
        # 已由 _from_import_violations 对 parent 判定；再对 sub_record 判 B01
        # 要么与那条重复，要么在 base 已是统一出入口时自相矛盾地推荐
        # 「from base import ...」（即原句）。这里只判「入口未登记子模块」。
        facade = (importer.is_package and parent.dotted == importer.dotted)
        same_package = parent.dotted == importer.package
        if (parent.is_package and parent.exports_complete
                and not facade and not same_package):
            return [_violation(
                "GOV-B03", ref, importer, topology, sub_record.dotted)]
        return []
    if sub_record is not None:
        return []
    if symbol in parent.exports:
        return []
    if not parent.exports_complete:
        # __all__ 动态构造/条件定义时无法静态定论（exports 为空仅表示未知，
        # 不表示未导出）：此时断言“符号未登记”属误报，且会阻断重构门禁。
        return []
    if _is_surface_composition_symbol(importer, parent, symbol, topology):
        return []
    return [_violation("GOV-B02", ref, importer, topology, parent.dotted,
                       symbol)]
def _from_import_violations(
        ref: ImportRef, importer: ModuleRecord,
        topology: ModuleTopology) -> list[BoundaryViolation]:
    base = _resolve_from_base(ref, importer)
    if not base:
        return []
    parent = topology.resolve(base)
    if parent is None:
        return []
    violations: list[BoundaryViolation] = []
    if _is_deep_target(parent, importer, topology):
        violations.append(_violation(
            "GOV-B01", ref, importer, topology, parent.dotted))
    if "*" in ref.names:
        violations.append(_violation(
            "GOV-B04", ref, importer, topology, parent.dotted, "*"))
        return violations
    for symbol in ref.names:
        violations.extend(_symbol_violations(
            ref, importer, topology, base, parent, symbol))
    return violations
def _plain_import_violations(
        ref: ImportRef, importer: ModuleRecord,
        topology: ModuleTopology) -> list[BoundaryViolation]:
    target = topology.resolve(ref.module)
    if target is None:
        return []
    if _is_deep_target(target, importer, topology):
        return [_violation(
            "GOV-B01", ref, importer, topology, target.dotted)]
    return []
def _relative_file(path: str, root_dir: str) -> str:
    try:
        rel = os.path.relpath(path, root_dir)
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_relative_file:ValueError')
        rel = path
    if rel == os.pardir or rel.startswith(os.pardir + os.sep):
        rel = path
    return rel.replace(os.sep, "/")
def _entry_module(target: str, topology: ModuleTopology) -> str:
    parts = [part for part in target.split(".") if part]
    if not parts:
        return target
    if topology.flat_layout:
        return parts[0]
    if parts[0] != topology.root_package:
        return parts[0]
    return ".".join(parts[:2]) if len(parts) > 1 else topology.root_package
def _violation(rule_id: str, ref: ImportRef, importer: ModuleRecord,
               topology: ModuleTopology, target: str,
               symbol: str = "") -> BoundaryViolation:
    file = _relative_file(importer.path, topology.root_dir)
    if os.path.isabs(file) and topology.skill_root:
        file = _relative_file(importer.path, topology.skill_root)
    return BoundaryViolation(
        rule_id=rule_id,
        file=file,
        line=ref.line,
        module=importer.dotted,
        target=target,
        symbol=symbol,
        type_only=ref.type_only,
        entry=_entry_module(target, topology))
def scan_boundary_imports(
        root_dir: str, include_tests: bool = _DEFAULT_INCLUDE_TESTS,
        topology: ModuleTopology | None = None) -> BoundaryReport:
    topo = topology or build_module_topology(root_dir, include_tests)
    violations: list[BoundaryViolation] = []
    for dotted in sorted(topo.modules):
        record = topo.modules[dotted]
        violations.extend(_collect_violations(record.imports, record, topo))
    violations.sort(key=lambda item: (item.file, item.line, item.rule_id))
    return BoundaryReport(
        root_dir=topo.root_dir, root_package=topo.root_package,
        scanned_files=topo.scanned_files, violations=tuple(violations),
        parse_errors=topo.parse_errors)
def check_source_boundary(
        source: str, filename: str, topology: ModuleTopology) -> list[BoundaryViolation]:
    file_text = _path_text(filename)
    if not file_text:
        return []
    try:
        tree = ast.parse(source, filename=file_text)
    except PARSE_DEGRADE_EXC as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='check_source_boundary:parse')
        return []
    record = _record_for_filename(file_text, topology)
    if record is None:
        return []
    return _collect_violations(_import_refs(tree), record, topology)
def _record_for_filename(
        filename: str, topology: ModuleTopology) -> ModuleRecord | None:
    text = _path_text(filename)
    if not text:
        return None
    root = topology.root_dir
    raw_target = text if os.path.isabs(text) else os.path.join(root, text)
    # topology 内的记录路径均为 realpath，调用方传入的文件路径须同样归一才能命中。
    target_path = os.path.normpath(os.path.realpath(os.path.abspath(raw_target)))
    norm_target = os.path.normcase(target_path)
    for record in topology.modules.values():
        if os.path.normcase(os.path.abspath(record.path)) == norm_target:
            return record
    identity_root = root
    flat_layout = topology.flat_layout
    if not _path_within(target_path, root):
        skill_root = topology.skill_root
        if not skill_root or not _path_within(target_path, skill_root):
            return None
        identity_root = skill_root
        flat_layout = True
    dotted, is_package = _dotted_for(
        target_path, identity_root, topology.root_package, flat_layout)
    parent, depth = _module_identity(dotted, is_package)
    return ModuleRecord(
        dotted=dotted, path=target_path, package=parent,
        depth=depth, is_package=is_package, exports=frozenset(),
        has_all=False)
def summarize_boundary_scan(report: BoundaryReport) -> dict[str, Any]:
    counts = report.counts
    return {
        "root_package": report.root_package,
        "scanned_files": report.scanned_files,
        "total": report.total,
        "counts": counts,
        "by_kind": {
            _RULE_KIND[rule_id]: counts.get(rule_id, 0)
            for rule_id in BOUNDARY_RULE_IDS
        },
        "parse_errors": len(report.parse_errors),
        "sample": [item.as_dict() for item in report.violations[:20]],
    }
def _cycle_keys(skill_dir: str, include_tests: bool) -> tuple[str, ...]:
    graph, _symbols = build_normalized_import_graph(
        skill_dir, include_tests=include_tests)
    cycles = find_graph_cycles(graph)
    keys: list[str] = []
    for cycle in cycles:
        nodes = sorted({str(node) for node in cycle})
        if nodes:
            keys.append("->".join(nodes))
    return tuple(sorted(set(keys)))
def _complexity_metrics(skill_dir: str, include_tests: bool) -> dict[str, Any]:
    total = 0
    maximum = 0
    count = 0
    scanned = 0
    for path in iter_py_files(skill_dir, include_tests):
        _source, tree = parse_py_file(path, quiet=True)
        if tree is None:
            continue
        scanned += 1
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            score = cyclomatic_complexity(
                node, partial(iter_own_scope, skip_lambda=True,
                              include_self=True))
            total += score
            maximum = max(maximum, score)
            count += 1
    return {
        "function_count": count,
        "total_complexity": total,
        "max_complexity": maximum,
        "avg_complexity": round(total / count, 4) if count else 0.0,
        "scanned_files": scanned,
    }
def _root_public_surface(
        topology: ModuleTopology) -> tuple[list[str], bool, bool]:
    if topology.flat_layout:
        records = [record for dotted, record in topology.modules.items()
                   if "." not in dotted]
        symbols = sorted({name for record in records
                          for name in record.exports})
        has_all = bool(records) and all(r.has_all for r in records)
        complete = all(record.exports_complete for record in records)
        return symbols, has_all, complete
    root_record = topology.resolve(topology.root_package)
    if root_record is None:
        return [], False, False
    return (sorted(root_record.exports), bool(root_record.has_all),
            root_record.exports_complete)
def capture_governance_metrics(
        skill_dir: str, include_tests: bool = _DEFAULT_INCLUDE_TESTS,
        health_score: float | None = None) -> dict[str, Any]:
    topology = build_module_topology(skill_dir, include_tests)
    boundary = scan_boundary_imports(skill_dir, include_tests, topology)
    public_symbols, public_has_all, public_complete = (
        _root_public_surface(topology))
    complexity = _complexity_metrics(skill_dir, include_tests)
    return {
        "cycles": _cycle_keys(skill_dir, include_tests),
        "illegal_imports": boundary.keys(),
        "illegal_import_counts": boundary.counts,
        "public_api": {
            "count": len(public_symbols),
            "symbols": public_symbols,
            "has_all": public_has_all,
            "complete": public_complete,
        },
        "complexity": complexity,
        "health_score": health_score,
        "scanned_files": boundary.scanned_files,
    }
def _self_declared_profile() -> Any | None:
    try:
        return load_declared_profile(self_skill_root())
    except (SkillProfileError, OSError, ValueError) as exc:
        log_swallowed(__name__, exc, context="diag_module_topology:self_profile")
        return None
_SELF_DECLARED = _self_declared_profile()
MODULE_LAYER_MAP: dict[str, int] = dict(
    _SELF_DECLARED.layer_map if _SELF_DECLARED is not None else {})
UNREGISTERED_BY_DESIGN: frozenset[str] = frozenset()
_LAYER_SECTION_NAMES = {
    0: "L0: 基础类型/常量/工具/日志",
    1: "L1: 守卫层",
    2: "L2: 检查层",
    3: "L3: 引擎层",
    4: "L4: 构建层",
    5: "L5: 编排层",
}
_LAYER_MAP_NAME = "MODULE_LAYER_MAP"
_LAYER_MAP_MODULE_FILE = LEGACY_DECLARATION_MODULE
_LAYER_REGISTRY_HOST_DIR = os.path.normcase(self_skill_root())
def _all_deps(graph, module: str,
              excluded_modules: frozenset[str]) -> set:
    deps = (graph.edges.get(module, set())
            | graph.implicit_edges.get(module, set()))
    return {dep for dep in deps if dep in graph.nodes} - excluded_modules
def _next_layer(dep_layers: list[int]) -> int:
    return max(dep_layers) + 1
def _known_dep_layers(deps: set, inferred: dict[str, int]) -> list[int]:
    return [inferred[d] for d in deps if d in inferred]
def _scc_external_deps(members: list[str], graph,
                        excluded_modules: frozenset[str]) -> set:
    external: set = set()
    for m in members:
        for d in _all_deps(graph, m, excluded_modules):
            if d not in members:
                external.add(d)
    return external
def _scc_external_consumers(members: list[str], graph,
                            excluded_modules: frozenset[str]) -> set:
    member_set = set(members)
    consumers: set = set()
    for module in graph.nodes:
        if module in member_set:
            continue
        if _all_deps(graph, module, excluded_modules) & member_set:
            consumers.add(module)
    return consumers
def _scc_components(graph) -> list[set[str]]:
    combined = {
        module: _all_deps(graph, module, frozenset())
        for module in graph.nodes
    }
    return [set(component) for component in _graph_scc(combined)]
def infer_layer_map(graph, current_map: dict,
                    excluded_modules: frozenset[str] = _DEFAULT_EXCLUDED_MODULES
                    ) -> tuple[dict, dict]:
    sccs = _scc_components(graph)
    module_to_scc: dict[str, int] = {}
    scc_sizes: dict[int, int] = {}
    for i, scc in enumerate(sccs):
        scc_sizes[i] = len(scc)
        for m in scc:
            module_to_scc[m] = i
    inferred: dict[str, int] = dict(current_map)
    _anchor_pass(inferred, graph, excluded_modules,
                 skip=frozenset(m for m in graph.nodes
                                if _in_scc_cycle(m, graph, module_to_scc,
                                                 scc_sizes)))
    unsolved = sorted(m for m in graph.nodes if m not in inferred)
    if unsolved:
        _resolve_scc_deferred(
            unsolved, module_to_scc, inferred, graph, excluded_modules)
    alt_layers = _recompute_alt_layers(
        graph, current_map, inferred, excluded_modules)
    return inferred, alt_layers
def _in_scc_cycle(module: str, graph, module_to_scc: dict[str, int],
                  scc_sizes: dict[int, int]) -> bool:
    idx = module_to_scc.get(module)
    if idx is None:
        return False
    if scc_sizes.get(idx, 1) > 1:
        return True
    return module in _all_deps(graph, module, frozenset())
def _anchor_pass(inferred: dict[str, int], graph,
                 excluded_modules: frozenset[str],
                 max_iter: int = 20,
                 skip: frozenset[str] = frozenset()) -> None:
    for _ in range(max_iter):
        changed = False
        for module in sorted(graph.nodes):
            if module in inferred or module in skip:
                continue
            if _assign_group_layer(
                    [module], graph, inferred, excluded_modules,
                    scc_scope=[module]):
                changed = True
        if not changed:
            break
def _build_scc_groups(unsolved: list[str],
                     module_to_scc: dict[str, int]) -> list[list[str]]:
    scc_groups: dict[int, list[str]] = {}
    _solo_key = -2
    for m in unsolved:
        scc_idx = module_to_scc.get(m, -1)
        if scc_idx == -1:
            scc_groups[_solo_key] = [m]
            _solo_key -= 1
        else:
            if scc_idx not in scc_groups:
                scc_groups[scc_idx] = []
            scc_groups[scc_idx].append(m)
    return list(scc_groups.values())
def _resolve_scc_deferred(unsolved: list[str],
                          module_to_scc: dict[str, int],
                          inferred: dict[str, int], graph,
                          excluded_modules: frozenset[str]) -> None:
    scope_by_scc = _scc_member_scope(module_to_scc)
    pending = _build_scc_groups(unsolved, module_to_scc)
    while pending:
        deferred = [members for members in pending
                    if not _assign_group_layer(
                        members, graph, inferred, excluded_modules,
                        scc_scope=_group_scc_scope(members, module_to_scc,
                                                   scope_by_scc))]
        if not deferred:
            break
        if len(deferred) == len(pending):
            for members in deferred:
                _assign_group_layer(
                    members, graph, inferred, excluded_modules, strict=False,
                    scc_scope=_group_scc_scope(members, module_to_scc,
                                               scope_by_scc))
            break
        pending = deferred
def _scc_member_scope(module_to_scc: dict[str, int]) -> dict[int, list[str]]:
    scope: dict[int, list[str]] = {}
    for module, idx in module_to_scc.items():
        scope.setdefault(idx, []).append(module)
    return scope
def _group_scc_scope(members: list[str], module_to_scc: dict[str, int],
                     scope_by_scc: dict[int, list[str]]) -> list[str]:
    idx = module_to_scc.get(members[0], -1)
    return sorted(scope_by_scc.get(idx, members))
def _assign_group_layer(members: list[str], graph,
                        inferred: dict[str, int],
                        excluded_modules: frozenset[str],
                        strict: bool = True,
                        scc_scope: list[str] | None = None) -> bool:
    scope = scc_scope if scc_scope is not None else members
    anchor_layers = [inferred[m] for m in scope if m in inferred]
    external_deps = _scc_external_deps(scope, graph, excluded_modules)
    dep_layers = _known_dep_layers(external_deps, inferred)
    if strict and len(dep_layers) != len(external_deps):
        return False
    required_layer = _next_layer(dep_layers) if dep_layers else 0
    minimum = max((*dep_layers, *anchor_layers), default=0)
    consumers = _scc_external_consumers(scope, graph, excluded_modules)
    consumer_caps = [inferred[m] for m in consumers if m in inferred]
    cap = min(consumer_caps) if consumer_caps else None
    if cap is not None and cap < minimum:
        return False
    if anchor_layers:
        anchor = anchor_layers[0]
        if any(layer != anchor for layer in anchor_layers[1:]) \
                or minimum > anchor or (cap is not None and cap < anchor):
            return False
        layer = anchor
    else:
        preferred = required_layer
        layer = min(preferred, cap) if cap is not None else preferred
    for module in members:
        inferred[module] = layer
    return True
def _recompute_alt_layers(graph, current_map: dict,
                          inferred: dict[str, int],
                          excluded_modules: frozenset[str]) -> dict[str, int]:
    alt_layers: dict[str, int] = {}
    resolved = dict(inferred)
    pending = [sorted(component) for component in _scc_components(graph)]
    while pending:
        deferred: list[list[str]] = []
        progressed = False
        for members in pending:
            external_deps = _scc_external_deps(
                members, graph, excluded_modules)
            if any(dep in current_map and dep not in alt_layers
                   for dep in external_deps):
                deferred.append(members)
                continue
            dep_layers = _known_dep_layers(external_deps, resolved)
            if len(dep_layers) != len(external_deps):
                deferred.append(members)
                continue
            alt_layer = _next_layer(dep_layers) if dep_layers else 0
            for module in members:
                if module in current_map:
                    alt_layers[module] = alt_layer
                    resolved[module] = alt_layer
            progressed = True
        if not deferred:
            break
        if not progressed:
            logger.warning("[auto_layer] 层级别名图存在未解分量，跳过其 update 建议: %s",
                           deferred)
            break
        pending = deferred
    return alt_layers
def _new_layer_inversions(graph, baseline: dict[str, int],
                          final: dict[str, int],
                          excluded_modules: frozenset[str]) -> list[tuple[str, str]]:
    inversions: list[tuple[str, str]] = []
    for module in sorted(graph.nodes):
        for dependency in sorted(
                _all_deps(graph, module, excluded_modules)):
            if (module not in baseline or dependency not in baseline
                    or module not in final or dependency not in final):
                continue
            if (final[module] < final[dependency]
                    and baseline[module] >= baseline[dependency]):
                inversions.append((module, dependency))
    return inversions
def _selected_update_components(graph, current_map: dict,
                                inferred: dict[str, int],
                                alt_layers: dict[str, int],
                                excluded_modules: frozenset[str]) -> set[int]:
    components = [sorted(component) for component in _scc_components(graph)]
    module_to_component = {
        module: index for index, members in enumerate(components)
        for module in members
    }
    updatable = {
        index for index, members in enumerate(components)
        if all(module in current_map and module in alt_layers
               and module not in excluded_modules
               for module in members)
    }
    selected = {
        index for index in updatable
        if any(abs(current_map[module] - alt_layers[module]) >= 2
               for module in components[index])
    }
    baseline = dict(inferred)
    baseline.update(current_map)
    while selected:
        final = dict(baseline)
        for index in selected:
            for module in components[index]:
                final[module] = alt_layers[module]
        inversions = _new_layer_inversions(
            graph, baseline, final, excluded_modules)
        if not inversions:
            return selected
        expanded = False
        for module, dependency in inversions:
            for endpoint in (module, dependency):
                index = module_to_component.get(endpoint)
                if index in updatable and index not in selected:
                    selected.add(index)
                    expanded = True
        if not expanded:
            logger.warning(
                "[auto_layer] 更新建议无法闭合层级约束，放弃本批 update: %s",
                inversions)
            return set()
    return selected
def _add_update_suggestions(graph, current_map: dict,
                            inferred: dict[str, int],
                            alt_layers: dict[str, int],
                            excluded_modules: frozenset[str]) -> list[dict]:
    suggestions: list[dict] = []
    for module in sorted(graph.nodes):
        if module in current_map or module in excluded_modules:
            continue
        suggested = inferred.get(module)
        if suggested is None:
            continue
        suggestions.append({
            "action": "add",
            "module": module,
            "current": None,
            "suggested": suggested,
        })
    components = [sorted(component) for component in _scc_components(graph)]
    selected = _selected_update_components(
        graph, current_map, inferred, alt_layers, excluded_modules)
    for index in sorted(selected):
        for module in components[index]:
            alt_layer = alt_layers[module]
            if current_map[module] == alt_layer:
                continue
            gap = abs(current_map[module] - alt_layer)
            suggestions.append({
                "action": "update",
                "module": module,
                "current": current_map[module],
                "suggested": alt_layer,
                "gap": gap,
                "reason": f"当前 L{current_map[module]} 与复算 L{alt_layer} 差距 {gap} 层",
            })
    suggestions.sort(key=lambda item: item["module"])
    return suggestions
def _remove_suggestions(current_map: dict, registry_host: bool,
                        known_modules: frozenset[str] | None = None,
                        excluded_modules: frozenset[str] = _DEFAULT_EXCLUDED_MODULES
                        ) -> list[dict]:
    if not registry_host:
        return []
    alive = known_modules if known_modules is not None else frozenset(current_map)
    return [{
        "action": "remove",
        "module": module,
        "current": current_map[module],
        "suggested": None,
        "reason": "模块文件已不存在",
    } for module in sorted(current_map)
        if module not in alive and module not in excluded_modules]
def build_layer_suggestions(graph, current_map: dict,
                       inferred: dict[str, int],
                       alt_layers: dict[str, int],
                       registry_host: bool,
                       excluded_modules: frozenset[str] = _DEFAULT_EXCLUDED_MODULES,
                       known_modules: frozenset[str] | None = None
                       ) -> list[dict]:
    suggestions = _add_update_suggestions(
        graph, current_map, inferred, alt_layers, excluded_modules)
    suggestions.extend(
        _remove_suggestions(
            current_map, registry_host, known_modules, excluded_modules))
    return suggestions
def is_registry_host(skill_dir: Any) -> bool:
    root = _path_text(skill_dir)
    if not root:
        return False
    return (os.path.normcase(os.path.realpath(os.path.abspath(root)))
            == _LAYER_REGISTRY_HOST_DIR)
def _authoritative_table_unreadable(skill_dir: str) -> bool:
    if _profile_declaration_unreadable(skill_dir):
        return True
    if (_profile_declares_layer_map(skill_dir)
            and _profile_layer_map(skill_dir) is None):
        return True
    path = os.path.join(skill_dir, _LAYER_MAP_MODULE_FILE)
    return os.path.isfile(path) and not _module_table_writable(path)
def has_layer_registry_surface(skill_dir: Any) -> bool:
    root = _path_text(skill_dir)
    if not root:
        return False
    return (_profile_declares_layer_map(root)
            or _module_table_writable(
                os.path.join(root, _LAYER_MAP_MODULE_FILE)))
def apply_layer_suggestions(suggestions: list[dict], skill_dir: Any,
                            dry_run: bool = True) -> bool:
    if dry_run:
        return False
    root = _path_text(skill_dir)
    if not root or not has_layer_registry_surface(root):
        logger.info("[auto_layer] 目标无权威层表，仅产建议（不写回）: %s",
                    root or skill_dir)
        return False
    applied = _apply_suggestions(suggestions, root)
    if not applied:
        logger.error("[auto_suggest_layer_map] 建议写回失败，"
                     "MODULE_LAYER_MAP 未变更: %s", root)
    return applied
_LAYER_SUGGESTION_ACTIONS: frozenset[str] = frozenset(
    {"add", "update", "remove"})
def _suggestion_error(suggestion: Any, index: int) -> str | None:
    if not isinstance(suggestion, dict):
        return f"建议 #{index} 非对象({type(suggestion).__name__})"
    module = suggestion.get("module")
    if not isinstance(module, str) or not module.strip():
        return f"建议 #{index} 缺少非空 module 键: {suggestion!r}"
    if module != module.strip():
        return f"建议 #{index} 的 module 含首尾空白: {module!r}"
    action = suggestion.get("action")
    if not isinstance(action, str) or action not in _LAYER_SUGGESTION_ACTIONS:
        return (f"建议 #{index} 的 action 非法({action!r})，"
                f"合法值: {sorted(_LAYER_SUGGESTION_ACTIONS)}")
    if action != "remove":
        suggested = suggestion.get("suggested")
        if (not isinstance(suggested, int) or isinstance(suggested, bool)
                or suggested < 0):
            return (f"建议 #{index} 的 suggested 须为非负纯 int，"
                    f"实际为 {suggested!r}")
    return None
def _apply_suggestions(suggestions: list[dict], skill_dir: str) -> bool:
    if _authoritative_table_unreadable(skill_dir):
        logger.error("[auto_layer] 权威表存在但不可读/校验失败，拒绝写回以免"
                     "整表被部分建议覆盖: %s", skill_dir)
        return False
    if not isinstance(suggestions, (list, tuple)):
        logger.error("[auto_layer] 建议容器非法(%s)，拒绝写回: %s",
                     type(suggestions).__name__, skill_dir)
        return False
    for index, suggestion in enumerate(suggestions):
        error = _suggestion_error(suggestion, index)
        if error is not None:
            logger.error("[auto_layer] %s，拒绝写回以免部分建议落盘: %s",
                         error, skill_dir)
            return False
    current_map = target_layer_map(skill_dir)
    new_map = dict(current_map)
    for s in suggestions:
        if s["action"] == "remove":
            new_map.pop(s["module"], None)
            continue
        new_map[s["module"]] = s["suggested"]
    if new_map == current_map:
        return True
    if _write_layer_map(new_map, skill_dir):
        if is_registry_host(skill_dir):
            MODULE_LAYER_MAP.clear()
            MODULE_LAYER_MAP.update(new_map)
        return True
    return False
def _validate_layer_map_input(layer_map: dict[str, int]) -> bool:
    if not isinstance(layer_map, dict):
        logger.warning("[auto_layer] 层表载荷非 dict(%s)，拒绝写回",
                       type(layer_map).__name__)
        return False
    for module, layer in layer_map.items():
        if not isinstance(module, str) or not module:
            logger.warning("[auto_layer] 非法登记键 %r（须为非空 str），拒绝写回", module)
            return False
        if module != module.strip():
            logger.warning("[auto_layer] 登记键 %r 含首尾空白，拒绝写回", module)
            return False
        if not isinstance(layer, int) or isinstance(layer, bool) or layer < 0:
            logger.warning(
                "[auto_layer] 模块 %r 层级值 %r 非法（须为非负纯 int，bool 排除），拒绝写回",
                module, layer)
            return False
    return True
def _write_layer_map(layer_map: dict[str, int], skill_dir: str) -> bool:
    if not _validate_layer_map_input(layer_map):
        return False
    write_profile = _profile_declares_layer_map(skill_dir)
    module_path = os.path.join(skill_dir, _LAYER_MAP_MODULE_FILE)
    module_exists = os.path.isfile(module_path)
    write_module = _module_table_writable(module_path)
    if not (write_profile or write_module):
        logger.warning("[auto_layer] 目标无权威声明面可写，拒绝凭空创建: %s",
                       skill_dir)
        return False
    if module_exists and not write_module:
        logger.error("[auto_layer] 模块常量表不可解析，拒绝写回以免整表被"
                     "部分建议覆盖: %s", module_path)
        return False
    profile_path = os.path.join(skill_dir, PROFILE_FILENAME)
    profile_source = (_read_table_source(profile_path)
                      if write_profile else None)
    if write_profile and profile_source is None:
        return False
    if write_profile and not _write_profile_layer_map(layer_map, skill_dir):
        return False
    if write_module and not rewrite_mapping_table(
            module_path, _LAYER_MAP_NAME, layer_map, _LAYER_SECTION_NAMES):
        if write_profile:
            try:
                atomic_write_text(
                    profile_path, profile_source,
                    tag="auto_layer_rollback", newline="")
            except OSError:
                logger.exception("[auto_layer] 模块表写回失败且画像恢复失败，"
                                 "声明面需要人工核对 %s", profile_path)
        return False
    logger.info("[auto_layer] 已更新 MODULE_LAYER_MAP (%d 模块)", len(layer_map))
    return True
_PROFILE_JSON_LOAD_EXC = (
    OSError, UnicodeDecodeError, json.JSONDecodeError, RecursionError,
)
def _read_profile_declaration(skill_dir: str) -> dict[str, Any] | None:
    path = os.path.join(skill_dir, PROFILE_FILENAME)
    if not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8-sig") as handle:
            payload = json.load(handle)
    except _PROFILE_JSON_LOAD_EXC as exc:
        logger.warning("[auto_layer] 画像声明不可解析，按未声明处理: %s: %s",
                       path, exc)
        return None
    return payload if isinstance(payload, dict) else None
def _profile_declaration_unreadable(skill_dir: str) -> bool:
    path = os.path.join(skill_dir, PROFILE_FILENAME)
    return os.path.isfile(path) and _read_profile_declaration(skill_dir) is None
def _profile_declares_layer_map(skill_dir: str) -> bool:
    payload = _read_profile_declaration(skill_dir)
    return payload is not None and "layer_map" in payload
def _module_table_writable(module_path: str) -> bool:
    if not os.path.isfile(module_path):
        return False
    try:
        return _read_layer_map_table(module_path) is not None
    except Exception as exc:
        log_swallowed(__name__, exc, context='_module_table_writable:read')
        return False
def _write_profile_layer_map(layer_map: dict[str, int],
                             skill_dir: str) -> bool:
    path = os.path.join(skill_dir, PROFILE_FILENAME)
    try:
        with open(path, encoding="utf-8-sig") as handle:
            payload = json.load(handle)
    except _PROFILE_JSON_LOAD_EXC as exc:
        logger.warning("[auto_layer] 读取画像声明失败，拒绝写回 %s: %s",
                       path, exc)
        return False
    if not isinstance(payload, dict):
        logger.warning("[auto_layer] 画像声明顶层非对象，拒绝写回: %s", path)
        return False
    payload["layer_map"] = dict(sorted(layer_map.items()))
    try:
        write_json_artifact(path, payload, indent=2)
    except OSError as exc:
        logger.warning("[auto_layer] 画像声明写回失败 %s: %s", path, exc)
        return False
    return True
_SECTION_COUNT_RE = re.compile(r"\(\s*\d+\s*模块\s*\)")
_TABLE_ENTRY_RE = re.compile(
    r'^(\s*)((?:"(?:\\.|[^"\\\r\n])*"'
    r"|(?:'(?:\\.|[^'\\\r\n])*')))"
    r'\s*:\s*(\d+)\s*,?(\s*(?:#.*)?)$')
_TABLE_HEADER_RE = re.compile(r"^\s*#\s*──\s*L(\d+)\b")
def _mk_table_item(kind: str, line: str, key: str | None = None,
                   layer: int | None = None, indent: str = "",
                   inline: str = "") -> dict:
    return {"kind": kind, "line": line, "key": key, "layer": layer,
            "indent": indent, "inline": inline}
def _parse_table_document(table_lines: list[str]) -> list[dict]:
    return [_classify_table_line(idx, line)
            for idx, line in enumerate(table_lines)]
def _classify_table_line(idx: int, line: str) -> dict:
    if idx == 0:
        return _mk_table_item("open", line)
    stripped = line.strip()
    if not stripped:
        return _mk_table_item("blank", line)
    if stripped.startswith("#"):
        header = _TABLE_HEADER_RE.match(line)
        if header:
            return _mk_table_item("header", line, layer=int(header.group(1)))
        return _mk_table_item("comment", line)
    entry = _TABLE_ENTRY_RE.match(line)
    if not entry:
        return _mk_table_item("other", line)
    try:
        key = str_constant_value(ast.parse(entry.group(2), mode="eval").body)
        layer = int(entry.group(3))
    except PARSE_DEGRADE_EXC:
        return _mk_table_item("other", line)
    if key is None:
        return _mk_table_item("other", line)
    return _mk_table_item(
        "entry", line, key=key, layer=layer,
        indent=entry.group(1), inline=entry.group(4) or "")
def _refresh_section_counts(items: list[dict]) -> None:
    header_pos = [i for i, it in enumerate(items) if it["kind"] == "header"]
    bounds = [*header_pos, len(items)]
    for seg, h in enumerate(header_pos):
        stop = bounds[seg + 1]
        n = sum(1 for it in items[h + 1:stop] if it["kind"] == "entry")
        if _SECTION_COUNT_RE.search(items[h]["line"]):
            items[h]["line"] = _SECTION_COUNT_RE.sub(
                f"({n} 模块)", items[h]["line"], count=1)
def _entry_keys(items: list[dict]) -> list[str]:
    return [it["key"] for it in items if it["kind"] == "entry"]
def _collect_incoming(items: list[dict], mapping: dict[str, int]
                      ) -> tuple[set[int], dict[int, list[list[dict]]]]:
    keys = _entry_keys(items)
    drop: set[int] = set()
    incoming: dict[int, list[list[dict]]] = {}
    for i, it in enumerate(items):
        if it["kind"] != "entry":
            continue
        want = mapping.get(it["key"])
        if want is None:
            drop.add(i)
            continue
        if want == it["layer"]:
            continue
        drop.add(i)
        payload = _collect_moved_entry(items, i, want, drop)
        incoming.setdefault(want, []).append(payload)
    _collect_added_entries(mapping, keys, incoming)
    return drop, incoming
def _entry_line(key: str, layer: int, indent: str = "    ",
                inline: str = "") -> str:
    return f'{indent}{json.dumps(key, ensure_ascii=False)}: {layer},' + inline
def _collect_moved_entry(items: list[dict], index: int, want: int,
                         drop: set[int]) -> list[dict]:
    item = items[index]
    payload: list[dict] = []
    cursor = index - 1
    while cursor >= 0 and items[cursor]["kind"] == "comment":
        drop.add(cursor)
        payload.insert(0, items[cursor])
        cursor -= 1
    moved = _mk_table_item(
        "entry",
        _entry_line(item["key"], want, item["indent"], item["inline"]),
        key=item["key"], layer=want, indent=item["indent"],
        inline=item["inline"])
    moved["eol"] = item.get("eol")
    payload.append(moved)
    return payload
def _collect_added_entries(mapping: dict[str, int], keys: list[str],
                           incoming: dict[int, list[list[dict]]]) -> None:
    for key in sorted(set(mapping) - set(keys)):
        layer = mapping[key]
        incoming.setdefault(layer, []).append(
            [_mk_table_item("entry", _entry_line(key, layer),
                            key=key, layer=layer, indent="    ")])
def _group_tail_anchor(items: list[dict], header_pos: list[int],
                       anchor: int, drop: set[int]) -> int:
    stop = next((h2 for h2 in header_pos if h2 > anchor), len(items))
    last_entry = max(
        (i for i in range(anchor + 1, stop)
         if items[i]["kind"] == "entry" and i not in drop),
        default=None)
    return last_entry if last_entry is not None else anchor
def _dominant_header_indent(items: list[dict]) -> str:
    for item in items:
        if item["kind"] == "header":
            line = item["line"]
            return line[:len(line) - len(line.lstrip())]
    return "    "
def _uses_blank_separators(items: list[dict]) -> bool:
    return any(item["kind"] == "blank" for item in items[1:])
def _build_group_section(layer: int, payloads: list[list[dict]],
                         section_titles: dict[int, str], *,
                         header_indent: str, lead_blank: bool,
                         trail_blank: bool) -> list[dict]:
    section: list[dict] = []
    if lead_blank:
        section.append(_mk_table_item("blank", ""))
    section.append(_mk_table_item(
        "header",
        f'{header_indent}# ── {section_titles.get(layer, f"L{layer}")}'
        f' ({len(payloads)} 模块) ──',
        layer=layer))
    for payload in payloads:
        section.extend(payload)
    if trail_blank:
        section.append(_mk_table_item("blank", ""))
    return section
def _group_anchor(items: list[dict], header_pos: list[int],
                  layer: int, drop: set[int]) -> int | None:
    header = next((h for h in header_pos if items[h]["layer"] == layer), None)
    if header is None:
        return None
    return _group_tail_anchor(items, header_pos, header, drop)
def _new_group_anchor(items: list[dict], header_pos: list[int],
                      layer: int, footer: int) -> int:
    return next((h for h in header_pos if items[h]["layer"] > layer), footer)
def _plan_insertions(items: list[dict], drop: set[int],
                     incoming: dict[int, list[list[dict]]],
                     section_titles: dict[int, str]
                     ) -> tuple[dict[int, list[dict]], dict[int, list[dict]]]:
    after_map: dict[int, list[dict]] = {}
    before_map: dict[int, list[dict]] = {}
    header_pos = [i for i, it in enumerate(items) if it["kind"] == "header"]
    footer = len(items) - 1
    header_indent = _dominant_header_indent(items)
    blank_style = _uses_blank_separators(items)
    for layer in sorted(incoming):
        payloads = incoming[layer]
        after = _group_anchor(items, header_pos, layer, drop)
        if after is not None:
            for payload in payloads:
                after_map.setdefault(after, []).extend(payload)
            continue
        anchor = _new_group_anchor(items, header_pos, layer, footer)
        lead_blank = blank_style and not (
            anchor > 0 and items[anchor - 1]["kind"] == "blank")
        trail_blank = (blank_style and anchor < len(items)
                       and items[anchor]["kind"] == "header")
        before_map.setdefault(anchor, []).extend(
            _build_group_section(layer, payloads, section_titles,
                                 header_indent=header_indent,
                                 lead_blank=lead_blank,
                                 trail_blank=trail_blank))
    return after_map, before_map
def _ensure_entry_commas(items: list[dict]) -> None:
    entry_positions = [index for index, item in enumerate(items)
                       if item["kind"] == "entry"]
    for index in entry_positions[:-1]:
        item = items[index]
        inline = item.get("inline", "")
        code = item["line"][:-len(inline)] if inline else item["line"]
        if code.rstrip().endswith(","):
            continue
        code_without_space = code.rstrip()
        item["line"] = (code_without_space + ","
                        + code[len(code_without_space):] + inline)
def _rewrite_table_document(items: list[dict], mapping: dict[str, int],
                            section_titles: dict[int, str]
                            ) -> list[dict] | None:
    keys = _entry_keys(items)
    if len(keys) != len(set(keys)):
        return None
    drop, incoming = _collect_incoming(items, mapping)
    after_map, before_map = _plan_insertions(
        items, drop, incoming, section_titles)
    new_items: list[dict] = []
    for i, it in enumerate(items):
        new_items.extend(before_map.get(i, []))
        if i in drop:
            continue
        new_items.append(it)
        new_items.extend(after_map.get(i, []))
    _ensure_entry_commas(new_items)
    _refresh_section_counts(new_items)
    return new_items
def _split_physical_lines(source: str) -> tuple[list[str], list[str]]:
    lines: list[str] = []
    eols: list[str] = []
    for chunk in split_tokenizer_lines(source):
        body = chunk.rstrip("\r\n")
        lines.append(body)
        eols.append(chunk[len(body):])
    if not lines:
        lines.append("")
        eols.append("")
    return lines, eols
def _join_phys(lines: list[str], eols: list[str]) -> str:
    return "".join(line + eol for line, eol in zip(lines, eols, strict=True))
def _read_table_source(module_path: str) -> str | None:
    try:
        with open(module_path, "rb") as f:
            source_bytes = f.read()
    except OSError as exc:
        logger.warning("[auto_layer] 读取 %s 失败: %s", module_path, exc)
        return None
    try:
        source_encoding = tokenize.detect_encoding(
            io.BytesIO(source_bytes).readline)[0]
    except (SyntaxError, LookupError) as exc:
        logger.warning("[auto_layer] 编码判定失败 %s，拒绝写回: %s",
                     module_path, exc)
        return None
    if source_encoding.lower() not in ("utf-8", "utf-8-sig"):
        logger.warning(
            "[auto_layer] 源码编码 %r 非 utf-8 族（重解码写回会丢原始"
            "字节信息），拒绝写回: %s", source_encoding, module_path)
        return None
    try:
        return source_bytes.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        logger.warning("[auto_layer] utf-8 解码失败 %s，拒绝写回: %s",
                     module_path, exc)
        return None
def _find_table_node(tree: ast.Module, table_name: str) -> ast.AST | None:
    matches = [stmt for stmt in tree.body
               if _declares_table(stmt, table_name)]
    return matches[0] if len(matches) == 1 else None
def _written_map_from_node(check_node: ast.AST) -> dict | None:
    dict_node = check_node.value
    if not isinstance(dict_node, ast.Dict):
        return None
    if not all(str_constant_value(k) is not None for k in dict_node.keys):
        return None
    if not all(_is_int_constant(v) for v in dict_node.values):
        return None
    written = {k.value: v.value
               for k, v in zip(dict_node.keys, dict_node.values, strict=True)}
    return written if len(written) == len(dict_node.keys) else None
def _is_int_constant(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, int)
            and not isinstance(node.value, bool))
def _verify_written_source(new_source: str, module_path: str,
                           mapping: dict[str, int], table_name: str) -> bool:
    try:
        check_tree = _compile_source_ast(new_source, module_path)
    except PARSE_DEGRADE_EXC:
        logger.exception("[auto_layer] 新文本语法校验失败，放弃写回")
        return False
    check_node = _find_table_node(check_tree, table_name)
    if check_node is None:
        logger.error("[auto_layer] 写回自校验失败：未定位到 %s 字典定义，"
                   "放弃写回", table_name)
        return False
    written = _written_map_from_node(check_node)
    if written is None:
        logger.error("[auto_layer] 写回自校验失败：映射段非纯常量字典/存在"
                   "重复键，放弃写回")
        return False
    if written != dict(mapping):
        logger.error("[auto_layer] 写回自校验失败：盘面映射与目标映射不一致，"
                   "放弃写回")
        return False
    return True
def _backup_table_source(module_path: str) -> bool:
    skill_dir = os.path.dirname(os.path.abspath(module_path))
    try:
        backup_path = archive_backup(module_path, skill_dir, "auto_layer")
    except Exception as exc:
        logger.error("[auto_layer] 写回前备份失败，拒绝写回: %s", exc)
        return False
    if not backup_path:
        logger.error("[auto_layer] 写回前备份失败，拒绝写回: %s", module_path)
        return False
    return True
def _backup_and_write(module_path: str, new_source: str) -> bool:
    if not _backup_table_source(module_path):
        return False
    try:
        atomic_write_text(
            module_path, new_source, tag="auto_layer", newline="")
    except OSError as exc:
        logger.warning("[auto_layer] 写入 %s 失败: %s", module_path, exc)
        return False
    return True
class _TableDocument(NamedTuple):
    module_path: str
    phys_lines: list[str]
    phys_eols: list[str]
    line_sep: str
    start_line: int
    end_line: int
    items: list[dict]
def _dominant_line_sep(source: str) -> str:
    if "\r\n" in source:
        return "\r\n"
    return "\r" if "\r" in source else "\n"
def _compile_source_ast(source: str, module_path: str) -> ast.Module:
    norm_source = (source.replace("\r\n", "\n")
                   .replace("\r", "\n").removeprefix("\ufeff"))
    return compile(norm_source, module_path, "exec", ast.PyCF_ONLY_AST)
def _definition_segment(source: str, phys_lines: list[str],
                        module_path: str, table_name: str
                        ) -> tuple[int, int, list[str]] | None:
    try:
        tree = _compile_source_ast(source, module_path)
    except PARSE_DEGRADE_EXC as exc:
        logger.warning("[auto_layer] 解析 %s 失败: %s", module_path, exc)
        return None
    node = _find_table_node(tree, table_name)
    if node is None:
        logger.warning("[auto_layer] 未找到 %s 定义，无法自动更新", table_name)
        return None
    start_line, end_line = node.lineno, node.end_lineno
    segment_lines = phys_lines[start_line - 1:end_line]
    if len(segment_lines) < 2 or not segment_lines[-1].strip().startswith("}"):
        logger.warning("[auto_layer] %s 非多行字典字面量，拒绝行级写回",
                     table_name)
        return None
    return start_line, end_line, segment_lines
def _load_table_document(module_path: str,
                         table_name: str) -> _TableDocument | None:
    source = _read_table_source(module_path)
    if source is None:
        return None
    phys_lines, phys_eols = _split_physical_lines(source)
    segment = _definition_segment(source, phys_lines, module_path, table_name)
    if segment is None:
        return None
    start_line, end_line, segment_lines = segment
    items = _parse_table_document(segment_lines)
    for item, eol in zip(items, phys_eols[start_line - 1:end_line], strict=True):
        item["eol"] = eol
    return _TableDocument(module_path, phys_lines, phys_eols,
                          _dominant_line_sep(source),
                          start_line, end_line, items)
def _render_table_source(doc: _TableDocument, mapping: dict[str, int],
                         section_titles: dict[int, str]) -> str | None:
    new_items = _rewrite_table_document(doc.items, mapping, section_titles)
    if new_items is None:
        logger.warning("[auto_layer] 盘面映射存在重复/不可解析登记，放弃写回")
        return None
    new_dict_text = "".join(
        item["line"] + (item["eol"] if item.get("eol") is not None
                        else doc.line_sep)
        for item in new_items)
    return (_join_phys(doc.phys_lines[: doc.start_line - 1],
                       doc.phys_eols[: doc.start_line - 1])
            + new_dict_text
            + _join_phys(doc.phys_lines[doc.end_line:],
                         doc.phys_eols[doc.end_line:]))
def rewrite_mapping_table(module_path: Any, table_name: str,
                          mapping: dict[str, int],
                          section_titles: dict[int, str]) -> bool:
    path = _path_text(module_path)
    if not path or not isinstance(table_name, str) or not table_name.strip():
        logger.warning("[auto_layer] 表格重写入参非法（路径/表名）: %r %r",
                       module_path, table_name)
        return False
    table_name = table_name.strip()
    if not isinstance(section_titles, dict):
        logger.warning("[auto_layer] section_titles 非 dict(%s)，拒绝写回: %s",
                       type(section_titles).__name__, path)
        return False
    if not _validate_layer_map_input(mapping):
        return False
    doc = _load_table_document(path, table_name)
    if doc is None:
        return False
    new_source = _render_table_source(doc, mapping, section_titles)
    if new_source is None:
        return False
    if not _verify_written_source(new_source, path, mapping, table_name):
        return False
    return _backup_and_write(path, new_source)
def _declares_table(node: ast.stmt, table_name: str) -> bool:
    if isinstance(node, ast.AnnAssign):
        targets: list[ast.expr] = [node.target]
    elif isinstance(node, ast.Assign):
        targets = list(node.targets)
    else:
        return False
    return any(isinstance(t, ast.Name) and t.id == table_name
               for t in targets)
def _read_table_literal(path: str, table_name: str) -> Any:
    tree = ast.parse(read_source_auto(path), filename=path)
    node = _find_table_node(tree, table_name)
    value = getattr(node, "value", None)
    if value is None:
        logger.debug("模块级登记表缺少唯一 %s 声明（未声明/重复/仅注解）: %s",
                     table_name, path)
        return None
    if isinstance(value, ast.Dict):
        keys = [str_constant_value(key) for key in value.keys]
        if (all(key is not None for key in keys)
                and len(set(keys)) != len(keys)):
            logger.debug("模块级登记表 %s 含重复字符串键，拒绝静默覆盖: %s",
                         table_name, path)
            return None
    return ast.literal_eval(value)
def _read_layer_map_table(path: str) -> dict | None:
    layer_map = _read_table_literal(path, _LAYER_MAP_NAME)
    if not isinstance(layer_map, dict):
        return None
    return layer_map if _validate_layer_map_input(layer_map) else None
def _profile_layer_map(skill_dir: str) -> dict[str, int] | None:
    payload = _read_profile_declaration(skill_dir)
    if payload is None or "layer_map" not in payload:
        return None
    try:
        resolve_skill_profile(skill_dir, strict=True)
    except (SkillProfileError, OSError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_profile_layer_map:profile')
        return None
    layer_map = payload["layer_map"]
    if (not isinstance(layer_map, dict)
            or not _validate_layer_map_input(layer_map)):
        logger.warning(
            "[auto_layer] 画像 layer_map 声明非法（须为 module->非负 int 映射），"
            "按不可用处理: %s", os.path.join(skill_dir, PROFILE_FILENAME))
        return None
    return dict(layer_map)
def load_authoritative_layer_map(skill_dir: Any) -> dict[str, int] | None:
    root = _path_text(skill_dir)
    if not root:
        return None
    if _profile_declaration_unreadable(root):
        logger.warning(
            "[auto_layer] 画像声明存在但不可用，分析降级为未分层且拒绝"
            "回退遗留表: %s", os.path.join(root, PROFILE_FILENAME))
        return None
    declared_present = _profile_declares_layer_map(root)
    declared = _profile_layer_map(root)
    if declared is not None:
        return declared
    if declared_present:
        logger.warning(
            "[auto_layer] 画像 layer_map 已声明但不可用，分析降级为未分层、"
            "写回 fail-closed: %s", os.path.join(root, PROFILE_FILENAME))
        return None
    path = os.path.join(root, _LAYER_MAP_MODULE_FILE)
    if not os.path.isfile(path):
        return None
    try:
        layer_map = _read_layer_map_table(path)
    except Exception as exc:
        log_swallowed(__name__, exc,
                      context='load_authoritative_layer_map:parse')
        return None
    if layer_map is None:
        logger.warning("[auto_layer] 权威表存在但不可用（非纯常量字典或层级值"
                       "越界），分析降级为未分层、写回 fail-closed: %s", path)
    return layer_map
def target_layer_map(skill_dir: Any) -> dict[str, int]:
    loaded = load_authoritative_layer_map(skill_dir)
    return dict(loaded) if loaded is not None else {}
TOPOLOGY_INFRA_MODULES: tuple[str, ...] = (
    tuple(_SELF_DECLARED.infra_modules) if _SELF_DECLARED is not None else ())
def _load_target_infra_modules(skill_dir: str) -> tuple[str, ...] | None:
    path = os.path.join(skill_dir, _LAYER_MAP_MODULE_FILE)
    if not os.path.isfile(path):
        return None
    try:
        value = _read_table_literal(path, 'TOPOLOGY_INFRA_MODULES')
    except (OSError, *PARSE_DEGRADE_EXC) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_load_target_infra_modules:{type(_swallowed_exc).__name__}')
        return None
    if isinstance(value, (set, frozenset)):
        if not all(isinstance(item, str) for item in value):
            return None
        return tuple(sorted(value))
    if (isinstance(value, (tuple, list))
            and all(isinstance(item, str) for item in value)):
        return tuple(value)
    return None
def import_in_degrees(graph: dict[str, set[str]]) -> dict[str, int]:
    if not isinstance(graph, dict):
        return {}
    degrees: dict[str, int] = {}
    for targets in graph.values():
        if not isinstance(targets, (set, list, tuple)):
            continue
        seen: set[str] = set()
        for target in targets:
            if isinstance(target, str) and target and target not in seen:
                seen.add(target)
                degrees[target] = degrees.get(target, 0) + 1
    return degrees
def derive_infra_modules(degrees: dict[str, int], *,
                         min_degree: int = 3,
                         top_ratio: float = 0.9) -> tuple[str, ...]:
    if not isinstance(degrees, dict) or not degrees:
        return ()
    values = sorted(
        int(value) for value in degrees.values()
        if isinstance(value, int) and not isinstance(value, bool) and value > 0)
    if not values:
        return ()
    position = min(len(values) - 1, max(0, int((len(values) - 1) * top_ratio)))
    threshold = max(int(min_degree), values[position])
    return tuple(sorted(
        str(name) for name, value in degrees.items()
        if isinstance(value, int) and not isinstance(value, bool)
        and value >= threshold))
def target_infra_modules(skill_dir: Any,
                         degrees: dict[str, int] | None = None) -> tuple[str, ...]:
    root = _path_text(skill_dir)
    if not root:
        return ()
    profile_declared, profile = _profile_infra_modules(root)
    if profile is not None:
        return profile
    if profile_declared:
        logger.warning(
            "[auto_layer] 画像 infra_modules 已声明但不可用，拒绝回退到遗留表"
            "或入度推导: %s", os.path.join(root, PROFILE_FILENAME))
        return ()
    declared = _load_target_infra_modules(root)
    if declared is not None:
        return declared
    derived = derive_infra_modules(degrees or {})
    if derived:
        return derived
    return ()
def _profile_infra_modules(
        skill_dir: str) -> tuple[bool, tuple[str, ...] | None]:
    payload = _read_profile_declaration(skill_dir)
    if payload is None:
        return _profile_declaration_unreadable(skill_dir), None
    if "infra_modules" not in payload:
        return False, None
    declared = payload["infra_modules"]
    if (not isinstance(declared, list)
            or not all(isinstance(item, str) and item for item in declared)):
        logger.warning(
            "[auto_layer] 画像 infra_modules 声明非法（须为非空 str 列表），"
            "按不可用处理: %s", os.path.join(skill_dir, PROFILE_FILENAME))
        return True, None
    try:
        resolve_skill_profile(skill_dir, strict=True)
    except (SkillProfileError, OSError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_profile_infra_modules:profile')
        return True, None
    return True, tuple(declared)

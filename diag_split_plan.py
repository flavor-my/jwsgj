from __future__ import annotations

import ast
import keyword
import logging
import math
import os
import re
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from difflib import SequenceMatcher
from enum import Enum
from typing import Any

from jwsgj.diag_guard_dirfile import ARCH_DIR_MAX_FILES_DEFAULT, review_architecture
from jwsgj.diag_shared_ast_nodes import (
    calc_nesting,
    call_tail_name,
    collect_param_names,
    count_params,
    cyclomatic_complexity,
    definition_start_line,
    is_abstract_class_def,
    iter_class_scope_methods,
    iter_handler_scope,
    iter_module_scope_entities,
    own_scope_line_span,
    parse_ast_safely,
    pattern_capture_name,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    count_lines,
    decode_source_bytes,
    read_source_with_fingerprint,
    scan_line_quote_state,
)
from jwsgj.diag_types_normalize import as_sequence, int_or, strip_bom
from jwsgj.diag_types_vocab import (
    HARD_MAX_CLASS_LINES,
    HARD_MAX_FUNC_LINES,
    HARD_MAX_PARAMS,
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    SplitStrategy,
    normalize_filepath,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import py_stem

logger = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
__all__ = [
    "DEFAULT_THRESHOLDS",
    "ClassMetrics",
    "FileMetrics",
    "FunctionMetrics",
    "GenerationGuard",
    "GuardIssue",
    "Severity",
    "SplitGuardResult",
    "SplitPlanItem",
    "SplitReport",
    "build_post_split_checks",
    "build_rollback_plan",
    "build_split_steps",
    "count_patch_forms",
    "detect_new_patch_style_fixes",
    "estimate_split_effort",
    "generate_checklist",
    "new_patch_fix_issues",
    "normalize_code",
    "plan_split",
    "wide_silent_swallow_lines",
]
class Severity(Enum):
    INFO = "INFO"
    WARN = "WARN"
    ERROR = "ERROR"
    BLOCK = "BLOCK"
@dataclass
class GuardIssue:
    severity: Severity
    code: str
    message: str
    line: int = 0
    suggestion: str = ""
@dataclass
class SplitPlanItem:
    target_module: str
    symbols: list[str]
    strategy: SplitStrategy
    rationale: str
    estimated_lines: int = 0
@dataclass
class FunctionMetrics:
    name: str
    line_start: int
    line_end: int
    total_lines: int
    complexity: int = 0
    param_count: int = 0
    nested_depth: int = 0
    is_async: bool = False
    is_method: bool = False
    docstring: str | None = None
@dataclass
class ClassMetrics:
    name: str
    line_start: int
    line_end: int
    total_lines: int
    method_count: int = 0
    attribute_count: int = 0
    base_classes: list[str] = field(default_factory=list)
    is_abstract: bool = False
@dataclass
class FileMetrics:
    filepath: str
    total_lines: int
    import_count: int
    functions: list[FunctionMetrics] = field(default_factory=list)
    classes: list[ClassMetrics] = field(default_factory=list)
    top_level_code_lines: int = 0
    comment_lines: int = 0
    blank_lines: int = 0
DEFAULT_THRESHOLDS = {
    "max_file_lines": 3000,
    "max_func_lines": HARD_MAX_FUNC_LINES,
    "max_class_lines": HARD_MAX_CLASS_LINES,
    "max_complexity": 15,
    "max_params": HARD_MAX_PARAMS,
    "max_nested_depth": 4,
    "max_dir_files": ARCH_DIR_MAX_FILES_DEFAULT,
    "max_imports": 30,
    "max_methods_per_class": 20,
    "min_docstring_coverage": 0.6,
}
BIG_FUNC_SPLIT_LINES = 150
SEMANTIC_PREFIXES = [
    'get_', 'set_', 'create_', 'delete_', 'update_', 'find_', 'query_',
    'handle_', 'process_', 'validate_', 'parse_', 'build_', 'compute_',
    'load_', 'save_', 'fetch_', 'send_', 'calc_', 'format_', 'render_',
    'export_', 'import_', 'init_', 'setup_', 'clean_', 'migrate_',
    'resolve_', 'generate_', 'convert_', 'transform_', 'apply_',
    'register_', 'unregister_', 'serialize_', 'deserialize_',
    'encrypt_', 'decrypt_', 'hash_', 'verify_', 'authenticate_',
    'authorize_', 'log_', 'track_', 'notify_', 'schedule_',
]
SPLIT_TRIGGER_CODES = frozenset((
    "MASSIVE_FILE", "LONG_FILE", "MASSIVE_FUNCTION", "LONG_FUNCTION"))
def threshold_of(thresholds: dict, key: str):
    return thresholds.get(key, DEFAULT_THRESHOLDS[key])
def _positive_int_threshold(thresholds: dict, key: str) -> int:
    value = threshold_of(thresholds, key)
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        return DEFAULT_THRESHOLDS[key]
    return value
def _unit_float_threshold(thresholds: dict, key: str) -> float:
    value = threshold_of(thresholds, key)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return DEFAULT_THRESHOLDS[key]
    value = float(value)
    if not math.isfinite(value) or not 0 <= value <= 1:
        return DEFAULT_THRESHOLDS[key]
    return value
_STRANGLER_MIN_LINES = 2000
_LARGE_FILE_LINES = 1000
_STRANGLER_OBSERVATION_DAYS = 4.5
_MANY_FUNCTIONS = 20
_MANY_IMPORTS = 15
def _split_strategy_for(metrics: FileMetrics,
                        max_file_lines: int) -> SplitStrategy:
    if (metrics.total_lines > _STRANGLER_MIN_LINES
            or metrics.total_lines > max_file_lines * 3):
        return SplitStrategy.STRANGLER_FIG
    if len(metrics.functions) >= _MANY_FUNCTIONS:
        return SplitStrategy.BY_RESPONSIBILITY
    if metrics.import_count > _MANY_IMPORTS:
        return SplitStrategy.BY_DEPENDENCY
    return SplitStrategy.BY_COHESION
def _semantic_prefix_groups(
        metrics: FileMetrics) -> dict[str, list[FunctionMetrics]]:
    prefix_groups: dict[str, list[FunctionMetrics]] = {}
    for fn in metrics.functions:
        if fn.is_method:
            continue
        group_key = _semantic_group_key(fn.name)
        if group_key is not None:
            prefix_groups.setdefault(group_key, []).append(fn)
    return prefix_groups
def _prefix_group_items(
        prefix_groups: dict[str, list[FunctionMetrics]]) -> list[SplitPlanItem]:
    return [
        SplitPlanItem(
            target_module=f"{group_name}_operations",
            symbols=[f.name for f in funcs],
            strategy=SplitStrategy.BY_RESPONSIBILITY,
            rationale=f"按前缀 '{group_name}' 分组: {len(funcs)} 个函数",
            estimated_lines=sum(f.total_lines for f in funcs),
        )
        for group_name, funcs in prefix_groups.items()
        if len(funcs) >= 2
    ]
def _big_func_plan(metrics: FileMetrics,
                   planned_symbols: set[str]) -> list[SplitPlanItem]:
    big_func_items: dict[str, SplitPlanItem] = {}
    for fn in metrics.functions:
        if (fn.is_method or fn.total_lines <= BIG_FUNC_SPLIT_LINES
                or fn.name in planned_symbols):
            continue
        _merge_big_func_item(big_func_items, fn, _camel_to_snake(fn.name))
    return list(big_func_items.values())
def _merge_big_func_item(items: dict[str, SplitPlanItem], fn: FunctionMetrics,
                         snake_name: str) -> None:
    item = items.get(snake_name)
    if item is None:
        items[snake_name] = SplitPlanItem(
            target_module=snake_name,
            symbols=[fn.name],
            strategy=SplitStrategy.BY_COHESION,
            rationale=f"大函数 '{fn.name}': {fn.total_lines} 行",
            estimated_lines=fn.total_lines,
        )
        return
    item.symbols.append(fn.name)
    item.estimated_lines += fn.total_lines
    item.rationale = (f"撞名大函数归并 {', '.join(item.symbols)}: "
                      f"共 {item.estimated_lines} 行")
def _merge_plan_items_by_target(
        plan: list[SplitPlanItem]) -> list[SplitPlanItem]:
    merged: dict[str, SplitPlanItem] = {}
    for item in plan:
        existing = merged.get(item.target_module)
        if existing is None:
            merged[item.target_module] = item
            continue
        for symbol in item.symbols:
            if symbol not in existing.symbols:
                existing.symbols.append(symbol)
        existing.estimated_lines += item.estimated_lines
        existing.rationale = (f"{existing.rationale}；归并同目标计划项: "
                              f"{item.rationale}")
    return list(merged.values())
def generate_split_plan(metrics: FileMetrics) -> list[SplitPlanItem]:
    plan = _prefix_group_items(_semantic_prefix_groups(metrics))
    planned_symbols = {s for p in plan for s in p.symbols}
    plan.extend(_big_func_plan(metrics, planned_symbols))
    return _merge_plan_items_by_target(plan)
def decide_split(metrics: FileMetrics,
                  issues: list[GuardIssue],
                  thresholds: dict) -> tuple[bool, SplitStrategy, list[SplitPlanItem]]:
    if not _has_split_trigger(issues):
        return False, SplitStrategy.NONE, []
    strategy = _split_strategy_for(
        metrics, _positive_int_threshold(thresholds, "max_file_lines"))
    return True, strategy, generate_split_plan(metrics)
def _has_split_trigger(issues: list[GuardIssue]) -> bool:
    return any(i.code in SPLIT_TRIGGER_CODES for i in issues)
def _star_import_risk(node: ast.ImportFrom) -> list[str]:
    if not any(alias.name == "*" for alias in node.names):
        return []
    star_src = ("." * node.level) + (node.module or "")
    return [f"L{node.lineno}: 星导入 from {star_src} import * 拆分后可能丢失符号"]
def detect_star_import_risks(tree: ast.Module) -> list[str]:
    risks = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.ImportFrom):
            risks.extend(_star_import_risk(node))
    return risks
def _import_bound_names(n: ast.Import | ast.ImportFrom) -> set[str]:
    if isinstance(n, ast.Import):
        return {_ia.asname or _ia.name.split(".")[0] for _ia in n.names}
    return {_ia.asname or _ia.name for _ia in n.names}
def _type_param_names(n: ast.AST) -> set[str]:
    return {
        param.name
        for param in (getattr(n, "type_params", ()) or ())
        if isinstance(getattr(param, "name", None), str)
    }
def _def_param_names(n: ast.AST) -> set[str]:
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        names = collect_param_names(n)
    elif isinstance(n, ast.ClassDef):
        names = set()
    else:
        return set()
    return names | _type_param_names(n)
_TYPE_ALIAS_NODES = ((ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ())
_COMPREHENSION_NODES = tuple(
    t for t in (getattr(ast, "ListComp", None), getattr(ast, "SetComp", None),
                getattr(ast, "DictComp", None), getattr(ast, "GeneratorExp", None))
    if t is not None
)
def _target_leaf_names(target: ast.AST):
    if isinstance(target, ast.Name):
        yield target
    elif isinstance(target, (ast.Tuple, ast.List)):
        for item in target.elts:
            yield from _target_leaf_names(item)
    elif isinstance(target, ast.Starred):
        yield from _target_leaf_names(target.value)
def _comprehension_target_names(target: ast.AST) -> set[str]:
    return {leaf.id for leaf in _target_leaf_names(target)}
def _comprehension_scope_children(n: ast.AST) -> list[tuple[ast.AST, bool]]:
    nodes: list[tuple[ast.AST, bool]] = []
    for gen in n.generators:
        nodes.append((gen.iter, False))
        nodes.extend((leaf, True) for leaf in _target_leaf_names(gen.target))
        nodes.extend((cond, False) for cond in gen.ifs)
    if isinstance(n, ast.DictComp):
        nodes.append((n.key, False))
        nodes.append((n.value, False))
    else:
        nodes.append((n.elt, False))
    return nodes
def _semantic_group_key(name: str) -> str | None:
    for prefix in SEMANTIC_PREFIXES:
        if name.startswith(prefix):
            return prefix.rstrip('_')
    return None
def _node_binding_names(n: ast.AST, root: ast.AST) -> tuple[set[str], set[str]]:
    if isinstance(n, (ast.Global, ast.Nonlocal)):
        return set(), set(n.names)
    if (n is not root
            and isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef))):
        return {n.name}, set()
    if isinstance(n, ast.Lambda):
        return set(), set()
    if isinstance(n, (ast.Import, ast.ImportFrom)):
        return _import_bound_names(n), set()
    return _scope_store_binding(n), set()
def _scope_store_binding(n: ast.AST) -> set[str]:
    bind = pattern_capture_name(n)
    if bind:
        return {bind}
    if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
        return {n.id}
    return set()
def _scope_external_children(n: ast.AST) -> list[ast.AST]:
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
        children = [*n.decorator_list, n.args]
        if n.returns is not None:
            children.append(n.returns)
        return children + list(getattr(n, "type_params", ()) or ())
    if isinstance(n, ast.ClassDef):
        return [*n.decorator_list, *n.bases,
                *(kw.value for kw in n.keywords),
                *list(getattr(n, "type_params", ()) or ())]
    if isinstance(n, ast.Lambda):
        return [n.args]
    return list(ast.iter_child_nodes(n))
def _definition_scope_children(
        n: ast.AST) -> tuple[list[ast.AST], list[ast.AST]]:
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        args = n.args
        outer = [*n.decorator_list, *args.defaults]
        outer.extend(value for value in args.kw_defaults if value is not None)
        if isinstance(n, ast.Lambda):
            return outer, []
        params = [*args.posonlyargs, *args.args, *args.kwonlyargs]
        if args.vararg is not None:
            params.append(args.vararg)
        if args.kwarg is not None:
            params.append(args.kwarg)
        typed = [param.annotation for param in params
                 if param.annotation is not None]
        if n.returns is not None:
            typed.append(n.returns)
        typed.extend(getattr(n, "type_params", ()) or ())
        return outer, typed
    if isinstance(n, ast.ClassDef):
        typed = [*n.bases, *(kw.value for kw in n.keywords)]
        typed.extend(getattr(n, "type_params", ()) or ())
        return list(n.decorator_list), typed
    return list(ast.iter_child_nodes(n)), []
def _collect_definition_refs(
        n: ast.AST, local_names: set[str], refs: set[str],
        root_name: str | None, closure_names: set[str] | None) -> None:
    type_names = _type_param_names(n)
    if not type_names:
        for part in _scope_external_children(n):
            _collect_scope_refs(
                part, local_names, refs, root_name, closure_names)
        return
    outer, typed = _definition_scope_children(n)
    for part in outer:
        _collect_scope_refs(part, local_names, refs, root_name, closure_names)
    typed_names = local_names | type_names
    for part in typed:
        _collect_scope_refs(part, typed_names, refs, root_name, closure_names)
def _unit_scope_names(node) -> tuple[set[str], set[str]]:
    scoped: set[str] = set()
    global_names: set[str] = set()
    stored: set[str] = set(_def_param_names(node))
    stack: list[tuple[ast.AST, bool]] = [
        (child, False) for child in ast.iter_child_nodes(node)]
    while stack:
        n, skip_binding = stack.pop()
        if isinstance(n, _COMPREHENSION_NODES):
            stack.extend(_comprehension_scope_children(n))
            continue
        bound, outer = _node_binding_names(n, node)
        if not skip_binding:
            stored |= bound
        scoped |= outer
        if isinstance(n, ast.Global):
            global_names.update(n.names)
        stack.extend((child, False) for child in _scope_external_children(n))
    return stored - scoped, global_names
def _top_symbol_refs(tree: ast.Module) -> dict[str, set[str]]:
    top_defs: dict[str, set[str]] = {}
    for node in iter_module_scope_entities(tree):
        top_defs.setdefault(node.name, set()).update(
            _load_symbol_refs(node, _unit_scope_names(node)[0]))
    return top_defs
def _load_symbol_refs(node: ast.AST, local_names: set[str]) -> set[str]:
    refs: set[str] = set()
    root_name = getattr(node, "name", None)
    outer_names: set[str] = set()
    _collect_definition_refs(
        node, outer_names, refs, root_name, outer_names)
    closure_names = (_type_param_names(node)
                     if isinstance(node, ast.ClassDef) else set(local_names))
    body = [node.body] if isinstance(node, ast.Lambda) else list(node.body)
    for child in body:
        _collect_scope_refs(
            child, set(local_names), refs, root_name, closure_names)
    return refs
def _collect_comprehension_refs(
        n: ast.AST, local_names: set[str], refs: set[str],
        root_name: str | None, closure_names: set[str] | None) -> None:
    outer = local_names if closure_names is None else closure_names
    comp_locals = set(outer)
    for index, gen in enumerate(n.generators):
        iter_closure = closure_names if index == 0 else comp_locals
        _collect_scope_refs(
            gen.iter, local_names if index == 0 else comp_locals,
            refs, root_name, iter_closure)
        comp_locals |= _comprehension_target_names(gen.target)
        _collect_scope_refs(
            gen.target, comp_locals, refs, root_name, comp_locals)
        for cond in gen.ifs:
            _collect_scope_refs(
                cond, comp_locals, refs, root_name, comp_locals)
    leaves = ([n.key, n.value] if isinstance(n, ast.DictComp) else [n.elt])
    for leaf in leaves:
        _collect_scope_refs(
            leaf, comp_locals, refs, root_name, comp_locals)
def _collect_scope_refs(
        n: ast.AST, local_names: set[str], refs: set[str],
        root_name: str | None, closure_names: set[str] | None = None) -> None:
    if isinstance(n, _COMPREHENSION_NODES):
        _collect_comprehension_refs(
            n, local_names, refs, root_name, closure_names)
        return
    if isinstance(n, ast.Name):
        if (isinstance(n.ctx, (ast.Load, ast.Store, ast.Del))
                and n.id != root_name and n.id not in local_names):
            refs.add(n.id)
        return
    if isinstance(n, _TYPE_ALIAS_NODES):
        _collect_scope_refs(n.name, local_names, refs, root_name, closure_names)
        typed_names = local_names | _type_param_names(n)
        for part in [*(getattr(n, "type_params", ()) or ()), n.value]:
            _collect_scope_refs(
                part, typed_names, refs, root_name, closure_names)
        return
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                      ast.ClassDef, ast.Lambda)):
        _collect_definition_refs(
            n, local_names, refs, root_name, closure_names)
        scoped_locals, global_names = _unit_scope_names(n)
        outer = local_names if closure_names is None else closure_names
        inner = (outer - global_names) | scoped_locals
        body = [n.body] if isinstance(n, ast.Lambda) else list(n.body)
        if isinstance(n, ast.ClassDef):
            inner = (outer - global_names) | scoped_locals
            inner_closure = outer | _type_param_names(n)
        else:
            inner_closure = inner
        for child in body:
            _collect_scope_refs(
                child, inner, refs, root_name, inner_closure)
        return
    for child in ast.iter_child_nodes(n):
        _collect_scope_refs(
            child, local_names, refs, root_name, closure_names)
def _mutual_reference_risks(top_defs: dict[str, set[str]],
                            plan: list[SplitPlanItem]) -> list[str]:
    risks = []
    for i in range(len(plan)):
        for j in range(i + 1, len(plan)):
            symbols_a, symbols_b = set(plan[i].symbols), set(plan[j].symbols)
            if (_plan_group_refs(top_defs, symbols_a, symbols_b)
                    and _plan_group_refs(top_defs, symbols_b, symbols_a)):
                risks.append(
                    f"警告: 候选模块 {plan[i].target_module} 与 {plan[j].target_module} "
                    f"符号互向引用，拆分后需参数注入/事件解耦打破循环")
    return risks
def _plan_group_refs(top_defs: dict[str, set[str]], from_symbols: set[str],
                     to_symbols: set[str]) -> bool:
    return any(top_defs.get(s, set()) & to_symbols for s in from_symbols)
def detect_candidate_circular_risks(tree: ast.Module,
                                     plan: list[SplitPlanItem]) -> list[str]:
    if len(plan) < 2:
        return []
    return _mutual_reference_risks(_top_symbol_refs(tree), plan)
def score_split_feasibility(file_lines: int, plan: list[SplitPlanItem],
                             import_risks: list[str],
                             circular_risks: list[str]) -> int:
    score = 100
    if file_lines > _STRANGLER_MIN_LINES:
        score -= 20
    elif file_lines > _LARGE_FILE_LINES:
        score -= 10
    if not plan:
        score -= 40
    score -= len(import_risks) * 10
    score -= len(circular_risks) * 15
    return max(0, min(100, score))
def _camel_to_snake(name: str) -> str:
    s1 = re.sub(r'(.)([A-Z][a-z]+)', r'\1_\2', name)
    s2 = re.sub(r'([a-z0-9])([A-Z])', r'\1_\2', s1).lower()
    return re.sub(r'_+', '_', s2).strip('_')
def normalize_code(code: object) -> str:
    if isinstance(code, str):
        return strip_bom(code)
    if isinstance(code, (bytes, bytearray)):
        return strip_bom(decode_source_bytes(bytes(code)))
    return str(code) if code else ""
def _parse_module_with_semantics(
        code: str, filepath: str,
) -> tuple[ast.Module | None, Exception | None]:
    tree, parse_err = parse_ast_safely(code)
    if tree is None:
        return None, parse_err
    try:
        compile(tree, filepath or "<string>", "exec")
    except PARSE_DEGRADE_EXC as exc:
        return None, exc
    return tree, None
def prepare_parse(code: str, filepath: str
                   ) -> tuple[str, str, ast.Module | None, Exception | None]:
    filepath = normalize_filepath(filepath)
    code = normalize_code(code)
    if not code.strip():
        return filepath, code, None, None
    tree, parse_err = _parse_module_with_semantics(code, filepath)
    if tree is None:
        logger.warning("%s [%s]: %s", MSG_SYNTAX_ERROR_SKIP,
                       filepath or "<未命名>",
                       getattr(parse_err, 'msg', str(parse_err)))
    return filepath, code, tree, parse_err
def _func_metrics_of(node: ast.FunctionDef | ast.AsyncFunctionDef,
                     *, is_method: bool) -> FunctionMetrics:
    start = definition_start_line(node)
    end = node.end_lineno or node.lineno
    return FunctionMetrics(
        name=node.name,
        line_start=start,
        line_end=end,
        total_lines=own_scope_line_span(node),
        complexity=cyclomatic_complexity(node),
        param_count=count_params(node, is_method=is_method),
        nested_depth=calc_nesting(node),
        is_async=isinstance(node, ast.AsyncFunctionDef),
        is_method=is_method,
        docstring=ast.get_docstring(node),
    )
def _count_line_kinds(lines: list[str]) -> tuple[int, int]:
    blank = comment = 0
    for line in lines:
        stripped = line.strip()
        if not stripped:
            blank += 1
        elif stripped.startswith('#'):
            comment += 1
    return blank, comment
def _class_method_metrics(node: ast.ClassDef) -> list[FunctionMetrics]:
    return [
        _func_metrics_of(body_node, is_method=True)
        for body_node in iter_class_scope_methods(node)
    ]
def _class_attr_count(node: ast.ClassDef) -> int:
    count = 0
    for body_node in node.body:
        if isinstance(body_node, ast.Assign):
            targets = body_node.targets
        elif isinstance(body_node, ast.AnnAssign):
            targets = [body_node.target]
        else:
            continue
        for target in targets:
            bound_names = list(_target_leaf_names(target))
            count += len(bound_names) or 1
    return count
def _class_metrics_of(
        node: ast.ClassDef) -> tuple[ClassMetrics, list[FunctionMetrics]]:
    start = definition_start_line(node)
    end = node.end_lineno or node.lineno
    methods = _class_method_metrics(node)
    return ClassMetrics(
        name=node.name,
        line_start=start,
        line_end=end,
        total_lines=end - start + 1,
        method_count=len(methods),
        attribute_count=_class_attr_count(node),
        base_classes=[
            _name_to_str(b) for b in node.bases
        ],
        is_abstract=is_abstract_class_def(node),
    ), methods
def _collect_top_level_metrics(
        tree: ast.Module) -> tuple[list[FunctionMetrics],
                                   list[ClassMetrics], int]:
    functions: list[FunctionMetrics] = []
    classes: list[ClassMetrics] = []
    entity_lines = 0
    for node in iter_module_scope_entities(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fm = _func_metrics_of(node, is_method=False)
            entity_lines += max(fm.line_end - fm.line_start + 1, 1)
            functions.append(fm)
        elif isinstance(node, ast.ClassDef):
            cm, methods = _class_metrics_of(node)
            entity_lines += cm.total_lines
            classes.append(cm)
            functions.extend(methods)
    return functions, classes, entity_lines
def compute_file_metrics(code: str, filepath: str,
                          tree: ast.Module) -> FileMetrics:
    lines = ast_split_lines(code)
    if lines and lines[-1] == "":
        lines = lines[:-1]
    total_lines = count_lines(code)
    import_count = sum(
        1 for node in walk_nodes(tree)
        if isinstance(node, (ast.Import, ast.ImportFrom))
    )
    functions, classes, entity_lines = _collect_top_level_metrics(tree)
    blank_lines, comment_lines = _count_line_kinds(lines)
    return FileMetrics(
        filepath=filepath,
        total_lines=total_lines,
        import_count=import_count,
        functions=functions,
        classes=classes,
        top_level_code_lines=total_lines - entity_lines,
        comment_lines=comment_lines,
        blank_lines=blank_lines,
    )
def _name_to_str(node) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return f"{_name_to_str(node.value)}.{node.attr}"
    try:
        return ast.unparse(node)
    except (ValueError, RecursionError) as _e:
        log_swallowed(__name__, _e, context='_name_to_str:ast.unparse')
        return type(node).__name__
def make_guard_issue(code: str, severity: Severity, message: str, *,
           line: int = 0, suggestion: str = "") -> GuardIssue:
    return GuardIssue(severity=severity, code=code, message=message,
                      line=line, suggestion=suggestion)
_FILE_SIZE_LEVELS: tuple[tuple[float, str, Severity, str, str], ...] = (
    (2.0, "MASSIVE_FILE", Severity.BLOCK, "巨文件",
     ("按 GOV-01 治理：简化逻辑/消除重复/收敛依赖/"
      "迁移无关块（禁止直接拆分文件或模块）")),
    (1.0, "LONG_FILE", Severity.ERROR, "长文件",
     ("治理候选：优先简化逻辑/消除重复/迁移无关块到"
      "既有职责模块（GOV-01 禁止直接拆分）")),
    (0.8, "APPROACHING_FILE_LIMIT", Severity.WARN, "接近文件上限",
     "接近上限：优先简化逻辑或迁移无关块，控制在阈值内"),
)
def _check_file_size(metrics: FileMetrics,
                     thresholds: dict) -> list[GuardIssue]:
    mfl = _positive_int_threshold(thresholds, "max_file_lines")
    for factor, code, severity, label, suggestion in _FILE_SIZE_LEVELS:
        if metrics.total_lines > mfl * factor:
            return [make_guard_issue(
                code, severity,
                message=f"{label}: {metrics.total_lines} 行 (阈值 {mfl})",
                suggestion=suggestion,
            )]
    return []
def _function_size_issues(fn: FunctionMetrics,
                         max_lines: int) -> list[GuardIssue]:
    if fn.total_lines > max_lines * 2:
        return [make_guard_issue(
            "MASSIVE_FUNCTION", Severity.ERROR,
            message=f"巨函数 '{fn.name}': {fn.total_lines} 行 (阈值 {max_lines})",
            line=fn.line_start,
            suggestion=(f"按执行阶段提取为 {fn.total_lines // max_lines + 1} "
                        "个同模块私有子函数"),
        )]
    if fn.total_lines > max_lines:
        return [make_guard_issue(
            "LONG_FUNCTION", Severity.WARN,
            message=f"大函数 '{fn.name}': {fn.total_lines} 行 (阈值 {max_lines})",
            line=fn.line_start,
            suggestion="提取子函数或使用策略模式",
        )]
    return []
def _function_param_issues(fn: FunctionMetrics,
                           max_params: int) -> list[GuardIssue]:
    if fn.param_count > max_params:
        return [make_guard_issue(
            "TOO_MANY_PARAMS", Severity.WARN,
            message=f"函数 '{fn.name}' 参数过多: {fn.param_count} (阈值 {max_params})",
            line=fn.line_start,
            suggestion="封装参数为数据对象或使用 Builder 模式",
        )]
    return []
def _function_nested_issues(fn: FunctionMetrics,
                            max_nested: int) -> list[GuardIssue]:
    if fn.nested_depth > max_nested:
        return [make_guard_issue(
            "DEEP_NESTED", Severity.WARN,
            message=f"函数 '{fn.name}' 嵌套过深: {fn.nested_depth} (阈值 {max_nested})",
            line=fn.line_start,
            suggestion="提取嵌套块为独立函数或使用早返回 (early return)",
        )]
    return []
def _check_functions(metrics: FileMetrics,
                     thresholds: dict) -> list[GuardIssue]:
    issues = []
    mfl = _positive_int_threshold(thresholds, "max_func_lines")
    max_params = _positive_int_threshold(thresholds, "max_params")
    max_nested = _positive_int_threshold(thresholds, "max_nested_depth")
    for fn in metrics.functions:
        issues.extend(_function_size_issues(fn, mfl))
        issues.extend(_function_param_issues(fn, max_params))
        issues.extend(_function_nested_issues(fn, max_nested))
    return issues
def _check_classes(metrics: FileMetrics,
                   thresholds: dict) -> list[GuardIssue]:
    issues = []
    max_class_lines = _positive_int_threshold(thresholds, "max_class_lines")
    max_methods = _positive_int_threshold(thresholds, "max_methods_per_class")
    for cls in metrics.classes:
        if cls.total_lines > max_class_lines:
            issues.append(make_guard_issue(
                "LARGE_CLASS", Severity.WARN,
                message=f"大类 '{cls.name}': {cls.total_lines} 行 (阈值 {max_class_lines})",
                line=cls.line_start,
                suggestion="提取同模块私有实现或组合委托",
            ))
        if cls.method_count > max_methods:
            issues.append(make_guard_issue(
                "TOO_MANY_METHODS", Severity.WARN,
                message=f"类 '{cls.name}' 方法过多: {cls.method_count} (阈值 {max_methods})",
                line=cls.line_start,
                suggestion="提取同模块私有实现或收敛同类方法",
            ))
    return issues
def _check_complexity(metrics: FileMetrics,
                      thresholds: dict) -> list[GuardIssue]:
    issues = []
    max_cc = _positive_int_threshold(thresholds, "max_complexity")
    for fn in metrics.functions:
        if fn.complexity > max_cc:
            issues.append(make_guard_issue(
                "HIGH_COMPLEXITY", Severity.WARN,
                message=f"函数 '{fn.name}' 圈复杂度过高: {fn.complexity} (阈值 {max_cc})",
                line=fn.line_start,
                suggestion="将条件分支提取为同模块私有子函数",
            ))
    return issues
def _split_trigger_issues(metrics: FileMetrics,
                          thresholds: dict) -> list[GuardIssue]:
    issues = _check_file_size(metrics, thresholds)
    issues.extend(_check_functions(metrics, thresholds))
    return issues
def split_gate_issues(metrics: FileMetrics,
                      thresholds: dict) -> list[GuardIssue]:
    issues = _split_trigger_issues(metrics, thresholds)
    issues.extend(_check_classes(metrics, thresholds))
    issues.extend(_check_complexity(metrics, thresholds))
    return issues
def _is_truncating_int_cast(default, value) -> bool:
    return (isinstance(default, int) and isinstance(value, float)
            and math.isfinite(value) and value != int(value))
def _coerce_single_threshold(default, value):
    if _same_type_passthrough(default, value):
        return value
    if isinstance(value, bool):
        return default
    try:
        coerced = type(default)(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(
            __name__, _e,
            context=f"coerce_thresholds:{type(_e).__name__}")
        return default
    return default if _is_truncating_int_cast(default, value) else coerced
@dataclass
class SplitReport:
    file_path: str
    score: int
    strategy: SplitStrategy
    can_split: bool
    candidates: list[dict] = field(default_factory=list)
    steps: list[dict] = field(default_factory=list)
    import_risks: list[str] = field(default_factory=list)
    circular_risks: list[str] = field(default_factory=list)
    post_split_checks: list[str] = field(default_factory=list)
    estimated_effort: str = ""
    rollback_plan: str = ""
    migration_checklist: str = ""
    def to_dict(self) -> dict:
        out = {k: v for k, v in self.__dict__.items() if not k.startswith("_")}
        out["strategy"] = (self.strategy.value
                           if isinstance(self.strategy, SplitStrategy)
                           else self.strategy)
        return out
def _plan_candidates(plan) -> list[dict]:
    return [
        {
            "suggested_module": p.target_module,
            "strategy": p.strategy.value,
            "symbols": list(p.symbols),
            "total_lines": p.estimated_lines,
            "rationale": p.rationale,
        }
        for p in plan
    ]
def _resolve_thresholds(thresholds: dict | None,
                        defaults: dict | None = None) -> dict:
    base = DEFAULT_THRESHOLDS if defaults is None else defaults
    return {**base, **coerce_thresholds(thresholds, defaults=base)}
def plan_split(code: str, filepath: str = _DEFAULT_FILEPATH,
               thresholds: dict | None = None) -> SplitReport:
    resolved = _resolve_thresholds(thresholds)
    filepath, code, tree, _parse_err = prepare_parse(code, filepath)
    if tree is None:
        return SplitReport(file_path=filepath, score=0,
                           strategy=SplitStrategy.NONE, can_split=False)
    metrics = compute_file_metrics(code, filepath, tree)
    issues = _split_trigger_issues(metrics, resolved)
    needs_split, strategy, plan = decide_split(metrics, issues, resolved)
    if not needs_split:
        plan = generate_split_plan(metrics)
        strategy = _split_strategy_for(metrics, resolved["max_file_lines"])
    candidates = _plan_candidates(plan)
    import_risks = detect_star_import_risks(tree)
    circular_risks = detect_candidate_circular_risks(tree, plan)
    score = score_split_feasibility(
        metrics.total_lines, plan, import_risks, circular_risks)
    steps = build_split_steps(plan, strategy, filepath)
    migration_checklist = ""
    if strategy == SplitStrategy.STRANGLER_FIG and steps:
        try:
            migration_checklist = generate_checklist(steps)
        except (AttributeError, KeyError, TypeError, ValueError,
                RuntimeError) as _e:
            log_swallowed(__name__, _e,
                          context="plan_split:generate_checklist")
    post_checks = build_post_split_checks(plan)
    effort = estimate_split_effort(
        metrics.total_lines, len(plan), strategy)
    rollback = build_rollback_plan(filepath)
    return SplitReport(
        file_path=filepath, score=score, strategy=strategy,
        can_split=bool(candidates),
        candidates=candidates, steps=steps,
        import_risks=import_risks, circular_risks=circular_risks,
        post_split_checks=post_checks,
        estimated_effort=effort, rollback_plan=rollback,
        migration_checklist=migration_checklist,
    )
def coerce_thresholds(thresholds: dict | None, defaults: dict) -> dict:
    if not isinstance(thresholds, dict):
        if thresholds:
            logger.warning(
                "[coerce_thresholds] thresholds/user_prefs 非 dict（%s），"
                "按空覆盖降级", type(thresholds).__name__)
        return {}
    out: dict = {}
    for key, value in thresholds.items():
        default = defaults.get(key, DEFAULT_THRESHOLDS.get(key))
        coerced = _coerce_single_threshold(default, value)
        if _invalid_threshold_domain(default, coerced):
            coerced = default
        out[key] = coerced
    return out
def _invalid_threshold_domain(default, v) -> bool:
    if default is None:
        return False
    if isinstance(default, int):
        return not isinstance(v, int) or v <= 0
    if isinstance(default, float):
        return not isinstance(v, float) or not 0 <= v <= 1
    return False
def _same_type_passthrough(default, value) -> bool:
    return (default is None
            or (isinstance(value, type(default))
                and not isinstance(value, bool)))
@dataclass
class SplitGuardResult:
    ok: bool
    filepath: str
    file_metrics: FileMetrics | None = None
    issues: list[GuardIssue] = field(default_factory=list)
    split_plan: list[SplitPlanItem] = field(default_factory=list)
    needs_split: bool = False
    recommended_strategy: SplitStrategy = SplitStrategy.NONE
    architecture_review: dict = field(default_factory=dict)
class GenerationGuard:
    def __init__(self, thresholds: dict | None = None):
        self.thresholds = _resolve_thresholds(thresholds)
    def before_write(self, code: str, filepath: str = _DEFAULT_FILEPATH,
                     user_prefs: dict | None = None) -> SplitGuardResult:
        thresholds = _resolve_thresholds(
            user_prefs, defaults=self.thresholds)
        filepath, code, tree, parse_err = prepare_parse(code, filepath)
        if tree is None:
            if parse_err is None:
                return SplitGuardResult(ok=True, filepath=filepath)
            return _syntax_block_result(filepath, parse_err)
        metrics = compute_file_metrics(code, filepath, tree)
        issues = _collect_gate_issues(code, filepath, metrics, thresholds)
        needs_split, strategy, split_plan = decide_split(
            metrics, issues, thresholds
        )
        arch_review = review_architecture(code, metrics, filepath)
        return SplitGuardResult(
            ok=not _has_blocking_issue(issues),
            filepath=filepath,
            file_metrics=metrics,
            issues=issues,
            split_plan=split_plan,
            needs_split=needs_split,
            recommended_strategy=strategy,
            architecture_review=arch_review,
        )
    def plan_split(self, code: str, filepath: str = _DEFAULT_FILEPATH) -> SplitReport:
        return plan_split(code, filepath, self.thresholds)
def _has_blocking_issue(issues: list[GuardIssue]) -> bool:
    return any(i.severity in (Severity.BLOCK, Severity.ERROR)
               for i in issues)
def _syntax_block_result(filepath: str,
                         parse_err: Exception) -> SplitGuardResult:
    return SplitGuardResult(
        ok=False, filepath=filepath,
        issues=[make_guard_issue(
            "SYNTAX_ERROR", Severity.BLOCK,
            f"语法错误: {getattr(parse_err, 'msg', str(parse_err))}",
            line=getattr(parse_err, 'lineno', 0) or 0,
        )],
    )
def _check_imports(metrics: FileMetrics,
                   thresholds: dict) -> list[GuardIssue]:
    issues = []
    max_imports = _positive_int_threshold(thresholds, "max_imports")
    if metrics.import_count > max_imports:
        issues.append(make_guard_issue(
            "TOO_MANY_IMPORTS", Severity.WARN,
            message=f"导入过多: {metrics.import_count} (阈值 {max_imports})",
            suggestion="收敛依赖：移除未用导入/合并同族导入/迁移无关依赖"
                       "（GOV-01 禁止以拆分替代治理）",
        ))
    return issues
def _check_docstring_coverage(metrics: FileMetrics,
                              thresholds: dict) -> list[GuardIssue]:
    issues = []
    min_coverage = _unit_float_threshold(thresholds, "min_docstring_coverage")
    public_funcs = [f for f in metrics.functions if not f.name.startswith('_')]
    total_funcs = len(public_funcs)
    if not total_funcs:
        return issues
    documented = sum(1 for f in public_funcs if f.docstring)
    coverage = documented / total_funcs
    if coverage < min_coverage:
        issues.append(make_guard_issue(
            "LOW_DOCSTRING_COVERAGE", Severity.INFO,
            message=f"文档覆盖不足: {coverage:.0%} (阈值 {min_coverage:.0%})",
            suggestion=f"为 {total_funcs - documented} 个公开函数添加 docstring",
        ))
    return issues
def new_patch_fix_issues(code: str,
                         filepath: str) -> list[GuardIssue]:
    _orig = ""
    if filepath:
        _orig, _ = read_source_with_fingerprint(filepath)
    if _orig is None:
        if os.path.exists(filepath):
            return [make_guard_issue(
                "NO_PATCH_FIX", Severity.ERROR,
                message=("原始源码读取或解码失败，补丁形态差集未完成，"
                         "禁止按未新增降级放行"),
                suggestion=("恢复可读取、可解码的原始源码基线后重新验证；"
                            "无法恢复时转人工审核，不得跳过差分校验"),
            )]
        _orig = ""
    _hits = detect_new_patch_style_fixes(_orig, code)
    if not _hits:
        return []
    return [make_guard_issue(
        "NO_PATCH_FIX", Severity.ERROR,
        message=("禁止补丁方式修复：" + "；".join(_hits)
                 + "——吞异常遮蔽/裸捕获属只治症状不除根因"),
        suggestion=("定位根因并以根因消除方式修复（SSOT 归口/契约"
                    "对齐/结构校正）；确属必要的样例/测试场景在该行"
                    "附 # nosec 显式豁免声明"),
    )]
def _collect_gate_issues(code: str, filepath: str, metrics: FileMetrics,
                         thresholds: dict) -> list[GuardIssue]:
    issues = split_gate_issues(metrics, thresholds)
    issues.extend(_check_imports(metrics, thresholds))
    issues.extend(_check_docstring_coverage(metrics, thresholds))
    issues.extend(new_patch_fix_issues(code, filepath))
    return issues
_EXPLICIT_EXEMPTION_RE = re.compile(
    r"#\s*(?:nosec|noqa)(?=$|[\s:])", re.IGNORECASE)
def line_has_explicit_exemption(line_text: str) -> bool:
    cut, _state = scan_line_quote_state(line_text)
    if cut < 0:
        return False
    _comment = line_text[cut:]
    return _EXPLICIT_EXEMPTION_RE.search(_comment) is not None
_WIDE_EXC_NAMES = frozenset({"Exception", "BaseException"})
_WIDE_EXC_TYPES = _WIDE_EXC_NAMES | frozenset(
    f"builtins.{n}" for n in _WIDE_EXC_NAMES)
def _is_wide_capture_type(node: ast.expr | None) -> bool:
    if node is None:
        return False
    if isinstance(node, ast.Tuple):
        return any(_is_wide_capture_type(elt) for elt in node.elts)
    name = node.id if isinstance(node, ast.Name) else ast.unparse(node)
    return name in _WIDE_EXC_TYPES
_LOG_TAIL_NAMES = frozenset({
    "debug", "info", "warning", "warn", "error", "exception",
    "critical", "log", "print",
})
def _is_observable_disposal(node: ast.AST, binding: str) -> bool:
    if isinstance(node, ast.Raise):
        return True
    if isinstance(node, ast.Call):
        return call_tail_name(node) in _LOG_TAIL_NAMES
    return (bool(binding) and isinstance(node, ast.Name)
            and node.id == binding and isinstance(node.ctx, ast.Load))
def _has_observable_disposal(handler: ast.ExceptHandler) -> bool:
    binding = handler.name or ""
    return any(_is_observable_disposal(sub, binding)
               for sub in iter_handler_scope(handler))
def _is_wide_silent_swallow(handler: ast.ExceptHandler) -> bool:
    if not _is_wide_capture_type(handler.type):
        return False
    return not _has_observable_disposal(handler)
def _is_bare_except(handler: ast.ExceptHandler) -> bool:
    return handler.type is None
def _is_ellipsis_expr_stmt(stmt: ast.AST) -> bool:
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and stmt.value.value is Ellipsis)
def _is_swallow_pass(handler: ast.ExceptHandler) -> bool:
    return all(
        isinstance(stmt, (ast.Pass, ast.Continue, ast.Break))
        or _is_ellipsis_expr_stmt(stmt)
        for stmt in handler.body
    )
_PATCH_FORMS: tuple[tuple[str, Callable[[ast.ExceptHandler], bool],
                          str, str], ...] = (
    ("bare_except", _is_bare_except, "新增裸 except",
     "（应明确捕获具体异常类型）"),
    ("swallow_pass", _is_swallow_pass,
     "新增吞异常遮蔽 except...:pass/continue/break/...", ""),
    ("wide_silent_swallow", _is_wide_silent_swallow,
     "新增宽捕获静默吞异常",
     ("（except Exception/BaseException 无留痕/无再抛/异常对象未消费"
      "——须消除成因而非掩盖症状）")),
)
_PATCH_FORM_KEYS: tuple[str, ...] = tuple(
    key for key, *_rest in _PATCH_FORMS)
def _classify_patch_form(handler: ast.ExceptHandler) -> str | None:
    for key, matched, _label, _suffix in _PATCH_FORMS:
        if matched(handler):
            return key
    return None
def _is_exempt_line(node: ast.ExceptHandler, lines: list[str]) -> bool:
    lineno = getattr(node, "lineno", 0)
    line_text = lines[lineno - 1] if 1 <= lineno <= len(lines) else ""
    return line_has_explicit_exemption(line_text)
def _iter_checked_handlers(tree: ast.AST,
                           lines: list[str]) -> Iterator[ast.ExceptHandler]:
    handlers = [
        node for node in walk_nodes(tree)
        if isinstance(node, ast.ExceptHandler) and not _is_exempt_line(
            node, lines)]
    handlers.sort(key=lambda handler: (getattr(handler, "lineno", 0),
                                       getattr(handler, "col_offset", 0)))
    yield from handlers
def wide_silent_swallow_lines(code: str, tree: ast.AST | None) -> list[int]:
    if not isinstance(tree, ast.AST):
        return []
    lines = ast_split_lines(code) if isinstance(code, str) and code else []
    out: list[int] = []
    for node in _iter_checked_handlers(tree, lines):
        if not (_is_bare_except(node) or _is_wide_silent_swallow(node)):
            continue
        out.append(getattr(node, "lineno", 0))
    return out
def _patch_form_signature(handler: ast.ExceptHandler) -> str:
    if handler.type is None:
        return ""
    return ast.dump(handler.type, include_attributes=False)
def _handler_scope_names(tree: ast.AST) -> dict[ast.AST, str]:
    scopes: dict[ast.AST, str] = {}
    stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while stack:
        node, scope = stack.pop()
        if isinstance(node, ast.ExceptHandler):
            scopes[node] = scope
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            name = getattr(node, "name", "<lambda>")
            scope = f"{scope}.{name}" if scope else name
        stack.extend((child, scope) for child in ast.iter_child_nodes(node))
    return scopes
def _handler_form_sites(
        src: str) -> list[tuple[int, str | None, str, str]] | None:
    if not isinstance(src, str):
        return None
    try:
        src = normalize_code(src)
        tree = ast.parse(src)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(
            __name__, _e, context=f"patch_form_sites:{type(_e).__name__}")
        return None
    lines = ast_split_lines(src)
    scopes = _handler_scope_names(tree)
    return [
        (getattr(node, "lineno", 0), _classify_patch_form(node),
         _patch_form_signature(node), scopes.get(node, ""))
        for node in _iter_checked_handlers(tree, lines)
    ]
def _patch_form_sites(src: str) -> dict[str, dict[str, list[int]]] | None:
    handlers = _handler_form_sites(src)
    if handlers is None:
        return None
    sites: dict[str, dict[str, list[int]]] = {
        key: {} for key in _PATCH_FORM_KEYS}
    for lineno, form_key, identity, _scope in handlers:
        if form_key is not None:
            sites[form_key].setdefault(identity, []).append(lineno)
    return sites
def _estimated_fixed_line(opcodes: list[tuple], lineno: int) -> int:
    pos = lineno - 1
    for _tag, i1, i2, j1, j2 in opcodes:
        if i1 <= pos < i2:
            new_span = j2 - j1
            offset = min(pos - i1, max(new_span - 1, 0))
            return j1 + offset + 1
    if opcodes:
        _tag, _i1, last_i2, _j1, last_j2 = opcodes[-1]
        return max(1, lineno + last_j2 - last_i2)
    return lineno
def _added_patch_form_lines(
        original_source: str, fixed_source: str) -> dict[str, list[int]] | None:
    fixed_handlers = _handler_form_sites(fixed_source)
    if fixed_handlers is None:
        return None
    origin_handlers = ([] if isinstance(original_source, str)
                       and not original_source
                       else _handler_form_sites(original_source))
    if origin_handlers is None:
        return None
    unmatched = set(range(len(fixed_handlers)))
    origin_patch = [item for item in origin_handlers if item[1] is not None]
    if origin_patch and fixed_handlers:
        matcher = SequenceMatcher(
            None,
            ast_split_lines(normalize_code(original_source)),
            ast_split_lines(normalize_code(fixed_source)),
            autojunk=False,
        )
        opcodes = matcher.get_opcodes()
        for old_line, old_form, old_identity, old_scope in origin_patch:
            candidates = [
                index for index in unmatched
                if fixed_handlers[index][2] == old_identity
                and fixed_handlers[index][1] in (None, old_form)
                and fixed_handlers[index][3] == old_scope
            ]
            if not candidates:
                continue
            expected = _estimated_fixed_line(opcodes, old_line)
            selected = min(
                candidates,
                key=lambda index: (
                    abs(fixed_handlers[index][0] - expected),
                    fixed_handlers[index][1] != old_form,
                    fixed_handlers[index][0],
                ),
            )
            unmatched.remove(selected)
    added: dict[str, list[int]] = {}
    for index, (lineno, form_key, _identity, _scope) in enumerate(
            fixed_handlers):
        if index in unmatched and form_key is not None:
            added.setdefault(form_key, []).append(lineno)
    return added
def count_patch_forms(src: str) -> dict[str, int]:
    sites = _patch_form_sites(src)
    if sites is None:
        logger.warning(
            "[PatchForm] 源码不可解析或形态非法，补丁形态计数按 0 降级"
            "（未分析≠无位点）")
        return {key: 0 for key in _PATCH_FORM_KEYS}
    return {key: sum(len(positions) for positions in sites[key].values())
            for key in _PATCH_FORM_KEYS}
def detect_new_patch_style_fixes(
        original_source: str, fixed_source: str) -> list[str]:
    added = _added_patch_form_lines(original_source, fixed_source)
    if added is None:
        reason = ("补丁形态差集不可归因（源码不可解析），"
                  "无法确认未新增补丁式修复，禁止降级放行")
        logger.warning("[PatchForm] %s", reason)
        return [reason]
    return [f"{label} x{len(added[key])}{suffix}"
            for key, _matched, label, suffix in _PATCH_FORMS
            if key in added]
def _as_module_name(raw: Any) -> str:
    if not isinstance(raw, str):
        return ""
    text = raw.strip().replace("\\", "/")
    if (not text or text.startswith("/")
            or re.match(r"^[A-Za-z]:", text)):
        return ""
    is_path = "/" in text or text.lower().endswith(".py")
    text = py_stem(text)
    parts: list[str] = []
    for segment in text.split("/"):
        if segment in ("", "."):
            continue
        if segment == "..":
            return ""
        segment_parts = [segment] if is_path else segment.split(".")
        if any(not part for part in segment_parts):
            return ""
        parts.extend(segment_parts)
    if parts and parts[-1] == "__init__":
        parts.pop()
    if (not parts or any(not part.isidentifier() or keyword.iskeyword(part)
                         for part in parts)):
        return ""
    return ".".join(parts)
def _target_path_label(raw: Any, module: str) -> str:
    raw_text = raw.strip().replace("\\", "/") if isinstance(raw, str) else ""
    if raw_text.lower().endswith(".py"):
        return raw_text
    if not raw_text:
        return f"{module or '<新模块>'}.py"
    if "/" in raw_text:
        return f"{raw_text}.py"
    raw_parts = raw_text.split(".")
    if raw_parts[-1] == "__init__":
        return f"{'/'.join(raw_parts)}.py"
    return f"{module.replace('.', '/') if module else raw_text}.py"
class MassiveFileMigratorV3:
    def plan_migration(
        self,
        source_file: str,
        target_modules: dict[str, list[str]],
        caller_files: list[str] | None = None,
    ) -> list[dict[str, Any]]:
        source_file = normalize_filepath(source_file)
        if not source_file:
            return []
        targets = target_modules if isinstance(target_modules, dict) else {}
        steps = self._extract_steps(source_file, targets, 1)
        if not steps:
            return []
        steps.extend(self._redirect_steps(
            source_file, as_sequence(caller_files), len(steps) + 1))
        steps.extend(self._closing_steps(source_file, len(steps) + 1))
        return steps
    @staticmethod
    def _extract_steps(source_file: str, target_modules: dict,
                       start_id: int) -> list[dict[str, Any]]:
        steps: list[dict[str, Any]] = []
        for offset, (target_mod, symbols) in enumerate(target_modules.items()):
            norm_symbols = as_sequence(symbols)
            module = _as_module_name(target_mod)
            target_path = _target_path_label(target_mod, module)
            if module:
                impact = (f"消费者 import 同步改为 from {module} import ..."
                          "（默认不加兼容桩/重导出门户，直接更新全部消费方）")
                verification = f"python -c 'import {module}' 确认成功"
            else:
                impact = ("消费者 import 同步改为新模块（默认不加兼容桩/"
                          "重导出门户）")
                verification = "python -c 'import <新模块>' 确认成功"
            steps.append({
                "step_id": start_id + offset,
                "phase": "EXTRACT",
                "action": f"提取 {len(norm_symbols)} 个符号到新模块 {target_path}",
                "source": source_file,
                "target": target_mod,
                "symbols": norm_symbols,
                "impact": impact,
                "verification": verification,
                "rollback": f"删除 {target_path},恢复源文件到备份",
            })
        return steps
    @staticmethod
    def _redirect_steps(source_file: str, caller_files: list,
                        start_id: int) -> list[dict[str, Any]]:
        steps: list[dict[str, Any]] = []
        for raw_caller in caller_files:
            caller = normalize_filepath(raw_caller)
            if not caller:
                logger.debug("[SplitPlan] 跳过空调用方路径（无落点可重定向）")
                continue
            caller_name = os.path.basename(caller)
            steps.append({
                "step_id": start_id + len(steps),
                "phase": "REDIRECT",
                "action": f"更新调用方 {caller_name} 指向新模块",
                "source": source_file,
                "target": caller,
                "symbols": [],
                "impact": "批量修改 import 语句",
                "verification": f"运行 {caller_name} 的测试确认无回归",
                "rollback": "从 git 恢复 import 语句",
            })
        return steps
    @staticmethod
    def _closing_steps(source_file: str, start_id: int) -> list[dict[str, Any]]:
        return [
            {
                "step_id": start_id,
                "phase": "DEPRECATE",
                "action": "在文档与 CHANGELOG 标记旧接口已弃用（不保留运行时包装器）",
                "source": source_file,
                "target": "",
                "symbols": [],
                "impact": "调用方已全部迁移，源模块不再保留运行时兼容层",
                "verification": "grep 确认无残留 import，全量导入验证通过",
                "rollback": "撤销弃用说明（实现未变更，无需回滚运行时代码）",
            },
            {
                "step_id": start_id + 1,
                "phase": "REMOVE",
                "action": "从源模块安全删除已迁移的符号定义",
                "source": source_file,
                "target": "",
                "symbols": [],
                "impact": "最终清理,所有调用方迁移完成后执行",
                "verification": "全量回归测试 + grep 确认无残留引用",
                "rollback": "从 git 恢复文件",
            },
        ]
    def estimate_timeline(
        self,
        symbol_count: int,
        caller_count: int,
    ) -> dict[str, Any]:
        symbol_count = max(0, int_or(symbol_count, 0))
        caller_count = max(0, int_or(caller_count, 0))
        extract_hours = max(1.0, symbol_count / 100)
        redirect_hours = max(0.5, caller_count * 0.5)
        deprecate_hours = 0.5
        remove_hours = 0.5
        total_hours = extract_hours + redirect_hours + deprecate_hours + remove_hours
        observation_days = _STRANGLER_OBSERVATION_DAYS
        return {
            "total_hours": round(total_hours, 1),
            "extract_hours": extract_hours,
            "redirect_hours": redirect_hours,
            "deprecate_hours": deprecate_hours,
            "remove_hours": remove_hours,
            "observation_days": observation_days,
        }
def generate_checklist(steps: list[dict[str, Any]]) -> str:
    lines = ["# Strangler Fig 迁移检查清单", "", "---", ""]
    current_phase = ""
    for step in as_sequence(steps):
        if not isinstance(step, dict):
            continue
        phase = step.get("phase", "")
        if phase != current_phase:
            current_phase = phase
            lines.append(f"## {_phase_label(phase)}")
            lines.append("")
        step_no = step.get("step_id", "")
        lines.append(f"- [ ] **Step {step_no}**: {step.get('action', '')}")
        for label, key in (("影响", "impact"), ("验证", "verification"), ("回滚", "rollback")):
            value = step.get(key, "")
            if value:
                lines.append(f"  - {label}: {value}")
        lines.append("")
    lines.extend([
        "---", "", "## 完成标准", "",
        "- [ ] 所有步骤已完成并验证",
        "- [ ] 全量回归测试通过",
        "- [ ] grep 确认源模块无残留引用",
        "- [ ] __pycache__ 已清理",
        "- [ ] CHANGELOG 已记录变更",
    ])
    return "\n".join(lines)
_STRANGLER_PHASE_SPECS: tuple[tuple[str, str, str], ...] = (
    ("EXTRACT", "提取阶段", "提取代码到新模块，并同步更新消费者 import"),
    ("REDIRECT", "重定向阶段", "更新调用方逐步指向新模块"),
    ("DEPRECATE", "弃用阶段", "在文档/CHANGELOG 标记旧接口弃用（不保留运行时包装器）"),
    ("REMOVE", "移除阶段", "安全删除旧代码（经 G5 删除依赖分析守卫确认无引用）"),
)
_MIGRATION_DETAIL_KEYS: tuple[str, ...] = ("impact", "verification", "rollback")
def _phase_label(phase: str) -> str:
    for index, (key, label, _desc) in enumerate(_STRANGLER_PHASE_SPECS):
        if key == phase:
            return f"{'一二三四五六七八九十'[index]}、{label} ({key})"
    return phase
def _migration_details(plan: list,
                       filepath: str) -> dict[str, dict]:
    target_modules: dict[str, list[str]] = {}
    for item in _plan_items(plan):
        target_modules.setdefault(
            _plan_target_module(item), []).extend(_plan_symbols(item))
    try:
        mig_steps = MassiveFileMigratorV3().plan_migration(
            filepath or "<目标文件>", target_modules)
    except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as _e:
        log_swallowed(__name__, _e, context="build_split_steps:migrate_file")
        return {}
    merged: dict[str, dict[str, list[str]]] = {}
    for step in mig_steps:
        phase = step.get("phase")
        if not isinstance(phase, str) or not phase:
            continue
        bucket = merged.setdefault(
            phase, {key: [] for key in _MIGRATION_DETAIL_KEYS})
        for key in _MIGRATION_DETAIL_KEYS:
            value = step.get(key)
            if isinstance(value, str) and value and value not in bucket[key]:
                bucket[key].append(value)
    return {
        phase: {key: "；".join(values) for key, values in bucket.items()}
        for phase, bucket in merged.items()
    }
def _strangler_step(step_id: int, phase: str, desc: str,
                    detail: dict | None) -> dict:
    step = {"step_id": step_id, "phase": phase, "action": desc}
    if detail:
        step["impact"] = detail.get("impact", "")
        step["verification"] = detail.get("verification", "")
        step["rollback"] = detail.get("rollback", "")
    return step
def _strangler_split_steps(plan: list,
                           filepath: str) -> list[dict]:
    details = _migration_details(plan, filepath)
    return [
        _strangler_step(step_id, phase, desc, details.get(phase))
        for step_id, (phase, _label, desc) in enumerate(
            _STRANGLER_PHASE_SPECS, start=1)
    ]
def _plan_field(item: Any, key: str) -> Any:
    if isinstance(item, dict):
        return item.get(key)
    return getattr(item, key, None)
def _plan_target_module(item: Any) -> str:
    target = _plan_field(item, "target_module")
    return target if isinstance(target, str) else ""
def _plan_symbols(item: Any) -> list[str]:
    return [sym for sym in as_sequence(_plan_field(item, "symbols"))
            if isinstance(sym, str)]
def _plan_items(plan: Any) -> list[Any]:
    items = as_sequence(plan)
    valid = [item for item in items if _plan_target_module(item)]
    if len(valid) != len(items):
        logger.warning("[SplitPlan] 跳过 %d 个形态非法的计划条目"
                     "（缺 target_module）", len(items) - len(valid))
    return valid
def _direct_split_steps(plan: list) -> list[dict]:
    steps = []
    step_id = 1
    for p in _plan_items(plan):
        raw_target = _plan_target_module(p)
        target_module = _as_module_name(raw_target) or raw_target
        target_path = _target_path_label(raw_target, target_module)
        symbols = _plan_symbols(p)
        steps.append({
            "step_id": step_id,
            "action": f"提取 {len(symbols)} 个符号到 {target_path}",
            "symbols": symbols,
            "target": target_module,
        })
        step_id += 1
    steps.append({"step_id": step_id, "action":
        "直接更新所有消费者 import 指向新模块（默认不加兼容桩/"
        "重导出门户；外部消费者或 10+ 内部消费者时才加桩并标注 "
        "TEMPORARY COMPAT STUB）"})
    step_id += 1
    steps.append({"step_id": step_id, "action":
                  "清理 __pycache__ 并运行全量导入验证"})
    return steps
def build_split_steps(plan: list,
                       strategy: SplitStrategy,
                       filepath: str = _DEFAULT_FILEPATH) -> list[dict]:
    if not plan:
        return []
    if strategy == SplitStrategy.STRANGLER_FIG:
        return _strangler_split_steps(plan, filepath)
    return _direct_split_steps(plan)
def build_post_split_checks(plan: list) -> list[str]:
    checks = ["python -c 'import <project>'", "全量导入测试"]
    for p in _plan_items(plan):
        module = _as_module_name(_plan_target_module(p))
        if not module:
            continue
        checks.append(f"python -c 'from <project>.{module} import *'")
        checks.append(
            f"确认旧模块无 'from {module} import *' 重导出门户，"
            f"消费者直接改为 from {module} import <符号>")
    checks.extend([
        "搜索旧模块中的残留引用",
        "运行全量单元测试",
        "检查 __pycache__ 已清理",
    ])
    return checks
def estimate_split_effort(file_lines: int, boundary_count: int,
                           strategy: SplitStrategy) -> str:
    file_lines = max(0, int_or(file_lines, 0))
    boundary_count = max(0, int_or(boundary_count, 0))
    if strategy == SplitStrategy.STRANGLER_FIG:
        hours = file_lines / 200
        return (
            f"约{hours:.1f}小时 (Strangler Fig 渐进式，分4个阶段，"
            f"建议观察期 {_STRANGLER_OBSERVATION_DAYS} 天)"
        )
    hours = file_lines / 500
    if boundary_count > 0:
        hours *= 1 + boundary_count * 0.3
    return f"约{hours:.1f}小时 ({boundary_count}个候选模块)"
def build_rollback_plan(filepath: str) -> str:
    target = filepath or "<目标文件>"
    return (
        f"拆分前先备份 {target}（文件级备份是唯一恢复通道，备份落在项目工作区"
        "的备份目录，不写入源码根）；任一阶段验证失败时，用该备份整体恢复原文件，"
        "清理 __pycache__ 后重跑全量导入验证"
    )

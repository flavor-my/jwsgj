from __future__ import annotations

import ast
import bisect as _bisect
import concurrent.futures as _cf
import logging
import os
from collections import defaultdict
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from functools import partial
from typing import NamedTuple

from jwsgj.diag_blindspot_file import (
    DEFAULT_PROJECT_ROOT,
    BlindspotAnalyzer,
    ModuleBlindspotScanner,
    ScriptBlindspotScanner,
    blindspot_histograms,
    collect_py_files,
    is_tests_domain_file,
)
from jwsgj.diag_blindspot_refs import (
    _REGISTRAR_DECORATORS,
    _WEB_HOOK_DECORATORS,
    _bound_attr_pair,
    _collect_class_attrs,
    _collect_module_all_exports,
    _collect_value_ref_names,
    _comprehension_shadow_name_ids,
    _container_func_refs,
    _decorator_ref,
    _decorator_ref_node_ids,
    _dotted_module_name,
    _module_scope_name_load_ids,
    _namespace_string_constants,
    _package_name_from_rel,
    _qualify,
    _rebinding_position,
    _registration_value,
    _rel_to_root,
    _simple_name,
    _statement_suite_index,
    _suite_path,
    is_library_project,
    parse_module,
    scan_dynamic_patterns,
    suppressed_declaration,
    suppressions_for,
)
from jwsgj.diag_business_flow import (
    diagnose_business_flows,
    diagnose_business_flows_enhanced,
)
from jwsgj.diag_exception_verdict import (
    run_exception_layer,
)
from jwsgj.diag_runtime_forensics import (
    ensure_coverage_hook,
    run_cross_validation_layer,
)
from jwsgj.diag_shared_ast_bindings import (
    ScopeNameResolver,
    collect_binding_names,
)
from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    class_base_names,
    iter_module_scope_entities,
    iter_module_scope_nodes,
    iter_own_nodes,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_source_core import load_module, sync_shared_ast_cache
from jwsgj.diag_types_vocab import (
    AST_VISITOR_PREFIXES,
    CLI_CMD_PREFIXES,
    FIELD_TOTAL_BLINDSPOTS,
    FIELD_TOTAL_FUNCTIONS,
    LAYER_DEGRADE_EXC_WITH_IMPORT,
    POLYMORPHIC_METHODS,
    RULE_PUBLIC_UNTESTED,
)
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
DEFAULT_INCLUDE_CODE_BLINDSPOTS = True
__all__ = [
    "ClassBlindspot",
    "ClassBlindspotReport",
    "ClassBlindspotScanner",
    "FunctionBlindspot",
    "FunctionBlindspotReport",
    "FunctionBlindspotScanner",
    "build_layer_scan_jobs",
    "pause_coverage_for_analysis",
    "resume_coverage_after_analysis",
    "run_business_chain_layer",
    "run_code_layer_scan",
    "run_layer14_parallel",
    "run_layers_5_to_76",
]
def _starts_with_any(name: str, prefixes) -> bool:
    return any(name.startswith(prefix) for prefix in prefixes)
def _is_name_exempt(simple_name: str) -> bool:
    if simple_name.startswith('__') and simple_name.endswith('__'):
        return True
    return simple_name.startswith('test_')
def _is_same_name_super_attr(func_node, method_name: str) -> bool:
    return (isinstance(func_node, ast.Attribute)
            and func_node.attr == method_name
            and isinstance(func_node.value, ast.Call)
            and isinstance(func_node.value.func, ast.Name)
            and func_node.value.func.id == 'super')
def _is_super_forward_stmt(stmt, method_name: str) -> bool:
    value = None
    if isinstance(stmt, (ast.Expr, ast.Return)):
        value = stmt.value
    if value is None:
        return False
    if isinstance(value, ast.Await):
        value = value.value
    if isinstance(value, ast.Call):
        return _is_same_name_super_attr(value.func, method_name)
    return _is_same_name_super_attr(value, method_name)
def _is_nonstub_impl_node(node) -> bool:
    body = _effective_body(node)
    if not body:
        return False
    is_stub, is_ellipsis_body = _classify_stub_body(body)
    if is_stub or is_ellipsis_body:
        return False
    if len(body) > 1:
        return True
    return not _is_super_forward_stmt(body[0], node.name)
def _effective_body(node) -> list:
    body = list(node.body)
    has_docstring = ast.get_docstring(node, clean=False) is not None
    return body[1:] if has_docstring else body
def _classify_stub_body(effective_body) -> tuple[bool, bool]:
    if not effective_body:
        return False, False
    is_stub = True
    is_ellipsis_body = True
    for stmt in effective_body:
        if (isinstance(stmt, ast.Pass)
                or (isinstance(stmt, ast.Raise)
                    and ast_name(stmt.exc) == 'NotImplementedError')):
            is_ellipsis_body = False
        elif (isinstance(stmt, ast.Expr)
              and isinstance(stmt.value, ast.Constant)
              and stmt.value.value is Ellipsis):
            is_stub = False
        else:
            return False, False
    return is_stub, is_ellipsis_body
def _overridden_by_subclass(func_info: dict, subclass_overrides: dict | None) -> bool:
    if not func_info.get('is_method'):
        return False
    class_name = func_info.get('class_name')
    return bool(class_name and subclass_overrides
                and func_info['simple_name']
                in subclass_overrides.get(class_name, ()))
def _is_stub_decl_exempt(func_info: dict, subclass_overrides: dict | None) -> bool:
    if _overridden_by_subclass(func_info, subclass_overrides):
        return True
    return bool(func_info.get('class_is_protocol')
                or func_info.get('is_abstract'))
def _report_blindspot(scanner, report, full_name: str, func_info: dict, *,
                      blindspot_type: str, severity: str,
                      message: str, suggestion: str) -> None:
    if _decl_suppressed(scanner, func_info, _suppress_rule_ids(blindspot_type)):
        return
    report.blindspots.append(FunctionBlindspot(
        function_name=full_name,
        filepath=func_info['filepath'],
        start_line=func_info['start_line'],
        end_line=func_info['end_line'],
        blindspot_type=blindspot_type,
        severity=severity,
        is_public=func_info['is_public'],
        is_method=func_info['is_method'],
        class_name=func_info.get('class_name'),
        params_count=func_info['params_count'],
        body_lines=func_info['body_lines'],
        message=message,
        suggestion=suggestion,
        body_first_line=func_info.get('body_first_line', 0),
    ))
def _report_uncalled_blindspot(scanner, report, full_name: str, func_info: dict) -> None:
    is_public = func_info['is_public']
    _report_blindspot(
        scanner, report, full_name, func_info,
        blindspot_type=RULE_PUBLIC_UNTESTED if is_public else 'orphan',
        severity='high' if is_public else 'medium',
        message=(f'公开函数 {full_name} 无任何调用者且无测试覆盖'
                 if is_public
                 else f'函数 {full_name} 定义了但从未被调用'),
        suggestion=('为该函数编写单元测试，或检查调用链是否断裂'
                   if is_public else '检查是否可移除，或添加调用链'))
def _report_dead_stub_blindspot(scanner, report, full_name: str, func_info: dict, subclass_overrides) -> None:
    if func_info['is_stub'] and not _is_stub_decl_exempt(func_info, subclass_overrides):
        detail = ('仅含文档字符串' if func_info.get('body_lines') == 0
                  else 'raise NotImplementedError 或 pass')
        _report_blindspot(
            scanner, report, full_name, func_info,
            blindspot_type='dead_stub', severity='high',
            message=f'桩函数 {full_name} 未实现（{detail}）',
            suggestion='实现函数体或标记为抽象方法 @abstractmethod')
def _report_empty_shell_blindspot(scanner, report, full_name: str, func_info: dict, subclass_overrides) -> None:
    if (func_info.get('is_ellipsis_body')
            and not _is_stub_decl_exempt(func_info, subclass_overrides)):
        _report_blindspot(
            scanner, report, full_name, func_info,
            blindspot_type='empty_shell', severity='low',
            message=f"函数 {full_name} 体仅包含省略号占位（无实现）",
            suggestion='检查是否遗漏了实现')
def _declaration_first_line(node) -> int:
    decorator_lines = [dec.lineno for dec in getattr(node, 'decorator_list', ())
                       if isinstance(getattr(dec, 'lineno', None), int)]
    return min(decorator_lines) if decorator_lines else node.lineno
def _decl_suppressed(scanner, func_info: dict, rule_ids) -> bool:
    suppressions = scanner._suppressions_for(func_info.get('filepath') or '')
    return suppressed_declaration(suppressions, func_info, rule_ids)
_SUPPRESS_RULE_ALIASES: dict[str, tuple[str, ...]] = {
    RULE_PUBLIC_UNTESTED: (RULE_PUBLIC_UNTESTED, 'orphan', 'D18'),
    'orphan': (RULE_PUBLIC_UNTESTED, 'orphan', 'D18'),
    'dead_stub': ('dead_stub', 'empty_function', 'stub_function', 'pass_stub',
                  'D18', 'D07'),
    'empty_shell': ('empty_shell', 'empty_function', 'D07'),
    'empty_function': ('empty_function', 'dead_stub', 'empty_shell', 'D07'),
}
def _suppress_rule_ids(blindspot_type: str) -> tuple[str, ...]:
    return _SUPPRESS_RULE_ALIASES.get(blindspot_type, (blindspot_type,))
def _iter_scoped_functions(all_functions, project_root):
    for full_name, func_info in all_functions.items():
        if is_tests_domain_file(func_info.get('filepath', ''), project_root):
            continue
        yield full_name, _simple_name(full_name), func_info
class _Evidence(NamedTuple):
    called_funcs: set
    dynamic_refs: set
    subclass_overrides: dict | None
def _private_class_method(func_info: dict) -> bool:
    class_name = func_info.get('class_name')
    return (bool(func_info.get('is_method'))
            and isinstance(class_name, str)
            and class_name.startswith('_'))
def _classify_function(scanner, full_name: str, simple_name: str,
                       func_info: dict, evidence: _Evidence, report) -> None:
    is_called = _is_called_func(
        full_name, simple_name, evidence.called_funcs,
        allow_simple=func_info['allow_simple_ref'])
    public_api_exports = scanner._all_exports_cache.get(
        func_info.get('module_name') or '', set())
    is_dynamic = scanner._is_dynamically_called(
        full_name, func_info, evidence.dynamic_refs, public_api_exports)
    is_value_ref = scanner._value_ref_hit(func_info, simple_name)
    is_hook = (_overridden_by_subclass(func_info, evidence.subclass_overrides)
               or scanner._override_via_self_dispatch(func_info, simple_name)
               or func_info.get('class_is_protocol', False)
               or func_info.get('is_abstract', False))
    if (not _private_class_method(func_info)
            and not is_called and not is_dynamic
            and not is_value_ref and not is_hook):
        _report_uncalled_blindspot(scanner, report, full_name, func_info)
    _report_dead_stub_blindspot(scanner, report, full_name, func_info,
                                evidence.subclass_overrides)
    _report_empty_shell_blindspot(scanner, report, full_name, func_info,
                                  evidence.subclass_overrides)
def _is_called_func(full_name: str, simple_name: str, called_funcs,
                    allow_simple: bool) -> bool:
    return full_name in called_funcs or (
        allow_simple and simple_name in called_funcs)
def _analyze_function_blindspots(scanner, all_functions, evidence: _Evidence, report) -> None:
    for full_name, simple_name, func_info in _iter_scoped_functions(
            all_functions, scanner.project_root):
        if _is_name_exempt(simple_name):
            continue
        _classify_function(scanner, full_name, simple_name, func_info,
                           evidence, report)
def _check_coverage_blindspots(scanner, coverage_hook, all_functions, called_funcs, report):
    for full_name, simple_name, func_info in _iter_scoped_functions(
            all_functions, scanner.project_root):
        if not func_info['is_public'] or not _is_called_func(
                full_name, simple_name, called_funcs,
                allow_simple=func_info['allow_simple_ref']):
            continue
        if scanner._check_func_coverage(coverage_hook, func_info):
            continue
        _report_blindspot(
            scanner, report, full_name, func_info,
            blindspot_type='no_test_coverage', severity='medium',
            message=f'函数 {full_name} 有调用者但未被任何测试覆盖',
            suggestion='补充测试用例覆盖函数的边界条件')
def _class_qualified_path(class_node, parents) -> str:
    names = [class_node.name]
    parent = parents.get(class_node)
    while parent is not None:
        if isinstance(parent, ast.ClassDef):
            names.append(parent.name)
        parent = parents.get(parent)
    return '.'.join(reversed(names))
def _class_path_index(tree) -> dict[ast.ClassDef, str]:
    parents = {child: parent for parent in walk_nodes(tree)
               for child in ast.iter_child_nodes(parent)}
    return {
        node: _class_qualified_path(node, parents)
        for node in walk_nodes(tree) if isinstance(node, ast.ClassDef)
    }
def _attribute_name_chain(node: ast.Attribute) -> tuple[ast.Name, list[str]] | None:
    parts: list[str] = []
    current: ast.AST = node
    while isinstance(current, ast.Attribute):
        parts.append(current.attr)
        current = current.value
    if not isinstance(current, ast.Name):
        return None
    parts.append(current.id)
    parts.reverse()
    return current, parts
def _collect_scoped_class_qualified_refs(
        tree, module_name: str, call_targets: set[int], class_attr_refs: dict,
        class_paths: dict[ast.ClassDef, str], module_name_load_ids: set[int],
) -> None:
    known_paths = set(class_paths.values())
    if not known_paths:
        return
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Attribute)
                and isinstance(node.ctx, ast.Load)
                and id(node) not in call_targets):
            continue
        chain = _attribute_name_chain(node)
        if chain is None:
            continue
        root, parts = chain
        if id(root) not in module_name_load_ids:
            continue
        for size in range(len(parts) - 1, 0, -1):
            class_path = '.'.join(parts[:size])
            if class_path in known_paths:
                class_attr_refs.setdefault(
                    (module_name, class_path), set()).add(parts[size])
                break
def _collect_top_nodes(tree) -> tuple:
    class_ranges: dict = {}
    func_defs: list = []
    parents = {child: parent for parent in walk_nodes(tree)
               for child in ast.iter_child_nodes(parent)}
    for top_node in walk_nodes(tree):
        if isinstance(top_node, ast.ClassDef):
            class_end = top_node.end_lineno or top_node.lineno
            class_ranges[(top_node.lineno, class_end)] = (
                top_node.name, class_base_names(top_node),
                _class_qualified_path(top_node, parents))
        elif isinstance(top_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_defs.append(top_node)
    return class_ranges, func_defs
def _prefix_max_end_seq(pairs) -> list:
    maxend: list = []
    cur = -1
    for _s, _e in pairs:
        cur = max(cur, _e)
        maxend.append(cur)
    return maxend
class _RangeIndexes(NamedTuple):
    f_starts: list
    f_maxend: list
    sorted_classes: list
    c_starts: list
    c_maxend: list
def _build_range_indexes(func_defs: list, class_ranges: dict) -> _RangeIndexes:
    sorted_funcs = sorted(func_defs, key=lambda n: n.lineno)
    f_starts = [n.lineno for n in sorted_funcs]
    f_maxend = _prefix_max_end_seq(
        (n.lineno, n.end_lineno or n.lineno) for n in sorted_funcs)
    sorted_classes = sorted(class_ranges.items(), key=lambda kv: kv[0][0])
    c_starts = [k[0] for k, _ in sorted_classes]
    c_maxend = _prefix_max_end_seq(
        (_s, _e) for ((_s, _e), _) in sorted_classes)
    return _RangeIndexes(f_starts, f_maxend, sorted_classes,
                         c_starts, c_maxend)
def _covering_prefix_index(starts: list, maxend: list, start: int, end: int) -> int:
    i = _bisect.bisect_left(starts, start)
    if i == 0 or maxend[i - 1] < end:
        return -1
    return i - 1
def _is_nested_func(func_node, idx: _RangeIndexes) -> bool:
    func_start = func_node.lineno
    func_end = func_node.end_lineno or func_node.lineno
    return _covering_prefix_index(idx.f_starts, idx.f_maxend,
                                  func_start, func_end) >= 0
def _enclosing_class_of(func_node, idx: _RangeIndexes) -> tuple[str, tuple[str, ...], str] | None:
    func_start = func_node.lineno
    func_end = func_node.end_lineno or func_node.lineno
    i = _covering_prefix_index(idx.c_starts, idx.c_maxend,
                               func_start, func_end)
    if i < 0:
        return None
    for j in range(i, -1, -1):
        ce = idx.sorted_classes[j][0][1]
        if func_end <= ce:
            return idx.sorted_classes[j][1]
    return None
def _merge_class_override_evidence(tree, overrides: dict[str, set[str]]) -> None:
    runtime_inactive = type_checking_body_node_ids(tree)
    for cls_node in walk_nodes(tree):
        if not isinstance(cls_node, ast.ClassDef):
            continue
        if id(cls_node) in runtime_inactive:
            continue
        base_names = class_base_names(cls_node)
        if not base_names:
            continue
        implemented = {
            item.name for item in iter_module_scope_entities(cls_node)
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
            and id(item) not in runtime_inactive
            and _is_nonstub_impl_node(item)
        }
        if not implemented:
            continue
        for bn in base_names:
            overrides.setdefault(bn, set()).update(implemented)
def _function_body_metrics(node) -> tuple:
    effective_body = _effective_body(node)
    body_lines = len(effective_body)
    is_stub = not effective_body
    is_ellipsis_body = False
    body_first_line = effective_body[0].lineno if effective_body else 0
    if effective_body:
        is_stub, is_ellipsis_body = _classify_stub_body(effective_body)
    return body_lines, is_stub, is_ellipsis_body, body_first_line
def _is_abstract_method(node) -> bool:
    for decorator in node.decorator_list:
        expression = (decorator.func if isinstance(decorator, ast.Call)
                      else decorator)
        if ast_name(expression) == 'abstractmethod':
            return True
    return False
def _count_params(args: ast.arguments) -> int:
    return (len(args.posonlyargs) + len(args.args) + len(args.kwonlyargs)
            + (1 if args.vararg else 0)
            + (1 if args.kwarg else 0))
def _wildcard_ref_hit(prefix: str, full_name: str, simple_name: str,
                      allow_simple: bool) -> bool:
    if full_name.startswith(prefix):
        return True
    last_seg = prefix.rsplit('.', 1)[-1]
    return allow_simple and simple_name.startswith(last_seg)
def _dynamic_refs_hit(full_name: str, simple_name: str, dynamic_refs: set,
                      allow_simple: bool) -> bool:
    if full_name in dynamic_refs or (allow_simple and simple_name in dynamic_refs):
        return True
    if f"attr:{simple_name}" in dynamic_refs:
        return True
    return any(
        _wildcard_ref_hit(ref[:-1], full_name, simple_name, allow_simple)
        for ref in dynamic_refs
        if ref.endswith('*')
    )
def _globals_introspection_hit(gi_mods, full_name: str, simple_name: str, is_method: bool) -> bool:
    if not gi_mods or is_method or not simple_name.startswith('_'):
        return False
    owning_mod = full_name.rsplit('.', 1)[0] if '.' in full_name else ''
    return owning_mod in gi_mods
def _name_shape_exempt(simple_name: str, is_method: bool, class_name) -> bool:
    if simple_name in _CLOSURE_SIGNAL_NAMES:
        return True
    if _starts_with_any(simple_name, CLI_CMD_PREFIXES):
        return True
    if not is_method:
        return False
    if _starts_with_any(simple_name, AST_VISITOR_PREFIXES):
        return True
    if simple_name in POLYMORPHIC_METHODS:
        return True
    return bool(class_name and class_name.endswith(_VISITOR_COLLECTOR_SUFFIXES))
def _public_api_hit(public_api_exports, full_name: str, simple_name: str, class_name) -> bool:
    if not public_api_exports:
        return False
    if class_name:
        return class_name in public_api_exports
    return full_name in public_api_exports or simple_name in public_api_exports
_CLOSURE_SIGNAL_NAMES = frozenset({'wrapper', 'decorator', 'inner', 'wrapped', '_wrapper', '_inner'})
_VISITOR_COLLECTOR_SUFFIXES = ('Visitor', 'Collector')
@dataclass
class FunctionBlindspot:
    function_name: str
    filepath: str
    start_line: int
    end_line: int
    blindspot_type: str
    severity: str
    is_public: bool = False
    is_method: bool = False
    class_name: str | None = None
    params_count: int = 0
    body_lines: int = 0
    message: str = ''
    suggestion: str = ''
    body_first_line: int = 0
    def to_dict(self) -> dict:
        return {
            'function_name': self.function_name,
            'filepath': self.filepath,
            'start_line': self.start_line,
            'end_line': self.end_line,
            'blindspot_type': self.blindspot_type,
            'severity': self.severity,
            'is_public': self.is_public,
            'is_method': self.is_method,
            'class_name': self.class_name,
            'params_count': self.params_count,
            'body_lines': self.body_lines,
            'message': self.message,
            'suggestion': self.suggestion,
            'body_first_line': self.body_first_line,
        }
@dataclass
class FunctionBlindspotReport:
    project_root: str
    total_functions: int = 0
    public_functions: int = 0
    blindspots: list[FunctionBlindspot] = field(default_factory=list)
    def summary(self) -> dict:
        sev, btype = blindspot_histograms(self.blindspots)
        return {
            FIELD_TOTAL_FUNCTIONS: self.total_functions,
            'public_functions': self.public_functions,
            FIELD_TOTAL_BLINDSPOTS: len(self.blindspots),
            'by_severity': sev,
            'by_type': btype,
        }
class FunctionBlindspotScanner:
    def __init__(self, project_root: str=DEFAULT_PROJECT_ROOT, ctx=None) -> None:
        self.project_root = os.path.abspath(project_root)
        self._ctx = ctx
        self._reset_scan_state()
    def _reset_scan_state(self) -> None:
        self._all_exports_cache: dict[str, set[str]] = {}
        self._globals_introspection_mods: set[str] = set()
        self._class_string_refs: dict[tuple[str, str], set[str]] = {}
        self._class_body_refs: dict[str, set[str]] = {}
        self._module_string_refs: dict[str, set[str]] = {}
        self._module_container_refs: dict[str, set[str]] = {}
        self._class_value_refs: dict[tuple[str, str], set[str]] = {}
        self._class_attr_refs: dict[tuple[str, str], set[str]] = {}
        self._module_value_refs: dict[str, set[str]] = {}
        self._suppress_cache: dict[str, dict] = {}
    def _suppressions_for(self, filepath: str) -> dict:
        if not filepath:
            return {}
        if not os.path.isabs(filepath):
            filepath = os.path.join(self.project_root, filepath)
        cached = self._suppress_cache.get(filepath)
        if cached is not None:
            return cached
        parsed = suppressions_for(filepath, self._ctx)
        self._suppress_cache[filepath] = parsed
        return parsed
    def _collect_value_refs(self, files: list[str]) -> None:
        for filepath in files:
            tree = parse_module(filepath, self._ctx)
            if tree is None:
                continue
            module_name = self._module_name(filepath)
            if module_name is None:
                continue
            call_targets = {id(node.func) for node in walk_nodes(tree)
                            if isinstance(node, ast.Call)}
            decorator_ids = _decorator_ref_node_ids(tree)
            module_name_load_ids = _module_scope_name_load_ids(tree)
            comprehension_shadowed = _comprehension_shadow_name_ids(tree)
            class_paths = _class_path_index(tree)
            module_slot = self._module_value_refs.setdefault(module_name, set())
            _collect_value_ref_names(
                tree, call_targets, module_slot, decorator_ids=decorator_ids,
                module_name_load_ids=module_name_load_ids)
            for class_node, class_path in class_paths.items():
                key = (module_name, class_path)
                bare_slot = self._class_value_refs.setdefault(key, set())
                attr_slot = self._class_attr_refs.setdefault(key, set())
                class_value_load_ids = {
                    id(name) for name in walk_nodes(class_node)
                    if isinstance(name, ast.Name)
                    and isinstance(name.ctx, ast.Load)
                    and id(name) not in comprehension_shadowed
                }
                _collect_value_ref_names(
                    class_node, call_targets, bare_slot, attr_slot,
                    decorator_ids, module_name_load_ids=class_value_load_ids,
                    module_slot=module_slot)
            _collect_scoped_class_qualified_refs(
                tree, module_name, call_targets, self._class_attr_refs,
                class_paths, module_name_load_ids)
    def _value_ref_hit(self, func_info: dict, simple_name: str) -> bool:
        module_name = func_info.get('module_name') or ''
        class_name = func_info.get('class_name')
        if func_info.get('is_method') and class_name:
            key = (module_name, func_info.get('class_path') or class_name)
            if simple_name in self._class_value_refs.get(key, ()):
                return True
            return simple_name in self._class_attr_refs.get(key, ())
        if not func_info['allow_simple_ref']:
            return False
        return simple_name in self._module_value_refs.get(module_name, ())
    def _override_via_self_dispatch(self, func_info: dict,
                                    simple_name: str) -> bool:
        if not func_info.get('is_method'):
            return False
        for base in func_info.get('class_base_names') or ():
            if any((owner == base or owner.endswith(f'.{base}'))
                   for (_mod, owner), refs in self._class_attr_refs.items()
                   if simple_name in refs):
                return True
        return False
    def _collect_reference_evidence(self, files: list[str]) -> None:
        for filepath in files:
            tree = parse_module(filepath, self._ctx)
            if tree is None:
                continue
            module_name = self._module_name(filepath)
            if module_name is None:
                continue
            module_strings = self._module_string_refs.setdefault(
                module_name, set())
            module_containers = self._module_container_refs.setdefault(
                module_name, set())
            class_paths = _class_path_index(tree)
            for node in iter_module_scope_nodes(tree, descend_classes=False):
                _value = _registration_value(node)
                if _value is None:
                    continue
                module_strings.update(_namespace_string_constants(_value))
                bare_names, _ = _container_func_refs(_value)
                module_containers.update(bare_names)
            for node in walk_nodes(tree):
                if not isinstance(node, ast.ClassDef):
                    continue
                slot = self._class_string_refs.setdefault(
                    (module_name, class_paths[node]), set())
                body_refs = self._class_body_refs.setdefault(module_name, set())
                class_bound: set[str] = set()
                for stmt in node.body:
                    if not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                             ast.ClassDef)):
                        for sub in (stmt, *iter_own_nodes(stmt)):
                            _value = _registration_value(sub)
                            if _value is None:
                                continue
                            bare_names, attr_names = _container_func_refs(_value)
                            slot.update(_namespace_string_constants(_value)
                                        | attr_names)
                            body_refs.update(bare_names - class_bound)
                    collect_binding_names(stmt, class_bound)
    def scan(self, source_paths: list[str] | None=None, call_graph=None, coverage_hook=None) -> FunctionBlindspotReport:
        self._reset_scan_state()
        report = FunctionBlindspotReport(project_root=self.project_root)
        files = collect_py_files(
            self.project_root, source_paths, ctx=self._ctx)
        dynamic_refs, globals_introspection_mods = scan_dynamic_patterns(
            self, source_paths, call_graph, files=files)
        self._globals_introspection_mods = globals_introspection_mods
        all_functions = self._extract_all_functions(files)
        self._collect_reference_evidence(files)
        self._collect_value_refs(files)
        self._apply_function_counts(report, all_functions)
        called_funcs = self._collect_called_funcs(call_graph)
        subclass_overrides = self._collect_subclass_overrides(files)
        evidence = _Evidence(called_funcs, dynamic_refs, subclass_overrides)
        _analyze_function_blindspots(self, all_functions, evidence, report)
        if coverage_hook is not None:
            _check_coverage_blindspots(self, coverage_hook, all_functions, called_funcs, report)
        return report
    def _apply_function_counts(self, report, all_functions) -> None:
        scoped = [fi for _full, _simple, fi in _iter_scoped_functions(
            all_functions, self.project_root)]
        report.total_functions = len(scoped)
        report.public_functions = sum(1 for fi in scoped if fi['is_public'])
    def _extract_all_functions(self, files: list[str]) -> dict[str, dict]:
        all_functions: dict[str, dict] = {}
        for filepath in files:
            if is_tests_domain_file(filepath, self.project_root):
                continue
            rel = _rel_to_root(self.project_root, filepath)
            if rel is None:
                continue
            for func_info in self._extract_functions(filepath):
                func_info['filepath'] = rel.replace('\\', '/')
                all_functions[func_info['full_name']] = func_info
        simple_counts = defaultdict(int)
        for full_name in all_functions:
            simple_counts[_simple_name(full_name)] += 1
        for func_info in all_functions.values():
            func_info['allow_simple_ref'] = (
                simple_counts[func_info['simple_name']] == 1)
        return all_functions
    @staticmethod
    def _collect_called_funcs(call_graph) -> set[str]:
        called_funcs: set[str] = set()
        if call_graph is None:
            return called_funcs
        for edge in call_graph.calls:
            called_funcs.add(edge.callee_func)
            # 外部被调方（如 json.dumps）的简单名不是项目内同名函数的调用证据：
            # 简单名仅在 allow_simple_ref（项目内唯一）时参与匹配，若不隔离会把
            # 从未被调用的本地函数误判为“有调用者”，进而漏报孤儿并伪造 no_test_coverage。
            if not getattr(edge, 'is_external', False):
                called_funcs.add(_simple_name(edge.callee_func))
        return called_funcs
    def _extract_functions(self, filepath: str) -> list[dict]:
        funcs = []
        tree = parse_module(filepath, self._ctx)
        if tree is None:
            return funcs
        module_name = self._module_name(filepath)
        if module_name is None:
            return funcs
        class_ranges, func_defs = _collect_top_nodes(tree)
        runtime_inactive = type_checking_body_node_ids(tree)
        func_defs = [node for node in func_defs
                     if id(node) not in runtime_inactive]
        _collect_module_all_exports(tree, module_name, self._all_exports_cache)
        idx = _build_range_indexes(func_defs, class_ranges)
        for node in func_defs:
            func_info = self._build_func_info(node, module_name, idx)
            if func_info is not None:
                funcs.append(func_info)
        return funcs
    def _build_func_info(self, node, module_name: str, idx) -> dict | None:
        if _is_nested_func(node, idx):
            return None
        name = node.name
        class_info = _enclosing_class_of(node, idx)
        current_class = class_info[0] if class_info else None
        class_bases = class_info[1] if class_info else ()
        class_path = class_info[2] if class_info else None
        if current_class and _starts_with_any(name, AST_VISITOR_PREFIXES):
            return None
        full_name = _qualify(
            module_name, f'{class_path}.{name}' if class_path else name)
        body_lines, is_stub, is_ellipsis_body, body_first_line = (
            _function_body_metrics(node))
        return {
            'full_name': full_name,
            'simple_name': name,
            'module_name': module_name,
            'start_line': node.lineno,
            'decl_first_line': _declaration_first_line(node),
            'end_line': node.end_lineno or node.lineno,
            'body_first_line': body_first_line,
            'is_public': not name.startswith('_'),
            'is_method': current_class is not None,
            'class_name': current_class,
            'class_path': class_path,
            'params_count': _count_params(node.args),
            'body_lines': body_lines,
            'is_stub': is_stub,
            'is_ellipsis_body': is_ellipsis_body,
            'class_base_names': class_bases,
            'class_is_protocol': 'Protocol' in class_bases,
            'is_abstract': _is_abstract_method(node),
        }
    def _collect_subclass_overrides(self, files: list[str]) -> dict[str, set[str]]:
        overrides: dict[str, set[str]] = {}
        for filepath in files:
            if is_tests_domain_file(filepath, self.project_root):
                continue
            tree = parse_module(filepath, self._ctx)
            if tree is None:
                continue
            _merge_class_override_evidence(tree, overrides)
        return overrides
    def _module_name(self, filepath: str) -> str | None:
        rel = _rel_to_root(self.project_root, filepath)
        if rel is None:
            return None
        return _dotted_module_name(rel)
    def _check_func_coverage(self, coverage_hook, func_info: dict) -> bool:
        try:
            filepath = os.path.normpath(os.path.join(self.project_root, func_info['filepath']))
            uncovered = coverage_hook.get_uncovered(filepath)
            body_first = func_info.get('body_first_line')
            if body_first is None:
                logger.debug('func_info 缺 body_first_line，默认已覆盖: %s',
                             func_info.get('filepath'))
                return True
            return body_first not in uncovered
        except Exception as exc:  # noqa: BLE001 — 覆盖率钩子是外部注入点，
            logger.warning('覆盖率判定失败，按已覆盖处理（可能掩盖未覆盖）: %s', exc)
            return True
    def _is_dynamically_called(self, full_name: str, func_info: dict,
                               dynamic_refs: set[str] | None,
                               public_api_exports: set[str] | None) -> bool:
        simple_name = _simple_name(full_name)
        class_name = func_info.get('class_name')
        is_method = func_info.get('is_method', False)
        if _globals_introspection_hit(self._globals_introspection_mods, full_name, simple_name, is_method):
            return True
        if _name_shape_exempt(simple_name, is_method, class_name):
            return True
        module_name = func_info.get('module_name') or ''
        if class_name and simple_name in self._class_string_refs.get(
                (module_name, func_info.get('class_path') or class_name), ()):
            return True
        if not class_name and simple_name in self._class_body_refs.get(
                module_name, ()):
            return True
        if simple_name in self._module_string_refs.get(module_name, ()):
            return True
        if simple_name in self._module_container_refs.get(module_name, ()):
            return True
        if dynamic_refs and _dynamic_refs_hit(
                full_name, simple_name, dynamic_refs,
                allow_simple=func_info['allow_simple_ref']):
            return True
        return _public_api_hit(public_api_exports, full_name, simple_name, class_name)
_EXEMPT_SUFFIXES = ('Mixin', 'Base', 'ABC', 'Protocol', 'Error', 'Exception', 'Enum')
_EXEMPT_BASES = frozenset({
    'Enum', 'IntEnum', 'StrEnum', 'ABC', 'Protocol', 'Exception', 'BaseException',
})
@dataclass
class ClassBlindspot:
    class_name: str
    filepath: str
    start_line: int
    end_line: int
    blindspot_type: str
    severity: str
    method_count: int = 0
    instantiation_count: int = 0
    inheritors: list[str] = field(default_factory=list)
    message: str = ''
    suggestion: str = ''
    def to_dict(self) -> dict:
        return {
            'class_name': self.class_name,
            'filepath': self.filepath,
            'start_line': self.start_line,
            'end_line': self.end_line,
            'blindspot_type': self.blindspot_type,
            'severity': self.severity,
            'method_count': self.method_count,
            'instantiation_count': self.instantiation_count,
            'inheritors': self.inheritors,
            'message': self.message,
            'suggestion': self.suggestion,
        }
@dataclass
class ClassBlindspotReport:
    project_root: str
    total_classes: int = 0
    total_instantiations: int = 0
    total_references: int = 0
    blindspots: list[ClassBlindspot] = field(default_factory=list)
    def summary(self) -> dict:
        sev, by_type = blindspot_histograms(self.blindspots)
        return {
            'total_classes': self.total_classes,
            'total_instantiations': self.total_instantiations,
            'total_references': self.total_references,
            FIELD_TOTAL_BLINDSPOTS: len(self.blindspots),
            'by_severity': sev,
            'by_type': by_type,
        }
def _class_decorator_names(decorator_list: list[ast.expr]) -> list[str]:
    names: list[str] = []
    for dec in decorator_list:
        _name = _decorator_ref(dec).name
        if _name is not None:
            names.append(_name)
    return names
_NON_REGISTRAR_ATTRIBUTE_OWNERS = frozenset({
    'abc', 'contextlib', 'dataclasses', 'functools', 'typing',
    'typing_extensions',
})
def _is_external_registrar_decorator(dec) -> bool:
    info = _decorator_ref(dec)
    if (info.name in _REGISTRAR_DECORATORS
            or info.name in _WEB_HOOK_DECORATORS):
        return True
    return (info.is_attribute
            and info.owner not in _NON_REGISTRAR_ATTRIBUTE_OWNERS)
def _has_external_method_registrar(decorator_list: list[ast.expr]) -> bool:
    return any(_is_external_registrar_decorator(dec)
               for dec in decorator_list)
def _class_body_method_stats(class_node: ast.ClassDef,
                             runtime_inactive) -> tuple[int, bool]:
    total_methods = 0
    has_external_registrar = False
    for item in iter_module_scope_entities(class_node):
        if not isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if id(item) in runtime_inactive:
            continue
        total_methods += 1
        if _has_external_method_registrar(item.decorator_list):
            has_external_registrar = True
    return total_methods, has_external_registrar
def _absolute_import_path(import_path: str | None,
                          source_package: str | None) -> str | None:
    if not import_path or not import_path.startswith('.'):
        return import_path
    level = len(import_path) - len(import_path.lstrip('.'))
    parts = source_package.split('.') if source_package else []
    ascend = level - 1
    if ascend and ascend >= len(parts):
        return None
    if ascend:
        parts = parts[:-ascend]
    suffix = import_path[level:]
    if suffix:
        parts.extend(suffix.split('.'))
    return '.'.join(parts)
def _visible_import_path(name_resolver: ScopeNameResolver, node: ast.Name,
                         source_package: str | None) -> str | None:
    return _absolute_import_path(
        name_resolver.import_path(node), source_package)
def _scoped_bound_attr_pair(node: ast.Attribute,
                            name_resolver: ScopeNameResolver,
                            source_package: str | None) -> tuple[str, str] | None:
    value = node
    while isinstance(value, ast.Attribute):
        value = value.value
    if isinstance(value, ast.Call):
        value = value.func
        while isinstance(value, ast.Attribute):
            value = value.value
    if not isinstance(value, ast.Name):
        return None
    imported = _visible_import_path(name_resolver, value, source_package)
    if imported is None:
        return None
    return _bound_attr_pair(node, {value.id: imported})
def _qualified_class_match(qualified: str, known) -> bool:
    if not known:
        return False
    if qualified in known:
        return True
    return any(qualified.endswith('.' + candidate)
               or candidate.endswith('.' + qualified)
               for candidate in known)
def _record_test_refs_in_tree(tree: ast.AST, remaining: set, referenced: set,
                              *, source_package: str, qualified_names: dict,
                              name_resolver: ScopeNameResolver) -> None:
    for node in walk_nodes(tree):
        if not isinstance(getattr(node, 'ctx', None), ast.Load):
            continue
        if isinstance(node, ast.Name):
            qualified = _visible_import_path(
                name_resolver, node, source_package)
            if qualified is None:
                continue
            class_name = qualified.rsplit('.', 1)[-1]
        elif isinstance(node, ast.Attribute):
            pair = _scoped_bound_attr_pair(
                node, name_resolver, source_package)
            if pair is None:
                continue
            dotted, class_name = pair
            qualified = _qualify(dotted, class_name)
        else:
            continue
        if (class_name in remaining
                and _qualified_class_match(
                    qualified, qualified_names.get(class_name, ()))):
            referenced.add(class_name)
            remaining.discard(class_name)
def _local_class_names(tree: ast.AST) -> set[str]:
    return {node.name
            for node in iter_module_scope_nodes(tree, descend_classes=False)
            if isinstance(node, ast.ClassDef)}
def _self_preserving_class_write(node, name: str) -> bool:
    if not isinstance(node, (ast.Assign, ast.AnnAssign)):
        return False
    if not (isinstance(node.value, ast.Name) and node.value.id == name):
        return False
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    return any(isinstance(target, ast.Name) and target.id == name
               for target in targets)
def _module_class_write_events(tree: ast.AST, local_classes: set[str],
                               *, preserve_self_write: bool = True,
                               with_paths: bool = False) -> dict:
    events: dict[str, list[tuple[tuple[int, int], bool, bool]]] = {
        name: [] for name in local_classes}
    if not local_classes:
        return events
    parents = {id(child): parent for parent in walk_nodes(tree)
               for child in ast.iter_child_nodes(parent)}
    statement_suites = _statement_suite_index(tree) if with_paths else {}

    def _conditional_write(node) -> bool:
        parent = parents.get(id(node))
        while parent is not None and not isinstance(parent, ast.Module):
            if isinstance(parent, (
                    ast.If, ast.For, ast.AsyncFor, ast.While, ast.Match,
                    ast.Try, getattr(ast, 'TryStar', ast.Try))):
                return True
            parent = parents.get(id(parent))
        return False

    def _event(node, is_class: bool):
        event = (_rebinding_position(node), is_class,
                 _conditional_write(node))
        if not with_paths:
            return event
        return (*event, _suite_path(
            node, tree, parents, statement_suites))

    for node in iter_module_scope_nodes(tree, descend_classes=False):
        is_class = isinstance(node, ast.ClassDef)
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        names = {node.name} if is_class else set()
        if not is_class:
            collect_binding_names(node, names, include_imports=False)
        for name in names & local_classes:
            if (not is_class and preserve_self_write
                    and _self_preserving_class_write(node, name)):
                continue
            events[name].append(_event(node, is_class))
    for node in iter_module_scope_entities(tree):
        if not isinstance(node, ast.ClassDef) and node.name in local_classes:
            events[node.name].append(_event(node, False))
    return events
def _deferred_name_load_ids(tree: ast.AST) -> set[int]:
    deferred: set[int] = set()
    for scope in walk_nodes(tree):
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            roots = scope.body
        elif isinstance(scope, ast.Lambda):
            roots = (scope.body,)
        elif isinstance(scope, ast.GeneratorExp):
            roots = [scope.elt]
            roots.extend(generator.iter for generator in scope.generators[1:])
            roots.extend(generator.target for generator in scope.generators)
            roots.extend(condition for generator in scope.generators
                         for condition in generator.ifs)
        else:
            continue
        for root in roots:
            deferred.update(
                id(node) for node in walk_nodes(root)
                if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
            )
    return deferred
def _class_body_unbound_possible(events, node: ast.Name,
                                 read_path: tuple) -> bool:
    position = (node.lineno, node.col_offset)
    for event_position, _is_class, _conditional, event_path in events:
        if (event_position <= position
                and read_path[:len(event_path)] == event_path):
            return False
    return True


def _class_body_fallback_name_load_ids(tree, local_classes: set[str]) -> set[int]:
    if not local_classes:
        return set()
    comprehension_shadowed = _comprehension_shadow_name_ids(tree)
    visible: set[int] = set()
    for scope in walk_nodes(tree):
        if not isinstance(scope, ast.ClassDef):
            continue
        parents = {id(child): parent for parent in walk_nodes(scope)
                   for child in ast.iter_child_nodes(parent)}
        statement_suites = _statement_suite_index(scope)
        events = _module_class_write_events(
            scope, local_classes, preserve_self_write=False, with_paths=True)
        for node in iter_own_nodes(scope):
            if not (isinstance(node, ast.Name)
                    and isinstance(node.ctx, ast.Load)
                    and node.id in local_classes
                    and id(node) not in comprehension_shadowed):
                continue
            read_path = _suite_path(
                node, scope, parents, statement_suites)
            if _class_body_unbound_possible(
                    events.get(node.id, ()), node, read_path):
                visible.add(id(node))
    return visible


def _module_local_class_hit(node: ast.Name, local_classes: set[str],
                            module_name_load_ids: set[int],
                            write_events: dict, deferred_name_load_ids: set[int]) -> bool:
    if node.id not in local_classes or id(node) not in module_name_load_ids:
        return False
    events = write_events.get(node.id, ())
    if id(node) in deferred_name_load_ids:
        applicable = list(events)
    else:
        position = (node.lineno, node.col_offset)
        applicable = [event for event in events if event[0] <= position]
    possible_class_bindings: set[bool] = set()
    for _position, is_class, conditional in sorted(applicable):
        if conditional:
            possible_class_bindings.add(is_class)
        else:
            possible_class_bindings = {is_class}
    return True in possible_class_bindings
def _class_name_from_bound_name(node: ast.Name,
                                name_resolver: ScopeNameResolver,
                                local_classes: set[str], qualified_names: dict,
                                source_package: str | None,
                                module_name_load_ids: set[int],
                                class_write_events: dict,
                                deferred_name_load_ids: set[int]) -> str | None:
    qualified = _visible_import_path(name_resolver, node, source_package)
    if qualified is None:
        return (node.id if _module_local_class_hit(
            node, local_classes, module_name_load_ids,
            class_write_events, deferred_name_load_ids) else None)
    class_name = qualified.rsplit('.', 1)[-1]
    if _qualified_class_match(
            qualified, qualified_names.get(class_name, ())):
        return class_name
    return None
def _class_name_from_bound_attr(node: ast.Attribute,
                                name_resolver: ScopeNameResolver,
                                qualified_names: dict,
                                source_package: str | None) -> str | None:
    pair = _scoped_bound_attr_pair(node, name_resolver, source_package)
    if pair is None:
        return None
    dotted, class_name = pair
    if _qualified_class_match(
            _qualify(dotted, class_name),
            qualified_names.get(class_name, ())):
        return class_name
    return None
def _iter_target_chain(node: ast.AST) -> Iterator[ast.AST]:
    while True:
        yield node
        if not isinstance(node, (ast.Attribute, ast.Subscript)):
            return
        node = node.value
def _build_inheritors_index(class_bases: dict[str, list[str]]) -> dict[str, list[str]]:
    idx: dict[str, list[str]] = {}
    for child, bases in class_bases.items():
        for b in bases:
            idx.setdefault(b, []).append(child)
    return idx
def _static_exempt(class_name, info, bases) -> bool:
    if class_name.endswith(_EXEMPT_SUFFIXES):
        return True
    if any(b in _EXEMPT_BASES for b in bases):
        return True
    if class_name.startswith('_'):
        return True
    if 'dataclass' in info.get('decorators', []):
        return True
    return bool(info.get('has_external_registrar'))
def _context_exempt(sc, class_name, filepath, inheritors) -> bool:
    if class_name in sc._ambiguous_classes:
        return True
    if inheritors:
        return True
    if os.path.normpath(filepath).replace('\\', '/').split('/')[-1] == '__init__.py':
        return True
    return is_tests_domain_file(filepath, sc.project_root)
class ClassBlindspotScanner:
    def __init__(self, project_root: str=DEFAULT_PROJECT_ROOT, ctx=None) -> None:
        self.project_root = os.path.abspath(project_root)
        self._ctx = ctx
        self._reset_scan_state()
    def _reset_scan_state(self) -> None:
        self._class_defs: dict[str, dict] = {}
        self._class_qualified_names: dict[str, set[str]] = {}
        self._class_definition_count = 0
        self._class_bases: dict[str, list[str]] = defaultdict(list)
        self._instantiations: dict[str, int] = defaultdict(int)
        self._class_references: dict[str, int] = defaultdict(int)
        self._ambiguous_classes: set[str] = set()
        self._test_referenced: set[str] = set()
        self._py_files_snapshot: list[str] | None = None
        self._test_py_files_snapshot: list[str] | None = None
    def scan(self, call_graph=None, *, source_paths=None) -> ClassBlindspotReport:
        self._reset_scan_state()
        self._py_files_snapshot = collect_py_files(
            self.project_root, source_paths, ctx=self._ctx)
        self._collect_class_definitions()
        self._collect_instantiations()
        report = ClassBlindspotReport(project_root=self.project_root)
        report.total_classes = self._class_definition_count
        report.total_instantiations = sum(self._instantiations.values())
        report.total_references = sum(self._class_references.values())
        usage_counts = {
            name: (self._instantiations.get(name, 0)
                   + self._class_references.get(name, 0))
            for name in self._class_defs}
        _candidates = {name for name in self._class_defs
                       if usage_counts.get(name, 0) == 0}
        if _candidates:
            self._collect_test_references(_candidates)
        inheritors_idx = _build_inheritors_index(self._class_bases)
        for class_name, info in list(self._class_defs.items()):
            usage_count = usage_counts.get(class_name, 0)
            inheritors = inheritors_idx.get(class_name, [])
            if usage_count == 0 and class_name in self._test_referenced:
                continue
            blindspot = self._classify(
                class_name=class_name,
                info=info,
                usage_count=usage_count,
                inheritors=inheritors,
            )
            if blindspot:
                report.blindspots.append(blindspot)
        return report
    def _collect_class_definitions(self) -> None:
        for filepath, tree, _source in self._iter_trees(tests_domain=False):
            self._visit_class_defs(tree, filepath)
    def _visit_class_defs(self, tree: ast.AST, filepath: str) -> None:
        runtime_inactive = type_checking_body_node_ids(tree)
        for node in iter_module_scope_nodes(tree, descend_classes=False):
            if not isinstance(node, ast.ClassDef):
                continue
            if id(node) in runtime_inactive:
                continue
            self._register_class_def(node, filepath, runtime_inactive)
    def _register_class_def(self, node: ast.ClassDef, filepath: str,
                            runtime_inactive) -> None:
        self._class_definition_count += 1
        class_name = node.name
        self._class_qualified_names.setdefault(class_name, set()).add(
            _qualify(_dotted_module_name(filepath), class_name))
        bases = list(class_base_names(node))
        decorators = _class_decorator_names(node.decorator_list)
        class_attrs = _collect_class_attrs(node)
        total_methods, has_external_registrar = _class_body_method_stats(
            node, runtime_inactive)
        has_external_registrar = (
            has_external_registrar
            or _has_external_method_registrar(node.decorator_list))
        _prior = self._class_defs.get(class_name)
        if _prior is not None and _prior.get('file') != filepath:
            self._ambiguous_classes.add(class_name)
        self._class_defs[class_name] = {
            'file': filepath,
            'line': node.lineno,
            'end_line': node.end_lineno or node.lineno,
            'decorators': decorators,
            'class_attributes': class_attrs,
            'has_external_registrar': has_external_registrar,
            'total_methods': total_methods,
        }
        _known_bases = self._class_bases[class_name]
        self._class_bases[class_name] = _known_bases + [
            b for b in bases if b not in _known_bases]
    def _iter_trees(self, *, tests_domain: bool) -> Iterator[tuple[str, ast.AST, str]]:
        for filepath in self._get_py_files():
            if is_tests_domain_file(filepath, self.project_root) != tests_domain:
                continue
            loaded = load_module(filepath, self._ctx)
            if loaded is None:
                continue
            source, tree = loaded
            rel = _rel_to_root(self.project_root, filepath)
            if rel is None:
                continue
            yield rel, tree, source
    def _get_py_files(self) -> list[str]:
        if self._py_files_snapshot is None:
            self._py_files_snapshot = collect_py_files(
                self.project_root, ctx=self._ctx)
        return self._py_files_snapshot
    def _collect_instantiations(self) -> None:
        for filepath, tree, source in self._iter_trees(tests_domain=False):
            self._visit_instantiations(tree, filepath, source)
    def _get_test_py_files(self) -> list[str]:
        if self._test_py_files_snapshot is None:
            self._test_py_files_snapshot = [
                fp for fp in collect_py_files(
                    self.project_root, None, ctx=self._ctx)
                if is_tests_domain_file(fp, self.project_root)
            ]
        return self._test_py_files_snapshot
    def _collect_test_references(self, candidates: set[str]) -> None:
        remaining = set(candidates)
        if not remaining:
            return
        for filepath in self._get_test_py_files():
            if not remaining:
                break
            loaded = load_module(filepath, self._ctx)
            if loaded is None:
                continue
            source, tree = loaded
            rel = _rel_to_root(self.project_root, filepath)
            if rel is None:
                continue
            _record_test_refs_in_tree(
                tree, remaining, self._test_referenced,
                source_package=_package_name_from_rel(rel),
                qualified_names=self._class_qualified_names,
                name_resolver=ScopeNameResolver(source, filepath, tree, set()))
    def _visit_instantiations(self, tree: ast.AST, filepath=None,
                              source: str = '') -> None:
        source_package = (_package_name_from_rel(filepath)
                          if filepath is not None else None)
        name_resolver = ScopeNameResolver(source, filepath or '', tree, set())
        module_name_load_ids = _module_scope_name_load_ids(tree)
        deferred_name_load_ids = _deferred_name_load_ids(tree)
        local_classes = _local_class_names(tree)
        module_name_load_ids |= _class_body_fallback_name_load_ids(
            tree, local_classes)
        class_write_events = _module_class_write_events(tree, local_classes)
        instantiation_target_ids: set[int] = set()
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            while isinstance(func, ast.Subscript):
                func = func.value
            if isinstance(func, ast.Name):
                class_name = _class_name_from_bound_name(
                    func, name_resolver, local_classes,
                    self._class_qualified_names, source_package,
                    module_name_load_ids, class_write_events,
                    deferred_name_load_ids)
            elif isinstance(func, ast.Attribute):
                class_name = _class_name_from_bound_attr(
                    func, name_resolver, self._class_qualified_names,
                    source_package)
            else:
                continue
            if class_name in self._class_defs:
                self._instantiations[class_name] += 1
                instantiation_target_ids.update(
                    id(target) for target in _iter_target_chain(node.func))
        self._collect_class_object_references(
            tree, name_resolver, local_classes, source_package,
            module_name_load_ids, class_write_events, deferred_name_load_ids,
            instantiation_target_ids)
        self._collect_init_reexport_references(tree, filepath, source_package)
    def _collect_init_reexport_references(self, tree: ast.AST, filepath,
                                          source_package: str | None) -> None:
        if filepath is None or os.path.basename(filepath) != '__init__.py':
            return
        for node in walk_nodes(tree):
            if not isinstance(node, ast.ImportFrom):
                continue
            base = _absolute_import_path(node.module, source_package)
            if not base:
                continue
            for alias in node.names:
                if alias.name == '*':
                    self._collect_star_reexport_references(base)
                    continue
                dotted = _qualify(base, alias.name)
                class_name = dotted.rsplit('.', 1)[-1]
                if _qualified_class_match(
                        dotted, self._class_qualified_names.get(class_name, ())):
                    self._class_references[class_name] += 1
    def _collect_star_reexport_references(self, base: str) -> None:
        for class_name, known in self._class_qualified_names.items():
            if not known:
                continue
            for candidate in known:
                module = candidate.rsplit('.', 1)[0]
                if (module == base or module.endswith('.' + base)
                        or base.endswith('.' + module)):
                    self._class_references[class_name] += 1
                    break
    def _collect_class_object_references(
            self, tree: ast.AST, name_resolver: ScopeNameResolver,
            local_classes: set[str], source_package: str | None,
            module_name_load_ids: set[int], class_write_events: dict,
            deferred_name_load_ids: set[int],
            instantiation_target_ids: set[int]) -> None:
        base_exprs = {
            id(target) for node in walk_nodes(tree)
            if isinstance(node, ast.ClassDef)
            for base in node.bases
            for target in _iter_target_chain(base)
        }
        for node in walk_nodes(tree):
            if not (isinstance(node, ast.Name)
                    and isinstance(node.ctx, ast.Load)):
                continue
            if id(node) in instantiation_target_ids or id(node) in base_exprs:
                continue
            class_name = _class_name_from_bound_name(
                node, name_resolver, local_classes,
                self._class_qualified_names, source_package,
                module_name_load_ids, class_write_events,
                deferred_name_load_ids)
            if class_name in self._class_defs:
                self._class_references[class_name] += 1
        for node in walk_nodes(tree):
            if not (isinstance(node, ast.Attribute)
                    and isinstance(node.ctx, ast.Load)):
                continue
            if id(node) in instantiation_target_ids or id(node) in base_exprs:
                continue
            class_name = _class_name_from_bound_attr(
                node, name_resolver, self._class_qualified_names,
                source_package)
            if class_name is not None:
                self._class_references[class_name] += 1
    @staticmethod
    def _orphan_entry(class_name: str, info: dict, method_count: int,
                      inheritors: list[str], *, severity: str,
                      message: str) -> ClassBlindspot:
        return ClassBlindspot(
            class_name=class_name,
            filepath=info['file'],
            start_line=info['line'],
            end_line=info.get('end_line', info['line']),
            blindspot_type='orphan',
            severity=severity,
            method_count=method_count,
            instantiation_count=0,
            inheritors=inheritors,
            message=message,
            suggestion='检查是否需要删除该类，或为其添加入口调用代码')
    def _classify(self, class_name, info, usage_count, inheritors) -> ClassBlindspot | None:
        if usage_count:
            return None
        bases = self._class_bases.get(class_name, [])
        if _static_exempt(class_name, info, bases):
            return None
        if _context_exempt(self, class_name, info['file'], inheritors):
            return None
        method_count = info.get('total_methods', 0)
        if method_count == 0:
            if info.get('class_attributes', []):
                return None
            return self._orphan_entry(
                class_name, info, method_count, inheritors, severity='low',
                message=f'类 {class_name} 未定义任何方法或属性且从未被实例化')
        return self._orphan_entry(
            class_name, info, method_count, inheritors, severity='medium',
            message=f'类 {class_name} 定义了 {method_count} 个方法但从未被实例化')
def _run_scanner_job(scanner_factory: Callable, *scan_args, **scan_kwargs):
    return scanner_factory().scan(*scan_args, **scan_kwargs)
def build_layer_scan_jobs(project_root, *, ctx, source_paths, coverage_hook,
                          call_graph, lazy_modules) -> dict[str, Callable[[], object]]:
    sync_shared_ast_cache(ctx)
    return {
        "script": partial(
            _run_scanner_job,
            partial(ScriptBlindspotScanner, project_root, ctx=ctx),
            source_paths, coverage_hook, call_graph),
        "module": partial(
            _run_scanner_job,
            partial(ModuleBlindspotScanner, project_root, ctx=ctx),
            source_paths, call_graph, lazy_modules=lazy_modules),
        "func": partial(
            _run_scanner_job,
            partial(FunctionBlindspotScanner, project_root, ctx=ctx),
            source_paths, call_graph, coverage_hook),
        "class": partial(
            _run_scanner_job,
            partial(ClassBlindspotScanner, project_root, ctx=ctx),
            call_graph=call_graph, source_paths=source_paths),
    }
def run_layer14_parallel(project_root, ctx, source_paths, coverage_hook,
                         call_graph, lazy_modules) -> dict:
    logger.info("[盲区] 1-4/7 并行扫描 (脚本/模块/函数/类)...")
    scan_jobs = build_layer_scan_jobs(
        project_root, ctx=ctx, source_paths=source_paths,
        coverage_hook=coverage_hook, call_graph=call_graph,
        lazy_modules=lazy_modules)
    layer_results = {}
    with _cf.ThreadPoolExecutor(max_workers=len(scan_jobs)) as executor:
        futures = {executor.submit(job): name
                   for name, job in scan_jobs.items()}
        for future in _cf.as_completed(futures):
            name = futures[future]
            try:
                layer_results[name] = future.result()
            except LAYER_DEGRADE_EXC_WITH_IMPORT as e:
                logger.warning("%s层扫描失败(该层发现归零): %s", name, e, exc_info=True)
                layer_results[name] = None
    return layer_results
def pause_coverage_for_analysis(coverage_hook) -> bool:
    _was_paused = bool(getattr(coverage_hook, "_paused", False))
    _pause_fn = getattr(coverage_hook, "pause", None)
    if not callable(_pause_fn) or _was_paused:
        return False
    try:
        _pause_fn()
    except (OSError, RuntimeError, AttributeError) as _p_e:
        logger.debug("Layer5 分析前暂停 coverage 失败(降级继续): %s", _p_e)
        return False
    return True
def resume_coverage_after_analysis(coverage_hook, paused_by_us: bool) -> None:
    if not paused_by_us:
        return
    _resume_fn = getattr(coverage_hook, "resume", None)
    if not callable(_resume_fn):
        return
    try:
        _resume_fn()
    except (OSError, RuntimeError, AttributeError) as _r_e:
        logger.debug("分析后恢复 coverage 失败(降级继续): %s", _r_e)
def _ensure_coverage_hook(coverage_hook, source_paths, project_root):
    if coverage_hook is not None:
        return coverage_hook
    logger.debug("[盲区] 5/7 代码层扫描: 自动安装运行时守卫")
    try:
        hook = ensure_coverage_hook(
            coverage_hook, source_paths or [project_root], project_root)
    except (OSError, RuntimeError, ImportError, AttributeError, TypeError) as exc:
        logger.warning("自动安装运行时守卫失败: %s", exc)
        return None
    if hook is None:
        logger.warning("自动安装运行时守卫失败: 安装后 coverage_hook 仍为 None")
    return hook
def _analyze_code_layer(coverage_hook, source_paths, project_root, report, ctx):
    analyzer = BlindspotAnalyzer(coverage_hook, project_root=project_root, ctx=ctx)
    paused_by_us = pause_coverage_for_analysis(coverage_hook)
    try:
        code_reports = analyzer.analyze(source_paths or [project_root])
    finally:
        resume_coverage_after_analysis(coverage_hook, paused_by_us)
    report.add_code_blindspots(code_reports)
    code_metrics = report.metrics.setdefault("code", {})
    code_metrics["file_reports"] = [r.to_dict() for r in code_reports]
    code_metrics["critical_blocks"] = sum(len(r.get_critical()) for r in code_reports)
    return code_reports
def _log_code_layer_summary(code_reports, report) -> None:
    code_metrics = report.metrics.get("code", {})
    fp_in_code = code_metrics.get("potential_false_positives", 0)
    fp_note = f", {fp_in_code}个疑似误报" if fp_in_code > 0 else ""
    logger.info(
        f"       代码: 分析{len(code_reports)}个文件, "
        f"{code_metrics.get('total_files_with_blindspots', 0)}个文件有盲区, "
        f"共{code_metrics['total_blocks']}个盲区块, "
        f"死代码块={code_metrics['dead_code_blocks']}, "
        f"critical={code_metrics['critical_blocks']}{fp_note}")
def _coverage_runtime_file_count(coverage_hook) -> int:
    try:
        payload = getattr(coverage_hook, "data", None)
        payload = payload() if callable(payload) else payload
    except Exception as exc:  # noqa: BLE001 — 第三方钩子属性异常不得中断主链
        logger.debug("覆盖率数据读取失败(按有数据保守处理): %s", exc)
        return -1
    if not isinstance(payload, dict):
        return -1
    files = payload.get("files")
    if files is None and not payload:
        return 0
    if not isinstance(files, dict):
        return -1
    return len(files)
def run_code_layer_scan(coverage_hook, source_paths, project_root, report, ctx=None):
    if source_paths is not None and not source_paths:
        logger.info("[盲区] 5/7 代码层扫描... 跳过（诊断范围过滤后为空）")
        return coverage_hook
    coverage_hook = _ensure_coverage_hook(coverage_hook, source_paths, project_root)
    if coverage_hook is None:
        logger.info("[盲区] 5/7 代码层扫描... 跳过（无法安装运行时守卫）")
        return coverage_hook
    if _coverage_runtime_file_count(coverage_hook) == 0:
        _code_metrics = report.metrics.setdefault("code", {})
        _code_metrics["skipped_reason"] = "no_runtime_coverage"
        _code_metrics["coverage_available"] = False
        logger.info(
            "[盲区] 5/7 代码层扫描... 跳过（无运行时覆盖率数据，未执行块不可判定）")
        return coverage_hook
    logger.info("[盲区] 5/7 代码层扫描...")
    try:
        code_reports = _analyze_code_layer(
            coverage_hook, source_paths, project_root, report, ctx)
        _log_code_layer_summary(code_reports, report)
    except LAYER_DEGRADE_EXC_WITH_IMPORT as e:
        logger.warning("代码层扫描失败(该层发现归零): %s", e, exc_info=True)
        logger.info(f"       失败: {e}")
    return coverage_hook
def _business_chain_applicable(report, call_graph) -> bool:
    return call_graph is not None and len(report.entries) > 0
def _log_business_chain_skip(report, call_graph) -> None:
    if call_graph is None and len(report.entries) == 0:
        logger.info("[盲区] 6/7 业务链活性验证... 跳过（需调用图与盲区条目）")
    elif call_graph is None:
        logger.info("[盲区] 6/7 业务链活性验证... 跳过（需调用图）")
    else:
        logger.info("[盲区] 6/7 业务链活性验证... 跳过（无盲区条目）")
def _business_chain_kwargs(report, project_root, call_graph, source_paths, ctx) -> dict:
    return {
        "project_root": project_root,
        "call_graph": call_graph,
        "blindspot_entries": [
            e.to_dict() if hasattr(e, "to_dict") else e
            for e in report.entries
        ],
        "source_paths": source_paths,
        "ctx": ctx,
    }
def _diagnose_business_chain(report, project_root, call_graph, source_paths, ctx):
    kwargs = _business_chain_kwargs(
        report, project_root, call_graph, source_paths, ctx)
    if is_library_project(project_root):
        return diagnose_business_flows_enhanced(**kwargs, skill_type="library")
    return diagnose_business_flows(**kwargs)
def run_business_chain_layer(report, project_root, call_graph, source_paths,
                             ctx) -> None:
    if not _business_chain_applicable(report, call_graph):
        _log_business_chain_skip(report, call_graph)
        return
    logger.info("[盲区] 6/7 业务链活性验证...")
    try:
        biz_report = _diagnose_business_chain(
            report, project_root, call_graph, source_paths, ctx)
        report.business_flow = biz_report
        logger.info(
            f'       业务链: {len(biz_report.chains)}条, '
            f'救回盲区={biz_report.blindspots_rescued}, '
            f'确认盲区={biz_report.blindspots_confirmed}')
    except LAYER_DEGRADE_EXC_WITH_IMPORT as e:
        logger.warning("业务链活性验证跳过(该层数据缺失): %s", e)
        logger.info(f"       跳过: {e}")
def run_layers_5_to_76(report, project_root, ctx, source_paths, coverage_hook,
                       call_graph, include_code_blindspots: bool = DEFAULT_INCLUDE_CODE_BLINDSPOTS,
                       before_clustering=None, after_code_scan=None):
    if include_code_blindspots:
        coverage_hook = run_code_layer_scan(
            coverage_hook, source_paths, project_root, report,
            ctx=ctx,
        )
        if after_code_scan is not None:
            after_code_scan()
    else:
        logger.info("[盲区] 5/7 代码层扫描... 已禁用")
    paused_by_us = (
        pause_coverage_for_analysis(coverage_hook)
        if coverage_hook is not None else False)
    try:
        run_business_chain_layer(
            report, project_root, call_graph, source_paths, ctx)
        logger.info("[盲区] 7/7 异常传播路径分析...")
        exception_analysis = run_exception_layer(
            report, project_root, call_graph, source_paths, ctx)
        run_cross_validation_layer(
            report, coverage_hook, call_graph, project_root, ctx,
            library_probe=is_library_project)
        if before_clustering is not None:
            before_clustering()
        report.apply_clustering(call_graph, diag_ctx=ctx)
        return exception_analysis
    finally:
        resume_coverage_after_analysis(coverage_hook, paused_by_us)

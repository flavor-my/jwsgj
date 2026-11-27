from __future__ import annotations

import ast
import logging
import math
import os
from collections import defaultdict, deque
from dataclasses import dataclass, field
from typing import Any, ClassVar, NamedTuple, Protocol

from jwsgj.diag_callgraph_facts import (
    DECORATOR_CLOSURE_NAMES,
    MAGIC_METHODS,
    CallEdge,
    FunctionNode,
    _as_name_tuple,
    _break_identity,
    _caller_is_test,
    _caller_node_key,
    _cross_skill_file_buckets,
    _declared_name,
    _FunctionTable,
    _has_decorator,
    _is_cross_file_call,
    _is_exported_member,
    _is_package_init_file,
    _path_text,
    _qualify_module_member,
    _simple_name,
    assignment_name_index,
    build_exemption_classification,
    check_framework_decorators,
    check_source_markers,
    class_method_names,
    collect_cross_skill_names,
    count_project_py_files,
    functions_ending_with,
    is_entry_point_name,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_CALLABLES,
    NON_PROJECT_TOP_MODULES,
    class_scope,
    is_dunder_name,
    is_self_caller_name,
    iter_arg_nodes,
    module_postpones_annotations,
    normalize_node_str,
    normalize_torn_name,
    path_to_dotted_module,
    pkg_root_name,
    strip_pkg_root,
)
from jwsgj.diag_types_normalize import normalize_severity_rank
from jwsgj.diag_types_vocab import (
    FIELD_POTENTIAL_FP,
    FIELD_TOTAL_FUNCTIONS,
    POLYMORPHIC_METHODS,
    SEVERITY_RANK,
    WIRING_DECLARATION_ATTR,
)
from jwsgj.prevention_scope_facts import walk_nodes

_logger = logging.getLogger(__name__)
__all__ = [
    'CallGraph',
    'CallGraphBuilderProtocol',
    'CallGraphStats',
    'GraphAnalyses',
    'LibraryProfile',
    'append_synthetic_edge',
    'build_callgraph_judgments',
    'build_graph_analyses',
    'build_weight_context',
    'callers_for_fnode',
    'check_side_effects',
    'detect_non_impacting_control_deps',
    'detect_path_sensitive_type_constraints',
    'external_callers_for_fnode',
    'find_orphans',
    'infer_type_annotation_reachability',
    'log_call_chain_summary',
]
@dataclass
class CallGraph:
    project_root: str = "."
    library_profile: LibraryProfile | None = None
    functions: dict[str, FunctionNode] = field(default_factory=_FunctionTable)
    calls: list[CallEdge] = field(default_factory=list)
    function_references: list[CallEdge] = field(default_factory=list)
    imports: dict[str, dict[str, str]] = field(default_factory=lambda: defaultdict(dict))
    callers: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    orphans: list[FunctionNode] = field(default_factory=list)
    external_deps: set[str] = field(default_factory=set)
    class_methods: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    dataclass_classes: set[str] = field(default_factory=set)
    dataclass_options: dict[str, dict[str, bool]] = field(default_factory=dict)
    class_inheritance: dict[str, list[str]] = field(default_factory=dict)
    class_files: dict[str, str] = field(default_factory=dict)
    singledispatch_funcs: set[str] = field(default_factory=set)
    singledispatch_register: dict[str, list[str]] = field(default_factory=lambda: defaultdict(list))
    cross_skill_imports: Any | None = None
    non_code_references: set[str] = field(default_factory=set)
    orphan_confidence_adjustments: dict[str, int] = field(default_factory=dict)
    orphan_caller_base: dict[str, int] = field(default_factory=dict)
    import_graph: dict[str, str] = field(default_factory=dict)
    dynamic_imports: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    syntax_errors: list[dict] = field(default_factory=list)
    global_all_exports: set[str] = field(default_factory=set)
    _is_lib_cache: bool | None = field(default=None)
    _break_points_cache: list[dict] | None = field(default=None)
    _return_type_store: dict[str, str | None] = field(default_factory=dict)
    _instance_attr_store: dict[str, str | None] = field(default_factory=dict)
    _file_lines_cache: dict[str, list] = field(default_factory=dict)
    _cross_skill_names_cache: set | None = field(default=None)
    _py_files_count_cache: int | None = field(default=None)
    _pkg_root_cache: str | None = field(default=None)
    _class_method_index_cache: tuple | None = field(default=None)
    def __post_init__(self) -> None:
        self.analyses = build_graph_analyses(self)
    def invalidate_analysis_caches(self) -> None:
        self._break_points_cache = None
        self._is_lib_cache = None
        self._cross_skill_names_cache = None
        self._py_files_count_cache = None
        self._pkg_root_cache = None
        self._class_method_index_cache = None
        self._file_lines_cache.clear()
        self.analyses.exemption.invalidate_caches()
class CallGraphBuilderProtocol(Protocol):
    graph: CallGraph
    project_root: str
    _import_aliases: dict[str, dict[str, str]]
    _plain_imports: dict[str, dict[str, set[str]]]
    _reexport_chain: dict[str, str]
    _file_symbols: dict[str, dict[str, FunctionNode]]
    _symbol_owner_index: dict[str, str] | None
    def get_source_and_ast(self, filepath: str) -> tuple[str | None, ast.Module | None]:
        ...
    def collect_build_scope_files(self) -> list[str]:
        ...
    def collect_callgraph_files(self) -> list[str]:
        ...
def append_synthetic_edge(graph: CallGraph, *, caller_func: str,
                           caller_file: str, callee_fqn: str,
                           line: int = 0, args_count: int = 0,
                           is_self_call: bool = False,
                           caller_record: str | None = None,
                           missing_ok: bool = True) -> bool:
    callee_fnode = graph.functions.get(callee_fqn)
    if callee_fnode is None:
        if missing_ok:
            return False
        raise KeyError(callee_fqn)
    graph.calls.append(CallEdge(
        caller_file=caller_file,
        caller_func=caller_func,
        callee_func=callee_fqn,
        callee_file=callee_fnode.filepath,
        line=line,
        is_external=False,
        is_self_call=is_self_call,
        args_count=args_count,
    ))
    graph.callers[callee_fqn].add(caller_record or caller_func)
    graph.invalidate_analysis_caches()
    return True
class CallGraphStats(NamedTuple):
    total: int
    public: int
    cross: int
    orphans: int
    breaks: int
    total_calls: int
    is_lib: bool
    syn_err: int
    ext_skills: int
    ext_files: int
def build_callgraph_judgments(call_graph, stats: CallGraphStats) -> dict:
    judgments = {
        "break_points": _judge_break_points(call_graph, stats),
        "orphans": _judge_orphans(stats),
        "cross_file_calls": _judge_cross_file_calls(call_graph, stats),
    }
    if stats.public > 0:
        judgments["public_coverage"] = _judge_public_coverage(call_graph, stats)
    if stats.syn_err > 0:
        judgments["syntax_errors"] = {"status": "fail",
                                      "label": f"{stats.syn_err} 个文件有语法错误"}
    if stats.ext_skills > 0 or stats.ext_files > 0:
        judgments["cross_skill"] = {
            "status": "info",
            "label": f"被 {stats.ext_skills} 个外部技能引用（{stats.ext_files} 个文件）"
        }
    return judgments
_P3_SEVERITY_RANK = SEVERITY_RANK["P3"]
def _is_severe_break(item: Any) -> bool:
    severity = item.get("severity") if isinstance(item, dict) else None
    return normalize_severity_rank(severity) < _P3_SEVERITY_RANK
def _judge_break_points(call_graph, stats: CallGraphStats) -> dict:
    breaks = stats.breaks
    severe = sum(
        1 for item in call_graph.analyses.breakpoints.get_break_points()
        if _is_severe_break(item))
    advisory = max(breaks - severe, 0)
    if stats.is_lib:
        if severe == 0:
            return {"status": "pass",
                    "label": f"{breaks} 个断裂点（库型技能，均为 P3 建议级，正常）"}
        return {"status": "warn" if severe <= 5 else "fail",
                "label": f"{severe} 个严重断裂点（库型技能，"
                         f"P3 建议级 {advisory} 个未计入）"}
    if severe == 0:
        if breaks:
            return {"status": "pass",
                    "label": f"无严重断裂点（P3 建议级 {breaks} 个未计入）"}
        return {"status": "pass", "label": "无断裂"}
    if severe <= 3:
        return {"status": "warn", "label": f"{severe} 个断裂点（可接受）"}
    return {"status": "fail", "label": f"{severe} 个断裂点（需修复）"}
def _judge_orphans(stats: CallGraphStats) -> dict:
    orphans = stats.orphans
    public = stats.public
    if orphans == 0:
        return {"status": "pass", "label": "无孤立函数"}
    if stats.is_lib:
        if orphans <= public * 0.50:
            pct = orphans * 100 // max(public, 1)
            return {"status": "pass",
                    "label": f"{orphans} 个孤立函数（库型技能，{pct}%公开函数，正常）"}
        if orphans <= public * 0.75:
            return {"status": "warn",
                    "label": f"{orphans} 个孤立函数（库型技能，偏高但仍可接受）"}
        return {"status": "info",
                "label": f"{orphans} 个孤立函数（库型技能，多数为公开 API 或类方法，"
                         f"正常现象）"}
    if orphans <= public * 0.05:
        return {"status": "warn", "label": f"{orphans} 个孤立函数（<5%公开函数）"}
    pct_label = (f"占公开函数{orphans * 100 / public:.0f}%"
                  if public else "无公开函数，孤立全为私有")
    return {"status": "fail",
            "label": f"{orphans} 个孤立函数（{pct_label}，超出5%阈值）"}
def _judge_cross_file_calls(call_graph, stats: CallGraphStats) -> dict:
    comparable_calls = sum(
        1 for edge in call_graph.calls
        if _path_text(getattr(edge, 'caller_file', None))
        and _path_text(getattr(edge, 'callee_file', None)))
    if comparable_calls > 0 and stats.total > 1:
        cross_ratio = stats.cross / comparable_calls
        func_paths = {_graph_filepath_key(call_graph, getattr(f, "filepath", ""))
                      for f in call_graph.functions.values()}
        func_paths.discard("")
        total_files = len(func_paths)
        if total_files == 0:
            count_fn = getattr(
                call_graph.analyses.summary, "_count_py_files", None)
            total_files = (count_fn() if callable(count_fn)
                           else count_project_py_files(
                               getattr(call_graph, "project_root", ".")))
        if total_files <= 5:
            return {"status": "pass",
                    "label": f"跨文件调用率 {cross_ratio:.1%}"
                             f"（{total_files}文件技能，正常）"}
        if cross_ratio >= 0.1:
            return {"status": "pass", "label": f"跨文件调用率 {cross_ratio:.1%}"}
        if cross_ratio >= 0.02:
            return {"status": "warn", "label": f"跨文件调用率偏低 {cross_ratio:.1%}"}
        return {"status": "fail", "label": f"跨文件调用率极低 {cross_ratio:.1%}"}
    return {"status": "info", "label": "样本不足，无法判定"}
def _judge_public_coverage(call_graph, stats: CallGraphStats) -> dict:
    called_public = sum(
        1 for fq, fnode in call_graph.functions.items()
        if fnode.is_public
        and any(not is_self_caller_name(caller, fq)
                for caller in (call_graph.callers.get(fq) or ())))
    pub_cov = called_public / stats.public
    if pub_cov >= 0.5:
        return {"status": "pass", "label": f"公开函数覆盖率 {pub_cov:.1%}",
                "coverage": round(pub_cov, 4)}
    if pub_cov >= 0.25:
        return {"status": "warn", "label": f"公开函数覆盖率偏低 {pub_cov:.1%}",
                "coverage": round(pub_cov, 4)}
    return {"status": "fail", "label": f"公开函数覆盖率低 {pub_cov:.1%}",
            "coverage": round(pub_cov, 4)}
def log_call_chain_summary(project_root: str, graph) -> None:
    break_points = graph.analyses.breakpoints.get_break_points()
    summary = graph.analyses.summary.summary()
    _logger.info("\n%s", "=" * 60)
    _logger.info("[jwsgj] 调用链诊断: %s", project_root)
    _logger.info("%s", "=" * 60)
    _logger.info("  总函数数: %s", summary.get(FIELD_TOTAL_FUNCTIONS))
    _logger.info("  公开函数: %s", summary.get("public_functions"))
    _logger.info("  总调用数: %s", summary.get("total_calls"))
    _logger.info("  跨文件调用: %s", summary.get("cross_file_calls"))
    _logger.info("  外部依赖: %s（总计 %s，已排除标准库）",
                 summary.get("external_deps"),
                 summary.get("external_deps_total"))
    _logger.info("  孤立函数: %s", summary.get("orphans"))
    _logger.info("  断裂点: %s", summary.get("break_points"))
    judgments = summary.get("judgments", {})
    if judgments:
        status_map = {"pass": "✓ 通过", "warn": "⚠ 警告", "fail": "✗ 异常", "info": "○ 信息"}
        _logger.info("\n  ── 判定 ──")
        for j in judgments.values():
            icon = status_map.get(j.get("status"), "?")
            _logger.info("  %s %s", icon, j.get("label"))
    if break_points:
        _logger.info("\n  断裂点详情:")
        for bp in break_points:
            sev = str(bp.get("severity", "?")).upper()
            _logger.info("    [%s] %s: %s", sev, bp.get("type"), str(bp.get("message", ""))[:100])
_WEIGHT_BANDS: tuple[tuple[float, str], ...] = (
    (0.9, "core_business"),
    (0.5, "well_connected"),
    (0.2, "loosely_connected"),
)
def _weight_band(weight: float) -> str:
    for lower_bound, label in _WEIGHT_BANDS:
        if weight >= lower_bound:
            return label
    return "orphan"
def build_weight_context(functions) -> dict:
    weights = [f.caller_weight for f in functions.values()]
    if not weights:
        return {"average_weight": 0.0, "distribution": {}}
    weight_dist = {label: 0 for _, label in _WEIGHT_BANDS}
    weight_dist["orphan"] = 0
    for weight in weights:
        weight_dist[_weight_band(weight)] += 1
    return {
        "average_weight": round(sum(weights) / len(weights), 3),
        "distribution": weight_dist,
    }
class _ConditionalDefCollector(ast.NodeVisitor):
    def __init__(self, rel_path, conditional_funcs):
        self._rel_path = rel_path
        self._conditional_funcs = conditional_funcs
        self._current_class = None
    def visit_ClassDef(self, node):
        # 与 _DefCollector 同口径：_current_class 保存点分类路径，
        # 使条件定义限定名与 FunctionNode.name 一致（class_scope 只写简单类名）。
        parent_path = self._current_class or ""
        with class_scope(self, node):
            self._current_class = (f"{parent_path}.{node.name}"
                                   if parent_path else node.name)
            self.generic_visit(node)
    def visit_FunctionDef(self, _node):  # jwsgj:suppress empty_function
        pass
    def visit_AsyncFunctionDef(self, _node):  # jwsgj:suppress empty_function
        pass
    def visit_If(self, node):
        self._register_conditional_defs(node.body)
        self._register_conditional_defs(node.orelse)
        self.generic_visit(node)
    def visit_ExceptHandler(self, node):
        self._register_conditional_defs(node.body)
        self.generic_visit(node)
    def visit_Try(self, node):
        for stmts in (node.body, node.orelse):
            self._register_conditional_defs(stmts)
        self.generic_visit(node)
    visit_TryStar = visit_Try
    def visit_For(self, node):
        self._register_conditional_defs(node.body)
        self._register_conditional_defs(node.orelse)
        self.generic_visit(node)
    visit_AsyncFor = visit_For
    def visit_While(self, node):
        self._register_conditional_defs(node.body)
        self._register_conditional_defs(node.orelse)
        self.generic_visit(node)
    def visit_Match(self, node):
        for case in node.cases:
            self._register_conditional_defs(case.body)
        self.generic_visit(node)
    def _register_conditional_defs(self, stmts, prefix=None):
        for sub in stmts:
            if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                owner = self._current_class if prefix is None else prefix
                qualified = f"{owner}.{sub.name}" if owner else sub.name
                self._conditional_funcs.add((self._rel_path, qualified))
            elif isinstance(sub, ast.ClassDef):
                owner = self._current_class if prefix is None else prefix
                nested = f"{owner}.{sub.name}" if owner else sub.name
                self._register_conditional_defs(sub.body, nested)
def detect_non_impacting_control_deps(builder: Any) -> int:
    graph = builder.graph
    conditional_funcs = set()
    root = _path_text(getattr(builder, 'project_root', '')) or "."
    for filepath in builder.collect_build_scope_files():
        _source, tree = builder.get_source_and_ast(filepath)
        if tree is None:
            continue
        rel_path = os.path.relpath(filepath, root).replace("\\", "/")
        _ConditionalDefCollector(rel_path, conditional_funcs).visit(tree)
    adjusted = 0
    for orphan in graph.orphans:
        orphan_name = normalize_node_str(getattr(orphan, 'name', ''))
        orphan_rel = _orphan_rel_path(builder, orphan)
        if (orphan_rel, orphan_name) not in conditional_funcs:
            continue
        if _downgrade_orphan(orphan, '_non_impacting_dep', '非影响性控制依赖',
                             path=orphan_rel):
            adjusted += 1
    return adjusted
def _orphan_rel_path(builder, orphan) -> str:
    orphan_file = _path_text(getattr(orphan, 'filepath', ''))
    if not orphan_file:
        return ''
    root = _path_text(getattr(builder, 'project_root', '')) or "."
    abs_path = (orphan_file if os.path.isabs(orphan_file)
                else os.path.normpath(os.path.join(root, orphan_file)))
    return os.path.relpath(abs_path, root).replace("\\", "/")
def _fnode_graph_key(graph, fnode) -> str:
    fp = _path_text(getattr(fnode, 'filepath', ''))
    name = getattr(fnode, 'name', '')
    if fp and isinstance(name, str):
        root = _path_text(getattr(graph, 'project_root', ''))
        if root and os.path.isabs(fp):
            try:
                fp = os.path.relpath(fp, root)
            except (OSError, ValueError):  # jwsgj:silent-ok
                pass
        key = _qualify_module_member(path_to_dotted_module(fp), name)
        if graph.functions.get(key) is fnode:
            return key
    for key, fn in graph.functions.items():
        if fn is fnode:
            return key
    return normalize_torn_name(name)
def _build_imported_by_index(graph) -> set[str]:
    imported: set[str] = set()
    for src_fqn in graph.import_graph.values():
        if not _declared_name(src_fqn):
            continue
        imported.add(normalize_torn_name(src_fqn))
    return imported
def _is_imported_symbol(graph, fnode, imported_by: set[str]) -> bool:
    if not imported_by:
        return False
    key = normalize_torn_name(_fnode_graph_key(graph, fnode))
    if not key:
        return False
    candidates = {key}
    root = _path_text(getattr(graph, 'project_root', ''))
    pkg_root = pkg_root_name(root) if root else ""
    if pkg_root:
        prefix = pkg_root + "."
        if key.startswith(prefix):
            candidates.add(key[len(prefix):])
        else:
            candidates.add(prefix + key)
    return bool(candidates & imported_by)
def _downgrade_orphan(fnode, flag: str, channel: str, *,
                      path: str | None = None, detail: str = '') -> bool:
    if getattr(fnode, 'confidence', 'unknown') != 'confirmed':
        return False
    fnode.confidence = FIELD_POTENTIAL_FP
    setattr(fnode, flag, True)
    _logger.info("[CallGraph] 精度通道降级@%s: %s (%s)%s",
                channel, getattr(fnode, 'name', '?'),
                getattr(fnode, 'filepath', '') if path is None else path,
                detail)
    return True
def _graph_filepath_key(graph, filepath) -> str:
    text = _path_text(filepath)
    if not text:
        return ""
    root = _path_text(getattr(graph, 'project_root', ''))
    absolute = (text if os.path.isabs(text)
                else os.path.join(root, text))
    return os.path.normcase(os.path.abspath(absolute))
class _OrphanScanIndex:
    def __init__(self, graph) -> None:
        self.graph = graph
        self.all_called = {
            normalize_torn_name(edge.callee_func) for edge in graph.calls
            if _declared_name(edge.callee_func)
            and not is_self_caller_name(edge.caller_func, edge.callee_func)}
        self.called_simples_by_file = defaultdict(set)
        for edge in graph.calls:
            file_key = _graph_filepath_key(graph, edge.callee_file)
            if not _declared_name(edge.callee_func) or not file_key \
                    or is_self_caller_name(edge.caller_func, edge.callee_func):
                continue
            callee = normalize_torn_name(edge.callee_func)
            if callee in graph.functions:
                continue
            self.called_simples_by_file[file_key].add(_simple_name(callee))
        self.imported_by = _build_imported_by_index(graph)
_ORPHAN_PRECISION_FLAGS = (
    '_non_impacting_dep',
    '_type_annotation_unreachable',
    '_side_effect_protected',
    '_path_sensitive_unreachable',
    '_side_effect_checked',
)


def _reset_orphan_precision_state(fnode) -> None:
    if getattr(fnode, 'confidence', 'unknown') in {
            'confirmed', FIELD_POTENTIAL_FP}:
        fnode.confidence = 'unknown'
    for flag in _ORPHAN_PRECISION_FLAGS:
        setattr(fnode, flag, False)


def find_orphans(graph) -> None:
    for fnode in graph.functions.values():
        _reset_orphan_precision_state(fnode)
    index = _OrphanScanIndex(graph)
    discovered: list[FunctionNode] = []
    for name, fnode in graph.functions.items():
        weight = graph.analyses.weights.compute_caller_weight(name, fnode)
        fnode.caller_weight = weight
        if _is_orphan_exempt(name, fnode, index):
            continue
        if weight < 0.3:
            fnode.confidence = 'confirmed'
            discovered.append(fnode)
    graph.orphans[:] = discovered
    graph.invalidate_analysis_caches()
def _is_orphan_exempt(name, fnode, index: _OrphanScanIndex) -> bool:
    return (
        _called_or_decorator_exempt(name, fnode, index)
        or _exposed_or_referenced_exempt(fnode, index)
        or _test_caller_exempt(name, index.graph)
    )
def _called_or_decorator_exempt(
        name, fnode, index: _OrphanScanIndex) -> bool:
    file_key = _graph_filepath_key(index.graph, fnode.filepath)
    return any((
        name in index.all_called,
        _simple_name(name) in index.called_simples_by_file.get(file_key, ()),
    )) or bool(index.graph.analyses.exemption.is_exempt_from_orphan(fnode))
def _exposed_or_referenced_exempt(
        fnode, index: _OrphanScanIndex) -> bool:
    graph = index.graph
    return (
        _is_exported_member(graph.global_all_exports, fnode)
        or _is_imported_symbol(graph, fnode, index.imported_by)
        or bool(graph.analyses.exemption.is_cross_skill_referenced(fnode))
    )
def _test_caller_exempt(name, graph) -> bool:
    if name not in graph.callers:
        return False
    return any(_caller_is_test(c, graph.functions)
               for c in graph.callers[name])
def callers_for_fnode(graph, fnode) -> list:
    key = _fnode_graph_key(graph, fnode)
    if key and key in graph.callers:
        return list(graph.callers.get(key, []))
    return []
def external_callers_for_fnode(graph, fnode) -> list:
    key = _fnode_graph_key(graph, fnode)
    return [caller for caller in callers_for_fnode(graph, fnode)
            if not is_self_caller_name(caller, key)]
def _find_func_node_in_tree(tree, func_name, start_line):
    simple = _simple_name(func_name)
    fallback = None
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name != simple:
            continue
        if node.lineno == start_line:
            return node
        if fallback is None:
            fallback = node
    return fallback
def _func_ast_at(builder, filepath, func_name, start_line):
    if not filepath:
        return None
    tree = builder.get_source_and_ast(filepath)[1]
    if tree is None:
        return None
    return _find_func_node_in_tree(tree, func_name, start_line)
def _iter_function_params(func_ast) -> tuple[list, int]:
    pos_count = len(func_ast.args.posonlyargs) + len(func_ast.args.args)
    return iter_arg_nodes(func_ast.args), pos_count
def _collect_type_annotations(func_ast) -> list[tuple[str, str]]:
    all_args, _pos_count = _iter_function_params(func_ast)
    return [
        (arg.arg, _annotation_hint_str(arg.annotation))
        for arg in all_args
        if arg.annotation
    ]
def _annotation_hint_str(annotation) -> str:
    if isinstance(annotation, ast.Name):
        return annotation.id
    if isinstance(annotation, ast.Attribute):
        return annotation.attr
    if isinstance(annotation, ast.Subscript):
        return 'complex'
    return ''
def _sole_guard_test(func_ast):
    body = list(func_ast.body)
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        body.pop(0)
    if len(body) != 1:
        return None
    guard = body[0]
    if not isinstance(guard, ast.If) or guard.orelse:
        return None
    return guard.test


def _iter_lexical_function_nodes(func_ast, *, postponed_annotations=False):
    stack = list(func_ast.body)
    immediate_lambdas: set[int] = set()
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Lambda):
            immediate_lambdas.add(id(node.func))
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            if postponed_annotations:
                stack.extend((*getattr(node, 'decorator_list', ()),
                              *getattr(node, 'type_params', ())))
                stack.extend(node.args.defaults)
                stack.extend(default for default in node.args.kw_defaults
                             if default is not None)
            else:
                stack.extend((node.args, *getattr(node, 'decorator_list', ()),
                              *getattr(node, 'type_params', ())))
            if (getattr(node, 'returns', None) is not None
                    and not postponed_annotations):
                stack.append(node.returns)
            if (isinstance(node, ast.Lambda)
                    and id(node) in immediate_lambdas):
                stack.append(node.body)
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _collect_isinstance_branches(func_ast) -> list[tuple[str, str, bool]]:
    isinstance_branches: list[tuple[str, str, bool]] = []
    for node in _iter_lexical_function_nodes(func_ast):
        if not isinstance(node, ast.If):
            continue
        call_node = _extract_isinstance_test(node.test)
        if call_node is None:
            continue
        target_name, type_name = _isinstance_arg_names(call_node)
        if target_name and type_name:
            is_not = isinstance(node.test, ast.UnaryOp)
            isinstance_branches.append((target_name, type_name, is_not))
    return isinstance_branches
def _extract_isinstance_test(test):
    if isinstance(test, ast.UnaryOp):
        if not (isinstance(test.op, ast.Not)
                and isinstance(test.operand, ast.Call)):
            return None
        test = test.operand
    if not isinstance(test, ast.Call):
        return None
    if not isinstance(test.func, ast.Name) or test.func.id != 'isinstance':
        return None
    return test if len(test.args) == 2 else None
def _isinstance_arg_names(call_node) -> tuple[str, str]:
    target_name = ''
    type_name = ''
    if isinstance(call_node.args[0], ast.Name):
        target_name = call_node.args[0].id
    if isinstance(call_node.args[1], ast.Name):
        type_name = call_node.args[1].id
    elif isinstance(call_node.args[1], ast.Attribute):
        type_name = call_node.args[1].attr
    return target_name, type_name
_SCALAR_CONST_HINTS: tuple[tuple[type, str], ...] = (
    (bool, 'bool'),
    (int, 'int'),
    (float, 'float'),
    (str, 'str'),
)
_LITERAL_NODE_HINTS: tuple[tuple[type, str], ...] = (
    (ast.List, 'list'),
    (ast.Dict, 'dict'),
    (ast.Tuple, 'tuple'),
    (ast.Set, 'set'),
)
def _arg_type_hint_of(arg_node) -> str:
    if isinstance(arg_node, ast.Constant):
        return _constant_value_hint(arg_node.value)
    if isinstance(arg_node, ast.Name):
        return 'variable'
    for node_type, hint in _LITERAL_NODE_HINTS:
        if isinstance(arg_node, node_type):
            return hint
    return ''
def _constant_value_hint(value) -> str:
    if value is None:
        return 'NoneType'
    for value_type, hint in _SCALAR_CONST_HINTS:
        if isinstance(value, value_type):
            return hint
    return ''
@dataclass(frozen=True)
class _ParamShape:
    param_names: list[str]
    pos_count: int | None = None
    @property
    def pos_limit(self) -> int:
        if self.pos_count is None:
            return len(self.param_names)
        return min(self.pos_count, len(self.param_names))
def _target_call_counts(graph, target_key: str, caller: str) -> dict[int, int]:
    caller_key = _caller_node_key(caller)
    normalized_target = normalize_torn_name(target_key)
    counts: dict[int, int] = defaultdict(int)
    for edge in graph.calls:
        line = getattr(edge, 'line', 0)
        if (not isinstance(line, int) or isinstance(line, bool) or line <= 0
                or _caller_node_key(edge.caller_func) != caller_key
                or normalize_torn_name(edge.callee_func) != normalized_target):
            continue
        counts[line] += 1
    return counts
_UNKNOWN_ARG_TYPE_HINT = 'unknown'

def _collect_caller_arg_types(builder, target_key, callers,
                              param_shape: _ParamShape, hint_fn
                              ) -> dict[str, set[str]] | None:
    type_hints: dict[str, set[str]] = {}
    simple_name = _simple_name(target_key)
    for caller in callers:
        caller_ast = _caller_func_ast(builder, caller)
        if caller_ast is None:
            return None
        call_counts = _target_call_counts(builder.graph, target_key, caller)
        if not call_counts:
            return None
        if not _collect_call_arg_hints(
                caller_ast, simple_name, call_counts,
                param_shape, hint_fn, type_hints):
            return None
    return type_hints
def _caller_func_ast(builder, caller):
    caller_func = builder.graph.functions.get(_caller_node_key(caller))
    if not caller_func or not caller_func.filepath:
        return None
    return _func_ast_at(builder, caller_func.filepath,
                        caller_func.name, caller_func.start_line)
def _collect_call_arg_hints(func_ast, simple_name: str,
                            target_call_counts: dict[int, int],
                            param_shape: _ParamShape,
                            hint_fn, type_hints: dict[str, set[str]]) -> bool:
    pos_limit = param_shape.pos_limit
    calls_by_line: dict[int, list] = defaultdict(list)
    for node in _iter_lexical_function_nodes(func_ast):
        if (isinstance(node, ast.Call)
                and _call_target_name(node.func) == simple_name):
            calls_by_line[node.lineno].append(node)
    for line, edge_count in target_call_counts.items():
        nodes = calls_by_line.get(line, [])
        if len(nodes) != edge_count:
            return False
        for node in nodes:
            hints = [*_positional_arg_hints(
                node.args, param_shape.param_names, pos_limit, hint_fn),
                *_keyword_arg_hints(
                    node.keywords, param_shape.param_names, hint_fn)]
            for pname, hint in hints:
                type_hints.setdefault(pname, set()).add(hint)
            bound = {pname for pname, _hint in hints}
            for pname in param_shape.param_names:
                if pname not in bound:
                    type_hints.setdefault(pname, set()).add(
                        _UNKNOWN_ARG_TYPE_HINT)
    return True
def _call_target_name(func_ref) -> str:
    if isinstance(func_ref, ast.Name):
        return func_ref.id
    if isinstance(func_ref, ast.Attribute):
        return func_ref.attr
    return ''
def _positional_arg_hints(
    args, param_names, pos_limit, hint_fn) -> list[tuple[str, str]]:
    pairs = []
    for i, arg_node in enumerate(args):
        if i >= pos_limit:
            break
        if isinstance(arg_node, ast.Starred):
            break
        type_hint = hint_fn(arg_node) or _UNKNOWN_ARG_TYPE_HINT
        pairs.append((param_names[i], type_hint))
    return pairs
def _keyword_arg_hints(keywords, param_names, hint_fn) -> list[tuple[str, str]]:
    pairs = []
    for kw in keywords:
        if not kw.arg:
            continue
        if kw.arg in param_names:
            type_hint = hint_fn(kw.value) or _UNKNOWN_ARG_TYPE_HINT
            pairs.append((kw.arg, type_hint))
    return pairs
_ISINSTANCE_SUBCLASS_COMPAT = frozenset({('bool', 'int')})
_CONCRETE_LITERAL_TYPE_NAMES = frozenset({
    'bool', 'int', 'float', 'str', 'NoneType',
    'list', 'dict', 'tuple', 'set',
})
_TYPE_CHANNEL_SKIP_FLAGS = ('_non_impacting_dep',)
_PATH_CHANNEL_SKIP_FLAGS = ('_non_impacting_dep',
                            '_type_annotation_unreachable',
                            '_side_effect_protected')
def _resolve_orphan_func_ast(builder, fnode, skip_flags):
    if any(getattr(fnode, flag, False) for flag in skip_flags):
        return None
    return _func_ast_at(builder, fnode.filepath, fnode.name, fnode.start_line)
def _collect_orphan_arg_hints(builder, fnode, func_ast, hint_fn):
    callers = external_callers_for_fnode(builder.graph, fnode)
    if not callers:
        return None
    return _collect_caller_arg_types(
        builder, _fnode_graph_key(builder.graph, fnode), callers,
        _bindable_param_shape(func_ast, fnode), hint_fn)
def infer_type_annotation_reachability(builder: Any) -> int:
    adjusted = 0
    for fnode in list(builder.graph.orphans):
        adjusted += _infer_fnode_type_reachability(builder, fnode)
    return adjusted
def _infer_fnode_type_reachability(builder, fnode) -> int:
    func_ast = _resolve_orphan_func_ast(builder, fnode, _TYPE_CHANNEL_SKIP_FLAGS)
    if func_ast is None:
        return 0
    branches = _annotated_isinstance_branches(func_ast)
    if not branches:
        return 0
    arg_type_hints = _collect_orphan_arg_hints(
        builder, fnode, func_ast, _arg_type_hint_of)
    if arg_type_hints is None:
        return 0
    adjusted = 0
    for target_name, type_name, is_not in branches:
        if _try_type_unreachable_downgrade(
                fnode, target_name, type_name, is_not, arg_type_hints):
            adjusted += 1
    return adjusted
def _annotated_isinstance_branches(func_ast) -> list[tuple[str, str, bool]]:
    branches = _collect_isinstance_branches(func_ast)
    if not branches or not _collect_type_annotations(func_ast):
        return []
    guard_test = _sole_guard_test(func_ast)
    if guard_test is None:
        return []
    call_node = _extract_isinstance_test(guard_test)
    if call_node is None:
        return []
    target_name, type_name = _isinstance_arg_names(call_node)
    sole_branch = (target_name, type_name,
                   isinstance(guard_test, ast.UnaryOp))
    return [branch for branch in branches if branch == sole_branch]
def _try_type_unreachable_downgrade(fnode, target_name: str, type_name: str,
                                    is_not: bool, arg_type_hints: dict) -> bool:
    observed_types = arg_type_hints.get(target_name, set())
    if not (observed_types and len(observed_types) == 1):
        return False
    observed = next(iter(observed_types))
    if observed == 'variable':
        return False
    guard_always_true = (type_name == 'object'
                         or observed == type_name
                         or (observed, type_name) in _ISINSTANCE_SUBCLASS_COMPAT)
    guard_always_false = (
        observed in _CONCRETE_LITERAL_TYPE_NAMES
        and type_name in _CONCRETE_LITERAL_TYPE_NAMES
        and not guard_always_true)
    unreachable = guard_always_true if is_not else guard_always_false
    if not unreachable:
        return False
    return _downgrade_orphan(
        fnode, '_type_annotation_unreachable', '类型注解不可达')
def _bindable_param_shape(func_ast, fnode) -> _ParamShape:
    all_args, pos_count = _iter_function_params(func_ast)
    if (getattr(fnode, 'is_method', False) and all_args
            and not _has_decorator(fnode, 'staticmethod')):
        all_args = all_args[1:]
        pos_count = max(0, pos_count - 1)
    vararg = func_ast.args.vararg
    kwarg = func_ast.args.kwarg
    param_names = [arg.arg for arg in all_args
                   if arg is not vararg and arg is not kwarg]
    return _ParamShape(param_names, pos_count)
_SIDE_EFFECT_CALLS = frozenset({
    'open', 'print', 'write', 'flush', 'close',
    'debug', 'info', 'warning', 'error', 'critical', 'exception', 'log',
    'system', 'popen', 'fork', 'spawn', 'kill',
    'exec', 'eval', 'setattr', 'delattr',
})
_SIDE_EFFECT_ATTRS = frozenset({
    'append', 'extend', 'insert', 'remove', 'pop', 'clear',
    'update', 'setdefault', 'popitem',
    'add', 'discard',
    'write', 'writelines', 'seek', 'truncate',
    'flush', 'close', 'start', 'terminate',
})
_MODULE_SIDE_EFFECT_CALLS = {
    'os': frozenset({
        'chdir', 'fchdir', 'chmod', 'chown', 'lchown', 'link',
        'mkdir', 'makedirs', 'remove', 'unlink', 'removedirs',
        'rename', 'renames', 'replace', 'rmdir', 'symlink', 'truncate',
        'utime', 'open', 'write', 'close', 'sendfile',
        'system', 'popen', 'fork', 'forkpty', 'kill', 'killpg',
        'posix_spawn', 'posix_spawnp', 'spawnl', 'spawnle', 'spawnlp',
        'spawnlpe', 'spawnv', 'spawnve', 'spawnvp', 'spawnvpe',
        'execl', 'execle', 'execlp', 'execlpe', 'execv', 'execve',
        'execvp', 'execvpe',
    }),
    'sys': frozenset({
        'exit', 'audit', 'addaudithook', 'setrecursionlimit',
        'setswitchinterval', 'settrace', 'setprofile', 'setdlopenflags',
        'set_int_max_str_digits',
    }),
    'subprocess': frozenset({
        'run', 'Popen', 'call', 'check_call', 'check_output',
        'getoutput', 'getstatusoutput',
    }),
    'logging': frozenset({
        'basicConfig', 'disable', 'addLevelName', 'setLogRecordFactory',
        'setLoggerClass',
    }),
    'json': frozenset({'dump'}),
    'pickle': frozenset({'dump'}),
    'shutil': frozenset({
        'copy', 'copy2', 'copyfile', 'copyfileobj', 'copymode',
        'copystat', 'copytree', 'move', 'rmtree', 'chown',
        'make_archive', 'unpack_archive', 'register_archive_format',
        'unregister_archive_format', 'register_unpack_format',
        'unregister_unpack_format',
    }),
}
def _module_call_side_effect(func_ref):
    if not isinstance(func_ref.value, ast.Name):
        return None
    mod_name = func_ref.value.id
    if func_ref.attr not in _MODULE_SIDE_EFFECT_CALLS.get(mod_name, ()):
        return None
    return 'module_call:' + mod_name + '.' + func_ref.attr
def _attr_target_dotted_label(target: ast.AST) -> str | None:
    if not isinstance(target, ast.Attribute):
        return None
    segs: list[str] = []
    node = target
    while isinstance(node, ast.Attribute):
        segs.append(node.attr)
        node = node.value
    if not isinstance(node, ast.Name):
        return None
    segs.append(node.id)
    segs.reverse()
    return ".".join(segs)
@dataclass(frozen=True, eq=False)
class _ScopeDeclarations:
    global_decls: dict
    nonlocal_decls: dict
    node_owner: dict
    def is_global_write(self, name: str, write_node_id: int) -> bool:
        owner_ids = self.global_decls.get(name)
        return bool(owner_ids) and self.node_owner.get(write_node_id) in owner_ids
    def is_declared_write(self, name: str, write_node_id: int) -> bool:
        if self.is_global_write(name, write_node_id):
            return True
        decl_owner_ids = self.nonlocal_decls.get(name)
        if not decl_owner_ids:
            return False
        return self.node_owner.get(write_node_id) in decl_owner_ids
def _scan_declared_var_scopes(func_ast) -> _ScopeDeclarations:
    global_decls: dict = {}
    nonlocal_decls: dict = {}
    node_owner: dict = {id(func_ast): id(func_ast)}
    def _scan(node, owner_id):
        for child in ast.iter_child_nodes(node):
            node_owner[id(child)] = owner_id
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                _scan(child, id(child))
            else:
                _scan(child, owner_id)
    _scan(func_ast, id(func_ast))
    for node in walk_nodes(func_ast):
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            decl_owner = node_owner.get(id(node))
            bucket = (global_decls if isinstance(node, ast.Global)
                      else nonlocal_decls)
            for name in node.names:
                bucket.setdefault(name, set()).add(decl_owner)
    return _ScopeDeclarations(global_decls, nonlocal_decls, node_owner)
def check_side_effects(builder: Any) -> int:
    graph = builder.graph
    adjusted = 0
    for fnode in list(graph.orphans):
        if not _should_scan_side_effect(fnode):
            continue
        side_effect_types = _scan_orphan_side_effects(builder, fnode)
        if side_effect_types and _downgrade_orphan(
                fnode, '_side_effect_protected', '副作用保护',
                detail=f" effects={side_effect_types}"):
            adjusted += 1
        fnode._side_effect_checked = True
    return adjusted
def _scan_orphan_side_effects(builder, fnode) -> list[str]:
    source, tree = builder.get_source_and_ast(fnode.filepath)
    if not source or tree is None:
        return []
    func_ast = _find_func_node_in_tree(tree, fnode.name, fnode.start_line)
    if func_ast is None:
        return []
    scope_decls = _scan_declared_var_scopes(func_ast)
    postponed = module_postpones_annotations(tree)
    for node in _iter_lexical_function_nodes(
            func_ast, postponed_annotations=postponed):
        label = _node_side_effect_label(node, scope_decls)
        if label is not None:
            return [label]
    return []
_SIDE_EFFECT_SKIP_FLAGS = ('_side_effect_checked', '_non_impacting_dep',
                           '_type_annotation_unreachable')
def _should_scan_side_effect(fnode) -> bool:
    if any(getattr(fnode, flag, False) for flag in _SIDE_EFFECT_SKIP_FLAGS):
        return False
    return bool(fnode.filepath)
def _node_side_effect_label(node, scope_decls: _ScopeDeclarations) -> str | None:
    if isinstance(node, ast.Call):
        return _call_side_effect_label(node)
    if isinstance(node, ast.Assign):
        return _assign_side_effect_label(node, scope_decls)
    if isinstance(node, ast.AugAssign):
        return _target_side_effect_label(
            node.target, scope_decls, id(node), _AUGMENTED_LABELS)
    if isinstance(node, ast.AnnAssign):
        if node.value is None:
            return None
        return _target_side_effect_label(
            node.target, scope_decls, id(node), _ASSIGN_LABELS)
    if isinstance(node, ast.NamedExpr):
        return _target_side_effect_label(
            node.target, scope_decls, id(node), _ASSIGN_LABELS)
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _target_side_effect_label(
            node.target, scope_decls, id(node), _ASSIGN_LABELS)
    if isinstance(node, ast.Delete):
        return _delete_side_effect_label(node, scope_decls)
    return None
def _call_side_effect_label(node) -> str | None:
    func_ref = node.func
    if isinstance(func_ref, ast.Name) and func_ref.id in _SIDE_EFFECT_CALLS:
        return 'call:' + func_ref.id
    if not isinstance(func_ref, ast.Attribute):
        return None
    label = _module_call_side_effect(func_ref)
    if label is not None:
        return label
    if func_ref.attr in _SIDE_EFFECT_ATTRS:
        return 'mutation:' + func_ref.attr
    if func_ref.attr in _SIDE_EFFECT_CALLS:
        return 'attr_call:' + func_ref.attr
    return None
def _container_base_label(target) -> str | None:
    if isinstance(target, ast.Name):
        return target.id
    return _attr_target_dotted_label(target)
@dataclass(frozen=True)
class _WriteLabels:
    attr: str
    declared: str
    subscript: str
_ASSIGN_LABELS = _WriteLabels(
    'attr_assign:', 'declared_assign:', 'subscript_assign:')
_AUGMENTED_LABELS = _WriteLabels(
    'augmented_assign:', 'augmented_assign:', 'subscript_aug_assign:')
_DELETE_LABELS = _WriteLabels(
    'attr_delete:', 'declared_delete:', 'subscript_delete:')
def _target_side_effect_label(target, scope_decls: _ScopeDeclarations,
                              write_node_id: int,
                              labels: _WriteLabels) -> str | None:
    if isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            label = _target_side_effect_label(
                element, scope_decls, write_node_id, labels)
            if label is not None:
                return label
        return None
    if isinstance(target, ast.Starred):
        return _target_side_effect_label(
            target.value, scope_decls, write_node_id, labels)
    if isinstance(target, ast.Subscript):
        base_label = _container_base_label(target.value)
        return None if base_label is None else labels.subscript + base_label
    attr_label = _attr_target_dotted_label(target)
    if attr_label is not None:
        return labels.attr + attr_label
    if isinstance(target, ast.Name):
        if scope_decls.is_global_write(target.id, write_node_id):
            return 'global_modification'
        if scope_decls.is_declared_write(target.id, write_node_id):
            return labels.declared + target.id
    return None
def _assign_side_effect_label(node, scope_decls: _ScopeDeclarations
                              ) -> str | None:
    for target in node.targets:
        label = _target_side_effect_label(
            target, scope_decls, id(node), _ASSIGN_LABELS)
        if label is not None:
            return label
    return None
def _delete_side_effect_label(node, scope_decls: _ScopeDeclarations
                              ) -> str | None:
    for target in node.targets:
        label = _target_side_effect_label(
            target, scope_decls, id(node), _DELETE_LABELS)
        if label is not None:
            return label
    return None
def _collect_path_guards(func_ast) -> list:
    guards = []
    for node in _iter_lexical_function_nodes(func_ast):
        if isinstance(node, ast.If):
            guard = _guard_of(node.test)
            if guard is not None:
                guards.append(guard)
    return guards
def _guard_of(test):
    pair = _none_compare_guard(test)
    if pair is not None:
        return pair
    if (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
            and isinstance(test.operand, ast.Name)):
        return (test.operand.id, 'not_truthy')
    if isinstance(test, ast.Name):
        return (test.id, 'truthy')
    return None
def _none_compare_guard(test):
    if not isinstance(test, ast.Compare):
        return None
    if not (len(test.ops) == 1 and len(test.comparators) == 1
            and isinstance(test.ops[0], (ast.Is, ast.IsNot))):
        return None
    if not isinstance(test.left, ast.Name):
        return None
    if not (isinstance(test.comparators[0], ast.Constant)
            and test.comparators[0].value is None):
        return None
    guard_type = 'is_none' if isinstance(test.ops[0], ast.Is) else 'is_not_none'
    return (test.left.id, guard_type)
def _guard_arg_type_hint_of(arg_node) -> str:
    if isinstance(arg_node, ast.Constant):
        if arg_node.value is None:
            return 'NoneType'
        if isinstance(arg_node.value, (bool, int, float, str)):
            return 'truthy' if arg_node.value else 'falsy'
    elif isinstance(arg_node, (ast.List, ast.Tuple, ast.Set)):
        if any(not isinstance(elt, ast.Starred) for elt in arg_node.elts):
            return 'truthy'
        return 'falsy' if not arg_node.elts else ''
    elif isinstance(arg_node, ast.Dict):
        if any(key is not None for key in arg_node.keys):
            return 'truthy'
        return 'falsy' if not arg_node.keys else ''
    elif isinstance(arg_node, ast.Name):
        return 'variable'
    return ''
def _guard_outcome(guard_type: str, hint: str) -> bool | None:
    if guard_type in {'is_none', 'is_not_none'}:
        if hint == 'NoneType':
            return guard_type == 'is_none'
        if hint in {'truthy', 'falsy', 'non_none', 'bool'}:
            return guard_type == 'is_not_none'
        return None
    if guard_type in {'truthy', 'not_truthy'}:
        if hint == 'truthy':
            return guard_type == 'truthy'
        if hint == 'falsy':
            return guard_type == 'not_truthy'
    return None
def _evaluate_guard_constraints(guards, param_types, fnode) -> bool:
    for guard_var, guard_type in guards:
        observed = param_types.get(guard_var, set())
        if not observed:
            continue
        outcomes = {_guard_outcome(guard_type, hint) for hint in observed}
        if len(outcomes) != 1 or None in outcomes:
            continue
        outcome = next(iter(outcomes))
        if outcome:
            continue
        return _downgrade_orphan(
            fnode, '_path_sensitive_unreachable', '路径敏感不可达',
            detail=f" guard={guard_var} outcome={outcome}")
    return False
def detect_path_sensitive_type_constraints(builder: Any) -> int:
    adjusted = 0
    for fnode in list(builder.graph.orphans):
        if _prune_path_sensitive_orphan(builder, fnode):
            adjusted += 1
    return adjusted
def _prune_path_sensitive_orphan(builder, fnode) -> bool:
    func_ast = _resolve_orphan_func_ast(builder, fnode, _PATH_CHANNEL_SKIP_FLAGS)
    if func_ast is None:
        return False
    guards = _collect_path_guards(func_ast)
    guard_test = _sole_guard_test(func_ast)
    if guard_test is not None:
        sole_guard = _guard_of(guard_test)
        guards = [guard for guard in guards if guard == sole_guard]
    else:
        guards = []
    if not guards:
        return False
    param_types = _collect_orphan_arg_hints(
        builder, fnode, func_ast, _guard_arg_type_hint_of)
    if param_types is None:
        return False
    return _evaluate_guard_constraints(guards, param_types, fnode)
def _collect_protocol_member_names(graph) -> set[str]:
    inheritance = getattr(graph, "class_inheritance", None) or {}
    protocol_classes: set[str] = set()
    changed = True
    while changed:
        changed = False
        for cls_key, bases in inheritance.items():
            simple = _simple_name(cls_key)
            if simple in protocol_classes:
                continue
            base_simples = {_simple_name(base) for base in _as_name_tuple(bases)}
            if ("Protocol" in base_simples
                    or base_simples & protocol_classes):
                protocol_classes.add(simple)
                changed = True
    members: set[str] = set()
    for simple in protocol_classes:
        members.update(normalize_torn_name(name)
                       for name in class_method_names(graph, simple))
    return members
class _ExemptionAnalysis:
    def __init__(self, graph, library) -> None:
        self.graph = graph
        self._library = library
        self._fqn_by_identity: dict[int, str] | None = None
        self._protocol_members: set[str] | None = None
    def invalidate_caches(self) -> None:
        self._fqn_by_identity = None
        self._protocol_members = None
    def is_exempt_from_orphan(self, fnode: Any) -> bool:
        simple_name = _simple_name(fnode.name)
        if is_dunder_name(simple_name):
            return True
        if self._exempt_entry_pattern(simple_name, fnode):
            return True
        if self._exempt_protocol_callback(simple_name, fnode):
            return True
        if self._exempt_private_closure(simple_name, fnode):
            return True
        if _is_exported_member(self.graph.global_all_exports, fnode):
            return True
        if self._exempt_implicit_invocation(fnode):
            return True
        return self._exempt_annotation_channel(fnode)
    def _exempt_annotation_channel(self, fnode: Any) -> bool:
        if check_framework_decorators(fnode):
            return True
        return bool(check_source_markers(
            fnode, self.graph._file_lines_cache, self.graph.project_root))
    @staticmethod
    def _exempt_entry_pattern(simple_name: str, fnode: Any) -> bool:
        if (is_entry_point_name(simple_name, strong_only=True)
                or simple_name.startswith("test_")):
            return True
        return fnode.is_public and _is_package_init_file(fnode.filepath)
    def _exempt_protocol_callback(self, simple_name: str, fnode: Any) -> bool:
        return (self._is_wiring_declaration(simple_name)
                or self._is_protocol_member(simple_name, fnode)
                or self._is_visitor_callback(simple_name, fnode))
    @staticmethod
    def _is_wiring_declaration(simple_name: str) -> bool:
        return simple_name == WIRING_DECLARATION_ATTR
    def _is_protocol_member(self, simple_name: str, fnode: Any) -> bool:
        if any((
            simple_name in MAGIC_METHODS,
            fnode.is_method and simple_name in POLYMORPHIC_METHODS,
            bool(fnode.is_property),
        )):
            return True
        return bool(fnode.is_method
                    and simple_name in self._protocol_member_names())
    def _protocol_member_names(self) -> set[str]:
        if self._protocol_members is None:
            self._protocol_members = _collect_protocol_member_names(self.graph)
        return self._protocol_members
    @staticmethod
    def _is_visitor_callback(simple_name: str, fnode: Any) -> bool:
        if fnode.is_method and simple_name.startswith("visit_"):
            return True
        class_name = fnode.class_name
        return bool(fnode.is_method and class_name and normalize_torn_name(
            class_name).endswith(("Visitor", "Collector")))
    @staticmethod
    def _exempt_private_closure(simple_name: str, fnode: Any) -> bool:
        if simple_name in DECORATOR_CLOSURE_NAMES:
            return True
        return bool(simple_name.startswith('_')
                    and not simple_name.startswith('__')
                    and fnode.is_method)
    @staticmethod
    def _exempt_implicit_invocation(fnode: Any) -> bool:
        filepath = _path_text(getattr(fnode, 'filepath', ''))
        if os.path.basename(filepath).lower() == "facade.py" and fnode.is_public:
            return True
        return _has_decorator(fnode, "contextmanager")
    def _is_orphan_public_exempt(self, fnode) -> bool:
        if self.is_exempt_from_orphan(fnode):
            return True
        if self.is_cross_skill_referenced(fnode):
            return True
        if self._is_method_orphan(fnode):
            return not self._is_override_dead_method(fnode)
        return False
    @staticmethod
    def _is_method_orphan(fnode) -> bool:
        return bool(fnode.class_name and fnode.is_method)
    def _is_override_dead_method(self, fnode) -> bool:
        if not fnode.class_name:
            return False
        if _has_decorator(fnode, "abstractmethod"):
            return False
        method = _simple_name(fnode.name)
        matched = False
        for _child in self._iter_child_classes(fnode.class_name):
            matched = True
            if not self._child_overrides(_child, method):
                return False
        return matched
    def _child_overrides(self, child: str, method: str) -> bool:
        if method in class_method_names(self.graph, child):
            return True
        # ``class_methods`` 的键是类路径（不含模块前缀），而 ``class_inheritance``
        # 的键是模块全限定类键；直接拿全限定 child 查会恒空，使“基类方法被所有
        # 子类重写”的死代码通道失效。这里按 class_files 的源文件还原类路径。
        class_path = self._class_path_of(child)
        return bool(class_path) and method in class_method_names(
            self.graph, class_path)

    def _class_path_of(self, class_key: str) -> str:
        filepath = self.graph.class_files.get(class_key, "")
        if not filepath:
            return ""
        module = path_to_dotted_module(
            str(filepath).replace("\\", "/"))
        if not module:
            return class_key
        prefix = module + "."
        return class_key[len(prefix):] if class_key.startswith(prefix) else ""
    def _iter_child_classes(self, base_class_name: str):
        base_class_name = normalize_torn_name(base_class_name)
        for child_cls, bases in self.graph.class_inheritance.items():
            if self._bases_include(bases, base_class_name):
                yield normalize_torn_name(child_cls)
    @staticmethod
    def _bases_include(bases, base_class_name: str) -> bool:
        base_class_name = normalize_torn_name(base_class_name)
        base_simple = _simple_name(base_class_name)
        for base_written in _as_name_tuple(bases):
            written = normalize_torn_name(base_written)
            if (written == base_class_name
                    or written.endswith('.' + base_class_name)
                    or ('.' in base_class_name and written == base_simple)):
                return True
        return False
    def _is_reachable(self, fnode, reachability_cache) -> bool:
        fqn = self._fqn_of(fnode)
        return bool(fqn and reachability_cache.get(fqn, False))
    def _fqn_of(self, fnode) -> str:
        cached = (self._fqn_by_identity or {}).get(id(fnode))
        if (cached is not None
                and self.graph.functions.get(cached) is fnode):
            return cached
        self._fqn_by_identity = {
            id(fn): fqn for fqn, fn in self.graph.functions.items()}
        return self._fqn_by_identity.get(id(fnode), "")
    def _compute_orphan_severity(self, fnode, reachability_cache) -> str:
        if self._is_reachable(fnode, reachability_cache):
            return "info"
        return "low" if self._library.is_library_skill() else "medium"
    def is_cross_skill_referenced(self, fnode: Any) -> bool:
        if self.graph.cross_skill_imports is None:
            return False
        if self.graph._cross_skill_names_cache is None:
            self.graph._cross_skill_names_cache = collect_cross_skill_names(
                self.graph.cross_skill_imports)
        full_name = normalize_torn_name(fnode.name)
        simple_name = _simple_name(full_name)
        cache = self.graph._cross_skill_names_cache
        return any((simple_name in cache, full_name in cache))
_DEFAULT_MIN_FUNCTIONS: int = 30
@dataclass(frozen=True)
class LibraryProfile:
    min_functions: int = _DEFAULT_MIN_FUNCTIONS
    public_ratio: float = 0.5
    min_classes: int = 5
    class_method_density: float = 3.0
    cross_skill_min_functions: int = _DEFAULT_MIN_FUNCTIONS
    def __post_init__(self) -> None:
        for name in ('min_functions', 'min_classes', 'cross_skill_min_functions'):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f'{name} 须为非负整数: {value!r}')
        for name in ('public_ratio', 'class_method_density'):
            value = getattr(self, name)
            if (isinstance(value, bool) or not isinstance(value, (int, float))
                    or not math.isfinite(value) or value < 0):
                raise ValueError(f'{name} 须为有限非负数: {value!r}')
        if self.public_ratio > 1:
            raise ValueError(f'public_ratio 须位于 [0, 1]: {self.public_ratio!r}')
class _LibrarySkillAnalysis:
    def __init__(self, graph, profile: LibraryProfile | None = None) -> None:
        self.graph = graph
        self._profile = profile or LibraryProfile()
    def is_library_skill(self) -> bool:
        if self.graph._is_lib_cache is not None:
            return self.graph._is_lib_cache
        self.graph._is_lib_cache = self._compute()
        return self.graph._is_lib_cache
    def _compute(self) -> bool:
        total = len(self.graph.functions)
        if total >= self._profile.min_functions:
            if self._public_ratio_exceeds_half(total):
                return True
            if self._class_method_density_high():
                return True
        return self._has_cross_skill_imports(total)
    def _public_ratio_exceeds_half(self, total: int) -> bool:
        public = sum(1 for f in self.graph.functions.values() if f.is_public)
        return public / max(total, 1) > self._profile.public_ratio
    def _class_method_density_high(self) -> bool:
        functions = self.graph.functions.values()
        methods = sum(1 for f in functions if f.is_method)
        classes = len({f.class_name for f in functions if f.class_name})
        return (classes >= self._profile.min_classes
                and methods / max(classes, 1)
                > self._profile.class_method_density)
    def _has_cross_skill_imports(self, total: int) -> bool:
        return (total >= self._profile.cross_skill_min_functions
                and bool(_cross_skill_file_buckets(
                    self.graph.cross_skill_imports)))
class _CallerWeightAnalysis:
    def __init__(self, graph, exempt) -> None:
        self.graph = graph
        self._exempt = exempt
    _WEIGHT_TABLE: ClassVar[dict] = {
        "core_business": 1.0,
        "test_caller": 0.9,
        "public_api": 0.7,
        "internal_caller": 0.4,
        "cross_skill": 0.6,
        "orphan": 0.0,
    }
    def compute_caller_weight(self, func_key: str, fnode: Any) -> float:  # jwsgj:suppress public_untested
        callers = {caller for caller in (self.graph.callers.get(func_key) or ())
                   if not is_self_caller_name(caller, func_key)}
        if not callers:
            return self._WEIGHT_TABLE["orphan"]
        func_level_weight = 0.0
        if fnode.is_public:
            func_level_weight = max(
                func_level_weight, self._WEIGHT_TABLE["public_api"])
        if self._exempt.is_cross_skill_referenced(fnode):
            func_level_weight = max(
                func_level_weight, self._WEIGHT_TABLE["cross_skill"])
        return max(self._caller_chain_weight(callers), func_level_weight)
    def _caller_chain_weight(self, callers: set) -> float:
        max_weight = 0.0
        for raw_caller in callers:
            caller = _caller_node_key(raw_caller)
            if self._is_core_entry(caller):
                max_weight = max(max_weight, self._WEIGHT_TABLE["core_business"])
                continue
            if _caller_is_test(raw_caller, self.graph.functions):
                max_weight = max(max_weight, self._WEIGHT_TABLE["test_caller"])
                continue
            max_weight = max(max_weight, self._WEIGHT_TABLE["internal_caller"])
        return max_weight
    def _is_core_entry(self, caller: str) -> bool:
        fnode = self.graph.functions.get(caller)
        if fnode is not None and fnode.is_method:
            return False
        if is_entry_point_name(_simple_name(caller)):
            return True
        if fnode is None or not fnode.is_public:
            return False
        return not any(not is_self_caller_name(other, caller)
                       for other in (self.graph.callers.get(caller) or ()))
def _is_public_candidate(fnode: Any) -> bool:
    return (fnode.is_public
            and getattr(fnode, 'confidence', None) != FIELD_POTENTIAL_FP
            and not normalize_torn_name(fnode.name).startswith("_"))
def _orphan_suffix(severity: str) -> str:
    if severity == "info":
        return " (entry reachable, infrastructure)"
    if severity == "low":
        return " (dead code candidate)"
    return ""
class _ReachabilityAnalysis:
    def __init__(self, graph) -> None:
        self.graph = graph
    def _internal_calls(self):
        return (edge for edge in self.graph.calls
                if not getattr(edge, 'is_external', False))
    def compute_reachability_from_entries(self) -> dict[str, bool]:
        reachable = dict.fromkeys(self.graph.functions, False)
        simple_to_fqn = assignment_name_index(
            self.graph, require_declared=True)
        entry_points = self._identify_entry_points(simple_to_fqn)
        if not entry_points:
            return reachable
        self._bfs_mark_reachable(
            entry_points, self._build_forward_adj(), simple_to_fqn, reachable)
        return reachable
    def _bfs_mark_reachable(self, entry_points, forward_adj, simple_to_fqn,
                            reachable) -> None:
        queue = deque(entry_points)
        for ep in entry_points:
            reachable[ep] = True
        while queue:
            current = queue.popleft()
            for callee_full in forward_adj.get(current, set()):
                self._mark_callee_reachable(
                    callee_full, simple_to_fqn, reachable, queue)
    def _identify_entry_points(self, simple_to_fqn: dict) -> set:
        entry_points = {
            full_name for full_name, fnode in self.graph.functions.items()
            if not fnode.is_method
            and is_entry_point_name(_simple_name(full_name))}
        if not entry_points:
            entry_points |= self._implicit_entry_points(simple_to_fqn)
        return entry_points
    def _implicit_entry_points(self, simple_to_fqn: dict) -> set:
        in_degree = self._call_in_degrees(simple_to_fqn)
        return {full_name
                for full_name, fnode in self.graph.functions.items()
                if (fnode.is_public and not fnode.is_method
                    and in_degree.get(full_name, 0) == 0)}
    def _call_in_degrees(self, simple_to_fqn: dict) -> dict[str, int]:
        in_degree: dict[str, int] = defaultdict(int)
        for edge in self._internal_calls():
            if is_self_caller_name(edge.caller_func, edge.callee_func):
                continue
            callee = normalize_torn_name(edge.callee_func)
            if callee in self.graph.functions:
                in_degree[callee] += 1
                continue
            for fqn in simple_to_fqn.get(_simple_name(callee), []):
                if is_self_caller_name(edge.caller_func, fqn):
                    continue
                in_degree[fqn] += 1
        return in_degree
    def _build_forward_adj(self) -> dict:
        forward_adj: dict[str, set[str]] = defaultdict(set)
        for edge in self._internal_calls():
            if is_self_caller_name(edge.caller_func, edge.callee_func):
                continue
            forward_adj[edge.caller_func].add(edge.callee_func)
        return forward_adj
    def _mark_callee_reachable(self, callee_full, simple_to_fqn,
                               reachable, queue) -> None:
        if callee_full in reachable and not reachable[callee_full]:
            reachable[callee_full] = True
            queue.append(callee_full)
            return
        if callee_full not in reachable:
            for fqn in simple_to_fqn.get(_simple_name(callee_full), []):
                if not reachable[fqn]:
                    reachable[fqn] = True
                    queue.append(fqn)
class _BreakPointAnalysis:
    def __init__(self, graph, orphan, library) -> None:
        self.graph = graph
        self.reach = _ReachabilityAnalysis(graph)
        self._orphan = orphan
        self._library = library
    def get_break_points(self) -> list[dict]:
        if self.graph._break_points_cache is not None:
            return [dict(item) for item in self.graph._break_points_cache]
        breaks = []
        breaks.extend(self._find_unresolved_calls())
        reachability_cache = (self.reach.compute_reachability_from_entries()
                              if self.graph.orphans else {})
        breaks.extend(self._find_orphan_public_breaks(reachability_cache))
        reported_orphans = {
            _break_identity(b.get("file"), b.get("line"), b.get("function"))
            for b in breaks if b.get("type") == "orphan_public"}
        breaks.extend(self._find_untested_public_breaks(reported_orphans))
        self.graph._break_points_cache = breaks
        if breaks:
            _by_type: dict[str, int] = defaultdict(int)
            for _b in breaks:
                _by_type[str(_b.get("type", "?"))] += 1
            _logger.info("[CallGraph] 断链检测: %d 处 %s", len(breaks), dict(_by_type))
        return [dict(item) for item in breaks]
    def _find_unresolved_calls(self) -> list[dict]:
        breaks = []
        all_funcs = {key for key in self.graph.functions
                     if _declared_name(key)}
        for edge in self.graph.calls:
            if edge.is_external or edge.is_self_call:
                continue
            callee = normalize_torn_name(edge.callee_func)
            if not self._is_call_resolved(all_funcs, callee, edge.caller_file):
                breaks.append({
                    "type": "unresolved_call",
                    "caller": edge.caller_func,
                    "callee": callee,
                    "file": edge.caller_file,
                    "line": edge.line,
                    "severity": "critical",
                    "message": f"{edge.caller_func} -> {callee}",
                })
        return breaks
    def _is_call_resolved(self, all_funcs: set[str], callee: str,
                          caller_file: str) -> bool:
        if self._in_function_table(all_funcs, callee):
            return True
        return self._resolve_via_import_graph(callee, caller_file) is not None
    @staticmethod
    def _in_function_table(all_funcs: set[str], callee: str) -> bool:
        return any((
            callee in all_funcs,
            f"{callee}.__init__" in all_funcs,
        ))
    def _resolve_via_import_graph(self, callee_name: str, caller_file: str) -> str | None:
        callee_name = normalize_torn_name(callee_name)
        caller_file = normalize_torn_name(caller_file) if caller_file else ""
        simple = _simple_name(callee_name)
        if not callee_name or not simple:
            return None
        hit = self._import_graph_hit(callee_name, simple)
        if hit is not None:
            return hit
        candidates = functions_ending_with(self.graph.functions, simple)
        if not candidates:
            return None
        return self._pick_resolution_candidate(candidates, caller_file)
    def _import_graph_hit(self, callee_name: str,
                          simple: str) -> str | None:
        for key in (callee_name, simple):
            hit = self._resolve_import_key(key)
            if hit is not None:
                return hit
        return None
    def _resolve_import_key(self, key: str) -> str | None:
        resolved = self.graph.import_graph.get(key)
        if resolved is None:
            return None
        if resolved in self.graph.functions:
            return resolved
        stripped = self._strip_pkg_root(resolved)
        if stripped is not None and stripped in self.graph.functions:
            return stripped
        return None
    def _pick_resolution_candidate(self, candidates: tuple,
                                   caller_file: str) -> str | None:
        if len(candidates) == 1:
            return candidates[0]
        caller_dir = os.path.dirname(
            _graph_filepath_key(self.graph, caller_file))
        same_dir = []
        if caller_dir:
            for candidate in candidates:
                fnode = self.graph.functions.get(candidate)
                candidate_file = _graph_filepath_key(
                    self.graph, getattr(fnode, "filepath", ""))
                if (candidate_file
                        and os.path.dirname(candidate_file) == caller_dir):
                    same_dir.append(candidate)
        if len(same_dir) == 1:
            return same_dir[0]
        if same_dir:
            return None
        normalized = caller_file.replace("\\", "/")
        relative_dir = (normalized.rsplit("/", 1)[0]
                        if "/" in normalized else "")
        dir_prefix = relative_dir.replace("/", ".")
        legacy_same_dir = [
            candidate for candidate in candidates
            if dir_prefix and str(candidate).startswith(dir_prefix + ".")]
        return legacy_same_dir[0] if len(legacy_same_dir) == 1 else None
    def _strip_pkg_root(self, fqn: str) -> str | None:
        if self.graph._pkg_root_cache is None:
            root_text = _path_text(getattr(self.graph, 'project_root', ''))
            self.graph._pkg_root_cache = (pkg_root_name(root_text)
                                          if root_text else "")
        root = self.graph._pkg_root_cache
        if not root:
            return None
        fqn = normalize_torn_name(fqn)
        stripped = strip_pkg_root(fqn, root)
        return stripped if stripped != fqn else None
    def _find_orphan_public_breaks(self, reachability_cache) -> list[dict]:
        breaks = []
        for fnode in self.graph.orphans:
            _brk = self._orphan_public_break(fnode, reachability_cache)
            if _brk is not None:
                breaks.append(_brk)
        return breaks
    def _orphan_public_break(self, fnode: Any,
                             reachability_cache) -> dict | None:
        if not _is_public_candidate(fnode):
            return None
        if self._orphan._is_orphan_public_exempt(fnode):
            return None
        severity = self._orphan._compute_orphan_severity(fnode, reachability_cache)
        return self._public_break(
            "orphan_public", fnode, severity,
            f"orphan public {fnode.name}{_orphan_suffix(severity)}")
    @staticmethod
    def _public_break(kind: str, fnode: Any, severity: str,
                      message: str) -> dict:
        return {
            "type": kind,
            "function": fnode.name,
            "file": fnode.filepath,
            "line": fnode.start_line,
            "severity": severity,
            "message": message,
        }
    def _find_untested_public_breaks(self, excluded_keys: set | None = None) -> list[dict]:
        breaks = []
        excluded = excluded_keys or set()
        for full_key, fnode in self.graph.functions.items():
            if not _is_public_candidate(fnode):
                continue
            if self._has_test_caller(full_key):
                continue
            if _break_identity(
                    fnode.filepath, fnode.start_line, fnode.name) in excluded:
                continue
            if self._is_untested_exempt(fnode):
                continue
            breaks.append(self._public_break(
                "untested_public", fnode, self._untested_severity(),
                f"untested public {fnode.name}"))
        return breaks
    def _untested_severity(self) -> str:
        return "info" if self._library.is_library_skill() else "low"
    def _has_test_caller(self, full_key: str) -> bool:
        keys = [full_key]
        simple = _simple_name(full_key)
        if (simple != full_key
                and functions_ending_with(self.graph.functions, simple)
                == (full_key,)):
            keys.append(simple)
        for key in keys:
            if any(not is_self_caller_name(caller, key)
                   and _caller_is_test(caller, self.graph.functions)
                   for caller in (self.graph.callers.get(key) or ())):
                return True
        return False
    def _is_untested_exempt(self, fnode: Any) -> bool:
        if self._orphan.is_exempt_from_orphan(fnode):
            return True
        return self._orphan.is_cross_skill_referenced(fnode)
class _SummaryAnalysis:
    def __init__(self, graph, breakpts, library) -> None:
        self.graph = graph
        self._bp = breakpts
        self._library = library
    def summary(self) -> dict:
        counts = self._collect_counts()
        is_lib = self._library.is_library_skill()
        judgments = build_callgraph_judgments(
            self.graph, CallGraphStats(
                counts["total"], counts["public"], counts["cross"],
                counts["orphans"], counts["breaks"], counts["total_calls"],
                is_lib, counts["syntax_errors"], counts["ext_skills"],
                counts["ext_files"]))
        return {
            FIELD_TOTAL_FUNCTIONS: counts["total"],
            "public_functions": counts["public"],
            "total_calls": counts["total_calls"],
            "cross_file_calls": counts["cross"],
            "self_calls": counts["self_calls"],
            "external_deps": counts["external_deps_real"],
            "external_deps_total": counts["external_deps_all"],
            "orphans": counts["orphans"],
            "break_points": counts["breaks"],
            "syntax_errors": counts["syntax_errors"],
            "cross_skill_skills": counts["ext_skills"],
            "cross_skill_files": counts["ext_files"],
            "exemption_classification": build_exemption_classification(
                self.graph.orphans),
            "judgments": judgments,
            "weight_context": build_weight_context(self.graph.functions),
        }
    def _collect_counts(self) -> dict:
        counts = {
            "total": len(self.graph.functions),
            "public": sum(1 for f in self.graph.functions.values()
                          if f.is_public),
            "orphans": len(self.graph.orphans),
            "total_calls": len(self.graph.calls),
            "external_deps_all": len(self.graph.external_deps),
            "external_deps_real": len(self.get_real_external_deps()),
            "syntax_errors": len(self.graph.syntax_errors),
        }
        counts.update(self._collect_call_counts())
        counts.update(self._collect_cross_skill_counts())
        return counts
    def _collect_call_counts(self) -> dict:
        return {
            "cross": sum(1 for e in self.graph.calls
                         if _is_cross_file_call(e.caller_file, e.callee_file)),
            "self_calls": sum(1 for e in self.graph.calls if e.is_self_call),
            "breaks": len(self._bp.get_break_points()),
        }
    def _collect_cross_skill_counts(self) -> dict:
        buckets = _cross_skill_file_buckets(self.graph.cross_skill_imports)
        return {"ext_skills": len(buckets),
                "ext_files": sum(len(files) for files in buckets)}
    def get_real_external_deps(self) -> set[str]:
        root_text = _path_text(getattr(self.graph, 'project_root', ''))
        pkg_root = pkg_root_name(root_text) if root_text else ""
        real = set()
        for raw_dep in self.graph.external_deps:
            dep = normalize_torn_name(raw_dep)
            if not dep:
                continue
            top = dep.split(".")[0]
            if top in NON_PROJECT_TOP_MODULES or top in BUILTIN_CALLABLES:
                continue
            if pkg_root and top == pkg_root:
                continue
            real.add(dep)
        return real
    def _count_py_files(self) -> int:
        if self.graph._py_files_count_cache is None:
            self.graph._py_files_count_cache = count_project_py_files(
                getattr(self.graph, 'project_root', ''))
        return self.graph._py_files_count_cache
class GraphAnalyses(NamedTuple):
    library: _LibrarySkillAnalysis
    exemption: _ExemptionAnalysis
    weights: _CallerWeightAnalysis
    breakpoints: _BreakPointAnalysis
    summary: _SummaryAnalysis
def build_graph_analyses(graph) -> GraphAnalyses:
    library = _LibrarySkillAnalysis(
        graph, getattr(graph, 'library_profile', None))
    exemption = _ExemptionAnalysis(graph, library)
    breakpoints = _BreakPointAnalysis(graph, exemption, library)
    return GraphAnalyses(
        library, exemption, _CallerWeightAnalysis(graph, exemption),
        breakpoints, _SummaryAnalysis(graph, breakpoints, library))

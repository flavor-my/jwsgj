from __future__ import annotations  # noqa: I001
import ast
import hashlib
import logging
from collections import defaultdict
from collections.abc import Iterator
from dataclasses import dataclass, field
from itertools import chain, combinations
from typing import Any, ClassVar, NamedTuple
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    FUNC_NODE_TYPES,
    ast_name,
    calc_nesting,
    chain_depth,
    chain_spine_calls,
    class_body_owner,
    cognitive_complexity,
    collect_param_names,
    cyclomatic_complexity,
    definition_time_exprs,
    expr_target_name,
    has_type_hints,
    is_overload_stub,
    is_static_method,
    iter_arg_nodes,
    iter_params,
    iter_pattern_capture_names,
    iter_scope_nodes,
    iter_target_bindings,
    iter_unpack_target_names,
    parse_ast_safely,
    parse_py_source,
)
from jwsgj.diag_shared_ast_views import parent_map
from jwsgj.diag_shared_source_core import (
    coerce_source_text,
    node_line_span,
)
from jwsgj.diag_types_defs import (
    Finding,
    FindingRecord,
    FunctionReport,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    MSG_SYNTAX_ERROR_SKIP,
    WIRING_DECLARATION_ATTR,
    CodeRegion,
    Severity,
    Thresholds,
)
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    'WHOLE_FILE_ONLY_SMELL_RULES',
    'CPGSmellAnalyzer',
    'ComprehensiveDiagnoser',
    'FunctionExcellence',
    'SmellDetectorV3',
    'SmellInstance',
    'check_RD27',
]
logger = logging.getLogger(__name__)
logger.info("diag_smell_detector 坏味道检测域已加载: %d 项导出", len(__all__))
def _iter_function_nodes(tree: ast.AST):
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node
def _parse_smell_tree(code: Any) -> ast.Module | None:
    return parse_py_source(coerce_source_text(code))
@dataclass
class SmellInstance:
    smell_type: str = ""
    severity: Severity | None = None
    region: CodeRegion | None = None
    description: str = ""
    metrics: dict = field(default_factory=dict)
    suggestions: list = field(default_factory=list)
class _MessageChainVisitor(ast.NodeVisitor):
    def __init__(self, filepath: Any) -> None:
        self.filepath = filepath
        self.results: list[SmellInstance] = []
        self._suppressed: set[int] = set()
    def collect(self, tree: ast.AST) -> list[SmellInstance]:
        self.visit(tree)
        return list(self.results)
    def visit_Call(self, node: Any) -> None:
        if id(node) not in self._suppressed:
            depth = chain_depth(node.func)
            if depth >= 3:
                self.results.append(SmellInstance(
                    smell_type="message_chains",
                    severity=Severity.MEDIUM if depth >= 4 else Severity.LOW,
                    region=CodeRegion(file=self.filepath,
                                      start_line=node.lineno,
                                      end_line=node.end_lineno or node.lineno),
                    description=f"msg chain depth={depth}: a.b().c()...",
                    metrics={"chain_depth": depth},
                    suggestions=["Break chain with intermediate variable",
                                 "Add delegating method on intermediate object"],
                ))
                for sub in chain_spine_calls(node.func):
                    self._suppressed.add(id(sub))
        self.generic_visit(node)
def _build_clump_instance(common: Any, funcs: Any, filepath: Any) -> Any:
    param_list = sorted(common)
    func_list = sorted(funcs)
    return SmellInstance(
        smell_type="data_clumps",
        severity=Severity.MEDIUM,
        region=CodeRegion(file=filepath, start_line=0, end_line=0),
        description="Parameter group [{}] co-occurs in {} functions: {}".format(
            ", ".join(param_list), len(func_list), ", ".join(func_list)),
        metrics={"common_params": param_list, "functions": func_list,
                 "param_count": len(param_list), "func_count": len(func_list)},
        suggestions=["Extract parameter group into a parameter object",
                     "Group related parameters into a context class"],
    )
def _build_divergent_instance(cls_key: Any, clusters: Any, filepath: Any) -> Any:
    cls_name = cls_key[0]
    cls_line = cls_key[1] if len(cls_key) > 1 else 0
    desc_parts = []
    cluster_metrics = []
    for i, (methods, attrs) in enumerate(clusters):
        desc_parts.append("C{}:[{}]->[{}]".format(
            i + 1, ", ".join(sorted(methods)[:3]),
            ", ".join(sorted(attrs)[:4])))
        cluster_metrics.append({
            "methods": sorted(methods),
            "attrs": sorted(attrs),
        })
    return SmellInstance(
        smell_type="divergent_change",
        severity=Severity.HIGH,
        region=CodeRegion(file=filepath, start_line=cls_line,
                          end_line=cls_line),
        description="类 {} 存在 {} 个方法/属性聚类（发散式变化）: {}".format(
            cls_name, len(clusters), "; ".join(desc_parts)),
        metrics={"class": cls_name, "cluster_count": len(clusters),
                 "clusters": cluster_metrics},
        suggestions=["按聚类将类拆分为多个职责单一的类",
                     "将同聚类的属性与方法提取到独立的协作类"],
    )
def _iter_class_scope_defs(cls_node: ast.AST):
    for child in ast.iter_child_nodes(cls_node):
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield child
        elif isinstance(child, (ast.ClassDef, ast.Lambda)):
            continue
        else:
            yield from _iter_class_scope_defs(child)
def _build_incomplete_instance(cls_node: Any, unique_missing: Any, filepath: Any) -> Any:
    have_names = [h for h, m in unique_missing[:3]]
    miss_names = [m for h, m in unique_missing[:3]]
    return SmellInstance(
        smell_type="incomplete_library",
        severity=Severity.MEDIUM,
        region=CodeRegion(file=filepath,
                          start_line=cls_node.lineno,
                          end_line=cls_node.end_lineno or cls_node.lineno),
        description=f"类 {cls_node.name} 缺失方法: {', '.join(miss_names)} (已有: {', '.join(have_names)})",
        metrics={"missing_count": len(unique_missing),
                 "class": cls_node.name},
        suggestions=["补齐对称方法以完整封装成对操作",
                     "或将成对操作收敛到同一协作类"],
    )
def _tramp_param_names(node: Any, parents: dict) -> set[str]:
    fixed = {id(a) for a in iter_params(node.args)}
    return {a.arg for a in _public_param_nodes(node, parents)
            if id(a) in fixed}
@dataclass
class _ScopeBindings:
    names: set[str] = field(default_factory=set)
    global_names: set[str] = field(default_factory=set)
    nonlocal_names: set[str] = field(default_factory=set)
    comprehension_targets: set[int] = field(default_factory=set)
def _mark_comprehension_targets(child: Any, state: _ScopeBindings) -> None:
    for generator in child.generators:
        state.comprehension_targets.update(
            id(target) for target in walk_nodes(generator.target))
def _mark_store_name(child: ast.Name, state: _ScopeBindings) -> None:
    if (isinstance(child.ctx, (ast.Store, ast.Del))
            and id(child) not in state.comprehension_targets):
        state.names.add(child.id)
def _mark_alias_binding(child: ast.alias, state: _ScopeBindings) -> None:
    if child.name != "*":
        state.names.add(child.asname or child.name.split(".")[0])
def _mark_pattern_binding(child: Any, state: _ScopeBindings) -> None:
    if isinstance(child, ast.MatchMapping):
        if child.rest:
            state.names.add(child.rest)
        return
    if child.name:
        state.names.add(child.name)
_SCOPE_BINDING_HANDLERS: tuple[tuple[tuple[type, ...], Any], ...] = (
    ((ast.Global,), lambda child, state: state.global_names.update(child.names)),
    ((ast.Nonlocal,),
     lambda child, state: state.nonlocal_names.update(child.names)),
    ((ast.Name,), _mark_store_name),
    ((ast.alias,), _mark_alias_binding),
    ((ast.ExceptHandler, ast.MatchAs, ast.MatchStar, ast.MatchMapping),
     _mark_pattern_binding),
)
def _record_scope_binding(child: Any, state: _ScopeBindings) -> bool:
    if isinstance(child, FUNC_NODE_TYPES + (ast.ClassDef,)):
        state.names.add(child.name)
        return False
    if isinstance(child, ast.Lambda):
        return False
    for node_types, handler in _SCOPE_BINDING_HANDLERS:
        if isinstance(child, node_types):
            handler(child, state)
            break
    return True
def _scope_shadowing_names(node: Any) -> set[str]:
    state = _ScopeBindings(names=set(collect_param_names(node)))
    pending = [node.body] if isinstance(node, ast.Lambda) else list(node.body)
    while pending:
        child = pending.pop()
        if isinstance(child, COMP_SCOPE_NODES):
            _mark_comprehension_targets(child, state)
        if not _record_scope_binding(child, state):
            continue
        pending.extend(ast.iter_child_nodes(child))
    state.names.difference_update(state.nonlocal_names | state.global_names)
    state.names.update(state.global_names)
    return state.names
def _function_scope_frames(
    node: Any, bound: frozenset[str],
) -> list[tuple[ast.AST, frozenset[str]]]:
    local = bound.union(_scope_shadowing_names(node))
    frames: list[tuple[ast.AST, frozenset[str]]] = [
        (child, local) for child in node.body]
    frames.extend((expr, bound) for expr in definition_time_exprs(node))
    frames.extend((arg.annotation, bound) for arg in iter_arg_nodes(node.args)
                  if arg.annotation is not None)
    if getattr(node, "returns", None) is not None:
        frames.append((node.returns, bound))
    return frames
def _read_ref_name(node: ast.AST, bound: frozenset[str]) -> str | None:
    if isinstance(node, ast.AugAssign):
        node = node.target
        if not isinstance(node, ast.Name):
            return None
    elif not (isinstance(node, ast.Name)
              and isinstance(node.ctx, ast.Load)):
        return None
    return None if node.id in bound else node.id
def _loaded_names_in_scope(nodes: Any) -> set[str]:
    names: set[str] = set()
    pending: list[tuple[ast.AST, frozenset[str]]] = [
        (node, frozenset()) for node in nodes]
    while pending:
        node, bound = pending.pop()
        ref = _read_ref_name(node, bound)
        if ref is not None:
            names.add(ref)
        pending.extend(_scope_frame_children(node, bound))
    return names
def _tramp_instance(
        node: Any, filepath: Any, parents: dict) -> SmellInstance | None:
    param_names = _tramp_param_names(node, parents)
    if len(param_names) < 2:
        return None
    tramp = param_names - _loaded_names_in_scope(node.body)
    if not tramp or len(tramp) >= len(param_names):
        return None
    return SmellInstance(
        smell_type="tramp_data",
        severity=Severity.LOW,
        region=CodeRegion(file=filepath,
                          start_line=node.lineno,
                          end_line=node.end_lineno or node.lineno),
        description="'{}' has {} unused params: {}".format(
            node.name, len(tramp), ", ".join(sorted(tramp))),
        metrics={"function": node.name, "tramp_params": sorted(tramp),
                 "total_params": len(param_names)},
        suggestions=[f"Remove unused params from '{node.name}'",
                     "Or wrap in context object if pass-through"],
    )
def _qualified_function_name(node: ast.AST, parents: dict) -> str:
    parts = [node.name]
    parent = parents.get(node)
    while parent is not None:
        if isinstance(parent, FUNC_NODE_TYPES + (ast.ClassDef,)):
            parts.append(parent.name)
        parent = parents.get(parent)
    return ".".join(reversed(parts))
def _method_receiver_name(node: ast.AST) -> str:
    positional = [*node.args.posonlyargs, *node.args.args]
    if not positional or is_static_method(node):
        return ""
    return positional[0].arg
def _iter_method_body_nodes(body: list) -> Iterator[ast.AST]:
    pending = list(body)
    while pending:
        child = pending.pop()
        yield child
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda, ast.ClassDef)):
            continue
        pending.extend(ast.iter_child_nodes(child))
class CPGSmellAnalyzer:
    _SYMMETRIC_PAIRS: ClassVar[dict] = {
        'get_': 'set_', 'set_': 'get_',
        'add_': 'remove_', 'remove_': 'add_',
        'open_': 'close_', 'close_': 'open_',
        'start_': 'stop_', 'stop_': 'start_',
        'create_': 'delete_', 'delete_': 'create_',
        'read_': 'write_', 'write_': 'read_',
        'load_': 'save_', 'save_': 'load_',
        'begin_': 'end_', 'end_': 'begin_',
        'push_': 'pop_', 'pop_': 'push_',
    }
    _DETECTORS: ClassVar[tuple[tuple[str, str], ...]] = (
        ("message_chains", "detect_message_chains"),
        ("data_clumps", "detect_data_clumps"),
        ("tramp_data", "detect_tramp_data"),
        ("divergent_change", "detect_divergent_change"),
        ("parallel_inheritance", "detect_parallel_inheritance"),
        ("incomplete_library", "detect_incomplete_library"),
    )
    def __init__(self) -> None:
        self._tree = None
    def _prepare(self, code: Any, tree: ast.AST | None) -> None:
        if isinstance(tree, ast.AST):
            self._tree = tree
            return
        self._tree, _error = parse_ast_safely(coerce_source_text(code))
    def analyze(self, code: Any, filepath="",
                tree: ast.AST | None = None, *,
                smell_types: Any = None) -> Any:
        self._prepare(code, tree)
        if smell_types is None:
            allowed = None
        elif isinstance(smell_types, str):
            allowed = frozenset((smell_types,))
        else:
            allowed = frozenset(smell_types)
        results = []
        for smell_type, method_name in self._DETECTORS:
            if allowed is not None and smell_type not in allowed:
                continue
            try:
                found = getattr(self, method_name)(filepath)
                if found:
                    results.extend(found)
            except (AttributeError, KeyError, TypeError, ValueError,
                    RuntimeError) as e:
                logger.warning("CPG 检测器 %s 异常跳过(%s): %s", method_name,
                               filepath or "<code>", e)
        return results
    def detect_message_chains(self, filepath: Any) -> Any:
        if self._tree is None:
            return []
        return _MessageChainVisitor(filepath).collect(self._tree)[:8]
    def detect_data_clumps(self, filepath: Any) -> Any:
        if self._tree is None:
            return []
        func_params = self._collect_func_params()
        results = self._find_cooccurring_params(func_params, filepath)
        return results[:5]
    def _collect_func_params(self) -> Any:
        func_params = {}
        parents = parent_map(self._tree)
        for node in _iter_function_nodes(self._tree):
            if is_overload_stub(node):
                continue
            params = set(_clump_param_names(node, parents))
            if len(params) >= 3:
                name = _qualified_function_name(node, parents)
                func_params[(name, node.lineno)] = params
        return func_params
    def _find_cooccurring_params(self, func_params: Any, filepath: Any) -> Any:
        results = []
        param_funcs = defaultdict(list)
        for fkey, pset in func_params.items():
            key = frozenset(pset)
            if len(key) >= 3 and fkey[0] not in param_funcs[key]:
                param_funcs[key].append(fkey[0])
        detected_pairs = set()
        results.extend(self._check_overlap_matches(
            param_funcs, filepath, detected_pairs))
        results.extend(self._check_exact_matches(
            param_funcs, filepath, detected_pairs))
        return results
    def _check_overlap_matches(
            self, param_funcs: Any, filepath: Any,
            detected_pairs: Any) -> Any:
        results = []
        for (pset, funcs), (other_pset, other_funcs) in combinations(
                param_funcs.items(), 2):
            pair_key = frozenset((pset, other_pset))
            if pair_key in detected_pairs:
                continue
            common = pset & other_pset
            if len(common) < 3:
                continue
            detected_pairs.add(pair_key)
            all_funcs = list(dict.fromkeys(funcs + other_funcs))
            if len(all_funcs) >= 2:
                results.append(_build_clump_instance(common, all_funcs, filepath))
        return results
    def _check_exact_matches(self, param_funcs: Any, filepath: Any, detected_pairs: Any) -> Any:
        results = []
        for pset, funcs in param_funcs.items():
            if len(funcs) >= 2 and not any(pset in pair for pair in detected_pairs):
                results.append(_build_clump_instance(pset, funcs, filepath))
        return results
    def detect_tramp_data(self, filepath: Any) -> Any:
        if self._tree is None:
            return []
        results = []
        parents = parent_map(self._tree)
        for node in _iter_function_nodes(self._tree):
            instance = _tramp_instance(node, filepath, parents)
            if instance is not None:
                results.append(instance)
        return results[:10]
    def detect_divergent_change(self, filepath: Any) -> Any:
        if self._tree is None:
            return []
        class_method_attrs = self._collect_class_attrs()
        return self._build_divergent_results(class_method_attrs, filepath)
    def _self_attrs_in_method(self, func_node: Any) -> set:
        receiver = _method_receiver_name(func_node)
        if not receiver:
            return set()
        return {
            child.attr
            for child in _iter_method_body_nodes(func_node.body)
            if isinstance(child, ast.Attribute)
            and isinstance(child.value, ast.Name)
            and child.value.id == receiver
        }
    def _collect_class_attrs(self) -> Any:
        class_method_attrs: dict = {}
        for cls_node in walk_nodes(self._tree):
            if not isinstance(cls_node, ast.ClassDef):
                continue
            method_attrs = {}
            for item in _iter_class_scope_defs(cls_node):
                if item.name.startswith('__') and item.name.endswith('__'):
                    continue
                attrs = self._self_attrs_in_method(item)
                if attrs:
                    method_attrs[item.name] = attrs
            if method_attrs:
                class_method_attrs[(cls_node.name, cls_node.lineno)] = method_attrs
        return class_method_attrs
    def _build_divergent_results(self, class_method_attrs: Any, filepath: Any) -> Any:
        results = []
        for cls_key, func_attrs in class_method_attrs.items():
            if len(func_attrs) < 3:
                continue
            clusters = self._cluster_sets(func_attrs)
            if len(clusters) >= 2:
                results.append(_build_divergent_instance(cls_key, clusters, filepath))
        return results[:5]
    @staticmethod
    def _absorb_cluster(seed: str, func_attrs: Any,
                        assigned: set) -> tuple[set, set]:
        cluster_methods = {seed}
        cluster_attrs = set(func_attrs[seed])
        changed = True
        while changed:
            changed = False
            for name, attrs in func_attrs.items():
                if name in assigned or name in cluster_methods:
                    continue
                if not attrs & cluster_attrs:
                    continue
                cluster_methods.add(name)
                cluster_attrs |= attrs
                changed = True
        return cluster_methods, cluster_attrs
    @staticmethod
    def _cluster_sets(func_attrs: Any) -> Any:
        clusters = []
        assigned = set()
        for seed in func_attrs:
            if seed in assigned:
                continue
            methods, attrs = CPGSmellAnalyzer._absorb_cluster(
                seed, func_attrs, assigned)
            assigned |= methods
            clusters.append((methods, attrs))
        return clusters
    @staticmethod
    def _inheritance_base_key(cls_node: Any, base_name: str,
                              parents: dict) -> tuple[Any, str]:
        scope = parents.get(cls_node)
        while (scope is not None
               and not isinstance(scope, FUNC_NODE_TYPES + (ast.ClassDef,))):
            scope = parents.get(scope)
        return scope, base_name
    def _resolve_inheritance_base_key(self, cls_node: Any, base_name: str,
                                      parents: dict, class_definitions: dict
                                      ) -> tuple[Any, str]:
        usage_key = self._inheritance_base_key(cls_node, base_name, parents)
        scope, name = usage_key
        while True:
            if (scope, name) in class_definitions:
                return scope, name
            if scope is None:
                return usage_key
            scope = self._inheritance_base_key(scope, name, parents)[0]
            while isinstance(scope, ast.ClassDef):
                scope = self._inheritance_base_key(scope, name, parents)[0]
    def _collect_class_children(self) -> tuple[dict, dict[tuple[Any, str], int]]:
        class_children: defaultdict = defaultdict(list)
        base_lines: dict[tuple[Any, str], int] = {}
        parents = parent_map(self._tree)
        class_definitions = {}
        for node in walk_nodes(self._tree):
            if isinstance(node, ast.ClassDef):
                key = self._inheritance_base_key(node, node.name, parents)
                class_definitions.setdefault(key, node.lineno)
        for node in walk_nodes(self._tree):
            if isinstance(node, ast.ClassDef):
                for base in node.bases:
                    if isinstance(base, ast.Name):
                        key = self._resolve_inheritance_base_key(
                            node, base.id, parents, class_definitions)
                        class_children[key].append(node.name)
                        base_lines.setdefault(key, class_definitions.get(key, 0))
        return class_children, base_lines
    def detect_parallel_inheritance(self, filepath: Any) -> Any:
        if self._tree is None:
            return []
        results = []
        class_children, base_lines = self._collect_class_children()
        parents = [k for k, v in class_children.items() if len(v) >= 2]
        for left, right in combinations(parents, 2):
            if len(class_children[left]) != len(class_children[right]):
                continue
            left_name, right_name = left[1], right[1]
            line_left = base_lines.get(left, 0)
            line_right = base_lines.get(right, 0)
            results.append(SmellInstance(
                smell_type="parallel_inheritance",
                severity=Severity.MEDIUM,
                region=CodeRegion(file=filepath,
                                  start_line=min(line_left, line_right),
                                  end_line=max(line_left, line_right)),
                description=f"Parallel: '{left_name}' {class_children[left]!r} <-> '{right_name}' {class_children[right]!r}",
                metrics={"hierarchy_a": {left_name: class_children[left]},
                         "hierarchy_b": {right_name: class_children[right]}},
                suggestions=["Consider merging hierarchies",
                             "Use Strategy/Visitor to eliminate parallel subclasses"],
            ))
        return results[:3]
    def detect_incomplete_library(self, filepath: Any) -> Any:
        if self._tree is None:
            return []
        results = []
        for cls_node in walk_nodes(self._tree):
            if not isinstance(cls_node, ast.ClassDef):
                continue
            methods = {
                item.name for item in _iter_class_scope_defs(cls_node)}
            unique_missing = self._find_missing_pairs(methods)
            if unique_missing:
                results.append(_build_incomplete_instance(cls_node, unique_missing, filepath))
        return results[:5]
    def _missing_for_method(self, method: str, methods: Any) -> list:
        missing = []
        for prefix, sym_prefix in self._SYMMETRIC_PAIRS.items():
            if not method.startswith(prefix):
                continue
            sym_method = method.replace(prefix, sym_prefix, 1)
            if sym_method != method and sym_method not in methods:
                missing.append((method, sym_method))
        return missing
    def _find_missing_pairs(self, methods: Any) -> Any:
        missing_pairs = []
        for method in sorted(methods):
            missing_pairs.extend(self._missing_for_method(method, methods))
        unique: dict = {}
        for have, miss in missing_pairs:
            unique.setdefault(tuple(sorted((have, miss))), (have, miss))
        return list(unique.values())
def _public_param_nodes(node: ast.AST, parents: dict) -> list:
    args = iter_arg_nodes(node.args)
    has_positional = bool(node.args.posonlyargs or node.args.args)
    if (args and has_positional and class_body_owner(node, parents) is not None
            and not is_static_method(node)):
        return args[1:]
    return args
def _clump_param_names(node: ast.AST, parents: dict) -> tuple[str, ...]:
    return tuple(sorted(
        a.arg for a in _public_param_nodes(node, parents)
        if not a.arg.startswith('_')))
def _enclosing_func_map(tree: Any) -> dict:
    scope: dict = {}
    stack: list = [(tree, "<module>")]
    while stack:
        node, owner = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            owner = node.name
        scope[id(node)] = owner
        stack.extend(
            (child, owner) for child in ast.iter_child_nodes(node))
    return scope
def _lambda_scope_frames(
    node: ast.Lambda, bound: frozenset[str],
) -> list[tuple[ast.AST, frozenset[str]]]:
    local = bound.union(_scope_shadowing_names(node))
    frames = [(node.body, local)]
    frames.extend((default, bound) for default in definition_time_exprs(node))
    return frames
def _comprehension_scope_frames(
    node: ast.AST, bound: frozenset[str],
) -> list[tuple[ast.AST, frozenset[str]]]:
    frames: list[tuple[ast.AST, frozenset[str]]] = []
    local = bound
    for generator in node.generators:
        frames.append((generator.iter, local))
        frames.append((generator.target, local))
        local = local.union(
            name for name, _line, _col
            in iter_target_bindings(generator.target))
        frames.extend((condition, local) for condition in generator.ifs)
    result_exprs = ((node.key, node.value)
                    if isinstance(node, ast.DictComp) else (node.elt,))
    frames.extend((result, local) for result in result_exprs)
    return frames
def _scope_frame_children(node: ast.AST,
                          bound: frozenset[str]) -> list[tuple]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return _function_scope_frames(node, bound)
    if isinstance(node, ast.Lambda):
        return _lambda_scope_frames(node, bound)
    if isinstance(node, COMP_SCOPE_NODES):
        return _comprehension_scope_frames(node, bound)
    return [(child, bound) for child in ast.iter_child_nodes(node)]
def _expr_ref_names(expr: ast.AST | None) -> set:
    names: set = set()
    if expr is None:
        return names
    pending: list[tuple[ast.AST, frozenset[str]]] = [(expr, frozenset())]
    while pending:
        node, bound = pending.pop()
        ref = _read_ref_name(node, bound)
        if ref is not None:
            names.add(ref)
        pending.extend(_scope_frame_children(node, bound))
    return names
_PRIMITIVE_ANNOT_NAMES = frozenset(
    {'str', 'int', 'float', 'bool', 'bytes'})
def _is_primitive_annotation(annotation: ast.AST) -> bool:
    if isinstance(annotation, ast.Name):
        return annotation.id in _PRIMITIVE_ANNOT_NAMES
    if (isinstance(annotation, ast.BinOp)
            and isinstance(annotation.op, ast.BitOr)):
        return (_is_primitive_annotation(annotation.left)
                and _is_primitive_annotation(annotation.right))
    if isinstance(annotation, ast.Constant):
        if annotation.value is None:
            return True
        if isinstance(annotation.value, str):
            return all(
                part.strip() in _PRIMITIVE_ANNOT_NAMES
                or part.strip() == "None"
                for part in annotation.value.split("|"))
    return False
def _cn_decorator_refs(node: Any, called: set) -> None:
    for _dec in node.decorator_list:
        called |= _expr_ref_names(_dec)
def _cn_call_refs(node: Any, called: set) -> None:
    if isinstance(node.func, ast.Name):
        called.add(node.func.id)
    _cn_getattr_ref(node, called)
    for _arg in node.args:
        called |= _expr_ref_names(_arg)
    for _kw in node.keywords:
        called |= _expr_ref_names(_kw.value)
    _cn_all_extend_refs(node, called)
def _cn_getattr_ref(node: Any, called: set) -> None:
    if len(node.args) < 2 or ast_name(node.func) != "getattr":
        return
    _ga = node.args[1]
    if isinstance(_ga, ast.Constant) and isinstance(_ga.value, str):
        called.add(_ga.value)
def _is_all_method_call(node: Any) -> bool:
    return (isinstance(node.func, ast.Attribute)
            and node.func.attr in ("append", "extend", "insert")
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == "__all__")
def _all_method_literal_names(arg: Any) -> set:
    elements = getattr(arg, "elts", None) or [arg]
    return {elt.value for elt in elements
            if isinstance(elt, ast.Constant) and isinstance(elt.value, str)}
def _cn_all_extend_refs(node: Any, called: set) -> None:
    if not _is_all_method_call(node):
        return
    for _arg in node.args:
        called |= _all_method_literal_names(_arg)
def _cn_type_param_refs(node: Any, called: set) -> None:
    for type_param in getattr(node, "type_params", ()):
        for attr in ("bound", "default", "default_value"):
            expr = getattr(type_param, attr, None)
            if expr is not None:
                called |= _expr_ref_names(expr)
def _cn_funcdef_refs(node: Any, called: set) -> None:
    _cn_decorator_refs(node, called)
    _cn_type_param_refs(node, called)
    defaults = chain(node.args.defaults,
                     (d for d in node.args.kw_defaults if d is not None))
    annotations = (_arg.annotation for _arg in iter_arg_nodes(node.args)
                   if _arg.annotation is not None)
    for expr in chain(defaults, annotations, (node.returns,)):
        if expr is not None:
            called |= _expr_ref_names(expr)
def _cn_classdef_refs(node: Any, called: set) -> None:
    _cn_decorator_refs(node, called)
    _cn_type_param_refs(node, called)
    for _ref in (*node.bases,
                 *(_kw.value for _kw in node.keywords)):
        called |= _expr_ref_names(_ref)
def _collect_called_names(tree: Any, *, skip_body_of: Any = None) -> set:
    called = set()
    if isinstance(skip_body_of, ast.AST):
        skip_body_ids = {id(skip_body_of)}
    else:
        skip_body_ids = {id(node) for node in (skip_body_of or ())}
    pending = [tree]
    while pending:
        node = pending.pop()
        for node_types, channel in _CALLED_NAME_CHANNELS:
            if isinstance(node, node_types):
                channel(node, called)
                break
        if id(node) in skip_body_ids:
            continue
        pending.extend(ast.iter_child_nodes(node))
    return called
def _is_all_export_assign(node: Any, targets: list) -> bool:
    return (node.value is not None
            and any(isinstance(t, ast.Name) and t.id == "__all__"
                    for t in targets))
def _cn_all_export_refs(node: Any, called: set) -> None:
    pending = [node.value]
    while pending:
        expr = pending.pop()
        if isinstance(expr, ast.Constant):
            if isinstance(expr.value, str):
                called.add(expr.value)
            continue
        if isinstance(expr, ast.Starred):
            pending.append(expr.value)
        elif isinstance(expr, (ast.List, ast.Tuple, ast.Set)):
            pending.extend(expr.elts)
        elif isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
            pending.extend((expr.left, expr.right))
        elif isinstance(expr, ast.IfExp):
            called |= _expr_ref_names(expr.test)
            pending.extend((expr.body, expr.orelse))
        else:
            called |= _expr_ref_names(expr)
def _collect_assign_refs(node: Any, called: set) -> None:
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    if isinstance(node, ast.AnnAssign):
        called |= _expr_ref_names(node.annotation)
    if _is_all_export_assign(node, targets):
        _cn_all_export_refs(node, called)
    elif node.value is not None:
        called |= _expr_ref_names(node.value)
    if node.value is not None:
        for target in targets:
            called |= _expr_ref_names(target)
    if isinstance(node, ast.AugAssign):
        ref = _read_ref_name(node, frozenset())
        if ref is not None:
            called.add(ref)
def _is_trivial_body(body: list) -> bool:
    return all(
        isinstance(s, ast.Pass)
        or (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant))
        for s in body)
def _function_implementation_body(node: Any) -> list:
    body = list(node.body)
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[1:]
    return body
_UNITTEST_LIFECYCLE_METHODS = frozenset({
    'setUp', 'tearDown', 'setUpClass', 'tearDownClass',
    'asyncSetUp', 'asyncTearDown', 'setUpModule', 'tearDownModule',
})
_PYTEST_LIFECYCLE_METHODS = frozenset({
    'setup_method', 'teardown_method',
    'setup_class', 'teardown_class',
    'setup_function', 'teardown_function',
    'setup_module', 'teardown_module',
})
_PROTOCOL_HOOK_ENTRY_NAMES = frozenset({WIRING_DECLARATION_ATTR})
def _is_framework_entry_name(name: str) -> bool:
    return (name.startswith(('test_', 'pytest_'))
            or name in _UNITTEST_LIFECYCLE_METHODS
            or name in _PYTEST_LIFECYCLE_METHODS
            or name in _PROTOCOL_HOOK_ENTRY_NAMES)
def _chained_if_ids(tree: Any) -> set[int]:
    chained: set[int] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, ast.If) and len(node.orelse) == 1
                and isinstance(node.orelse[0], ast.If)):
            chained.add(id(node.orelse[0]))
    return chained
def _if_chain_length(node: ast.If) -> int:
    conditions = 0
    current: Any = node
    while current is not None:
        conditions += 1
        orelse = current.orelse
        if len(orelse) == 1 and isinstance(orelse[0], ast.If):
            current = orelse[0]
        else:
            current = None
    return conditions
_CPG_SMELL_MAP: dict[str, str] = {
    "tramp_data": "SMELL-TRAMP-DATA",
    "divergent_change": "SMELL-DIVERGENT-CHANGE",
    "parallel_inheritance": "SMELL-PARALLEL-INHERITANCE",
    "incomplete_library": "SMELL-INCOMPLETE-LIBRARY",
}
def _metric_location(metrics: dict, keys: tuple[str, ...]) -> str | None:
    for key in keys:
        val = metrics.get(key)
        if isinstance(val, str) and val:
            return val
    return None
def _hierarchy_pair_location(metrics: dict) -> str | None:
    a_map = metrics.get("hierarchy_a")
    b_map = metrics.get("hierarchy_b")
    if not isinstance(a_map, dict) or not isinstance(b_map, dict):
        return None
    a = next(iter(a_map), "")
    b = next(iter(b_map), "")
    if not (isinstance(a, str) and isinstance(b, str) and a and b):
        return None
    return f"{a} ≡ {b}"
_CPG_LOCATION_RESOLVERS: dict = {
    "tramp_data": lambda m: _metric_location(m, ("function",)),
    "divergent_change": lambda m: _metric_location(m, ("class",)),
    "incomplete_library": lambda m: _metric_location(m, ("class",)),
    "parallel_inheritance": _hierarchy_pair_location,
}
def _cpg_semantic_location(sm: Any) -> str:
    resolver = _CPG_LOCATION_RESOLVERS.get(getattr(sm, "smell_type", None))
    metrics = getattr(sm, "metrics", None)
    location = resolver(metrics) if (resolver is not None
                                     and isinstance(metrics, dict)) else None
    if location:
        return location
    file = getattr(getattr(sm, "region", None), "file", None)
    return file if isinstance(file, str) else ""
def _first_suggestion(suggestions: Any) -> str:
    if isinstance(suggestions, str):
        return suggestions
    if isinstance(suggestions, (list, tuple)):
        for item in suggestions:
            if isinstance(item, str):
                return item
    return ""
def _iter_clump_pairs(func_params: list) -> Any:
    for i, (p1, n1, ln1) in enumerate(func_params):
        for p2, n2, _ln2 in func_params[i + 1:]:
            if n1 == n2:
                continue
            overlap = set(p1) & set(p2)
            if len(overlap) >= 3:
                yield overlap, n1, n2, ln1
def _cn_return_refs(node: Any, called: set) -> None:
    if node.value is not None:
        called |= _expr_ref_names(node.value)
def _cn_cond_refs(node: Any, called: set) -> None:
    for attr in ("test", "iter", "target", "value", "msg"):
        expr = getattr(node, attr, None)
        if expr is not None:
            called |= _expr_ref_names(expr)
def _cn_raise_refs(node: Any, called: set) -> None:
    for expr in (node.exc, node.cause):
        if expr is not None:
            called |= _expr_ref_names(expr)
def _cn_delete_refs(node: Any, called: set) -> None:
    for target in node.targets:
        called.update(node_name.id for node_name in walk_nodes(target)
                      if isinstance(node_name, ast.Name))
def _cn_with_refs(node: Any, called: set) -> None:
    for item in node.items:
        called |= _expr_ref_names(item.context_expr)
        if item.optional_vars is not None:
            called |= _expr_ref_names(item.optional_vars)
def _cn_expr_stmt_refs(node: Any, called: set) -> None:
    called |= _expr_ref_names(node.value)
def _cn_comp_refs(node: Any, called: set) -> None:
    called |= _expr_ref_names(node)
def _cn_match_refs(node: ast.Match, called: set) -> None:
    called |= _expr_ref_names(node.subject)
    for case in node.cases:
        called |= _expr_ref_names(case.pattern)
        called |= _expr_ref_names(case.guard)
def _cn_type_alias_refs(node: Any, called: set) -> None:
    _cn_type_param_refs(node, called)
    called |= _expr_ref_names(node.value)
_TYPE_ALIAS_NODE_TYPES = (ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ()
_CALLED_NAME_CHANNELS = (
    ((ast.Call,), _cn_call_refs),
    ((ast.FunctionDef, ast.AsyncFunctionDef), _cn_funcdef_refs),
    ((ast.ClassDef,), _cn_classdef_refs),
    ((ast.Return, ast.Yield, ast.YieldFrom), _cn_return_refs),
    ((ast.Raise,), _cn_raise_refs),
    ((ast.Delete,), _cn_delete_refs),
    ((ast.With, ast.AsyncWith), _cn_with_refs),
    ((ast.Assign, ast.AnnAssign, ast.AugAssign), _collect_assign_refs),
    ((ast.If, ast.While, ast.Assert, ast.For, ast.AsyncFor, ast.NamedExpr),
     _cn_cond_refs),
    ((ast.Expr,), _cn_expr_stmt_refs),
    ((ast.Match,), _cn_match_refs),
    (_TYPE_ALIAS_NODE_TYPES, _cn_type_alias_refs),
    ((ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp),
     _cn_comp_refs),
)
_LARGE_CLASS_LINES = 300
WHOLE_FILE_ONLY_SMELL_RULES: frozenset[str] = frozenset({"SMELL-DEAD-CODE"})
class SmellDetectorV3:
    _RULE_CATALOG: ClassVar[dict[str, tuple[str, str, Severity]]] = {
        "SMELL-LONG-METHOD": ("Long Method", "Extract Method 拆分",
                              Severity.HIGH),
        "SMELL-LARGE-CLASS": ("Large Class",
                              "Extract Class / Extract Subclass",
                              Severity.HIGH),
        "SMELL-PRIMITIVE-OBSESSION": ("Primitive Obsession",
                                      "引入值对象(Value Object)封装",
                                      Severity.MEDIUM),
        "SMELL-LONG-PARAM-LIST": ("Long Parameter List",
                                  "Introduce Parameter Object",
                                  Severity.MEDIUM),
        "SMELL-DATA-CLUMPS": ("Data Clumps",
                              "Introduce Parameter Object / Extract Class",
                              Severity.MEDIUM),
        "SMELL-DUPLICATED-CODE": ("Duplicated Code",
                                  "Extract Method 提取公共逻辑",
                                  Severity.CRITICAL),
        "SMELL-SWITCH": ("Switch Statements", "用字典映射或多态替换",
                         Severity.LOW),
        "SMELL-DEAD-CODE": ("Dead Code",
                            "确认后移除,或在注释中说明保留原因",
                            Severity.MEDIUM),
        "SMELL-MESSAGE-CHAINS": ("Message Chains",
                                 "Hide Delegate / Introduce Middle Man",
                                 Severity.MEDIUM),
        "SMELL-TRAMP-DATA": ("Tramp Data", "", Severity.LOW),
        "SMELL-DIVERGENT-CHANGE": ("Divergent Change", "", Severity.HIGH),
        "SMELL-PARALLEL-INHERITANCE": ("Parallel Inheritance", "",
                                       Severity.MEDIUM),
        "SMELL-INCOMPLETE-LIBRARY": ("Incomplete Library", "",
                                     Severity.MEDIUM),
    }
    SMELL_SEVERITY: ClassVar[dict] = {
        rule_id: severity
        for rule_id, (_name, _suggestion, severity) in _RULE_CATALOG.items()
    }
    def _finding(self, rule_id: str, location: str, line: int,
                 message: str, metrics: dict) -> Finding:
        _smell, suggestion, severity = self._RULE_CATALOG[rule_id]
        return Finding(
            rule_id=rule_id,
            severity=severity,
            location=location, line=line,
            message=message, suggestion=suggestion,
            metrics=metrics)
    def detect_all(self, code: str,
                   tree: ast.AST | None = None) -> list[Finding]:
        findings = []
        tree = tree if isinstance(tree, ast.AST) else _parse_smell_tree(code)
        if tree is None:
            return []
        detectors = [
            self._detect_long_method, self._detect_large_class,
            self._detect_primitive_obsession,
            self._detect_long_parameter_list, self._detect_data_clumps,
            self._detect_duplicated_code, self._detect_switch_statements,
            self._detect_dead_code, self._detect_message_chains,
        ]
        for detector in detectors:
            try:
                findings.extend(detector(tree))
            except (AttributeError, KeyError, TypeError, ValueError,
                    RuntimeError) as e:
                logger.warning("SmellDetectorV3 检测器 %s 异常跳过: %s",
                               detector.__name__, e)
        findings.extend(self._detect_cpg_enhanced(code, tree))
        return findings
    def _detect_long_method(self, tree: Any) -> list[Finding]:
        findings = []
        for node in _iter_function_nodes(tree):
            lines = node_line_span(node)
            if lines > Thresholds.FUNC_LINES_BLOCK:
                findings.append(self._finding(
                    "SMELL-LONG-METHOD", node.name, node.lineno,
                    f"长函数: {node.name}({lines}行)",
                    {"lines": lines}))
        return findings
    def _detect_large_class(self, tree: Any) -> list[Finding]:
        findings = []
        for node in walk_nodes(tree):
            if isinstance(node, ast.ClassDef):
                lines = node_line_span(node)
                if lines > _LARGE_CLASS_LINES:
                    findings.append(self._finding(
                        "SMELL-LARGE-CLASS", node.name, node.lineno,
                        f"大类: {node.name}({lines}行)",
                        {"lines": lines}))
        return findings
    def _detect_primitive_obsession(self, tree: Any) -> list[Finding]:
        findings = []
        parents = parent_map(tree)
        for node in _iter_function_nodes(tree):
            variadic = {id(arg) for arg in (node.args.vararg, node.args.kwarg)
                        if arg is not None}
            primitive_params = sum(
                1 for arg in _public_param_nodes(node, parents)
                if id(arg) not in variadic
                and (not arg.annotation
                     or _is_primitive_annotation(arg.annotation)))
            if primitive_params > 4:
                findings.append(self._finding(
                    "SMELL-PRIMITIVE-OBSESSION", node.name, node.lineno,
                    f"原始类型偏执: {node.name} 有 {primitive_params} 个原始类型参数",
                    {"primitive_params": primitive_params}))
        return findings
    def _detect_long_parameter_list(self, tree: Any) -> list[Finding]:
        findings = []
        parents = parent_map(tree)
        for node in _iter_function_nodes(tree):
            params = len(_public_param_nodes(node, parents))
            if params > Thresholds.PARAMS_BLOCK:
                findings.append(self._finding(
                    "SMELL-LONG-PARAM-LIST", node.name, node.lineno,
                    f"长参数列表: {node.name}({params}个参数)",
                    {"params": params}))
        return findings
    def _detect_data_clumps(self, tree: Any) -> list[Finding]:
        findings = []
        parents = parent_map(tree)
        func_params = []
        for node in _iter_function_nodes(tree):
            if is_overload_stub(node):
                continue
            param_names = _clump_param_names(node, parents)
            qualified_name = _qualified_function_name(node, parents)
            if len(param_names) >= 3:
                func_params.append((param_names, qualified_name, node.lineno))
        for overlap, n1, n2, ln1 in _iter_clump_pairs(func_params):
            findings.append(self._finding(
                "SMELL-DATA-CLUMPS", f"{n1} ≡ {n2}", ln1,
                f"数据泥团: {', '.join(sorted(overlap)[:5])} 在多个函数中共同出现",
                {"shared_params": len(overlap)}))
        return findings[:5]
    def _detect_duplicated_code(self, tree: Any) -> list[Finding]:
        findings = []
        func_bodies = {}
        for node in _iter_function_nodes(tree):
            body = _function_implementation_body(node)
            if _is_trivial_body(body):
                continue
            body_str = ''.join(
                ast.dump(s, annotate_fields=False)
                for s in body)
            fingerprint = hashlib.md5(body_str.encode(), usedforsecurity=False).hexdigest()[:12]
            if fingerprint in func_bodies:
                original = func_bodies[fingerprint]
                findings.append(self._finding(
                    "SMELL-DUPLICATED-CODE", f"{node.name} ≡ {original}",
                    node.lineno,
                    f"重复代码: {node.name} 与 {original} 函数体相同",
                    {"fingerprint": fingerprint}))
            else:
                func_bodies[fingerprint] = node.name
        return findings
    def _detect_switch_statements(self, tree: Any) -> list[Finding]:
        findings = []
        scope = _enclosing_func_map(tree)
        chained = _chained_if_ids(tree)
        for node in walk_nodes(tree):
            if isinstance(node, ast.If) and id(node) not in chained:
                conditions = _if_chain_length(node)
                if conditions >= 5:
                    findings.append(self._finding(
                        "SMELL-SWITCH", scope.get(id(node), "<module>"),
                        node.lineno,
                        f"长条件链: {conditions} 个条件分支",
                        {"branches": conditions}))
        return findings
    def _detect_dead_code(self, tree: Any) -> list[Finding]:
        findings = []
        all_defs = {}
        shadowed_defs = []
        for node in getattr(tree, "body", ()):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name in all_defs:
                    shadowed_defs.append(all_defs[node.name])
                all_defs[node.name] = node
        external_called = _collect_called_names(
            tree, skip_body_of=[*shadowed_defs, *all_defs.values()])
        reachable = {
            name for name, node in all_defs.items()
            if (name in external_called or node.decorator_list
                or _is_framework_entry_name(name)
                or (name.startswith('__') and name.endswith('__')))
        }
        pending = list(reachable)
        while pending:
            node = all_defs[pending.pop()]
            body_called = set()
            for statement in node.body:
                body_called |= _collect_called_names(statement)
            for name in body_called.intersection(all_defs):
                if name not in reachable:
                    reachable.add(name)
                    pending.append(name)
        unused = set(all_defs) - reachable
        for name in sorted(unused):
            node = all_defs[name]
            if node.decorator_list:
                continue
            findings.append(self._finding(
                "SMELL-DEAD-CODE", name, node.lineno,
                f"可能的死代码: {name} 未被调用",
                {}))
        return findings
    def _detect_cpg_enhanced(self, code: str,
                             tree: ast.AST | None) -> list[Finding]:
        findings: list[Finding] = []
        try:
            smells = CPGSmellAnalyzer().analyze(
                code, "<smell_detector>", tree=tree,
                smell_types=tuple(_CPG_SMELL_MAP))
        except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as e:
            logger.warning("CPG 增强坏味道检测降级跳过: %s", e)
            return findings
        for sm in smells:
            try:
                finding = self._cpg_finding(sm)
            except (AttributeError, KeyError, TypeError, ValueError,
                    RuntimeError) as e:
                logger.warning("CPG 单条坏味映射降级跳过: %s", e)
                continue
            if finding is not None:
                findings.append(finding)
        return findings
    def _cpg_finding(self, sm: Any) -> Finding | None:
        rule_id = _CPG_SMELL_MAP.get(getattr(sm, "smell_type", None))
        if rule_id is None:
            return None
        start_line = getattr(getattr(sm, "region", None), "start_line", 0)
        line = start_line if (isinstance(start_line, int)
                              and not isinstance(start_line, bool)
                              and start_line >= 0) else 0
        metrics = getattr(sm, "metrics", None)
        return Finding(
            rule_id=rule_id,
            severity=self.SMELL_SEVERITY.get(rule_id, Severity.MEDIUM),
            location=_cpg_semantic_location(sm), line=line,
            message=getattr(sm, "description", "") or rule_id,
            suggestion=_first_suggestion(getattr(sm, "suggestions", None)),
            metrics=dict(metrics) if isinstance(metrics, dict) else {},
        )
    def _detect_message_chains(self, tree: Any) -> list[Finding]:
        findings = []
        scope = _enclosing_func_map(tree)
        suppressed: set[int] = set()
        for node in walk_nodes(tree):
            if isinstance(node, ast.Call):
                if id(node) in suppressed:
                    continue
                chain_length = chain_depth(node.func)
                if chain_length >= 4:
                    findings.append(self._finding(
                        "SMELL-MESSAGE-CHAINS", scope.get(id(node), "<module>"),
                        node.lineno,
                        f"消息链: 深度 {chain_length}",
                        {"chain_length": chain_length}))
                    for sub in chain_spine_calls(node.func):
                        suppressed.add(id(sub))
        return findings[:10]
def _keyword_hits(name: str, keyword: str) -> bool:
    if keyword.endswith("_"):
        return name.startswith(keyword)
    return name == keyword or name.startswith(keyword + "_")
def _iter_call_names(func: Any) -> Iterator[str]:
    for node in iter_scope_nodes(func):
        if isinstance(node, ast.Call):
            name = expr_target_name(node.func).lower()
            if name:
                yield name
def _names_hit_keywords(names: list[str], keywords: tuple[str, ...]) -> bool:
    return any(_keyword_hits(name, keyword)
               for name in names for keyword in keywords)
def _find_effective_function(tree: ast.AST, function_name: str) -> Any:
    if isinstance(tree, ast.Module) and function_name:
        definitions = [
            node for node in tree.body
            if isinstance(node, FUNC_NODE_TYPES) and node.name == function_name
            and not is_overload_stub(node)
        ]
        if definitions:
            return definitions[-1]
    definitions = [
        node for node in walk_nodes(tree)
        if isinstance(node, FUNC_NODE_TYPES) and node.name == function_name
        and not is_overload_stub(node)
    ]
    if not definitions:
        return None
    parents = parent_map(tree)
    def definition_scope(node: ast.AST) -> ast.AST | None:
        scope = parents.get(node)
        while (scope is not None and not isinstance(
                scope, (ast.Module, ast.ClassDef) + FUNC_NODE_TYPES)):
            scope = parents.get(scope)
        return scope
    selected_scope = definition_scope(definitions[0])
    return [
        node for node in definitions
        if definition_scope(node) is selected_scope
    ][-1]
def _function_position_index(tree: ast.AST) -> dict[tuple[str, int, int], Any]:
    index: dict[tuple[str, int, int], Any] = {}
    for node in walk_nodes(tree):
        if isinstance(node, FUNC_NODE_TYPES):
            index.setdefault(
                (node.name, node.lineno, node.col_offset), node)
    return index
_SLAP_LOW_LEVEL_KEYWORDS: tuple[str, ...] = (
    'len', 'range', 'int', 'str', 'append', 'pop',
)
_SLAP_HIGH_LEVEL_KEYWORDS: tuple[str, ...] = (
    'handle_', 'process_', 'create_', 'initialize_',
)
class _FuncMetrics(NamedTuple):
    lines: int
    params: int
    cyclomatic: int
    cognitive: int
    nesting: int
    has_docstring: bool
    has_annotations: bool
class _MetricSpec(NamedTuple):
    key: str
    block_attr: str
    rec_attr: str | None
    block_spec: tuple
    rec_spec: tuple | None
    block_penalty: int
    rec_penalty: int
class FunctionExcellence:
    def __init__(self) -> None:
        self._relocate_tree: ast.AST | None = None
        self._relocate_index: dict[tuple[str, int, int], Any] = {}
    def _relocate_function(self, tree: ast.AST, func_node: Any) -> Any:
        if tree is not self._relocate_tree:
            self._relocate_index = _function_position_index(tree)
            self._relocate_tree = tree
        candidate = self._relocate_index.get(
            (func_node.name, func_node.lineno, func_node.col_offset))
        if candidate is None:
            return None
        if candidate is not func_node and (
                ast.dump(candidate, include_attributes=False)
                != ast.dump(func_node, include_attributes=False)):
            return None
        return candidate
    def analyze(self, code: str, function_name: str = "",
                tree: ast.AST | None = None,
                func_node: Any = None) -> FunctionReport | None:
        func, resolved_tree = self._resolve_target_func(
            code, function_name, tree, func_node)
        if func is None or is_overload_stub(func):
            return None
        name = func.name
        m = _FuncMetrics(
            lines=node_line_span(func),
            params=self._count_public_params(func, resolved_tree),
            cyclomatic=cyclomatic_complexity(func),
            cognitive=cognitive_complexity(func),
            nesting=calc_nesting(func),
            has_docstring=ast.get_docstring(func) is not None,
            has_annotations=has_type_hints(func),
        )
        violations = self._check_srp(func)
        slap_issues = self._check_slap(func)
        findings = self._collect_findings(m, name, func.lineno)
        suggestions = self._collect_quality_suggestions(m, slap_issues)
        score = self._calculate_score(m, len(violations))
        return FunctionReport(
            name=name,
            score=score,
            lines=m.lines,
            params=m.params,
            cyclomatic_complexity=m.cyclomatic,
            cognitive_complexity=m.cognitive,
            nesting_depth=m.nesting,
            has_docstring=m.has_docstring,
            has_type_annotations=m.has_annotations,
            violates_srp=bool(violations),
            slap_violations=slap_issues,
            findings=findings,
            suggestions=suggestions,
            summary=self._generate_summary(score),
        )
    def _resolve_target_func(self, code: str, function_name: str,
                              tree: ast.AST | None,
                              func_node: Any) -> tuple[Any, ast.AST | None]:
        if func_node is not None:
            if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return None, None
            if tree is not None:
                if not isinstance(tree, ast.AST):
                    return None, None
                relocated = self._relocate_function(tree, func_node)
                if relocated is None:
                    logger.warning(
                        "[FunctionExcellence] 函数节点不属于显式 AST，放弃函数级度量: %s",
                        function_name or func_node.name)
                    return None, None
                return relocated, tree
            resolved = _parse_smell_tree(code)
            if resolved is None:
                logger.warning(
                    "[FunctionExcellence] 源码不可解析，放弃函数级度量: %s",
                    function_name or getattr(func_node, "name", "<unknown>"))
                return None, None
            relocated = self._relocate_function(resolved, func_node)
            if relocated is None:
                logger.warning(
                    "[FunctionExcellence] 函数节点无法重定位，放弃函数级度量: "
                    "%s", function_name or getattr(func_node, "name", "<unknown>"))
                return None, None
            return relocated, resolved
        resolved_tree = tree if tree is not None else _parse_smell_tree(code)
        if resolved_tree is None:
            return None, None
        return _find_effective_function(resolved_tree, function_name), resolved_tree
    @staticmethod
    def _count_public_params(func: Any, tree: ast.AST | None) -> int:
        if tree is None:
            return len(list(iter_arg_nodes(func.args)))
        return len(_public_param_nodes(func, parent_map(tree)))
    _FUNCTION_METRIC_SPECS: ClassVar[tuple[_MetricSpec, ...]] = (
        _MetricSpec("lines", "FUNC_LINES_BLOCK", "FUNC_LINES_RECOMMEND",
         ("FUNC-01", Severity.CRITICAL,
          "函数 {v} 行,超过上限 {t}", "拆分函数,每个≤{rt}行", "lines"),
         ("FUNC-01", Severity.MEDIUM,
          "函数 {v} 行,建议≤{t}", "考虑 Extract Method 拆分", "lines"),
         30, 10),
        _MetricSpec("params", "PARAMS_BLOCK", "PARAMS_RECOMMEND",
         ("FUNC-02", Severity.HIGH,
          "参数 {v} 个,超过上限 {t}",
          "使用数据类/字典封装,或拆分为多个函数", "params"),
         ("FUNC-02", Severity.MEDIUM,
          "参数 {v} 个,建议≤{t}", "使用参数对象封装关联参数", "params"),
         20, 10),
        _MetricSpec("cyclomatic", "CYCLOMATIC_BLOCK", "CYCLOMATIC_RECOMMEND",
         ("FUNC-03", Severity.CRITICAL,
          "圈复杂度 {v},超过阻断值 {t}",
          "Extract Method 降低分支数", "cyclomatic"),
         ("FUNC-03", Severity.MEDIUM,
          "圈复杂度 {v},建议≤{t}",
          "拆分条件分支或提取判定函数", "cyclomatic"),
         25, 10),
        _MetricSpec("cognitive", "COGNITIVE_BLOCK", "COGNITIVE_RECOMMEND",
         ("FUNC-04", Severity.HIGH,
          "认知复杂度 {v},超过上限", "重组嵌套结构和条件逻辑",
          "cognitive"),
         ("FUNC-04", Severity.MEDIUM,
          "认知复杂度 {v},建议≤{t}", "提取内聚子逻辑降低认知负担",
          "cognitive"),
         20, 10),
        _MetricSpec("nesting", "NESTING_BLOCK", None,
         ("FUNC-05", Severity.HIGH,
          "最大嵌套深度 {v},超过 {t}", "使用 Guard Clause 或 Extract Method",
          "nesting"),
         None, 15, 0),
    )
    @staticmethod
    def _spec_finding(spec: tuple, value: int, threshold: int, recommend: int,
                      name: str, lineno: int) -> Finding:
        rule_id, severity, msg_t, sugg_t, key = spec
        return Finding(
            rule_id=rule_id, severity=severity,
            location=f"{name}", line=lineno,
            message=msg_t.format(v=value, t=threshold, rt=recommend),
            suggestion=sugg_t.format(v=value, t=threshold, rt=recommend),
            metrics={key: value})
    @staticmethod
    def _recommend_threshold(spec: _MetricSpec, block_t: int) -> int:
        return (getattr(Thresholds, spec.rec_attr)
                if spec.rec_attr is not None else block_t)
    @staticmethod
    def _collect_findings(m: _FuncMetrics, name: str, lineno: int) -> list:
        findings = []
        for spec in FunctionExcellence._FUNCTION_METRIC_SPECS:
            value = getattr(m, spec.key)
            block_t = getattr(Thresholds, spec.block_attr)
            rec_t = FunctionExcellence._recommend_threshold(spec, block_t)
            if value > block_t:
                findings.append(FunctionExcellence._spec_finding(
                    spec.block_spec, value, block_t, rec_t, name, lineno))
            elif spec.rec_spec is not None and value > rec_t:
                findings.append(FunctionExcellence._spec_finding(
                    spec.rec_spec, value, rec_t, rec_t, name, lineno))
        return findings
    @staticmethod
    def _collect_quality_suggestions(m: _FuncMetrics,
                                     slap_issues: list) -> list:
        suggestions = []
        if not m.has_docstring:
            suggestions.append("添加函数文档字符串 (docstring)")
        if not m.has_annotations:
            suggestions.append("添加参数和返回值类型注解")
        if m.params >= 3:
            suggestions.append(f"参数较多({m.params}个),考虑封装或拆分")
        if slap_issues:
            suggestions.append(f"SLAP违规: {'; '.join(slap_issues[:3])}")
        return suggestions
    _SRP_CATEGORY_KEYWORDS: ClassVar[tuple[tuple[str, ...], ...]] = (
        ('open', 'read', 'write', 'print'),
        ('calc', 'compute', 'sum', 'avg'),
        ('format', 'render'),
        ('validate', 'check', 'assert'),
    )
    def _check_srp(self, func: Any) -> list[str]:
        names = list(_iter_call_names(func))
        hit_count = sum(
            1 for kws in self._SRP_CATEGORY_KEYWORDS
            if _names_hit_keywords(names, kws))
        if hit_count >= 3:
            return ["函数混合了多种不相关的职责类型"]
        return []
    def _check_slap(self, func: Any) -> list[str]:
        names = list(_iter_call_names(func))
        if (_names_hit_keywords(names, _SLAP_LOW_LEVEL_KEYWORDS)
                and _names_hit_keywords(names, _SLAP_HIGH_LEVEL_KEYWORDS)):
            return ["混合了底层操作和高层调用,违反SLAP原则"]
        return []
    @staticmethod
    def _dimension_penalty(value: int, block_t: int, rec_t: int | None,
                           block_p: int, rec_p: int) -> int:
        if value > block_t:
            return block_p
        if rec_t is not None and value > rec_t:
            return rec_p
        return 0
    def _calculate_score(self, m: _FuncMetrics, srp_count: int) -> int:
        penalty = sum(
            self._dimension_penalty(
                getattr(m, spec.key), getattr(Thresholds, spec.block_attr),
                (getattr(Thresholds, spec.rec_attr)
                 if spec.rec_attr is not None else None),
                spec.block_penalty, spec.rec_penalty)
            for spec in self._FUNCTION_METRIC_SPECS
        )
        penalty += 0 if m.has_docstring else 5
        penalty += 0 if m.has_annotations else 5
        penalty += 10 if srp_count > 0 else 0
        return max(0, min(100, 100 - penalty))
    _SUMMARY_BANDS: ClassVar[tuple[tuple[int, str], ...]] = (
        (90, "优秀: 函数质量高,几乎无需改进"),
        (70, "良好: 函数质量可接受,有少量改进空间"),
        (50, "一般: 建议重构,存在多处可改进点"),
    )
    def _generate_summary(self, score: int) -> str:
        for floor, text in self._SUMMARY_BANDS:
            if score >= floor:
                return text
        return "差: 强烈建议重构,多项指标不达标"
class ComprehensiveDiagnoser:
    def __init__(self) -> None:
        self.smell_detector = SmellDetectorV3()
        self.func_excellence = FunctionExcellence()
    @staticmethod
    def _degraded_payload(reason: str) -> dict:
        return {
            "smells": [], "recommendations": [],
            "overall_score": 0, "maintainability_index": 0.0,
            "analysis_complete": False, "error": reason,
        }
    def _analyze_all_functions(self, code: str,
                               tree: ast.AST | None) -> list[FunctionReport]:
        resolved = tree if tree is not None else _parse_smell_tree(code)
        if resolved is None:
            logger.warning(MSG_SYNTAX_ERROR_SKIP)
            return []
        reports = []
        for node in walk_nodes(resolved):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                report = self.func_excellence.analyze(
                    code, node.name, tree=resolved, func_node=node)
                if report is not None:
                    reports.append(report)
        return reports
    @staticmethod
    def _to_smell_dicts(findings) -> list[dict]:
        smells = []
        for f in findings:
            if not hasattr(f, "rule_id"):
                continue
            _sev = getattr(f, "severity", "MEDIUM")
            smells.append({
                "rule_id": getattr(f, "rule_id", ""),
                "message": getattr(f, "message", ""),
                "severity": getattr(_sev, "value", _sev),
                "line": getattr(f, "line", 0),
            })
        return smells
    def diag_code(self, code: str, smell_findings: list | None = None) -> dict:
        if not isinstance(code, str) or not code.strip():
            return self._degraded_payload("invalid_code")
        tree = _parse_smell_tree(code)
        if tree is None:
            return self._degraded_payload("syntax_error")
        findings = (smell_findings if smell_findings is not None
                    else self.smell_detector.detect_all(code, tree))
        smells = self._to_smell_dicts(findings)
        func_reports = self._analyze_all_functions(code, tree)
        avg_score = (sum(r.score for r in func_reports)
                     / len(func_reports)) if func_reports else 100.0
        overall = max(0, min(100, int(avg_score - len(smells) * 5)))
        recs = [f"{s['rule_id']}: {s['message']}" for s in smells]
        return {
            "smells": smells,
            "recommendations": recs,
            "overall_score": overall,
            "maintainability_index": round(
                max(0.0, (100 - len(smells) * 10) / 100.0), 3),
            "analysis_complete": True,
        }
def _rd27_rebind_assign_targets(assign: Any) -> set[str]:
    names: set[str] = set()
    for _tgt in assign.targets:
        names.update(iter_unpack_target_names(_tgt))
    return names
def _rd27_rebind_with_items(with_node: Any) -> set[str]:
    names: set[str] = set()
    for _item in with_node.items:
        if _item.optional_vars is not None:
            names.update(iter_unpack_target_names(_item.optional_vars))
    return names
def _rd27_rebind_names(child: Any) -> set[str] | None:
    if isinstance(child, (ast.Import, ast.ImportFrom)):
        return {
            alias.asname or alias.name.split(".")[0]
            for alias in child.names if alias.name != "*"
        }
    if isinstance(child, FUNC_NODE_TYPES + (ast.ClassDef,)):
        return {child.name}
    if isinstance(child, ast.Assign):
        return _rd27_rebind_assign_targets(child)
    if isinstance(child, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
        return _rd27_simple_rebind_target(child)
    if isinstance(child, (ast.For, ast.AsyncFor)):
        return set(iter_unpack_target_names(child.target))
    if isinstance(child, (ast.With, ast.AsyncWith)):
        return _rd27_rebind_with_items(child)
    if isinstance(child, ast.ExceptHandler) and child.name:
        return {child.name}
    if isinstance(child, ast.Match):
        return _rd27_match_capture_names(child)
    return None
def _rd27_simple_rebind_target(child: Any) -> set[str] | None:
    if isinstance(child, ast.AnnAssign) and child.value is None:
        return None
    if isinstance(child.target, ast.Name):
        return {child.target.id}
    return None
def _rd27_match_capture_names(child: ast.Match) -> set[str]:
    names: set[str] = set()
    for _case in child.cases:
        names.update(iter_pattern_capture_names(_case.pattern))
    return names
def _rd27_start_position(node: Any) -> tuple[int, int]:
    return (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
def _rd27_end_position(node: Any) -> tuple[int, int]:
    return (
        getattr(node, "end_lineno", None) or getattr(node, "lineno", 0),
        getattr(node, "end_col_offset", None)
        if getattr(node, "end_col_offset", None) is not None
        else getattr(node, "col_offset", 0),
    )
def _rd27_rebind_sites(child: Any) -> list[tuple[str, tuple[int, int]]]:
    if isinstance(child, (ast.With, ast.AsyncWith)):
        sites = []
        for _item in child.items:
            if _item.optional_vars is None:
                continue
            position = _rd27_end_position(_item.context_expr)
            sites.extend((name, position) for name
                         in iter_unpack_target_names(_item.optional_vars))
        return sites
    if isinstance(child, ast.Match):
        sites = []
        for _case in child.cases:
            position = _rd27_end_position(_case.pattern)
            sites.extend((name, position) for name
                         in iter_pattern_capture_names(_case.pattern))
        return sites
    names = _rd27_rebind_names(child)
    if not names:
        return []
    if isinstance(child, (ast.For, ast.AsyncFor)):
        position = _rd27_end_position(child.iter)
    elif isinstance(child, ast.ExceptHandler) and child.type is not None:
        position = _rd27_end_position(child.type)
    else:
        position = _rd27_end_position(child)
    return [(name, position) for name in sorted(names)]
@dataclass
class _RD27ScanState:
    self_attrs: int = 0
    external_positions: dict[str, list[tuple[int, int]]] = field(
        default_factory=dict)
    rebind_positions: dict[str, list[tuple[int, int]]] = field(
        default_factory=dict)
    receiver_name: str = ""
def _rd27_absorb_node(child: Any, state: _RD27ScanState) -> None:
    if isinstance(child, ast.Attribute) and isinstance(child.value, ast.Name):
        _base = child.value.id
        if state.receiver_name and _base == state.receiver_name:
            state.self_attrs += 1
        else:
            state.external_positions.setdefault(_base, []).append(
                _rd27_start_position(child))
    for _name, _position in _rd27_rebind_sites(child):
        state.rebind_positions.setdefault(_name, []).append(_position)
def _rd27_scan_method_body(func: Any) -> _RD27ScanState:
    state = _RD27ScanState(receiver_name=_method_receiver_name(func))
    for child in _iter_method_body_nodes(func.body):
        _rd27_absorb_node(child, state)
    return state
def _rd27_external_counts(state: _RD27ScanState) -> dict[str, int]:
    counts = {}
    for base, positions in state.external_positions.items():
        rebinds = state.rebind_positions.get(base)
        if rebinds:
            first_rebind = min(rebinds)
            positions = [position for position in positions
                         if position < first_rebind]
        if positions:
            counts[base] = len(positions)
    return counts
def _rd27_envy_base(state: _RD27ScanState,
                    param_names: set[str]) -> str:
    external_by_base = _rd27_external_counts(state)
    if not external_by_base:
        return ""
    external_attrs = sum(external_by_base.values())
    top_base, top_cnt = max(external_by_base.items(), key=lambda kv: kv[1])
    if (top_base in param_names and top_cnt >= 3
            and top_cnt > state.self_attrs * 2
            and top_cnt * 2 >= external_attrs):
        return top_base
    return ""
def _rd27_iter_methods(tree: Any):
    for cls_node in walk_nodes(tree):
        if not isinstance(cls_node, ast.ClassDef):
            continue
        for func in _iter_class_scope_defs(cls_node):
            yield cls_node, func
_AST_VISITOR_BASE_NAMES = frozenset({"NodeVisitor", "NodeTransformer"})
def _rd27_is_ast_visitor(cls_node: ast.ClassDef) -> bool:
    return any(ast_name(base).rpartition(".")[2] in _AST_VISITOR_BASE_NAMES
               for base in cls_node.bases)
def _rd27_method_finding(cls_node: Any, func: Any,
                         filepath: Any) -> FindingRecord | None:
    if _rd27_is_ast_visitor(cls_node):
        return None
    state = _rd27_scan_method_body(func)
    envy_base = _rd27_envy_base(state, collect_param_names(func))
    if not envy_base:
        return None
    external_top = _rd27_external_counts(state).get(envy_base, 0)
    self_attrs = state.self_attrs
    return FindingRecord(
        id="RD-27", severity="P2", dimension="quality",
        file=filepath, line=func.lineno,
        title=f"Feature envy: '{cls_node.name}.{func.name}' 集中访问外来对象 '{envy_base}' {external_top} 次 vs self {self_attrs} 次",
        description="方法对外部对象数据的依赖显著超过对自身类的依赖，"
                    "数据与行为分离，属依恋情结（Feature Envy）代码坏味。",
        suggestion="考虑 Move Method：将该方法的主体移到它所依恋的类中"
                   "（code-reconstruction.md 4.2.5）。",
    )
def check_RD27(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    for cls_node, func in _rd27_iter_methods(tree):
        finding = _rd27_method_finding(cls_node, func, filepath)
        if finding is not None:
            issues.append(finding)
    return issues
def wiring_declarations() -> dict:
    return {"catalogs": {"diag4_direct": {"RD-27": check_RD27}}}

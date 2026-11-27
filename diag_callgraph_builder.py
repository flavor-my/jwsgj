from __future__ import annotations  # noqa: I001
import ast
import logging
import os
import sys
import time as _time
from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Any
from jwsgj.diag_callgraph_collect import (
    ImportAliasCollector,
    collect_dynamic_patterns,
    track_assignment_chains,
)
from jwsgj.diag_callgraph_facts import (
    CALLGRAPH_BUILD_ERRORS,
    FunctionNode,
    assignment_name_index,
    build_symbol_lookup_index,
    method_to_classes_index,
    reset_index_caches,
    short_name_index,
    symbol_owner_index,
)
from jwsgj.diag_callgraph_source import (
    _DEFAULT_INCLUDE_TESTS,
    _class_spans_for_file,
    _collect_all_exports,
    _DefCollector,
    _FileInventoryMixin,
    _FileScanContext,
    _path_key,
    _qualify,
    _read_noncode_text,
    _source_root_module_aliases,
    _SourceAstCacheMixin,
)
from jwsgj.diag_callgraph_verdicts import (
    CallGraph,
    CallGraphBuilderProtocol,
    append_synthetic_edge,
    check_side_effects,
    detect_non_impacting_control_deps,
    detect_path_sensitive_type_constraints,
    external_callers_for_fnode,
    find_orphans,
    infer_type_annotation_reachability,
)
from jwsgj.diag_implicit_calls import (
    DynamicCallTracer,
    filter_suspicious_files,
    generate_dataclass_methods,
    link_implicit_calls,
    link_init_subclass,
    link_mixin_methods,
    link_singledispatch,
)
from jwsgj.diag_shared_ast_nodes import (
    iter_module_scope_nodes,
    normalize_torn_name,
    path_to_dotted_module,
    pkg_root_name,
    strip_pkg_root,
)
from jwsgj.runtime_scope import (
    LEGACY_BACKUP_DIR_NAME,
    SCAN_COLLECT_PRUNE_DIRS,
    prune_ignore_dirs,
)
from jwsgj.prevention_scope_facts import walk_nodes
logger = logging.getLogger(__name__)
__all__ = [
    "CallGraphBuilder",
    "build_call_graph_once",
    "ensure_built_call_graph",
    "prepare_instrumentation_paths",
    "split_methods_by_definition",
    "start_dynamic_tracer",
]
_REEXPORT_MAX_HOPS = 8
_NONCODE_SCAN_EXTRA_EXCLUDED_DIRS = frozenset({
    "reports", "_baseline", LEGACY_BACKUP_DIR_NAME, "__pypackages__",
})
_NONCODE_SCAN_EXCLUDED_DIRS = (
    SCAN_COLLECT_PRUNE_DIRS | _NONCODE_SCAN_EXTRA_EXCLUDED_DIRS)
_NONCODE_SCAN_EXCLUDED_LOWER = frozenset(
    s.lower() for s in _NONCODE_SCAN_EXCLUDED_DIRS)
_NONCODE_CONFIG_EXTENSIONS = ('.yaml', '.yml', '.json', '.ini', '.cfg', '.toml')
_NONCODE_DOC_LOWER = frozenset({
    'skill.md', 'readme.md', 'readme.rst', 'readme.txt', 'readme',
})
class CallGraphBuilder(_SourceAstCacheMixin, _FileInventoryMixin):
    def __init__(self, project_root: str = ".", ctx=None,
                 include_tests: bool | None = _DEFAULT_INCLUDE_TESTS) -> None:
        self.project_root = os.path.abspath(project_root)
        self.include_tests = include_tests
        self.graph = CallGraph(project_root=self.project_root)
        self._file_symbols: dict[str, dict[str, FunctionNode]] = defaultdict(dict)
        self._symbol_owner_index: dict[str, str] | None = None
        self._import_aliases: dict[str, dict[str, str]] = defaultdict(dict)
        self._plain_imports: dict[str, dict[str, set[str]]] = defaultdict(dict)
        self._reexport_chain: dict[str, str] = {}
        self._init_export_names: dict[str, set[str]] = {}
        self._ast_cache: dict = {}
        self._ast_depth_cache: dict[str, tuple[object, int]] = {}
        self._file_list_cache: list[str] | None = None
        self._build_py_files: list[str] | None = None
        self._scanned_abs: set[str] | None = None
        self._symbol_lookup_index: dict | None = None
        self._ctx = ctx
        self._step_mark: float | None = None
    def _reset_build_state(self) -> None:
        self.graph = CallGraph(project_root=self.project_root)
        self._file_symbols = defaultdict(dict)
        self._import_aliases = defaultdict(dict)
        self._plain_imports = defaultdict(dict)
        self._symbol_owner_index = None
        self._reexport_chain = {}
        self._init_export_names = {}
        self._ast_cache = {}
        self._ast_depth_cache = {}
        self._file_list_cache = None
        self._build_py_files = None
        self._scanned_abs = None
        self._symbol_lookup_index = None
    def _log_step(self, name: str) -> None:
        _now = _time.perf_counter()
        logger.info("  [D1] %s: %.1fs", name, _now - self._step_mark)
        self._step_mark = _now
    def _collect_init_exports(self, py_files: list[str]) -> None:
        for filepath in py_files:
            if os.path.basename(filepath).lower() != "__init__.py":
                continue
            _source, tree = self.get_source_and_ast(filepath)
            if tree is None:
                continue
            rel_path = os.path.relpath(
                filepath, self.project_root).replace("\\", "/")
            self._init_export_names[rel_path] = _collect_all_exports(tree)
    def build(self, source_paths: list[str] | None = None) -> CallGraph:
        reset_index_caches()
        self._reset_build_state()
        py_files = self._collect_source_files(source_paths)
        self._scanned_abs = {os.path.normpath(f) for f in py_files}
        self._build_py_files = list(py_files)
        self._collect_init_exports(py_files)
        self._step_mark = _time.perf_counter()
        self._run_definition_phase(py_files)
        self._run_linking_phase()
        self._run_prune_phase()
        self._run_orphan_phase()
        self._run_precision_phase()
        return self.graph
    def _run_definition_phase(self, py_files: list[str]) -> None:
        for filepath in py_files:
            self._collect_definitions(filepath)
        self._log_step("_collect_definitions")
        self._sync_global_exports()
        self._link_definition_implicits()
        self._log_step("dataclass/init_subclass/singledispatch")
        self._symbol_owner_index = symbol_owner_index(
            self._file_symbols, _path_key)
        for filepath in py_files:
            collect_dynamic_patterns(self, filepath)
        self._log_step("dynamic_reg/dispatch/calls")
    def _sync_global_exports(self) -> None:
        for fnode in self.graph.functions.values():
            fnode._global_exports = self.graph.global_all_exports
    def _register_init_export_targets(self) -> None:
        self.graph.global_all_exports.clear()
        for filepath, exports in self._init_export_names.items():
            module_name = path_to_dotted_module(filepath)
            aliases = _torn_alias_bucket(self._import_aliases, filepath)
            for export in exports:
                candidates = {_qualify(module_name, export)}
                original = aliases.get(export)
                if original:
                    candidates.add(normalize_torn_name(original))
                resolved = self._reexport_chain.get(filepath + ":" + export)
                if resolved:
                    candidates.add(resolved)
                for candidate in candidates:
                    self._register_init_export_target(candidate)
    def _register_init_export_target(self, candidate: str) -> None:
        candidate = normalize_torn_name(candidate)
        if not candidate:
            return
        if candidate in self.graph.functions:
            self.graph.global_all_exports.add(candidate)
        class_keys = [candidate] if candidate in self.graph.class_files else []
        if not class_keys:
            suffix = "." + candidate
            matches = [key for key in self.graph.class_files
                       if isinstance(key, str) and key.endswith(suffix)]
            if len(matches) == 1:
                class_keys = matches
        for class_key in class_keys:
            for function_key in self.graph.functions:
                if (isinstance(function_key, str)
                        and function_key.rsplit(".", 1)[0] == class_key):
                    self.graph.global_all_exports.add(function_key)
    def _link_definition_implicits(self) -> None:
        generate_dataclass_methods(self.graph)
        link_init_subclass(self.graph)
        link_singledispatch(self.graph)
    def symbol_lookup_index(self) -> dict:
        if self._symbol_lookup_index is None:
            self._symbol_lookup_index = build_symbol_lookup_index(
                self._file_symbols)
        return self._symbol_lookup_index
    def _run_linking_phase(self) -> None:
        link_mixin_methods(self.graph)
        self._log_step("mixin_methods")
        _qualify_root_package_import_aliases(self)
        _build_reexport_chain(self)
        self._register_init_export_targets()
        self._log_step("reexport_chain")
        _normalize_module_calls(self)
        self._log_step("normalize_module_calls")
        link_implicit_calls(self)
        self._log_step("link_implicit_calls")
    def _run_prune_phase(self) -> None:
        track_assignment_chains(self)
        self._log_step("track_assignment_chains")
        _prune_infeasible_edges(self)
        self._log_step("prune_infeasible_edges")
    def _run_orphan_phase(self) -> None:
        self._build_import_graph()
        self._log_step("import_graph")
        find_orphans(self.graph)
        self._log_step("find_orphans")
        _scan_non_code_references(self)
        self._log_step("scan_non_code_references")
    def _run_precision_phase(self) -> None:
        channels = (
            ("non_impacting_dep", detect_non_impacting_control_deps),
            ("type_annotation_unreachable", infer_type_annotation_reachability),
            ("side_effect_protected", check_side_effects),
            ("path_sensitive_unreachable", detect_path_sensitive_type_constraints),
        )
        adjustments: dict[str, int] = {}
        for key, channel in channels:
            adjustments[key] = channel(self)
            self._log_step(channel.__name__)
        self._emit_orphan_confidence_adjustments(adjustments)
        self.graph.invalidate_analysis_caches()
    def _build_import_graph(self) -> None:
        self.graph.import_graph.clear()
        self.graph.imports.clear()
        for _file_rel, aliases in self._import_aliases.items():
            self.graph.imports[_file_rel].update(aliases)
            for full_path in aliases.values():
                simple = full_path.split(".")[-1]
                self.graph.import_graph[full_path] = full_path
                self.graph.import_graph.setdefault(simple, full_path)
    def _emit_orphan_confidence_adjustments(self, adjustments: dict[str, int]) -> None:
        self.graph.orphan_confidence_adjustments = dict(adjustments)
        _adj_total = sum(adjustments.values())
        if _adj_total:
            logger.info("  [D1] orphan confidence 降级 %d/%d: %s", _adj_total,
                        len(self.graph.orphans),
                        self.graph.orphan_confidence_adjustments)
        self.graph.orphan_caller_base = {
            "orphans_total": len(self.graph.orphans),
            "orphans_with_callers": sum(
                1 for o in self.graph.orphans
                if external_callers_for_fnode(self.graph, o)),
        }
    def _collect_definitions(self, filepath: str):
        tree, rel_path, module_name = self._scan_target(filepath)
        if tree is None:
            return
        all_exports = _collect_all_exports(tree)
        scan_ctx = _FileScanContext(rel_path, module_name, all_exports)
        ImportAliasCollector(
            rel_path, self._import_aliases, self._plain_imports).visit(tree)
        visitor = _DefCollector(
            scan_ctx, graph=self.graph,
            file_symbols=self._file_symbols,
            import_aliases=self._import_aliases.get(rel_path),
        )
        visitor.visit(tree)
def _enclosing_class_span(method: str, call_graph: Any,
                          named: list) -> tuple[int, int] | None:
    fnode = call_graph.functions.get(method)
    line = getattr(fnode, "start_line", 0)
    enclosing = [span for span in named if span[1] <= line <= span[2]]
    if not enclosing:
        return None
    span = max(enclosing, key=lambda item: item[1])
    return (span[1], span[2])
def split_methods_by_definition(
        key: str,
        methods: list[str],
        call_graph: Any,
        span_cache: dict[str, list[tuple[str, int, int]] | None],
) -> list[list[str]] | None:
    filepath, _, class_name = key.rpartition("::")
    if not filepath or not class_name:
        return None
    spans = _class_spans_for_file(filepath, call_graph, span_cache) or []
    named = [span for span in spans if span[0] == class_name]
    if not named:
        return None
    grouped: dict[tuple[int, int], list[str]] = defaultdict(list)
    for method in methods:
        bounds = _enclosing_class_span(method, call_graph, named)
        if bounds is None:
            return None
        grouped[bounds].append(method)
    return list(grouped.values())
def _torn_alias_bucket(aliases_map: dict, file_key) -> dict:
    bucket = aliases_map.get(file_key)
    return bucket if isinstance(bucket, dict) else {}
def _torn_plain_bucket(plain_map: dict | None, file_key) -> dict:
    bucket = (plain_map or {}).get(file_key)
    return bucket if isinstance(bucket, dict) else {}
@dataclass(frozen=True)
class _ReexportIndexes:
    defined_by: dict
    module_to_file: dict
    import_aliases: dict
    logical_defined: dict[str, str]
    class_defined: dict[str, str]
def _build_reexport_indexes(builder) -> _ReexportIndexes:
    graph = builder.graph
    defined_by = {}
    logical_candidates: dict[str, set[str]] = defaultdict(set)
    alias_cache: dict[str, tuple[str, ...]] = {}
    for full_fqn, fnode in graph.functions.items():
        if getattr(fnode, "class_name", None) is not None:
            continue
        normalized = normalize_torn_name(full_fqn)
        simple = normalized.split(".")[-1]
        defined_by.setdefault(simple, []).append(full_fqn)
        module_name = normalized.rsplit(".", 1)[0]
        for alias in _source_root_module_aliases(
                builder, module_name, alias_cache):
            logical_candidates[_qualify(alias, simple)].add(full_fqn)
    logical_defined = {
        name: next(iter(candidates))
        for name, candidates in logical_candidates.items()
        if len(candidates) == 1
    }
    class_defined = {}
    logical_class_candidates: dict[str, set[str]] = defaultdict(set)
    for class_key in graph.class_files:
        normalized = normalize_torn_name(class_key)
        class_defined[normalized] = class_key
        module_name, _, simple = normalized.rpartition(".")
        if not module_name:
            continue
        for alias in _source_root_module_aliases(
                builder, module_name, alias_cache):
            logical_class_candidates[_qualify(alias, simple)].add(class_key)
    class_defined.update({
        name: next(iter(candidates))
        for name, candidates in logical_class_candidates.items()
        if len(candidates) == 1
    })
    module_to_file = {}
    for _fp in builder._import_aliases:
        _mod = path_to_dotted_module(normalize_torn_name(_fp))
        if not _mod and normalize_torn_name(_fp) == "__init__.py":
            _mod = pkg_root_name(builder.project_root)
        if _mod and _mod not in module_to_file:
            module_to_file[_mod] = _fp
    module_aliases: dict[str, set[str]] = defaultdict(set)
    for _fp in builder._import_aliases:
        _mod = path_to_dotted_module(normalize_torn_name(_fp))
        for alias in _source_root_module_aliases(builder, _mod, alias_cache):
            module_aliases[alias].add(_fp)
    for alias, files in module_aliases.items():
        if alias not in module_to_file and len(files) == 1:
            module_to_file[alias] = next(iter(files))
    return _ReexportIndexes(
        defined_by, module_to_file, builder._import_aliases, logical_defined,
        class_defined)
def _reexport_candidate_match(indexes: _ReexportIndexes, sym_part: str,
                              mod_part: str) -> str | None:
    expected = _qualify(mod_part, sym_part)
    for candidate in indexes.defined_by.get(sym_part, []):
        if normalize_torn_name(candidate) == expected:
            return candidate
    return indexes.logical_defined.get(expected)
def _resolve_reexport_hops(graph, indexes: _ReexportIndexes,
                           mod_part: str, sym_part: str,
                           pkg_root: str) -> str | None:
    hop_module, hop_alias = mod_part, sym_part
    seen_hops = {(mod_part, sym_part)}
    for _ in range(_REEXPORT_MAX_HOPS):
        step = _transit_reexport_value(
            graph, indexes, hop_module, hop_alias, pkg_root)
        if step is None:
            break
        hit, transit = step
        if hit is not None:
            return hit
        next_hop = _reexport_hop_target(transit, pkg_root)
        if (next_hop is None or not next_hop[0]
                or next_hop in seen_hops):
            break
        seen_hops.add(next_hop)
        hop_module, hop_alias = next_hop
    return None
def _transit_reexport_value(graph, indexes: _ReexportIndexes,
                            hop_module: str, hop_alias: str,
                            pkg_root: str):
    hop_file = indexes.module_to_file.get(hop_module)
    if hop_file is None:
        return None
    transit = _torn_alias_bucket(indexes.import_aliases, hop_file).get(hop_alias)
    if not transit:
        return None
    transit = normalize_torn_name(transit)
    hit = _reexport_value_hit(graph, indexes, transit, pkg_root)
    if hit is None:
        hit = indexes.class_defined.get(transit)
    if hit is None:
        hit = indexes.class_defined.get(strip_pkg_root(transit, pkg_root))
    return hit, transit
def _reexport_value_hit(graph, indexes: _ReexportIndexes,
                        value: str, pkg_root: str) -> str | None:
    stripped = strip_pkg_root(value, pkg_root)
    if value in graph.functions:
        return value
    if stripped != value and stripped in graph.functions:
        return stripped
    next_hop = _reexport_hop_target(value, pkg_root)
    if next_hop is None:
        return None
    next_module, next_simple = next_hop
    return _reexport_candidate_match(indexes, next_simple, next_module)
def _reexport_hop_target(transit: str, pkg_root: str) -> tuple[str, str] | None:
    transit_parts = transit.rsplit(".", 1)
    if len(transit_parts) != 2:
        return None
    return strip_pkg_root(transit_parts[0], pkg_root), transit_parts[1]
def _qualify_root_package_import_aliases(builder) -> None:
    file_keys = {normalize_torn_name(fp) for fp in builder._import_aliases}
    pkg_root = pkg_root_name(builder.project_root)
    if not pkg_root or "__init__.py" not in file_keys:
        return
    for _fp in list(builder._import_aliases):
        filepath = normalize_torn_name(_fp)
        if "/" in filepath:
            continue
        _source, tree = builder.get_source_and_ast(filepath)
        if tree is None:
            continue
        aliases = _torn_alias_bucket(builder._import_aliases, _fp)
        for node in iter_module_scope_nodes(tree, descend_classes=False):
            if (not isinstance(node, ast.ImportFrom) or node.level != 1
                    or node.module is not None):
                continue
            for imported in node.names:
                if imported.name == "*":
                    continue
                aliases[imported.asname or imported.name] = _qualify(
                    pkg_root, imported.name)
def _build_reexport_chain(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    _pkg_root = pkg_root_name(builder.project_root)
    indexes = _build_reexport_indexes(builder)
    builder._reexport_chain = {}
    for _fp_raw in builder._import_aliases:
        filepath = normalize_torn_name(_fp_raw)
        aliases = _torn_alias_bucket(builder._import_aliases, _fp_raw)
        for _alias_raw, _original_raw in aliases.items():
            alias = normalize_torn_name(_alias_raw)
            original = normalize_torn_name(_original_raw)
            if "." not in original:
                continue
            hit = _resolve_reexport_target(
                graph, indexes, original, _pkg_root)
            if hit is not None:
                builder._reexport_chain[filepath + ":" + alias] = hit
    _register_reexport_call_sites(builder, graph, indexes, _pkg_root)
def _register_reexport_call_sites(builder, graph, indexes: _ReexportIndexes,
                                  pkg_root: str) -> None:
    calls_by_file = defaultdict(list)
    for edge in graph.calls:
        if not edge.is_external or not edge.caller_file:
            continue
        caller_file = normalize_torn_name(edge.caller_file)
        calls_by_file[caller_file].append(edge)
    for _fp_raw, aliases in builder._import_aliases.items():
        filepath = normalize_torn_name(_fp_raw)
        plain = _torn_plain_bucket(builder._plain_imports, _fp_raw)
        for edge in calls_by_file.get(filepath, ()):
            callee = normalize_torn_name(edge.callee_func)
            if "." not in callee:
                continue
            seg = callee.split(".", 1)[0]
            plain_modules = plain.get(seg)
            if seg not in aliases:
                if not any(
                        callee == original
                        or callee.startswith(original + ".")
                        for original in map(
                            normalize_torn_name, aliases.values())):
                    continue
                logical_callee = callee
            elif plain_modules is not None:
                callee_module = callee.rsplit(".", 1)[0]
                if not any(
                        callee_module == mod
                        or callee_module.startswith(mod + ".")
                        for mod in plain_modules):
                    continue
                logical_callee = callee
            else:
                alias_target = normalize_torn_name(aliases[seg])
                if not alias_target:
                    continue
                logical_callee = alias_target + callee[len(seg):]
            hit = _resolve_reexport_target(
                graph, indexes, logical_callee, pkg_root)
            if hit is not None:
                builder._reexport_chain[filepath + ":" + callee] = hit
def _resolve_reexport_target(graph, indexes: _ReexportIndexes,
                             original: str, pkg_root: str) -> str | None:
    hit = _reexport_value_hit(graph, indexes, original, pkg_root)
    if hit is not None:
        return hit
    next_hop = _reexport_hop_target(original, pkg_root)
    if next_hop is None:
        return None
    next_module, next_simple = next_hop
    return _resolve_reexport_hops(graph, indexes, next_module, next_simple,
                                  pkg_root)
def _edge_caller_keys(edge) -> set:
    keys = {edge.caller_func}
    if edge.caller_file:
        keys.add(f"{edge.caller_func}:{edge.caller_file}")
    return keys
def _migrate_callers(graph, old_key: str, new_key: str, edge=None):
    callers = graph.callers.get(old_key)
    if callers is None:
        return
    if edge is None:
        graph.callers.pop(old_key)
        graph.callers[new_key].update(callers)
        return
    moved = callers.intersection(_edge_caller_keys(edge))
    if not moved:
        return
    callers.difference_update(moved)
    if not callers:
        graph.callers.pop(old_key, None)
    graph.callers[new_key].update(moved)
@dataclass(frozen=True)
class _RenameTarget:
    new_callee: str
    target_fnode: FunctionNode
def _apply_callee_rename(graph, edge, old_callee, target: _RenameTarget):
    edge.callee_func = target.new_callee
    edge.callee_file = target.target_fnode.filepath
    edge.is_external = False
    _migrate_callers(graph, old_callee, target.new_callee, edge=edge)
def _apply_class_reexport_resolution(graph, edge, old_callee: str,
                                     class_key: str) -> None:
    edge.callee_func = class_key
    edge.callee_file = graph.class_files[class_key]
    edge.is_external = False
    _migrate_callers(graph, old_callee, class_key, edge=edge)
    init_key = f"{class_key}.__init__"
    if init_key not in graph.functions:
        return
    if any(existing.caller_file == edge.caller_file
           and existing.caller_func == edge.caller_func
           and existing.callee_func == init_key
           and existing.line == edge.line
           for existing in graph.calls):
        return
    append_synthetic_edge(
        graph, caller_func=edge.caller_func, caller_file=edge.caller_file,
        callee_fqn=init_key, line=edge.line, args_count=edge.args_count,
        is_self_call=edge.is_self_call)
def _retain_live_external_deps(graph) -> None:
    live_external = {edge.callee_func for edge in graph.calls if edge.is_external}
    graph.external_deps.intersection_update(live_external)
def _rename_stripped_target(graph, edge, old_callee, stripped):
    target_key = stripped
    target_fnode = graph.functions.get(target_key)
    if target_fnode is None:
        target_key = f"{stripped}.__init__"
        target_fnode = graph.functions.get(target_key)
    if target_fnode is not None:
        _apply_callee_rename(
            graph, edge, old_callee,
            _RenameTarget(target_key, target_fnode))
def _target_matches_callee(callee: str, target_fqn: str,
                           project_root: str) -> bool:
    candidates = {target_fqn}
    pkg_root = pkg_root_name(project_root)
    if pkg_root:
        candidates.add(_qualify(pkg_root, target_fqn))
    return any(candidate == callee or candidate.endswith("." + callee)
               for candidate in candidates)
def _alias_guard_allows(callee, target_fqn, caller_file, import_aliases,
                        reexport_chain, plain_imports, project_root) -> bool:
    target_fqn = normalize_torn_name(target_fqn)
    caller_file = normalize_torn_name(caller_file) if caller_file else ""
    seg = callee.split(".")[0]
    plain = _torn_plain_bucket(plain_imports, caller_file).get(seg)
    if plain is not None:
        return _plain_import_allows(
            callee, plain, target_fqn, project_root)
    aliases = _torn_alias_bucket(import_aliases, caller_file)
    alias_target = aliases.get(seg)
    if alias_target is not None:
        return _alias_target_compatible(alias_target, target_fqn)
    if callee in aliases.values():
        return _target_matches_callee(callee, target_fqn, project_root)
    return _reexport_edge_target(
        aliases, callee, caller_file, reexport_chain) == target_fqn
def _plain_import_allows(callee: str, imported: set, target_fqn: str,
                         project_root: str) -> bool:
    callee_module = callee.rsplit(".", 1)[0] if "." in callee else ""
    if not callee_module or not any(
            callee_module == mod or callee_module.startswith(mod + ".")
            for mod in imported):
        return False
    return _target_matches_callee(callee, target_fqn, project_root)
def _alias_target_compatible(alias_target, target_fqn: str) -> bool:
    alias_target = normalize_torn_name(alias_target)
    target_module = target_fqn.rsplit(".", 1)[0]
    return (alias_target == target_module
            or alias_target.endswith("." + target_module)
            or target_module.startswith(alias_target + "."))
def _reexport_edge_target(aliases: dict, callee: str, caller_file: str,
                          reexport_chain) -> str | None:
    if not reexport_chain:
        return None
    direct = reexport_chain.get(caller_file + ":" + callee)
    if direct is not None:
        return direct
    for alias, value in aliases.items():
        if value != callee:
            continue
        target = reexport_chain.get(caller_file + ":" + alias)
        if target is not None:
            return target
    return None
def _normalize_dot_func_edge(graph, edge, callee: str, dot_func: str) -> None:
    dot_fnode = graph.functions[dot_func]
    callee_fnode = graph.functions.get(callee)
    if callee_fnode is None:
        if not normalize_torn_name(dot_fnode.filepath).lower().endswith(
                "__init__.py"):
            return
    elif callee_fnode.filepath != dot_fnode.filepath:
        return
    _apply_callee_rename(graph, edge, callee,
                         _RenameTarget(dot_func, dot_fnode))
def _resolve_fallback_target(graph, callee: str, func_part: str,
                             simple_name_index: dict) -> str | None:
    candidates = simple_name_index.get(func_part, [])
    if len(candidates) != 1:
        return None
    target_fqn = candidates[0]
    callee_fnode = graph.functions.get(callee)
    if callee_fnode is not None and callee_fnode.filepath != graph.functions[target_fqn].filepath:
        return None
    return target_fqn
def _normalize_phase1_known_funcs(graph, simple_name_index, import_aliases,
                                  reexport_chain, plain_imports):
    for edge in list(graph.calls):
        callee = normalize_torn_name(edge.callee_func)
        if not _is_relative_dotted(callee):
            continue
        _normalize_known_func_edge(graph, edge, callee, simple_name_index,
                                   import_aliases, reexport_chain,
                                   plain_imports)
    _retain_live_external_deps(graph)
def _is_relative_dotted(callee: str) -> bool:
    return "." in callee and not callee.startswith(".")
def _normalize_known_func_edge(graph, edge, callee: str, simple_name_index,
                               import_aliases, reexport_chain,
                               plain_imports) -> None:
    func_part = callee.rsplit(".", 1)[-1]
    dot_func = "." + func_part
    if dot_func in graph.functions:
        _normalize_dot_func_edge(graph, edge, callee, dot_func)
        return
    caller_file = normalize_torn_name(edge.caller_file) if edge.caller_file else ""
    aliases = _torn_alias_bucket(import_aliases, caller_file)
    target_fqn = _reexport_edge_target(
        aliases, callee, caller_file, reexport_chain)
    if target_fqn in graph.functions:
        _apply_callee_rename(
            graph, edge, callee,
            _RenameTarget(target_fqn, graph.functions[target_fqn]))
        return
    if target_fqn in graph.class_files:
        _apply_class_reexport_resolution(graph, edge, callee, target_fqn)
        return
    target_fqn = _resolve_fallback_target(
        graph, callee, func_part, simple_name_index)
    if target_fqn is None:
        return
    if not _alias_guard_allows(
            callee, target_fqn, edge.caller_file, import_aliases,
            reexport_chain, plain_imports, graph.project_root):
        return
    _apply_callee_rename(
        graph, edge, callee,
        _RenameTarget(target_fqn, graph.functions[target_fqn]))
def _resolve_class_prefix_caller(caller: str,
                                 method_to_classes: dict[str, list[str]],
                                 functions: dict) -> str | None:
    if caller in functions or "." not in caller:
        return None
    mod_prefix, method_name = caller.rsplit(".", 1)
    candidates = []
    for cls_name in method_to_classes.get(method_name, ()):
        candidate = mod_prefix + "." + cls_name + "." + method_name
        if candidate in functions:
            candidates.append(candidate)
    return candidates[0] if len(candidates) == 1 else None
def _sync_caller_renames(graph, caller_renames: dict[str, str]) -> None:
    if not caller_renames:
        return
    for old, new in caller_renames.items():
        if old == new or old not in graph.callers:
            continue
        moved = graph.callers.pop(old)
        target = graph.callers.get(new)
        if target is None:
            graph.callers[new] = moved
        else:
            target.update(moved)
    for callers_set in graph.callers.values():
        stale = {c for c in callers_set
                 if isinstance(c, str) and c in caller_renames}
        if stale:
            callers_set.difference_update(stale)
            callers_set.update(caller_renames[c] for c in stale)
        _rename_composite_callers(callers_set, caller_renames)
def _rename_composite_callers(callers_set: set,
                              caller_renames: dict[str, str]) -> None:
    renamed: dict[str, str] = {}
    for caller in callers_set:
        if not isinstance(caller, str):
            continue
        for old, new in caller_renames.items():
            prefix = old + ":"
            if caller.startswith(prefix):
                renamed[caller] = new + caller[len(old):]
                break
    if renamed:
        callers_set.difference_update(renamed)
        callers_set.update(renamed.values())
def _normalize_phase2_class_prefix(graph):
    method_to_classes = method_to_classes_index(graph.class_methods)
    caller_renames: dict[str, str] = {}
    for edge in list(graph.calls):
        caller = normalize_torn_name(edge.caller_func)
        candidate = _resolve_class_prefix_caller(
            caller, method_to_classes, graph.functions)
        if candidate is None:
            continue
        edge.caller_func = candidate
        caller_renames[caller] = candidate
    _sync_caller_renames(graph, caller_renames)
def _normalize_phase3_dot_prefix(graph):
    for edge in list(graph.calls):
        caller = normalize_torn_name(edge.caller_func)
        callee = normalize_torn_name(edge.callee_func)
        if not caller.startswith(".") or "." in callee:
            continue
        dot_callee = "." + callee
        if dot_callee in graph.functions:
            _apply_callee_rename(
                graph, edge, callee,
                _RenameTarget(dot_callee, graph.functions[dot_callee]))
    _retain_live_external_deps(graph)
def _normalize_phase4_cross_skill_fqn(graph, fqn_prefix: str):
    for edge in list(graph.calls):
        callee = normalize_torn_name(edge.callee_func)
        if not callee.startswith(fqn_prefix):
            continue
        if _graph_has_exact_callee(graph, callee):
            continue
        _rename_stripped_target(graph, edge, callee, callee[len(fqn_prefix):])
    _retain_live_external_deps(graph)
def _graph_has_exact_callee(graph, callee: str) -> bool:
    functions = graph.functions
    return callee in functions or f"{callee}.__init__" in functions
def _normalize_phase5_import_aliases(builder, fqn_prefix: str):
    graph = builder.graph
    for edge in list(graph.calls):
        callee = normalize_torn_name(edge.callee_func)
        if "." in callee:
            continue
        caller_file = edge.caller_file
        if not caller_file:
            continue
        caller_file = normalize_torn_name(caller_file)
        resolved = _resolve_import_alias(builder, callee, caller_file)
        if resolved is None:
            continue
        _apply_alias_resolution(graph, edge, callee, resolved, fqn_prefix)
    _retain_live_external_deps(graph)
def _resolve_import_alias(builder, callee: str, caller_file: str):
    aliases = _torn_alias_bucket(builder._import_aliases, caller_file)
    if callee not in aliases:
        return None
    resolved = aliases[callee]
    reexport_chain = builder._reexport_chain
    if reexport_chain and caller_file + ":" + callee in reexport_chain:
        resolved = reexport_chain[caller_file + ":" + callee]
    return resolved
def _apply_alias_resolution(graph, edge, callee: str, resolved,
                            fqn_prefix: str) -> None:
    resolved_text = normalize_torn_name(resolved)
    if resolved_text in graph.functions:
        _apply_callee_rename(
            graph, edge, callee,
            _RenameTarget(resolved_text, graph.functions[resolved_text]))
        return
    if resolved_text in graph.class_files:
        _apply_class_reexport_resolution(graph, edge, callee, resolved_text)
        return
    if not (fqn_prefix and resolved_text.startswith(fqn_prefix)):
        return
    _rename_stripped_target(
        graph, edge, callee, resolved_text[len(fqn_prefix):])
def _normalize_module_calls(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    simple_name_index = assignment_name_index(
        graph, include_methods=False, include_torn=False,
        include_non_str=True)
    _normalize_phase1_known_funcs(
        graph, simple_name_index, builder._import_aliases,
        builder._reexport_chain, builder._plain_imports)
    _normalize_phase2_class_prefix(graph)
    _normalize_phase3_dot_prefix(graph)
    _pkg = pkg_root_name(builder.project_root)
    fqn_prefix = _pkg + "." if _pkg else ""
    if fqn_prefix:
        _normalize_phase4_cross_skill_fqn(graph, fqn_prefix)
    _normalize_phase5_import_aliases(builder, fqn_prefix)
def _is_constant_false_test(test) -> bool:
    if isinstance(test, ast.Constant):
        return not test.value
    if isinstance(test, ast.Name) and test.id == '__debug__':
        return sys.flags.optimize > 0
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        operand = test.operand
        if isinstance(operand, ast.Constant):
            return bool(operand.value)
        if isinstance(operand, ast.Name) and operand.id == '__debug__':
            return sys.flags.optimize == 0
    return False
def _caller_file_key(path: str) -> str:
    return os.path.normcase(os.path.normpath(path.replace("\\", "/")))
def _prune_infeasible_edges(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    edges_by_file = _index_edges_by_caller_file(graph.calls)
    references_by_file = _index_edges_by_caller_file(
        graph.function_references)
    for filepath in builder.collect_build_scope_files():
        _source, tree = builder.get_source_and_ast(filepath)
        if tree is None:
            continue
        infeasible_ranges = _collect_infeasible_ranges(tree)
        if not infeasible_ranges:
            continue
        rel_path = os.path.relpath(filepath, builder.project_root)
        file_key = _caller_file_key(rel_path)
        edges_to_remove = _collect_infeasible_edges(
            edges_by_file.get(file_key, ()), infeasible_ranges)
        references_to_remove = _collect_infeasible_edges(
            references_by_file.get(file_key, ()), infeasible_ranges)
        if not edges_to_remove and not references_to_remove:
            continue
        _apply_edge_prune(
            graph, edges_to_remove, references_to_remove)
def _collect_infeasible_ranges(tree) -> list:
    infeasible_ranges = []
    for _node in walk_nodes(tree):
        if not isinstance(_node, (ast.If, ast.While)):
            continue
        if not _is_constant_false_test(_node.test):
            continue
        _span = _infeasible_body_span(_node)
        if _span is not None:
            infeasible_ranges.append(_span)
    return infeasible_ranges
def _infeasible_body_span(node) -> tuple | None:
    node_lineno = getattr(node, 'lineno', None)
    if not node.body or not isinstance(node_lineno, int):
        return None
    body_nodes = list(walk_nodes(
        ast.Module(body=node.body, type_ignores=[])))
    body_start = min(
        (getattr(_n, 'lineno', None) or node_lineno for _n in body_nodes),
        default=node_lineno)
    body_end = max(
        (_node_end_line(_n, node_lineno) for _n in body_nodes),
        default=node_lineno)
    return body_start, body_end
def _node_end_line(node, fallback: int) -> int:
    return (getattr(node, 'end_lineno', None)
            or getattr(node, 'lineno', None)
            or fallback)
def _index_edges_by_caller_file(edges) -> dict:
    index: dict = {}
    for edge in edges:
        index.setdefault(_caller_file_key(edge.caller_file or ""), []).append(edge)
    return index
def _collect_infeasible_edges(file_edges, infeasible_ranges: list) -> list:
    return [
        edge for edge in file_edges
        if isinstance(edge.line, int) and not isinstance(edge.line, bool)
        and any(start <= edge.line <= end
                for start, end in infeasible_ranges)
    ]
def _apply_edge_prune(graph, edges_to_remove: list,
                      references_to_remove: list) -> None:
    remove_ids = {id(e) for e in edges_to_remove}
    survivors = [e for e in graph.calls if id(e) not in remove_ids]
    graph.calls = survivors
    remove_reference_ids = {id(e) for e in references_to_remove}
    reference_survivors = [
        ref for ref in graph.function_references
        if id(ref) not in remove_reference_ids]
    graph.function_references = reference_survivors
    alive_index = _alive_caller_keys(
        [*survivors, *reference_survivors])
    for edge in [*edges_to_remove, *references_to_remove]:
        _discard_pruned_callers(graph, edge, alive_index)
    _retain_live_external_deps(graph)
def _alive_caller_keys(survivors: list) -> tuple[set, set]:
    bare_alive = {(e.caller_func, e.callee_func) for e in survivors}
    composite_alive = {
        (f"{e.caller_func}:{e.caller_file}", e.callee_func)
        for e in survivors if e.caller_file}
    return bare_alive, composite_alive
def _discard_pruned_callers(graph, edge, alive_index: tuple[set, set]) -> None:
    bare_alive, composite_alive = alive_index
    callers_set = graph.callers.get(edge.callee_func)
    if not callers_set:
        return
    if (edge.caller_func, edge.callee_func) not in bare_alive:
        callers_set.discard(edge.caller_func)
    if not edge.caller_file:
        return
    composite = f"{edge.caller_func}:{edge.caller_file}"
    if (composite, edge.callee_func) not in composite_alive:
        callers_set.discard(composite)
def _ac_insert_pattern(root: dict, pattern: str) -> None:
    node = root
    for ch in pattern:
        nxt = node['c'].get(ch)
        if nxt is None:
            nxt = {'c': {}, 'f': None, 'o': ()}
            node['c'][ch] = nxt
        node = nxt
    node['o'] = (pattern,)
def _build_ac_automaton(patterns):
    root = {'c': {}, 'f': None, 'o': ()}
    for pattern in patterns:
        if pattern:
            _ac_insert_pattern(root, pattern)
    queue = deque()
    for child in root['c'].values():
        child['f'] = root
        queue.append(child)
    while queue:
        node = queue.popleft()
        for ch, child in node['c'].items():
            queue.append(child)
            _ac_link_child(root, node, ch, child)
    return root
def _ac_fail_target(node: dict, ch: str) -> dict | None:
    fail_node = node['f']
    while fail_node is not None and ch not in fail_node['c']:
        fail_node = fail_node['f']
    if fail_node is None:
        return None
    return fail_node['c'][ch]
def _ac_link_child(root: dict, node: dict, ch: str, child: dict) -> None:
    fail_target = _ac_fail_target(node, ch)
    child['f'] = fail_target if fail_target is not None else root
    if child['f'] is not child and child['f']['o']:
        child['o'] = tuple(set(child['o']) | set(child['f']['o']))
def _identifier_char_at(content: str, index: int) -> bool:
    return 0 <= index < len(content) and (
        content[index].isalnum() or content[index] == '_')
def _ac_find_all(root, content, identifier_only: bool = False):
    found = set()
    node = root
    for end, ch in enumerate(content):
        nxt = node['c'].get(ch)
        while nxt is None and node is not root:
            node = node['f']
            nxt = node['c'].get(ch)
        node = nxt if nxt is not None else root
        for pattern in node['o']:
            start = end - len(pattern) + 1
            if identifier_only and (
                    _identifier_char_at(content, start - 1)
                    or _identifier_char_at(content, end + 1)):
                continue
            found.add(pattern)
    return found
def _is_noncode_referenced(name, referenced: set,
                           referenced_simples: set) -> bool:
    text = normalize_torn_name(name)
    return (text in referenced
            or text.rsplit(".", 1)[-1] in referenced_simples)
def _scan_non_code_references(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    defined_short_names = short_name_index(graph)
    if not defined_short_names:
        return
    ac_root = _build_ac_automaton(defined_short_names)
    text_files = _collect_noncode_text_files(builder.project_root)
    referenced, referenced_simples = _scan_text_files(
        ac_root, defined_short_names, text_files)
    if referenced:
        graph.orphans = [
            o for o in graph.orphans
            if not _is_noncode_referenced(
                o.name, referenced, referenced_simples)
        ]
        graph.non_code_references.update(referenced)
def _visible_scan_dirs(dirs: list[str]) -> list[str]:
    prune_ignore_dirs(dirs)
    return [d for d in dirs
            if d.lower() not in _NONCODE_SCAN_EXCLUDED_LOWER]
def _collect_noncode_text_files(project_root: str) -> list:
    text_files = []
    _root_key = os.path.normcase(os.path.normpath(project_root))
    for root, dirs, files in os.walk(project_root):
        dirs[:] = _visible_scan_dirs(dirs)
        _at_root = os.path.normcase(os.path.normpath(root)) == _root_key
        for fname in files:
            _lower = fname.lower()
            if _lower.endswith(_NONCODE_CONFIG_EXTENSIONS) or (
                    _at_root and _lower in _NONCODE_DOC_LOWER):
                text_files.append(os.path.join(root, fname))
    return text_files
def _scan_text_files(ac_root, defined_short_names: dict,
                     text_files: list) -> tuple[set, set]:
    referenced = set()
    referenced_simples = set()
    for fpath in text_files:
        content = _read_noncode_text(fpath)
        if content is None:
            logger.warning("非代码引用扫描跳过不可读文件: %s", fpath)
            continue
        for sn in _ac_find_all(ac_root, content, identifier_only=True):
            referenced.add(defined_short_names[sn])
            referenced_simples.add(sn)
    return referenced, referenced_simples
def build_call_graph_once(project_root: str, attempt: int):
    try:
        return True, CallGraphBuilder(
            project_root, include_tests=False).build()
    except CALLGRAPH_BUILD_ERRORS as exc:
        if attempt == 0:
            logger.warning("[Simulate] 调用图构建失败: %s", exc)
        else:
            logger.warning("[Simulate] 调用图重试仍失败，图依赖诊断降级: %s", exc)
        return False, None
def ensure_built_call_graph(project_root: str, existing_call_graph):
    if existing_call_graph is not None:
        return existing_call_graph
    logger.warning(
        "simulate_and_diagnose: existing_call_graph=None, 正在构建 CallGraph（性能警告）")
    for attempt in range(2):
        _ok, call_graph = build_call_graph_once(project_root, attempt)
        if _ok:
            return call_graph
    return None
def prepare_instrumentation_paths(project_root: str, call_graph) -> list[str]:
    if call_graph is None:
        return [project_root]
    try:
        filtered = filter_suspicious_files(project_root, call_graph=call_graph)
    except (KeyError, TypeError, AttributeError, ValueError, OSError):
        logger.debug("suppressed suspicious-file filter failure", exc_info=True)
        return [project_root]
    if filtered == [project_root]:
        return [project_root]
    logger.info(f"  [DynaPyt] 按需插桩: {len(filtered)} 文件")
    return filtered
def start_dynamic_tracer(project_root: str,
                         engine_files: tuple[str, ...] | None = None):
    try:
        kwargs = ({"engine_files": engine_files}
                  if engine_files is not None else {})
        tracer = DynamicCallTracer(project_root, **kwargs)
        tracer.start()
        return tracer, None
    except Exception as _tr_e:  # noqa: BLE001 — 追踪启动失败降级为无追踪执行
        logger.warning("[Simulate] tracer 启动失败，降级为无追踪执行: %s", _tr_e)
        return None, _tr_e
logger.info("%s 已加载: %d 项导出", __name__, len(__all__))

from __future__ import annotations

import ast
import hashlib
import importlib.util
import os
import re
import sys
import threading
from collections import defaultdict
from collections.abc import Collection
from dataclasses import dataclass, field
from functools import lru_cache, partial
from typing import ClassVar, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    class_scope,
    collect_docstring_node_ids,
    executable_line_numbers,
    is_main_check,
    iter_module_scope_funcdefs,
    iter_module_scope_nodes,
)
from jwsgj.diag_shared_source_core import (
    load_module,
    parse_cached,
    read_source,
)
from jwsgj.diag_types_vocab import (
    CAT_DYNAMIC_IMPORTS,
    FIELD_TOTAL_BLINDSPOTS,
    PARSE_DEGRADE_EXC,
    Severity,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    DIAG_OUT_OF_SCOPE_DIRS,
    GENERIC_DIAG_OUT_OF_SCOPE_DIRS,
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    SCAN_IGNORE_DIRS_LOWER,
    is_backup_path,
    is_pruned_dirname,
    is_test_file_path,
    skill_root_of,
    tarjan_scc,
    validate_source_paths,
)

logger = get_module_logger(__name__, __file__)
DEFAULT_PROJECT_ROOT = "."
DEFAULT_SEVERITY = Severity.MEDIUM
COVERAGE_UNMEASURED = -1.0
def _parse_tree(filepath, ctx=None):
    loaded = load_module(filepath, ctx)
    return loaded[1] if loaded else None
def _rel_path(project_root: str, filepath: str) -> str | None:
    try:
        return os.path.relpath(filepath, project_root).replace('\\', '/')
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_rel_path:ValueError')
        return None
def _is_init_basename(rel: str) -> bool:
    return os.path.basename(rel).lower() == '__init__.py'
def _is_main_basename(rel: str) -> bool:
    return os.path.basename(rel).lower() == '__main__.py'
def module_stem_index(project_root: str, files) -> dict[str, set[str]]:
    index: dict[str, set[str]] = {}
    for filepath in files or []:
        rel = _rel_path(project_root, filepath)
        if rel is None:
            continue
        if _is_init_basename(rel):
            mod_name = os.path.dirname(rel).replace('/', '.')
        else:
            mod_name = rel_to_dotted_module(rel)
        if mod_name:
            index.setdefault(mod_name.rsplit('.', 1)[-1], set()).add(mod_name)
    return index
def _iter_tests_domain_files(project_root: str,
                             files: list | None = None) -> list[str]:
    candidates = (collect_py_files(project_root) if files is None else files)
    return [f for f in candidates if is_tests_domain_file(f, project_root)]
def tests_domain_files(project_root: str) -> list[str]:
    try:
        return _iter_tests_domain_files(project_root)
    except (OSError, ValueError) as exc:
        log_swallowed(__name__, exc, context='tests_domain_files:collect')
        return []
def _main_blocks(tree: ast.AST) -> tuple[ast.If, ...]:
    return tuple(
        node for node in iter_module_scope_nodes(tree, descend_classes=False)
        if isinstance(node, ast.If) and is_main_check(node.test))
def _function_scope_import_nodes(tree: ast.AST) -> tuple[set, int]:
    nodes: set = set()
    defined = 0
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            defined += 1
            nodes.update(
                child for child in walk_nodes(node)
                if isinstance(child, (ast.Import, ast.ImportFrom)))
    return nodes, defined
__all__ = [
    "MAX_LAZY_MODULES_CACHE",
    "BlindspotAnalyzer",
    "BlindspotBlock",
    "BlindspotReport",
    "ModuleBlindspot",
    "ModuleBlindspotReport",
    "ModuleBlindspotScanner",
    "ResolveMemo",
    "ScriptBlindspot",
    "ScriptBlindspotReport",
    "ScriptBlindspotScanner",
    "blindspot_histograms",
    "build_file_index",
    "collect_py_files",
    "extract_lazy_modules_from_init",
    "filter_scannable_files",
    "find_package_init",
    "is_pytest_plugin_module",
    "is_tests_domain_file",
    "iter_py_files_under",
    "load_registry_lazy_modules",
    "module_stem_index",
    "rel_to_dotted_module",
    "resolve_import",
    "tests_domain_files",
]
_COVERAGE_HOOK_EXCS = (Exception,)
_TRY_NODES: tuple[type[ast.AST], ...] = (
    (ast.Try, ast.TryStar) if hasattr(ast, "TryStar") else (ast.Try,))
def _iter_import_targets(node: ast.AST, resolve, files: list,
                         rel_source: str, _file_index: dict | None = None):
    if not isinstance(node, (ast.Import, ast.ImportFrom)):
        return
    for spec in _iter_import_specs(node):
        resolved = resolve(spec, files, rel_source, _file_index=_file_index)
        if resolved:
            yield resolved
def _iter_importfrom_specs(node: ast.ImportFrom):
    if node.module:
        yield (('abs', node.module) if node.level == 0
               else ('rel', node.level, node.module))
        for alias in node.names:
            yield (('abs', f'{node.module}.{alias.name}') if node.level == 0
                    else ('rel', node.level, f'{node.module}.{alias.name}'))
        return
    if node.level > 0:
        yield ('rel', node.level, '')
        for alias in node.names:
            yield ('rel', node.level, alias.name)
def _iter_import_specs(node: ast.AST):
    if isinstance(node, ast.Import):
        for alias in node.names:
            yield ('abs', alias.name)
    elif isinstance(node, ast.ImportFrom):
        yield from _iter_importfrom_specs(node)
def _invisible_consumption_hit(rel: str, filepath: str, call_graph,
                               tests_consumed, ctx) -> bool:
    if _dynamic_import_consumed(rel, call_graph):
        return True
    if tests_consumed and rel in tests_consumed:
        return True
    return is_pytest_plugin_module(filepath, ctx)
def _dynamic_import_consumed(rel: str, call_graph) -> bool:
    return bool(
        call_graph is not None
        and hasattr(call_graph, CAT_DYNAMIC_IMPORTS)
        and call_graph.dynamic_imports.get(rel, set()))
def _strip_init_suffix(dotted: str) -> str:
    return dotted.removesuffix('.__init__') if dotted else dotted
def _lazy_dotted_name(rel: str) -> str:
    return _strip_init_suffix(rel_to_dotted_module(rel))
def _coerce_lazy_modules(lazy_modules) -> set:
    if lazy_modules is None:
        return set()
    if isinstance(lazy_modules, str):
        return {lazy_modules}
    try:
        return set(lazy_modules)
    except TypeError as _e:
        log_swallowed(__name__, _e, context='_coerce_lazy_modules:TypeError')
        return set()
def _has_unobservable_consumption(ctx, rel: str, filepath: str,
                                  call_graph, tests_consumed,
                                  lazy_modules: set | None) -> bool:
    if _invisible_consumption_hit(rel, filepath, call_graph, tests_consumed, ctx):
        return True
    return lazy_modules is not None and _lazy_dotted_name(rel) in lazy_modules
class _TestsConsumptionIndex(NamedTuple):
    modules: set[str]
    analysis_complete: bool
def _collect_tests_consumed_modules(project_root: str, raw_files: list,
                                    ctx=None,
                                    _file_index: dict | None = None,
                                    ) -> _TestsConsumptionIndex:
    tests_files = _iter_tests_domain_files(project_root, raw_files)
    if not tests_files:
        return _TestsConsumptionIndex(modules=set(), analysis_complete=True)
    prod_files = [f for f in raw_files if not is_tests_domain_file(f, project_root)]
    if _file_index is None:
        _file_index = build_file_index(project_root, prod_files)
    resolve_memo = ResolveMemo(partial(resolve_import, project_root))
    consumed: set[str] = set()
    analysis_complete = True
    for tf in tests_files:
        targets = _test_file_import_targets(
            tf, project_root, resolve_memo, prod_files, _file_index, ctx)
        if targets is None:
            analysis_complete = False
            continue
        consumed |= targets
    return _TestsConsumptionIndex(
        modules=consumed, analysis_complete=analysis_complete)
def _test_file_import_targets(tf: str, project_root: str, resolve_memo,
                              prod_files: list, _file_index: dict | None,
                              ctx=None) -> set[str] | None:
    tree = _parse_tree(tf, ctx)
    if tree is None:
        return None
    rel_source = _rel_path(project_root, tf)
    if rel_source is None:
        return None
    targets: set[str] = set()
    for node in walk_nodes(tree):
        targets.update(_iter_import_targets(
            node, resolve_memo.resolve, prod_files, rel_source,
            _file_index=_file_index))
    return targets
@dataclass
class ModuleBlindspot:
    filepath: str
    blindspot_type: str
    severity: str
    in_degree: int = 0
    out_degree: int = 0
    imported_by: list[str] = field(default_factory=list)
    imports_modules: list[str] = field(default_factory=list)
    defined_functions: int = 0
    called_functions: int = 0
    cycle_members: list[str] = field(default_factory=list)
    message: str = ''
    suggestion: str = ''
    def to_dict(self) -> dict:
        return {'filepath': self.filepath, 'blindspot_type': self.blindspot_type, 'severity': self.severity, 'in_degree': self.in_degree, 'out_degree': self.out_degree, 'imported_by': self.imported_by, 'imports_modules': self.imports_modules, 'defined_functions': self.defined_functions, 'called_functions': self.called_functions, 'cycle_members': self.cycle_members, 'message': self.message, 'suggestion': self.suggestion}
def blindspot_histograms(blindspots) -> tuple[dict, dict]:
    sev = defaultdict(int)
    btype = defaultdict(int)
    for b in blindspots:
        sev[b.severity] += 1
        btype[b.blindspot_type] += 1
    return dict(sev), dict(btype)
@dataclass
class ModuleBlindspotReport:
    project_root: str
    total_modules: int = 0
    import_edges: int = 0
    import_cycles: int = 0
    cycle_modules: list[str] = field(default_factory=list)
    blindspots: list[ModuleBlindspot] = field(default_factory=list)
    def summary(self) -> dict:
        sev, btype = blindspot_histograms(self.blindspots)
        return {'total_modules': self.total_modules, 'import_edges': self.import_edges, 'import_cycles': self.import_cycles, 'cycle_module_count': len(self.cycle_modules), FIELD_TOTAL_BLINDSPOTS: len(self.blindspots), 'by_severity': sev, 'by_type': btype}
class _ModuleClassifyEvidence(NamedTuple):
    reverse_graph: dict
    import_graph: dict
    defined_funcs: dict
    called_funcs: dict
    lazy_modules: set
    tests_consumed: set
    call_graph: object
    has_call_edges: bool
class _ModuleGraphIndex(NamedTuple):
    import_graph: dict
    reverse_graph: dict
    defined_funcs: dict
    inferred_lazy: set
    main_modules: set
    analyzed_modules: set
    total_edges: int
    analysis_complete: bool
def _build_module_graphs(scanner, all_files: list,
                         _file_index: dict | None) -> _ModuleGraphIndex:
    import_graph: dict[str, set[str]] = defaultdict(set)
    reverse_graph: dict[str, set[str]] = defaultdict(set)
    defined_funcs: dict[str, int] = {}
    inferred_lazy: set[str] = set()
    main_modules: set[str] = set()
    analyzed_modules: set[str] = set()
    analysis_complete = True
    for filepath in all_files:
        info = scanner._analyze_module(filepath, all_files, _file_index=_file_index)
        rel = _rel_path(scanner.project_root, filepath)
        if rel is None:
            analysis_complete = False
            continue
        imports = info['imports']
        import_graph[rel] = imports
        reverse_graph.setdefault(rel, set())
        defined_funcs[rel] = info['defined_funcs']
        if info.get('has_main'):
            main_modules.add(rel)
        if info['analyzed']:
            analyzed_modules.add(rel)
        else:
            analysis_complete = False
        for imp in imports:
            if imp == rel:
                continue
            reverse_graph[imp].add(rel)
        for lazy_imp in info.get('lazy_imports', set()):
            inferred_lazy.add(_lazy_dotted_name(lazy_imp))
    total_edges = sum(len(imports) for imports in import_graph.values())
    return _ModuleGraphIndex(
        import_graph=import_graph, reverse_graph=reverse_graph,
        defined_funcs=defined_funcs, inferred_lazy=inferred_lazy,
        main_modules=main_modules, analyzed_modules=analyzed_modules,
        total_edges=total_edges, analysis_complete=analysis_complete)
def _extract_called_funcs(call_graph):
    calls = getattr(call_graph, 'calls', None) if call_graph is not None else None
    if not isinstance(calls, (list, tuple)) or not calls:
        return False, defaultdict(int)
    called_funcs: dict[str, int] = defaultdict(int)
    for edge in calls:
        callee_file = getattr(edge, 'callee_file', '')
        if callee_file:
            called_funcs[str(callee_file).replace('\\', '/')] += 1
    return True, called_funcs
def _classify_orphan_module(report, ev, rel: str, filepath: str, ctx,
                            has_main: bool) -> None:
    imported_by = sorted(ev.reverse_graph.get(rel, set()))
    if (imported_by or _is_init_basename(rel) or _is_main_basename(rel)
            or has_main):
        return
    if _has_unobservable_consumption(
            ctx, rel, filepath, ev.call_graph, ev.tests_consumed,
            ev.lazy_modules):
        return
    imports = sorted(ev.import_graph.get(rel, set()))
    report.blindspots.append(ModuleBlindspot(
        filepath=rel,
        blindspot_type='orphan_module',
        severity='high',
        in_degree=0,
        out_degree=len(imports),
        imported_by=[],
        imports_modules=imports[:10],
        defined_functions=ev.defined_funcs.get(rel, 0),
        called_functions=ev.called_funcs.get(rel, 0),
        message='模块不被任何其他模块导入',
        suggestion='检查是否遗漏了导入，或将公共 API 注册到父级 __init__.py',
    ))
def _classify_dead_module(report, ev, rel: str, filepath: str, ctx) -> None:
    if (not ev.has_call_edges or _is_init_basename(rel)
            or _is_main_basename(rel)):
        return
    df = ev.defined_funcs.get(rel, 0)
    if df <= 0:
        return
    if ev.called_funcs.get(rel, 0) > 0:
        return
    if _has_unobservable_consumption(
            ctx, rel, filepath, ev.call_graph, ev.tests_consumed,
            ev.lazy_modules):
        return
    imported_by = sorted(ev.reverse_graph.get(rel, set()))
    imports = sorted(ev.import_graph.get(rel, set()))
    report.blindspots.append(ModuleBlindspot(
        filepath=rel,
        blindspot_type='dead_module',
        severity='medium',
        in_degree=len(imported_by),
        out_degree=len(imports),
        imported_by=imported_by[:10],
        imports_modules=imports[:10],
        defined_functions=df,
        called_functions=0,
        message=f'模块定义了 {df} 个函数，但无一被调用',
        suggestion='检查模块是否仍在使用，或标记为废弃',
    ))
def _cycle_entry(mod: str, cycle_modules: list, import_graph: dict,
                 reverse_graph: dict, threshold: int) -> ModuleBlindspot:
    if len(cycle_modules) == 1:
        imported_by = sorted(reverse_graph.get(mod, set()))
        imports = sorted(import_graph.get(mod, set()))
        return ModuleBlindspot(
            filepath=mod,
            blindspot_type='cycle_module',
            severity='medium',
            in_degree=len(imported_by),
            out_degree=len(imports),
            imported_by=imported_by[:10],
            imports_modules=imports[:10],
            cycle_members=[],
            message='模块导入自身（自引用环）',
            suggestion='删除自引用导入：模块导入自身不构成真实依赖拓扑',
        )
    cycle_size = len(cycle_modules)
    other_members = [m for m in cycle_modules if m != mod]
    imported_by = sorted(reverse_graph.get(mod, set()))
    imports = sorted(import_graph.get(mod, set()))
    message = (f"模块处于 {cycle_size} 元导入环中: "
               f"{' → '.join(other_members[:3])}"
               + (f' ... ({cycle_size - 4} more)' if cycle_size > 4 else ''))
    return ModuleBlindspot(
        filepath=mod,
        blindspot_type='cycle_module',
        severity='high' if cycle_size >= threshold else 'medium',
        in_degree=len(imported_by),
        out_degree=len(imports),
        imported_by=imported_by[:10],
        imports_modules=imports[:10],
        cycle_members=other_members[:10],
        message=message,
        suggestion='重构以打破循环：提取共享接口到独立模块，或使用延迟导入',
    )
def _is_package_descendant(init_mod: str, other_mod: str) -> bool:
    package_dir = os.path.dirname(init_mod).replace('\\', '/').rstrip('/')
    other_dir = os.path.dirname(other_mod).replace('\\', '/').rstrip('/')
    if other_mod.startswith('../') or other_dir.startswith('../'):
        return False
    if not package_dir:
        return True
    return other_dir == package_dir or other_dir.startswith(package_dir + '/')
def _is_package_init_cycle(cycle_modules: list) -> bool:
    if len(cycle_modules) != 2:
        return False
    return any(
        _is_init_basename(init_mod)
        and _is_package_descendant(init_mod, other_mod)
        for init_mod in cycle_modules
        for other_mod in cycle_modules
        if other_mod != init_mod)
def _report_cycle_blindspots(report, cycles: list, import_graph: dict,
                             reverse_graph: dict, threshold: int) -> None:
    for cycle_modules in cycles:
        if _is_package_init_cycle(cycle_modules):
            continue
        for mod in cycle_modules:
            report.cycle_modules.append(mod)
            report.blindspots.append(_cycle_entry(
                mod, cycle_modules, import_graph, reverse_graph, threshold))
class ModuleBlindspotScanner:
    _CYCLE_SEVERITY_THRESHOLD = 5
    def __init__(self, project_root: str=DEFAULT_PROJECT_ROOT, ctx=None) -> None:
        self.project_root = os.path.abspath(project_root)
        self._ctx = ctx
        self._resolve_memo = ResolveMemo(partial(resolve_import, self.project_root))
    def scan(self, source_paths: list[str] | None=None, call_graph=None, lazy_modules: set | None=None) -> ModuleBlindspotReport:
        self._resolve_memo.clear()
        report = ModuleBlindspotReport(project_root=self.project_root)
        scope = _prepare_scan_scope(self.project_root, source_paths, self._ctx)
        report.total_modules = len(scope.all_files)
        _file_index = scope.file_index
        graphs = _build_module_graphs(self, scope.all_files, _file_index)
        report.import_edges = graphs.total_edges
        lazy_modules = (_coerce_lazy_modules(lazy_modules) | graphs.inferred_lazy
                        | load_registry_lazy_modules(
                            self.project_root, scope.all_files, _file_index)
                        | extract_lazy_modules_from_init(self.project_root))
        cycles = self._detect_import_cycles(graphs.import_graph)
        report.import_cycles = sum(
            1 for c in cycles if not _is_package_init_cycle(c))
        has_call_edges, called_funcs = _extract_called_funcs(call_graph)
        ev = _ModuleClassifyEvidence(
            reverse_graph=graphs.reverse_graph, import_graph=graphs.import_graph,
            defined_funcs=graphs.defined_funcs, called_funcs=called_funcs,
            lazy_modules=lazy_modules, tests_consumed=scope.tests_consumed,
            call_graph=call_graph, has_call_edges=has_call_edges)
        if graphs.analysis_complete and scope.tests_analysis_complete:
            for filepath in scope.all_files:
                rel = _rel_path(self.project_root, filepath)
                if rel is None or rel not in graphs.analyzed_modules:
                    continue
                has_main = rel in graphs.main_modules
                _classify_orphan_module(
                    report, ev, rel, filepath, self._ctx, has_main)
                _classify_dead_module(report, ev, rel, filepath, self._ctx)
        _report_cycle_blindspots(
            report, cycles, graphs.import_graph, graphs.reverse_graph,
            self._CYCLE_SEVERITY_THRESHOLD)
        return report
    def _detect_import_cycles(self, import_graph: dict[str, set[str]]) -> list[list[str]]:
        cycles: list[list[str]] = []
        for scc in tarjan_scc(import_graph):
            modules = sorted(scc)
            if len(modules) > 1 or (
                    modules and modules[0] in import_graph.get(modules[0], ())):
                cycles.append(modules)
        return cycles
    def _analyze_module(self, filepath: str, all_files: list[str], _file_index: dict | None=None) -> dict:
        rel = _rel_path(self.project_root, filepath)
        result = {'imports': set(), 'lazy_imports': set(), 'defined_funcs': 0,
                  'has_main': False, 'analyzed': False}
        tree = _parse_tree(filepath, self._ctx)
        if tree is None or rel is None:
            return result
        result['analyzed'] = True
        func_nodes, result['defined_funcs'] = _function_scope_import_nodes(tree)
        def _collect_imports(node: ast.AST, target: set) -> None:
            target.update(_iter_import_targets(
                node, self._resolve_memo.resolve, all_files, rel,
                _file_index=_file_index))
        for node in iter_module_scope_nodes(tree):
            _collect_imports(node, result['imports'])
        result['has_main'] = bool(_main_blocks(tree))
        for node in func_nodes:
            _collect_imports(node, result['lazy_imports'])
        return result
@dataclass
class ScriptBlindspot:
    filepath: str
    blindspot_type: str
    severity: str
    has_main_block: bool = False
    main_block_lines: tuple[int, int] = (0, 0)
    imported_by: list[str] = field(default_factory=list)
    imports_modules: list[str] = field(default_factory=list)
    coverage_pct: float = COVERAGE_UNMEASURED
    message: str = ''
    suggestion: str = ''
    def to_dict(self) -> dict:
        return {'filepath': self.filepath, 'blindspot_type': self.blindspot_type, 'severity': self.severity, 'has_main_block': self.has_main_block, 'main_block_lines': list(self.main_block_lines), 'imported_by': self.imported_by, 'imports_modules': self.imports_modules, 'coverage_pct': self.coverage_pct, 'message': self.message, 'suggestion': self.suggestion}
@dataclass
class ScriptBlindspotReport:
    project_root: str
    total_scripts: int = 0
    cli_scripts: int = 0
    standalone_scripts: int = 0
    blindspots: list[ScriptBlindspot] = field(default_factory=list)
    def summary(self) -> dict:
        sev, btype = blindspot_histograms(self.blindspots)
        return {'total_scripts': self.total_scripts, 'cli_scripts': self.cli_scripts, 'standalone_scripts': self.standalone_scripts, FIELD_TOTAL_BLINDSPOTS: len(self.blindspots), 'by_severity': sev, 'by_type': btype}
class _ScriptFileRow(NamedTuple):
    rel: str
    filepath: str
    imported_by: list
    imports: list
class _ScriptGraphIndex(NamedTuple):
    reverse_graph: dict
    main_blocks: dict
    main_body_starts: dict
    file_imports: dict
    analyzed_files: set
    analysis_complete: bool
    main_entries: dict
def _report_cli_entry_blindspot(report, row, preview_imports: list,
                                main_range: tuple, main_covered: bool) -> None:
    if main_covered:
        return
    report.blindspots.append(ScriptBlindspot(
        filepath=row.rel,
        blindspot_type='cli_entry_unexecuted',
        severity='high',
        has_main_block=True,
        main_block_lines=main_range,
        imported_by=row.imported_by,
        imports_modules=preview_imports,
        message="脚本入口（if __name__ == '__main__'）从未被执行",
        suggestion=f'运行: python {row.rel} 或通过 CLI 命令触发',
    ))
def _report_standalone_blindspot(report, row, preview_imports: list) -> None:
    report.standalone_scripts += 1
    report.blindspots.append(ScriptBlindspot(
        filepath=row.rel,
        blindspot_type='standalone_unimported',
        severity='medium',
        has_main_block=False,
        imported_by=[],
        imports_modules=preview_imports,
        message='模块从未被任何其他模块导入，且无入口点',
        suggestion='检查是否应被导入到项目中，或添加 __main__ 入口',
    ))
def _report_low_coverage_blindspot(report, row, preview_imports: list,
                                  has_main: bool, cov_pct,
                                  threshold: float,
                                  main_range: tuple) -> None:
    if cov_pct is None or cov_pct >= threshold:
        return
    report.blindspots.append(ScriptBlindspot(
        filepath=row.rel,
        blindspot_type='low_coverage',
        severity='high' if cov_pct == 0 else 'medium',
        has_main_block=has_main,
        main_block_lines=main_range if has_main else (0, 0),
        coverage_pct=cov_pct,
        imported_by=row.imported_by,
        imports_modules=preview_imports,
        message=f'脚本覆盖率仅 {cov_pct}%，可能存在大量未测试代码',
        suggestion='为该脚本编写单元测试或集成测试',
    ))
class ScriptBlindspotScanner:
    _LOW_COVERAGE_THRESHOLD = 10.0
    def __init__(self, project_root: str=DEFAULT_PROJECT_ROOT, ctx=None) -> None:
        self.project_root = os.path.abspath(project_root)
        self._ctx = ctx
    @staticmethod
    def _preview_imports(imports: list) -> list[str]:
        preview: list[str] = []
        for spec in imports[:10]:
            if isinstance(spec, tuple) and spec:
                kind = spec[0]
                if kind == 'abs' and len(spec) >= 2:
                    preview.append(str(spec[1]))
                    continue
                if kind == 'rel' and len(spec) >= 3:
                    level = spec[1] if isinstance(spec[1], int) else 1
                    preview.append('.' * max(level, 0) + str(spec[2]))
                    continue
            preview.append(str(spec))
        return preview
    def scan(self, source_paths: list[str] | None=None, coverage_hook=None, call_graph=None) -> ScriptBlindspotReport:
        report = ScriptBlindspotReport(project_root=self.project_root)
        scope = _prepare_scan_scope(self.project_root, source_paths, self._ctx)
        report.total_scripts = len(scope.all_files)
        _file_index = scope.file_index
        registry_lazy = (load_registry_lazy_modules(
                             self.project_root, scope.all_files, _file_index)
                         | extract_lazy_modules_from_init(self.project_root))
        graphs = self._build_script_graph(scope.all_files, _file_index)
        for filepath in scope.all_files:
            rel = _rel_path(self.project_root, filepath)
            if rel is None or rel not in graphs.analyzed_files:
                continue
            imported_by = sorted(graphs.reverse_graph.get(rel, set()))
            has_main = rel in graphs.main_blocks
            row = _ScriptFileRow(rel=rel, filepath=filepath,
                                 imported_by=imported_by,
                                 imports=graphs.file_imports.get(rel, []))
            preview = self._preview_imports(row.imports)
            if has_main:
                report.cli_scripts += 1
                for main_range, body_start in graphs.main_entries.get(rel, ()):
                    _report_cli_entry_blindspot(
                        report, row, preview, main_range,
                        self._main_entry_covered(
                            coverage_hook, filepath, main_range, body_start))
            if graphs.analysis_complete and scope.tests_analysis_complete:
                self._report_standalone_if_unimported(
                    report, row, preview, has_main, registry_lazy, call_graph,
                    scope.tests_consumed)
            if coverage_hook is not None:
                _report_low_coverage_blindspot(
                    report, row, preview, has_main,
                    self._get_coverage_pct(coverage_hook, filepath),
                    self._LOW_COVERAGE_THRESHOLD,
                    graphs.main_blocks.get(rel, (0, 0)))
        return report
    def _report_standalone_if_unimported(
            self, report: ScriptBlindspotReport, row: _ScriptFileRow,
            preview_imports: list, has_main: bool, registry_lazy: set,
            call_graph, tests_consumed) -> None:
        if (row.imported_by or has_main or _is_init_basename(row.rel)
                or _is_main_basename(row.rel) or _has_unobservable_consumption(
                    self._ctx, row.rel, row.filepath, call_graph,
                    tests_consumed, registry_lazy)):
            return
        _report_standalone_blindspot(report, row, preview_imports)
    def _build_script_graph(self, all_files: list,
                            _file_index: dict) -> _ScriptGraphIndex:
        resolve_memo = ResolveMemo(partial(resolve_import, self.project_root))
        reverse_import_graph: dict[str, set[str]] = defaultdict(set)
        all_main_blocks: dict[str, tuple[int, int]] = {}
        all_main_body_starts: dict[str, int] = {}
        all_main_entries: dict[str, tuple] = {}
        file_imports: dict[str, list[str]] = defaultdict(list)
        analyzed_files: set[str] = set()
        analysis_complete = True
        for filepath in all_files:
            rel = _rel_path(self.project_root, filepath)
            if rel is None:
                analysis_complete = False
                continue
            info = self._analyze_file(filepath)
            if not info['analyzed']:
                analysis_complete = False
                continue
            analyzed_files.add(rel)
            if info['has_main']:
                all_main_blocks[rel] = info['main_range']
                all_main_body_starts[rel] = info.get(
                    'main_body_start', info['main_range'][0])
                all_main_entries[rel] = info['main_entries']
            if not info['imports']:
                continue
            tree = info.get('tree')
            if tree is None:
                continue
            file_imports[rel] = info['imports']
            targets: set[str] = set()
            for node in walk_nodes(tree):
                targets.update(_iter_import_targets(
                    node, resolve_memo.resolve, all_files, rel,
                    _file_index=_file_index))
            for resolved in targets:
                if resolved != rel:
                    reverse_import_graph[resolved].add(rel)
        return _ScriptGraphIndex(
            reverse_graph=reverse_import_graph,
            main_blocks=all_main_blocks, main_body_starts=all_main_body_starts,
            file_imports=file_imports, analyzed_files=analyzed_files,
            analysis_complete=analysis_complete, main_entries=all_main_entries)
    def _analyze_file(self, filepath: str) -> dict:
        result = {'has_main': False, 'main_range': (0, 0), 'imports': [],
                  'tree': None, 'analyzed': False, 'main_entries': ()}
        tree = _parse_tree(filepath, self._ctx)
        if tree is None:
            return result
        result['analyzed'] = True
        result['tree'] = tree
        main_nodes = _main_blocks(tree)
        if main_nodes:
            result['has_main'] = True
            entries = []
            for main_node in main_nodes:
                start = main_node.lineno
                main_range = (start, main_node.end_lineno or start)
                body_start = (
                    main_node.body[0].lineno if main_node.body else start)
                entries.append((main_range, body_start))
            result['main_entries'] = tuple(entries)
            result['main_range'] = entries[0][0]
            result['main_body_start'] = entries[0][1]
        for node in walk_nodes(tree):
            result['imports'].extend(_iter_import_specs(node))
        return result
    def _main_evidence_lines(self, filepath: str, start: int, end: int) -> list[int]:
        tree = _parse_tree(filepath, self._ctx)
        if tree is None:
            logger.debug('覆盖率证据行读取失败: %s', filepath)
            return []
        main_node = next((
            node for node in _main_blocks(tree)
            if node.body
            and node.body[0].lineno == start
            and (node.end_lineno or node.lineno) == end), None)
        if main_node is not None:
            return sorted({stmt.lineno for stmt in main_node.body})
        return sorted({
            node.lineno for node in walk_nodes(tree)
            if isinstance(node, ast.stmt) and start <= node.lineno <= end
        })
    def _main_entry_covered(self, coverage_hook, filepath: str,
                            main_range: tuple,
                            body_start: int | None) -> bool:
        if coverage_hook is None:
            return True
        if body_start is None:
            body_start = (main_range[0] + 1
                          if main_range[1] > main_range[0] else main_range[0])
        return self._check_coverage(
            coverage_hook, filepath, body_start, main_range[1])
    def _check_coverage(self, coverage_hook, filepath: str, start: int, end: int) -> bool:
        try:
            uncovered = coverage_hook.get_uncovered(filepath)
            evidence_lines = self._main_evidence_lines(filepath, start, end)
            if not evidence_lines:
                return True
            return any(ln not in uncovered for ln in evidence_lines)
        except _COVERAGE_HOOK_EXCS as exc:
            # 覆盖率探针失败时按“已覆盖”收敛会让盲区静默消失，必须留可感知痕迹。
            log_swallowed(__name__, exc, context='_check_coverage')
            logger.debug('覆盖率检查失败: %s', exc)
            return True
    def _get_coverage_pct(self, coverage_hook, filepath: str) -> float | None:
        try:
            uncovered = coverage_hook.get_uncovered(filepath)
            if uncovered is None:
                return None
            source = read_source(filepath, self._ctx)
            if source is None:
                logger.debug('覆盖率文件读取失败: %s', filepath)
                return None
            executable_lines = executable_line_numbers(source.split('\n'))
            if not executable_lines:
                return 100.0
            effective_uncovered = len(set(uncovered) & executable_lines)
            return round((1 - effective_uncovered / len(executable_lines)) * 100, 1)
        except _COVERAGE_HOOK_EXCS as exc:
            logger.warning('覆盖率百分比计算失败: %s', exc, exc_info=True)
            return None
def _prune_scan_dirs(dirs: list, project_root: str | None = None,
                     *, is_skill: bool | None = None) -> None:
    if project_root is None and is_skill is None:
        dirs[:] = [d for d in dirs
                   if not is_pruned_dirname(d) and not is_backup_path(d)]
        return
    if is_skill is None:
        is_skill = bool(skill_root_of(project_root))
    active_view = (SCAN_IGNORE_DIRS_LOWER if is_skill
                   else GENERIC_SCAN_IGNORE_DIRS_LOWER)
    skill_only = (
        (SCAN_IGNORE_DIRS_LOWER - GENERIC_SCAN_IGNORE_DIRS_LOWER)
        | {name.lower() for name in
           (DIAG_OUT_OF_SCOPE_DIRS - GENERIC_DIAG_OUT_OF_SCOPE_DIRS)}
    )
    dirs[:] = [
        d for d in dirs
        if not _should_prune_scan_dir(d, active_view, skill_only, is_skill)
    ]
def _should_prune_scan_dir(name: str, active_view: frozenset,
                           skill_only: frozenset, is_skill: bool) -> bool:
    lowered = str(name).lower()
    if not is_skill and lowered in skill_only:
        return False
    return (lowered in active_view
            or is_pruned_dirname(name)
            or is_backup_path(name))
def _walk_error(error: OSError) -> None:
    log_swallowed(__name__, error, context='iter_py_files_under:OSError')
def iter_py_files_under(path: str):
    is_skill = bool(skill_root_of(path))
    for root, dirs, fnames in os.walk(path, onerror=_walk_error):
        _prune_scan_dirs(dirs, path, is_skill=is_skill)
        dirs.sort()
        for fn in sorted(fnames):
            if fn.lower().endswith('.py') and not fn.startswith('.'):
                yield os.path.join(root, fn)
def _files_from_ctx_or_paths(project_root: str, source_paths, ctx) -> list:
    if ctx is not None and source_paths is None:
        py_files = getattr(ctx, "py_files", None)
        if py_files is not None:
            if isinstance(py_files, (str, os.PathLike)):
                return [os.fsdecode(os.fspath(py_files))]
            if not isinstance(py_files, (list, tuple)):
                py_files = list(py_files)
                try:
                    ctx.py_files = py_files
                except (AttributeError, TypeError) as _e:
                    log_swallowed(__name__, _e,
                                  context='_files_from_ctx_or_paths:AttributeError')
            return list(py_files)
    if source_paths is None:
        source_paths = [project_root]
    files: list = []
    for p in source_paths:
        files.extend(_expand_source_path(p, project_root))
    return files
def _expand_source_path(path, project_root: str) -> list:
    path = os.fsdecode(os.fspath(path))
    if not os.path.isabs(path):
        path = os.path.join(project_root, path)
    path = os.path.abspath(path)
    if os.path.isfile(path) and path.lower().endswith('.py'):
        return [path]
    if os.path.isdir(path):
        return list(iter_py_files_under(path))
    return []
def collect_py_files(project_root: str, source_paths=None, ctx=None) -> list:
    validate_source_paths(source_paths)
    files = _files_from_ctx_or_paths(project_root, source_paths, ctx)
    normalized: dict[str, str] = {}
    for f in files:
        absolute = f if os.path.isabs(f) else os.path.join(project_root, f)
        absolute = os.path.abspath(absolute)
        normalized.setdefault(os.path.normcase(absolute), absolute)
    return list(normalized.values())
def filter_scannable_files(project_root: str, files: list) -> list:
    filtered = []
    for f in files:
        rel = _rel_path(project_root, f)
        if rel is None:
            logger.debug('[BlindSpot] 跨盘路径无法归一,跳过: %s', f)
            continue
        if is_tests_domain_file(rel, project_root):
            continue
        filtered.append(f)
    return filtered
class _ScanScope(NamedTuple):
    raw_files: list
    all_files: list
    tests_consumed: set
    tests_analysis_complete: bool
    file_index: dict
def _prepare_scan_scope(project_root: str, source_paths, ctx=None) -> _ScanScope:
    raw_files = collect_py_files(project_root, source_paths, ctx=ctx)
    all_files = filter_scannable_files(project_root, raw_files)
    file_index = build_file_index(project_root, all_files)
    tests_consumption = _collect_tests_consumed_modules(
        project_root, raw_files, ctx, _file_index=file_index)
    return _ScanScope(
        raw_files=raw_files,
        all_files=all_files,
        tests_consumed=tests_consumption.modules,
        tests_analysis_complete=tests_consumption.analysis_complete,
        file_index=file_index)
def rel_to_dotted_module(rel: str) -> str:
    rel = rel.replace('\\', '/')
    if rel.lower().endswith('.py'):
        rel = rel[:-len('.py')]
    return rel.replace('/', '.')
def is_tests_domain_file(filepath: str, project_root: str) -> bool:
    if os.path.isabs(filepath):
        rel = _rel_path(project_root, filepath)
        if rel is None:
            return False
    else:
        rel = filepath
    return is_test_file_path(rel)
def build_file_index(project_root: str, all_files: list) -> dict:
    index = {'rel_path': {}, 'module_name': {}, 'rel_list': []}
    for f in all_files:
        absolute = f if os.path.isabs(f) else os.path.join(project_root, f)
        absolute = os.path.abspath(absolute)
        rel = _rel_path(project_root, absolute)
        if rel is None:
            continue
        index['rel_list'].append(rel)
        index['rel_path'][rel] = absolute
        if _is_init_basename(rel):
            mod_name = os.path.dirname(rel).replace('/', '.')
        else:
            mod_name = rel_to_dotted_module(rel)
        if mod_name:
            index['module_name'][mod_name] = absolute
    return index
_lazy_modules_cache: dict[tuple, frozenset] = {}
_LAZY_CACHE_LOCK = threading.Lock()
MAX_LAZY_MODULES_CACHE = 2000
_PYTEST_HOOK_FUNCS = frozenset({
    "pytest_addoption", "pytest_addhooks", "pytest_configure",
    "pytest_unconfigure", "pytest_sessionstart", "pytest_sessionfinish",
    "pytest_collection", "pytest_collectstart", "pytest_itemcollected",
    "pytest_collection_modifyitems", "pytest_collection_finish",
    "pytest_deselected", "pytest_runtestloop", "pytest_runtest_protocol",
    "pytest_runtest_setup", "pytest_runtest_call", "pytest_runtest_teardown",
    "pytest_runtest_makereport", "pytest_pyfunc_call",
    "pytest_fixture_setup", "pytest_fixture_post_finalizer",
    "pytest_plugin_registered", "pytest_report_header",
    "pytest_report_collectionfinish", "pytest_terminal_summary",
    "pytest_warning_recorded", "pytest_load_initial_conftests",
    "pytest_cmdline_main", "pytest_exception_interact",
    "pytest_enter_pdb", "pytest_leave_pdb", "pytest_namespace",
})
def is_pytest_plugin_module(filepath: str, ctx=None) -> bool:
    loaded = load_module(filepath, ctx)
    if loaded is None:
        return False
    for node in iter_module_scope_funcdefs(loaded[1]):
        if node.name in _PYTEST_HOOK_FUNCS:
            return True
    return False
_REGISTRY_TARGET_TOKENS = (
    "MODULE", "REGISTR", "CATALOG", "TABLE", "WIRING", "IMPORT", "LAZY",
)
_REGISTRY_SPEC_CTOR_SUFFIXES = (
    "Spec", "Entry", "Registration", "Provider",
)
_LAZY_SELF_NAMES = frozenset({"__init__", "__pycache__"})
def _is_registry_target(name: str) -> bool:
    upper = str(name).upper()
    return any(token in upper for token in _REGISTRY_TARGET_TOKENS)
def _iter_registry_module_names(value_node, assignments=None, _seen=None):
    if assignments is None:
        assignments = {}
    if _seen is None:
        _seen = set()
    if isinstance(value_node, ast.Constant):
        if isinstance(value_node.value, str):
            name = value_node.value.strip()
            if ':' in name:
                name = name.split(':', 1)[0].strip()
            if name:
                yield name
        return
    if isinstance(value_node, ast.Dict):
        for key, value in zip(value_node.keys, value_node.values,
                              strict=True):
            if key is not None:
                yield from _iter_registry_module_names(key, assignments, _seen)
            yield from _iter_registry_module_names(value, assignments, _seen)
        return
    if isinstance(value_node, ast.Starred):
        yield from _iter_registry_module_names(
            value_node.value, assignments, _seen)
        return
    if isinstance(value_node, (ast.Tuple, ast.List, ast.Set)):
        for element in value_node.elts:
            yield from _iter_registry_module_names(element, assignments, _seen)
        return
    if isinstance(value_node, ast.BinOp) and isinstance(value_node.op, ast.Add):
        yield from _iter_registry_module_names(
            value_node.left, assignments, _seen)
        yield from _iter_registry_module_names(
            value_node.right, assignments, _seen)
        return
    if isinstance(value_node, ast.Call):
        if str(ast_name(value_node.func)).endswith(_REGISTRY_SPEC_CTOR_SUFFIXES):
            for arg in (*value_node.args, *(kw.value for kw in value_node.keywords)):
                yield from _iter_registry_module_names(arg, assignments, _seen)
        return
    if isinstance(value_node, ast.Name):
        if value_node.id in _seen:
            return
        targets = assignments.get(value_node.id)
        if not targets:
            return
        _seen.add(value_node.id)
        try:
            for target in targets:
                yield from _iter_registry_module_names(
                    target, assignments, _seen)
        finally:
            _seen.discard(value_node.id)
def _registry_assignments(tree: ast.Module) -> list[tuple[list[str], ast.AST]]:
    entries: list[tuple[list[str], ast.AST]] = []
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if isinstance(node, ast.Assign):
            targets = [t.id for t in node.targets if isinstance(t, ast.Name)]
            entries.append((targets, node.value))
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets = ([node.target.id]
                       if isinstance(node.target, ast.Name) else [])
            entries.append((targets, node.value))
    return entries
def _collect_registry_modules(tree: ast.Module, project_root: str,
                              files: list, file_index: dict) -> set:
    entries = _registry_assignments(tree)
    assignments: dict[str, list[ast.AST]] = {}
    for targets, value in entries:
        for target in targets:
            assignments.setdefault(target, []).append(value)
    mods: set = set()
    for targets, value in entries:
        if not any(_is_registry_target(name) for name in targets) and not (
                isinstance(value, ast.Dict)):
            continue
        for name in _iter_registry_module_names(value, assignments):
            if not name or name.startswith('.'):
                continue
            resolved = resolve_import(
                project_root, ('abs', name), files, _file_index=file_index)
            if resolved is None:
                continue
            lazy_name = _lazy_dotted_name(resolved)
            if lazy_name not in _LAZY_SELF_NAMES:
                mods.add(lazy_name)
    return mods
def _registry_fingerprint(registry: str) -> tuple | None:
    try:
        st = os.stat(registry)
        digest = hashlib.blake2b(digest_size=16)
        with open(registry, 'rb') as registry_file:
            for chunk in iter(lambda: registry_file.read(1024 * 1024), b''):
                digest.update(chunk)
    except OSError as _e:
        log_swallowed(__name__, _e, context='_registry_fingerprint:OSError')
        return None
    return (registry, st.st_mtime_ns, st.st_size, digest.digest())
def _files_fingerprint(files) -> bytes:
    digest = hashlib.blake2b(digest_size=8)
    for rel in sorted(os.path.normcase(os.path.abspath(f)) for f in files or ()):
        digest.update(rel.encode('utf-8', 'surrogatepass'))
        digest.update(b'\x00')
    return digest.digest()
def _load_single_lazy_table(project_root: str, table_name: str,
                            files: list, file_index: dict) -> set:
    registry = os.path.join(project_root, table_name)
    if not os.path.isfile(registry):
        return set()
    _fp = _registry_fingerprint(registry)
    cache_key = ((_fp, _files_fingerprint(files)) if _fp is not None else None)
    if cache_key is not None:
        with _LAZY_CACHE_LOCK:
            _cached = _lazy_modules_cache.get(cache_key)
        if _cached is not None:
            return set(_cached)
    tree = _parse_tree(registry)
    if tree is None:
        return set()
    mods = _collect_registry_modules(tree, project_root, files, file_index)
    if cache_key is not None:
        with _LAZY_CACHE_LOCK:
            if len(_lazy_modules_cache) >= MAX_LAZY_MODULES_CACHE:
                logger.warning("lazy 登记表指纹缓存达上限 %d，整体清空（内存加固兜底触发）",
                               MAX_LAZY_MODULES_CACHE)
                _lazy_modules_cache.clear()
            _lazy_modules_cache[cache_key] = frozenset(mods)
    return mods
_REGISTRY_FILE_TOKENS = ("lazy", "registr", "wiring", "catalog",
                         "modules")
_PACKAGE_SOURCE_ROOTS = ("src", "lib", "python")
def _iter_package_inits(project_root: str) -> list[tuple[str, str, str]]:
    root = os.path.abspath(project_root)
    root_init = os.path.join(root, "__init__.py")
    if os.path.isfile(root_init):
        return [(root_init, os.path.basename(root), "")]
    found: list[tuple[str, str, str]] = []
    seen: set[str] = set()
    for base_rel in ("", *_PACKAGE_SOURCE_ROOTS):
        base = os.path.join(root, base_rel) if base_rel else root
        try:
            entries = sorted(os.listdir(base))
        except FileNotFoundError:
            continue
        except OSError as exc:
            log_swallowed(__name__, exc, context='_iter_package_inits:OSError')
            continue
        for name in entries:
            if (name.startswith(".")
                    or name.lower() in GENERIC_SCAN_IGNORE_DIRS_LOWER
                    or is_backup_path(name)):
                continue
            init_path = os.path.join(base, name, "__init__.py")
            if not os.path.isfile(init_path):
                continue
            if is_test_file_path(init_path):
                continue
            key = os.path.normcase(os.path.abspath(init_path))
            if key in seen:
                continue
            seen.add(key)
            rel_dir = os.path.dirname(os.path.relpath(init_path, root))
            prefix = ("" if rel_dir in ("", ".")
                      else rel_dir.replace("\\", ".").replace("/", "."))
            found.append((init_path, name, prefix))
    return found
def find_package_init(project_root: str) -> tuple[str, str, str] | None:
    candidates = _iter_package_inits(project_root)
    if len(candidates) == 1:
        return candidates[0]
    return None
class _LazyInitContext(NamedTuple):
    init_path: str
    skill_name: str
    module_prefix: str
    package_path: str
    package_depth: int
def _iter_lazy_init_contexts(project_root: str) -> list[_LazyInitContext]:
    root = os.path.abspath(project_root)
    root_is_package = os.path.isfile(os.path.join(root, '__init__.py'))
    contexts: list[_LazyInitContext] = []
    for init_path in iter_py_files_under(root):
        rel = _rel_path(root, init_path)
        if rel is None or not _is_init_basename(rel) or is_test_file_path(rel):
            continue
        dir_parts = rel.replace('\\', '/').split('/')[:-1]
        if root_is_package:
            contexts.append(_LazyInitContext(
                init_path=init_path,
                skill_name=os.path.basename(root),
                module_prefix='',
                package_path='.'.join(dir_parts),
                package_depth=len(dir_parts) + 1,
            ))
            continue
        source_depth = int(
            len(dir_parts) > 1
            and dir_parts[0].lower() in _PACKAGE_SOURCE_ROOTS)
        runtime_parts = dir_parts[source_depth:]
        contexts.append(_LazyInitContext(
            init_path=init_path,
            skill_name=runtime_parts[0],
            module_prefix='.'.join(dir_parts[:source_depth + 1]),
            package_path='.'.join(dir_parts),
            package_depth=len(runtime_parts),
        ))
    return contexts
def _iter_registry_candidate_tables(project_root: str) -> list[str]:
    try:
        names = sorted(os.listdir(project_root))
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context='_iter_registry_candidate_tables:OSError')
        return []
    candidates = []
    for name in names:
        if not name.lower().endswith('.py'):
            continue
        stem = os.path.splitext(name)[0].lower()
        if name.lower() == '__init__.py' or any(
                token in stem for token in _REGISTRY_FILE_TOKENS):
            candidates.append(name)
    for context in _iter_lazy_init_contexts(project_root):
        init_rel = os.path.relpath(
            context.init_path, project_root).replace('\\', '/')
        if init_rel not in candidates:
            candidates.append(init_rel)
    return candidates
def _lazy_modules_from_init_tree(
        tree: ast.Module, skill_name: str, module_prefix: str,
        *, package_path: str, package_depth: int) -> set:
    lazy_modules = set()
    known_pattern = re.compile(
        r'^' + re.escape(skill_name)
        + r'\.([^\W\d]\w*(?:\.[^\W\d]\w*)*)')
    docstring_ids = collect_docstring_node_ids(tree)
    function_imports = _function_scope_import_nodes(tree)[0]
    absolute_prefix = skill_name + '.'
    importlib_names = {'importlib'}
    import_module_names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            importlib_names.update(
                alias.asname or alias.name.split('.', 1)[0]
                for alias in node.names if alias.name == 'importlib')
        elif isinstance(node, ast.ImportFrom) and node.module == 'importlib':
            import_module_names.update(
                alias.asname or alias.name for alias in node.names
                if alias.name == 'import_module')
    def _qualify(name: str) -> str:
        return f"{module_prefix}.{name}" if module_prefix else name
    def _dotted_chain(qualified_name: str) -> set[str]:
        parts = qualified_name.split('.')
        return {'.'.join(parts[:index])
                for index in range(1, len(parts) + 1)}
    def _qualified_chain(relative_name: str) -> set[str]:
        parts = relative_name.split('.')
        return {
            _qualify('.'.join(parts[:index]))
            for index in range(1, len(parts) + 1)
        }
    def _collect_absolute_module(module_name: str) -> None:
        if not module_name.startswith(absolute_prefix):
            return
        relative_name = module_name[len(absolute_prefix):]
        if all(part.isidentifier() for part in relative_name.split('.')):
            lazy_modules.update(_qualified_chain(relative_name))
    def _relative_import_module(node: ast.AST) -> str | None:
        if not isinstance(node, ast.Call):
            return None
        func = node.func
        is_import_module = (
            (isinstance(func, ast.Name) and func.id in import_module_names)
            or (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)
                and func.value.id in importlib_names
                and func.attr == 'import_module'))
        if not is_import_module:
            return None
        name_node = (node.args[0] if node.args else next(
            (kw.value for kw in node.keywords if kw.arg == 'name'), None))
        package_node = (node.args[1] if len(node.args) > 1 else next(
            (kw.value for kw in node.keywords if kw.arg == 'package'), None))
        if (not isinstance(name_node, ast.Constant)
                or not isinstance(name_node.value, str)
                or not name_node.value.startswith('.')
                or not isinstance(package_node, ast.Name)
                or package_node.id not in {'__name__', '__package__'}):
            return None
        module_name = name_node.value
        level = len(module_name) - len(module_name.lstrip('.'))
        tail = module_name[level:]
        if tail and not all(part.isidentifier() for part in tail.split('.')):
            return None
        ascend = level - 1
        if ascend >= package_depth:
            return None
        parts = package_path.split('.') if package_path else []
        if ascend:
            parts = parts[:-ascend]
        if tail:
            parts.extend(tail.split('.'))
        return '.'.join(parts) or None
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Constant) and isinstance(node.value, str)
                and id(node) not in docstring_ids):
            for match in known_pattern.finditer(node.value):
                lazy_modules.update(_qualified_chain(match.group(1)))
        elif isinstance(node, ast.Import) and node in function_imports:
            for alias in node.names:
                _collect_absolute_module(alias.name)
        elif (isinstance(node, ast.ImportFrom) and node.level == 0
                and node in function_imports and node.module):
            _collect_absolute_module(node.module)
            for alias in node.names:
                _collect_absolute_module(f'{node.module}.{alias.name}')
        elif isinstance(node, ast.Call):
            relative_name = _relative_import_module(node)
            if relative_name:
                lazy_modules.update(_dotted_chain(relative_name))
    return lazy_modules
def extract_lazy_modules_from_init(project_root: str | None) -> set:
    if not project_root:
        return set()
    lazy_modules: set = set()
    for context in _iter_lazy_init_contexts(project_root):
        init_content = read_source(context.init_path)
        if init_content is None:
            logger.warning("[ImpIdx] init read failed: %s", context.init_path)
            continue
        try:
            tree = parse_cached(init_content, context.init_path)
        except PARSE_DEGRADE_EXC as exc:
            logger.warning(
                "[ImpIdx] init parse failed %s: %s", context.init_path, exc)
            continue
        lazy_modules |= _lazy_modules_from_init_tree(
            tree, context.skill_name, context.module_prefix,
            package_path=context.package_path,
            package_depth=context.package_depth)
    lazy_modules = {_strip_init_suffix(name) for name in lazy_modules if name}
    lazy_modules -= _LAZY_SELF_NAMES
    return lazy_modules
def load_registry_lazy_modules(project_root: str, files: list | None = None,
                               _file_index: dict | None = None) -> set:
    if files is None:
        files = filter_scannable_files(
            project_root, collect_py_files(project_root))
    if _file_index is None:
        _file_index = build_file_index(project_root, files)
    mods: set = set()
    for table_name in _iter_registry_candidate_tables(project_root):
        mods |= _load_single_lazy_table(
            project_root, table_name, files, _file_index)
    return mods
class _ImportResolver:
    __slots__ = ('_file_index', 'all_files', 'project_root')
    def __init__(self, project_root: str, all_files: list[str],
                 _file_index: dict | None=None) -> None:
        self.project_root = os.path.abspath(project_root)
        self.all_files = all_files
        self._file_index = _file_index
    @staticmethod
    def _is_typed_spec_segments(import_spec: tuple, types: tuple) -> bool:
        if len(import_spec) < len(types) + 1:
            return False
        return all(isinstance(import_spec[i + 1], t)
                   for i, t in enumerate(types))
    @staticmethod
    def _normalize_import_spec(import_spec) -> tuple | None:
        if isinstance(import_spec, tuple):
            return import_spec or None
        if not isinstance(import_spec, str) or import_spec.startswith('.'):
            return None
        return ('abs', import_spec)
    def resolve(self, import_spec, source_file: str | None=None) -> str | None:
        import_spec = self._normalize_import_spec(import_spec)
        if import_spec is None:
            return None
        imp_type = import_spec[0]
        if imp_type == 'abs':
            if not self._is_typed_spec_segments(import_spec, (str,)):
                return None
            return self._resolve_abs_import(import_spec[1])
        if imp_type == 'rel':
            if not self._is_typed_spec_segments(import_spec, (int, str)):
                return None
            return self._resolve_rel_import(
                import_spec[1], import_spec[2], source_file)
        return None
    def _resolve_root_package_import(self, parts: list[str]) -> str | None:
        inner_parts = parts[1:]
        inner_candidates = (['__init__.py'] if not inner_parts
                            else ['/'.join(inner_parts) + '/__init__.py',
                                  '/'.join(inner_parts) + '.py'])
        return self._lookup_rel_exact(inner_candidates)
    def _resolve_abs_import(self, import_name: str) -> str | None:
        parts = import_name.split('.')
        root_name = os.path.basename(self.project_root)
        candidates = ['/'.join(parts) + '/__init__.py',
                      '/'.join(parts) + '.py']
        if parts[0] == root_name:
            if self._lookup_rel_exact(('__init__.py',)) is None:
                hit = self._lookup_rel_exact(candidates)
                if hit is not None:
                    return hit
            hit = self._resolve_root_package_import(parts)
            if hit is not None:
                return hit
        if self._file_index is not None:
            hit = self._lookup_index_exact(candidates)
            if hit is not None:
                return hit
            mod_index = self._file_index.get('module_name', {})
            if import_name in mod_index:
                return _rel_path(self.project_root, mod_index[import_name])
        if len(parts) == 1 and _is_external_module(import_name):
            hit = self._lookup_rel_exact(candidates)
            if hit is not None:
                return hit
            source_candidates = {
                f'{source_root}/{candidate}'
                for source_root in _PACKAGE_SOURCE_ROOTS
                for candidate in candidates
            }
            source_matches = [
                rel for rel in self._iter_rel_files()
                if rel in source_candidates
            ]
            return source_matches[0] if len(source_matches) == 1 else None
        return self._resolve_abs_import_fallback(import_name, candidates)
    def _resolve_abs_import_fallback(self, import_name: str,
                                     candidates) -> str | None:
        exact = self._lookup_rel_exact(candidates)
        if exact is not None:
            return exact
        matches_by_candidate = [
            (cand, [
                rel for rel in self._iter_rel_files()
                if rel == cand or rel.endswith('/' + cand)
            ])
            for cand in candidates
        ]
        if any(len(matches) > 1 for _cand, matches in matches_by_candidate):
            return None
        unique_matches = [
            (cand, matches[0])
            for cand, matches in matches_by_candidate if matches
        ]
        if len(unique_matches) == 1:
            return unique_matches[0][1]
        if len(unique_matches) == 2:
            roots = {
                match[:-len(cand)].rstrip('/')
                for cand, match in unique_matches
            }
            if len(roots) > 1:
                return None
            return unique_matches[0][1]
        dotted_matches = [
            rel for rel in self._iter_rel_files()
            if (rel_to_dotted_module(rel) == import_name
                or rel_to_dotted_module(rel).endswith('.' + import_name))
        ]
        return dotted_matches[0] if len(dotted_matches) == 1 else None
    def _resolve_rel_import(self, level: int, module: str,
                            source_file: str | None) -> str | None:
        if level == 0:
            return self._resolve_abs_import(module) if module else None
        if source_file is None:
            return None
        self_key = self._self_rel_key(source_file)
        target = self._rel_import_target(level, module, source_file)
        if target is None:
            return None
        candidates = (('__init__.py',) if not target else
                      (target + '/__init__.py', target + '.py'))
        hit = self._lookup_rel_exact(candidates)
        if hit is not None and self._is_self_edge(hit, self_key):
            return None
        return hit
    def _lookup_rel_exact(self, candidates) -> str | None:
        hit = self._lookup_index_exact(candidates)
        if hit is not None:
            return hit
        for cand in candidates:
            for rel in self._iter_rel_files():
                if rel == cand:
                    return rel
        return None
    def _lookup_index_exact(self, candidates) -> str | None:
        if self._file_index is None:
            return None
        rel_index = self._file_index.get('rel_path', {})
        for cand in candidates:
            if cand in rel_index:
                return cand
        return None
    def _iter_rel_files(self):
        if self._file_index is not None:
            rel_list = self._file_index.get('rel_list')
            if rel_list is not None:
                yield from rel_list
                return
        for f in self.all_files:
            rel = _rel_path(self.project_root, f)
            if rel is None:
                continue
            yield rel
    def _self_rel_key(self, source_file: str) -> str | None:
        if os.path.isabs(source_file):
            self_rel = _rel_path(self.project_root, source_file)
            return None if self_rel is None else os.path.normcase(self_rel)
        return os.path.normcase(source_file.replace('\\', '/'))
    def _rel_import_target(self, level: int, module: str,
                           source_file: str) -> str | None:
        src_rel = self._source_dir_rel(source_file, level)
        if src_rel is None:
            return None
        tail = module.replace('.', '/')
        if not tail:
            return src_rel
        return f'{src_rel}/{tail}' if src_rel else tail
    def _source_dir_rel(self, source_file: str, level: int) -> str | None:
        source_dir = os.path.dirname(source_file)
        for _ in range(level - 1):
            parent = os.path.dirname(source_dir)
            if parent == source_dir:
                return None
            source_dir = parent
        src_rel = self._rel_project_dir(source_dir)
        if src_rel is None:
            return None
        if not src_rel or src_rel.lower() in _PACKAGE_SOURCE_ROOTS:
            init_rel = f'{src_rel}/__init__.py' if src_rel else '__init__.py'
            if (self._lookup_rel_exact((init_rel,)) is None
                    and not os.path.isfile(
                        os.path.join(self.project_root, init_rel))):
                return None
        return src_rel
    def _rel_project_dir(self, source_dir: str) -> str | None:
        if source_dir and os.path.isabs(source_dir):
            src_rel = _rel_path(self.project_root, source_dir)
            if src_rel is None or src_rel.startswith('..'):
                return None
        else:
            src_rel = (source_dir or '').replace('\\', '/')
        if src_rel == '.':
            src_rel = ''
        while src_rel.startswith('./'):
            src_rel = src_rel[2:]
        return src_rel
    @staticmethod
    def _is_self_edge(rel: str, self_key: str | None) -> bool:
        return self_key is not None and os.path.normcase(rel) == self_key
@lru_cache(maxsize=4096)
def _is_external_module(name: str) -> bool:
    if not name:
        return False
    if name in sys.stdlib_module_names:
        return True
    try:
        return importlib.util.find_spec(name) is not None
    except (ImportError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_is_external_module:ImportError')
        return False
def resolve_import(project_root: str, import_spec, all_files: list[str],
                   source_file: str | None=None,
                   _file_index: dict | None=None) -> str | None:
    return _ImportResolver(
        project_root, all_files, _file_index).resolve(import_spec, source_file)
class ResolveMemo:
    def __init__(self, underlying) -> None:
        self._underlying = underlying
        self._cache: dict[tuple, str | None] = {}
        self._scope_refs: tuple[object, object] | None = None
        self._scope_sizes: tuple[int, int] | None = None
        self._scope_content: tuple | None = None
    def clear(self) -> None:
        self._cache.clear()
        self._scope_refs = None
        self._scope_sizes = None
        self._scope_content = None
    @staticmethod
    def _content_snapshot(all_files, _file_index) -> tuple:
        index_snapshot = None
        if isinstance(_file_index, dict):
            rel_list = _file_index.get('rel_list')
            index_snapshot = (
                None if rel_list is None else tuple(rel_list),
                tuple(_file_index.get('rel_path', {}).items()),
                tuple(_file_index.get('module_name', {}).items()),
            )
        return tuple(all_files), index_snapshot
    def _scope_changed(self, all_files, _file_index) -> bool:
        rel_count = (len(_file_index.get('rel_path', ()))
                     if isinstance(_file_index, dict) else -1)
        sizes = (len(all_files), rel_count)
        content = self._content_snapshot(all_files, _file_index)
        if (self._scope_refs is not None
                and all_files is self._scope_refs[0]
                and _file_index is self._scope_refs[1]
                and sizes == self._scope_sizes
                and content == self._scope_content):
            return False
        self._scope_refs = (all_files, _file_index)
        self._scope_sizes = sizes
        self._scope_content = content
        return True
    def resolve(self, import_spec, all_files: list[str],
                source_file: str | None=None,
                _file_index: dict | None=None) -> str | None:
        if self._scope_changed(all_files, _file_index):
            self._cache.clear()
        is_rel = (isinstance(import_spec, tuple) and bool(import_spec)
                  and import_spec[0] == 'rel')
        key = (import_spec, source_file if is_rel else None)
        try:
            hash(key)
        except TypeError as _swallow_e:
            log_swallowed(__name__, _swallow_e,
                          context='ResolveMemo.resolve:TypeError')
            return self._underlying(
                import_spec, all_files, source_file, _file_index)
        if key not in self._cache:
            self._cache[key] = self._underlying(
                import_spec, all_files, source_file, _file_index)
        return self._cache[key]
_DEFENSIVE_EXCEPTIONS = frozenset({
    "IOError", "UnicodeDecodeError", "SyntaxError", "OSError",
    "FileNotFoundError", "PermissionError", "ImportError", "ModuleNotFoundError",
    "ConnectionError", "TimeoutError",
    "TypeError", "ValueError", "AttributeError", "RuntimeError",
    "KeyError", "IndexError", "NameError", "UnboundLocalError",
})
@dataclass
class BlindspotBlock:
    block_type: str
    name: str
    start_line: int
    end_line: int
    uncovered_lines: list[int] = field(default_factory=list)
    trigger_conditions: list[str] = field(default_factory=list)
    severity: Severity = DEFAULT_SEVERITY
    is_dead_code: bool = False
    sibling_covered: bool = False
    suggested_inputs: list[str] = field(default_factory=list)
    executable_line_count: int = 0
    def _ratio_total(self) -> int:
        total = self.executable_line_count
        if total > 0:
            return total
        total = self.end_line - self.start_line + 1
        return max(0, total)
    @property
    def coverage_pct(self) -> float:
        total = self._ratio_total()
        if total <= 0:
            return 0.0
        covered = max(total - len(self.uncovered_lines), 0)
        return round(covered / total * 100, 1)
    @property
    def density(self) -> float:
        total = self._ratio_total()
        if total <= 0:
            return 0.0
        return round(min(len(self.uncovered_lines), total) / total, 3)
@dataclass
class BlindspotReport:
    filepath: str
    blocks: list[BlindspotBlock] = field(default_factory=list)
    total_uncovered_lines: int = 0
    total_executable_lines: int = 0
    dead_code_blocks: int = 0
    @property
    def coverage_pct(self) -> float:
        if self.total_executable_lines <= 0:
            return 100.0
        covered = self.total_executable_lines - self.total_uncovered_lines
        return round(covered / self.total_executable_lines * 100, 1)
    @property
    def blindspot_density(self) -> float:
        if self.total_executable_lines <= 0:
            return 0.0
        return round(self.total_uncovered_lines / self.total_executable_lines, 3)
    def to_dict(self) -> dict:
        return {
            "filepath": self.filepath,
            "coverage_pct": self.coverage_pct,
            "blindspot_density": self.blindspot_density,
            "total_executable_lines": self.total_executable_lines,
            "total_uncovered_lines": self.total_uncovered_lines,
            "dead_code_blocks": self.dead_code_blocks,
            "blocks": [
                {
                    "block_type": b.block_type,
                    "name": b.name,
                    "start_line": b.start_line,
                    "end_line": b.end_line,
                    "uncovered_lines": b.uncovered_lines,
                    "coverage_pct": b.coverage_pct,
                    "density": b.density,
                    "severity": b.severity.value,
                    "is_dead_code": b.is_dead_code,
                    "sibling_covered": b.sibling_covered,
                    "executable_line_count": b.executable_line_count,
                    "trigger_conditions": b.trigger_conditions,
                    "suggested_inputs": b.suggested_inputs,
                }
                for b in self.blocks
            ],
        }
    def get_by_severity(self, severity: Severity) -> list[BlindspotBlock]:
        return [b for b in self.blocks if b.severity == severity]
    def get_critical(self) -> list[BlindspotBlock]:
        return self.get_by_severity(Severity.CRITICAL)
    def get_dead_code(self) -> list[BlindspotBlock]:
        return [b for b in self.blocks if b.is_dead_code]
class BlindspotAnalyzer:
    def __init__(self, coverage_hook=None,
                 project_root: str = DEFAULT_PROJECT_ROOT, ctx=None) -> None:
        self._coverage_hook = coverage_hook
        self._project_root = project_root
        self._ctx = ctx
    def analyze(
        self, source_paths: list[str] | None = None, detect_dead_code: bool = True
    ) -> list[BlindspotReport]:
        if self._coverage_hook is None:
            raise ValueError("BlindspotAnalyzer 需要 coverage_hook（get_uncovered 数据源），不允许为 None")
        all_py_files = self._collect_files(source_paths)
        reports: list[BlindspotReport] = []
        for filepath in all_py_files:
            report = self._analyze_file(filepath, detect_dead_code)
            if report is not None:
                reports.append(report)
        return reports
    def _collect_files(self, paths: list[str] | None) -> list[str]:
        if paths is None:
            hook_paths = getattr(self._coverage_hook, "source_paths", None)
            if not isinstance(hook_paths, (list, tuple, set, frozenset)):
                hook_paths = getattr(self._coverage_hook, "_source_paths", None)
            if isinstance(hook_paths, (list, tuple, set, frozenset)) and hook_paths:
                paths = list(hook_paths)
        return filter_scannable_files(
            self._project_root,
            collect_py_files(self._project_root, paths, ctx=self._ctx))
    def _resolve_source_tree(
        self, filepath: str
    ) -> tuple[str, ast.Module] | None:
        loaded = load_module(filepath, self._ctx)
        if loaded is None:
            logger.debug("[盲区] blindspot_core source/AST unavailable: %s", filepath)
            return None
        return loaded
    def _uncovered_lines(self, filepath: str) -> frozenset[int] | None:
        try:
            uncovered = self._coverage_hook.get_uncovered(filepath)
        except Exception as e:
            logger.debug("blindspot_core get_uncovered 失败: %s", e)
            return None
        if not isinstance(uncovered, (set, frozenset, list, tuple, dict)):
            logger.debug(
                "blindspot_core get_uncovered 返回非集合形态 %s，跳过: %s",
                type(uncovered).__name__, filepath)
            return None
        return frozenset(
            ln for ln in uncovered
            if isinstance(ln, int) and not isinstance(ln, bool))
    def _analyze_file(
        self, filepath: str, detect_dead_code: bool
    ) -> BlindspotReport | None:
        resolved = self._resolve_source_tree(filepath)
        if resolved is None:
            return None
        source, tree = resolved
        uncovered_lines = self._uncovered_lines(filepath)
        if uncovered_lines is None:
            return None
        lines = source.split("\n")
        visitor = _EnhancedBlindspotVisitor(
            uncovered_lines, lines, detect_dead_code,
            const_dead_spans=(_collect_const_dead_spans(tree)
                              if detect_dead_code else ()),
        )
        try:
            visitor.visit(tree)
        except (RecursionError, MemoryError) as e:
            logger.debug(
                "blindspot_core AST 遍历病态深度，按单文件降级跳过: %s: %s",
                filepath, e)
            return None
        return BlindspotReport(
            filepath=filepath,
            blocks=visitor.blocks,
            total_uncovered_lines=len(uncovered_lines & visitor.executable_lines),
            total_executable_lines=visitor.total_executable,
            dead_code_blocks=sum(1 for b in visitor.blocks if b.is_dead_code),
        )
_BLOCK_TRIGGER_TEMPLATES = {
    "function": "调用 {name}() 并确保其内部路径被执行",
    "method": "实例化类并调用 {name}()",
    "branch": "构造输入使条件 '{name}' 为 True",
    "else_block": "构造输入使条件取反（进入 else 分支）",
    "loop": "提供非空可迭代对象使循环体执行",
    "loop_else": "构造使循环正常穷尽（未 break）的输入以执行 else 子句",
    "except": "触发异常 {name}（如非法输入/网络错误/文件不存在）",
    "try_body": "正常执行 try 块（无异常抛出）",
    "with": "进入 with 上下文管理器",
    "match_case": "构造匹配模式 '{name}' 的输入值",
    "comprehension": "提供非空可迭代对象使 {name} 执行",
    "lambda": "调用包含此 lambda 的高阶函数（如 map/filter/sorted）",
    "decorator": "调用被装饰的函数",
    "generator": "迭代生成器表达式",
    "try_else": "正常执行 try 块且无异常抛出（进入 else 子句）",
    "finally": "执行至 finally 子句（异常与非异常路径均应验证）",
}
def _is_empty_container_literal(node: ast.AST) -> bool:
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return False
def _literal_truthiness(test: ast.AST | None) -> bool | None:
    if isinstance(test, ast.Constant):
        return bool(test.value)
    if isinstance(test, (ast.Tuple, ast.List, ast.Set)):
        if not test.elts:
            return False
        if any(not isinstance(element, ast.Starred) for element in test.elts):
            return True
        return None
    if isinstance(test, ast.Dict):
        if not test.keys:
            return False
        if any(key is not None for key in test.keys):
            return True
        return None
    return None
def _const_falsy_dead_span(node: ast.AST) -> tuple[int, int] | None:
    test = getattr(node, "test", None)
    if _literal_truthiness(test) is not False:
        return None
    if isinstance(node, (ast.If, ast.While)):
        if node.body:
            end = node.body[-1].end_lineno or node.body[-1].lineno
        else:
            end = node.end_lineno or node.lineno
        return (node.lineno, end)
    return None
def _const_truthy_else_dead_span(node: ast.AST) -> tuple[int, int] | None:
    # ``while True ... else ...`` 的 else 子句同样不可达：循环永不因条件
    # 变假而结束；若以 break 退出则 else 被跳过。故与 ``if True`` 的 else
    # 共用同一死区判定，避免漏报整段 else 死代码。
    if (not isinstance(node, (ast.If, ast.While)) or not node.orelse
            or _literal_truthiness(node.test) is not True):
        return None
    return _stmt_span(node.orelse, node.lineno)
def _collect_const_dead_spans(tree: ast.Module) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    for node in walk_nodes(tree):
        for span in (_const_falsy_dead_span(node),
                     _const_truthy_else_dead_span(node)):
            if span is not None:
                spans.append(span)
    return spans
def _try_unparse(node: ast.AST) -> str | None:
    if not hasattr(ast, "unparse"):
        return None
    try:
        return ast.unparse(node)
    except (OSError, ValueError, TypeError, KeyError, AttributeError,
            RecursionError, MemoryError) as e:
        logger.debug("_try_unparse: ast.unparse 失败: %s", e, exc_info=True)
        return None
def _safe_unparse(node: ast.AST, fallback: str) -> str:
    result = _try_unparse(node)
    return result if result is not None else fallback
_DEAD_CODE_EXC_NAMES = frozenset({"NotImplementedError"})
_CMP_OP_TEXT: dict[type[ast.cmpop], str] = {
    ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=",
    ast.Gt: ">", ast.GtE: ">=", ast.Is: "is", ast.IsNot: "is not",
    ast.In: "in", ast.NotIn: "not in",
}
_SOFT_LOG_FUNCS = frozenset({
    "log", "warning", "error", "info", "debug",
    "_log", "_warn", "_record", "print",
})
_EMPTY_CONTAINER_CTORS = frozenset({"set", "dict", "list", "tuple"})
_DEFENSIVE_DELEGATE_RECEIVERS = frozenset({"self", "cls"})
def _is_defensive_delegate_call(func: ast.expr) -> bool:
    return (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id in _DEFENSIVE_DELEGATE_RECEIVERS
            and func.attr.startswith("_"))
def _is_empty_container_ctor(call: ast.Call) -> bool:
    return (isinstance(call.func, ast.Name)
            and call.func.id in _EMPTY_CONTAINER_CTORS
            and not call.args and not call.keywords)
@dataclass(frozen=True)
class _BlockScanScope:
    uncovered: Collection[int]
    detect_dead: bool
    const_dead_spans: Collection[tuple[int, int]] | None
    executable: Collection[int] = frozenset()
@dataclass(frozen=True)
class _BlockSemantics:
    trigger_conditions: list[str] | None = None
    suggested_inputs: list[str] | None = None
    sibling_covered: bool = False
def _nested_callable_body_spans(node: ast.AST) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    for child in walk_nodes(node):
        if child is node:
            continue
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not child.body:
                continue
            body_start = child.body[0].lineno
            last_stmt = child.body[-1]
            body_end = last_stmt.end_lineno or last_stmt.lineno
        elif isinstance(child, ast.Lambda):
            body_start = getattr(child.body, 'lineno', child.lineno)
            body_end = (getattr(child.body, 'end_lineno', None)
                        or body_start)
        else:
            continue
        body_start = max(body_start, child.lineno + 1)
        if body_start <= body_end:
            spans.append((body_start, body_end))
    return spans
def _own_scope_lines(start: int, end: int, node: ast.AST) -> list[int]:
    nested_spans = _nested_callable_body_spans(node)
    return [
        ln for ln in range(start, end + 1)
        if not any(nested_start <= ln <= nested_end
                   for nested_start, nested_end in nested_spans)
    ]
def _is_covered(scope: _BlockScanScope, start: int, end: int,
                executable_lines: Collection[int]) -> bool:
    return any(
        start <= ln <= end and ln not in scope.uncovered
        for ln in executable_lines
    )
def _stmt_span(stmts: list[ast.stmt], fallback_line: int) -> tuple[int, int]:
    if not stmts:
        return (fallback_line, fallback_line)
    last_stmt = stmts[-1]
    return (stmts[0].lineno, last_stmt.end_lineno or last_stmt.lineno)
def _dead_block_statements(node: ast.AST, start: int,
                           end: int) -> list[ast.stmt]:
    if isinstance(node, (ast.With, ast.AsyncWith, ast.ExceptHandler)):
        return node.body
    if isinstance(node, (ast.If, ast.For, ast.While)):
        return node.body if start == node.lineno else node.orelse
    if isinstance(node, _TRY_NODES):
        candidates = [node.body, node.orelse, node.finalbody]
        candidates.extend(handler.body for handler in node.handlers)
        for statements in candidates:
            if statements and _stmt_span(statements, node.lineno) == (start, end):
                return statements
        return []
    if isinstance(node, ast.Match):
        for case in node.cases:
            case_start = getattr(case.pattern, "lineno", 0) or node.lineno
            if (case_start, _stmt_span(case.body, case_start)[1]) == (start, end):
                return case.body
    return []
def _contains_dead_raise(node: ast.AST, start: int, end: int) -> bool:
    return _function_outcomes(
        _dead_block_statements(node, start, end)) == {'dead'}
def _function_outcomes(statements: list[ast.stmt]) -> set[str]:
    outcomes = {'continue'}
    for stmt in statements:
        if 'continue' not in outcomes:
            break
        terminal = outcomes - {'continue'}
        if isinstance(stmt, ast.Raise):
            current = ({'dead'}
                       if ast_name(stmt.exc) in _DEAD_CODE_EXC_NAMES
                       else {'exit'})
        elif isinstance(stmt, (ast.Return, ast.Break, ast.Continue)):
            current = {'exit'}
        elif isinstance(stmt, ast.If):
            alternate = (_function_outcomes(stmt.orelse)
                         if stmt.orelse else {'continue'})
            current = _function_outcomes(stmt.body) | alternate
        elif isinstance(stmt, _TRY_NODES):
            current = _function_outcomes([*stmt.body, *stmt.orelse])
            for handler in stmt.handlers:
                current |= _function_outcomes(handler.body)
            final = _function_outcomes(stmt.finalbody)
            if 'continue' not in final:
                current = final
            else:
                current |= final - {'continue'}
        elif isinstance(stmt, (ast.With, ast.AsyncWith)):
            current = _function_outcomes(stmt.body)
        else:
            current = {'continue'}
        outcomes = terminal | current
    return outcomes
def _span_within(span: tuple[int, int], start: int, end: int) -> bool:
    return start <= span[0] and span[1] <= end
def _contains_const_dead_span(scope: _BlockScanScope, start: int, end: int,
                             node: ast.AST) -> bool:
    candidates = (set(scope.const_dead_spans)
                  if scope.const_dead_spans is not None else None)
    for span in (_const_falsy_dead_span(node),
                 _const_truthy_else_dead_span(node)):
        if span is None or not _span_within(span, start, end):
            continue
        if candidates is None or span in candidates:
            return True
    return False
def _is_dead_code(scope: _BlockScanScope, start: int, end: int,
                  node: ast.AST) -> bool:
    if not scope.detect_dead:
        return False
    if _contains_const_dead_span(scope, start, end, node):
        return True
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return _function_outcomes(node.body) == {'dead'}
    return _contains_dead_raise(node, start, end)
def _infer_triggers(block_type: str, name: str) -> list[str]:
    template = _BLOCK_TRIGGER_TEMPLATES.get(block_type)
    if template is None:
        return []
    return [template.replace("{name}", name)]
_CONDITION_RENDER_DEPTH_LIMIT = 50
def _get_condition(test: ast.AST, _depth: int = 0) -> str:
    if _depth > _CONDITION_RENDER_DEPTH_LIMIT:
        return "condition"
    unparsed = _try_unparse(test)
    if unparsed is not None:
        return unparsed
    if isinstance(test, ast.Name):
        return test.id
    if isinstance(test, ast.Constant):
        return repr(test.value)
    if isinstance(test, ast.Compare):
        parts = [_get_condition(test.left, _depth + 1)]
        for op, comp in zip(test.ops, test.comparators, strict=False):
            parts.append(_CMP_OP_TEXT.get(type(op), "?"))
            parts.append(_get_condition(comp, _depth + 1))
        return " ".join(parts)
    return "condition"
_BLOCK_INPUT_TEMPLATES: dict[str, str] = {
    "branch": "输入使 '{cond}' 为 True 的值",
    "else_block": "输入使 '{cond}' 为 False 的值",
}
def _suggest_inputs(block_type: str, node: ast.AST) -> list[str]:
    template = _BLOCK_INPUT_TEMPLATES.get(block_type)
    if template is None or not isinstance(node, ast.If):
        return []
    return [template.replace("{cond}", _get_condition(node.test))]
def _get_exc_name(handler: ast.ExceptHandler) -> str:
    if handler.type is None:
        return "bare except"
    if isinstance(handler.type, ast.Tuple):
        names = [ast_name(elt) or "exception"
                 for elt in handler.type.elts]
        return " | ".join(names) if names else "exception"
    return ast_name(handler.type) or "exception"
def _exc_name_parts(exc_name: str) -> tuple[str, ...]:
    return tuple(
        part.strip() for part in exc_name.split(" | ") if part.strip())
def _is_defensive_exception(exc_name: str) -> bool:
    parts = _exc_name_parts(exc_name)
    return bool(parts) and all(
        part in _DEFENSIVE_EXCEPTIONS for part in parts)
def _is_soft_return_value(value: ast.expr) -> bool:
    if isinstance(value, ast.Constant):
        return True
    if _is_empty_container_literal(value):
        return True
    if isinstance(value, ast.Call):
        return (_is_empty_container_ctor(value)
                or _is_defensive_delegate_call(value.func))
    return False
def _is_soft_call_stmt(stmt: ast.Expr) -> bool:
    if not isinstance(stmt.value, ast.Call):
        return False
    func = stmt.value.func
    if isinstance(func, ast.Name):
        func_name = func.id
    elif isinstance(func, ast.Attribute):
        func_name = func.attr
    else:
        func_name = ""
    if func_name in _SOFT_LOG_FUNCS:
        return True
    return _is_defensive_delegate_call(func)
def _is_soft_stmt(stmt: ast.stmt) -> bool:
    if isinstance(stmt, (ast.Pass, ast.Continue, ast.Break)):
        return True
    if isinstance(stmt, ast.Raise):
        return stmt.exc is None
    if isinstance(stmt, ast.Return):
        return stmt.value is None or _is_soft_return_value(stmt.value)
    if isinstance(stmt, ast.Expr):
        return _is_soft_call_stmt(stmt)
    return False
def _is_soft_exception_handler(handler: ast.ExceptHandler) -> bool:
    return all(_is_soft_stmt(stmt) for stmt in handler.body)
def _except_handler_severity(exc_name: str,
                             handler: ast.ExceptHandler) -> Severity:
    if exc_name == "bare except":
        return Severity.HIGH
    if "Exception" in _exc_name_parts(exc_name):
        return (Severity.MEDIUM
                if _is_soft_exception_handler(handler)
                else Severity.HIGH)
    if _is_defensive_exception(exc_name):
        return Severity.MEDIUM
    return Severity.HIGH
def _format_pattern(pattern) -> str:
    unparsed = _try_unparse(pattern)
    if unparsed is not None:
        return unparsed
    if isinstance(pattern, ast.MatchValue) and isinstance(pattern.value, ast.Constant):
        return repr(pattern.value.value)
    if isinstance(pattern, ast.MatchSingleton):
        return str(pattern.value)
    if isinstance(pattern, ast.MatchAs) and pattern.name:
        return pattern.name
    return "pattern"
def _resolve_block_span(
    node: ast.AST, span: tuple[int, int] | None
) -> tuple[int, int] | None:
    if not hasattr(node, "lineno") or not hasattr(node, "end_lineno"):
        return None
    if span is not None:
        return span
    start = node.lineno
    return (start, node.end_lineno or start)
def _resolve_block_semantics(
    block_type: str, name: str, node: ast.AST,
    semantics: _BlockSemantics | None,
) -> tuple[list[str], list[str], bool]:
    effective = semantics or _BlockSemantics()
    triggers = (effective.trigger_conditions
                if effective.trigger_conditions is not None
                else _infer_triggers(block_type, name))
    inputs = (effective.suggested_inputs
              if effective.suggested_inputs is not None
              else _suggest_inputs(block_type, node))
    return triggers, inputs, effective.sibling_covered
def _make_block(
    scope: _BlockScanScope, block_type: str, name: str, node: ast.AST,
    severity: Severity = DEFAULT_SEVERITY,
    span: tuple[int, int] | None = None,
    *,
    semantics: _BlockSemantics | None = None,
) -> BlindspotBlock | None:
    block_span = _resolve_block_span(node, span)
    if block_span is None:
        return None
    start, end = block_span
    own_lines = _own_scope_lines(start, end, node)
    uncovered_in = [
        ln for ln in own_lines
        if ln in scope.executable and ln in scope.uncovered
    ]
    if not uncovered_in:
        return None
    executable_in_block = sum(ln in scope.executable for ln in own_lines)
    triggers, inputs, sibling_covered = _resolve_block_semantics(
        block_type, name, node, semantics)
    return BlindspotBlock(
        block_type=block_type,
        name=name,
        start_line=start,
        end_line=end,
        uncovered_lines=uncovered_in,
        executable_line_count=executable_in_block,
        severity=severity,
        is_dead_code=_is_dead_code(scope, start, end, node),
        sibling_covered=sibling_covered,
        trigger_conditions=triggers,
        suggested_inputs=inputs,
    )
class _EnhancedBlindspotVisitor(ast.NodeVisitor):
    def __init__(
        self, uncovered_lines: Collection[int], source_lines: list[str], detect_dead: bool,
        const_dead_spans: Collection[tuple[int, int]] | None = None,
    ):
        self.blocks: list[BlindspotBlock] = []
        self.executable_lines: frozenset[int] = executable_line_numbers(
            source_lines)
        self.total_executable: int = len(self.executable_lines)
        self._scope = _BlockScanScope(
            uncovered=uncovered_lines,
            detect_dead=detect_dead,
            const_dead_spans=const_dead_spans,
            executable=self.executable_lines,
        )
        self._current_class: str | None = None
    def _emit_block(
        self, block_type: str, name: str, node: ast.AST,
        severity: Severity,
        span: tuple[int, int] | None = None,
        *,
        semantics: _BlockSemantics | None = None,
    ) -> BlindspotBlock | None:
        block = _make_block(self._scope, block_type, name, node, severity,
                            span, semantics=semantics)
        if block is not None:
            self.blocks.append(block)
        return block
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        full_name = node.name
        sev = Severity.HIGH
        if self._current_class:
            full_name = f"{self._current_class}.{node.name}"
        for dec in node.decorator_list:
            if hasattr(dec, "lineno") and hasattr(dec, "end_lineno"):
                self._emit_block(
                    "decorator", f"@{_safe_unparse(dec, 'decorator')}", dec,
                    Severity.INFO)
        self._emit_block(
            "method" if self._current_class else "function", full_name, node,
            sev)
        saved_class = self._current_class
        self._current_class = None
        self.generic_visit(node)
        self._current_class = saved_class
    visit_AsyncFunctionDef = visit_FunctionDef
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        with class_scope(self, node):
            self.generic_visit(node)
    def visit_If(self, node: ast.If) -> None:
        cond_text = _get_condition(node.test)
        if_covered = self._visit_if_branch(node, cond_text)
        self._visit_if_else(node, cond_text, if_covered)
        self.generic_visit(node)
    def _visit_if_branch(self, node: ast.If, cond_text: str) -> bool:
        if_body_start, if_body_end = _stmt_span(node.body, node.lineno)
        if_covered = _is_covered(
            self._scope, if_body_start, if_body_end,
            {stmt.lineno for stmt in node.body})
        self._emit_block(
            "branch", f"if {cond_text}", node, Severity.MEDIUM,
            span=(node.lineno, if_body_end))
        return if_covered
    def _visit_if_else(self, node: ast.If, cond_text: str,
                       if_covered: bool) -> None:
        if not node.orelse or (
                len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If)):
            return
        self._emit_clause_block(
            node, "else_block", f"else (not {cond_text})", node.orelse, if_covered,
            trigger_conditions=[f"构造输入使 '{cond_text}' 为 False"],
            suggested_inputs=[f"输入使 '{cond_text}' 为 False 的值"])
    def _emit_clause_block(
        self, node: ast.AST, block_type: str, name: str,
        stmts: list[ast.stmt], sibling_covered: bool,
        *,
        trigger_conditions: list[str] | None = None,
        suggested_inputs: list[str] | None = None,
    ) -> None:
        start, end = _stmt_span(stmts, node.lineno)
        severity = Severity.HIGH if sibling_covered else Severity.MEDIUM
        self._emit_block(
            block_type, name, node, severity, span=(start, end),
            semantics=_BlockSemantics(
                trigger_conditions=trigger_conditions,
                suggested_inputs=suggested_inputs,
                sibling_covered=sibling_covered,
            ))
    def _make_loop_else_block(self, node: ast.AST, name: str) -> None:
        if not node.orelse:
            return
        b_start, b_end = _stmt_span(node.body, node.lineno)
        self._emit_clause_block(
            node, "loop_else", name, node.orelse,
            _is_covered(self._scope, b_start, b_end,
                        {stmt.lineno for stmt in node.body}))
    def visit_For(self, node: ast.For) -> None:
        target_text = _safe_unparse(node.target, "_")
        iter_text = _safe_unparse(node.iter, "iterable")
        _, body_end = _stmt_span(node.body, node.lineno)
        self._emit_block(
            "loop", f"for {target_text} in {iter_text}", node, Severity.MEDIUM,
            span=(node.lineno, body_end))
        self._make_loop_else_block(node, "for...else")
        self.generic_visit(node)
    visit_AsyncFor = visit_For
    def visit_While(self, node: ast.While) -> None:
        cond_text = _get_condition(node.test)
        _, body_end = _stmt_span(node.body, node.lineno)
        self._emit_block(
            "loop", f"while {cond_text}", node, Severity.MEDIUM,
            span=(node.lineno, body_end))
        self._make_loop_else_block(node, "while...else")
        self.generic_visit(node)
    def _visit_try_handlers(self, node: ast.Try) -> None:
        for handler in node.handlers:
            exc_name = _get_exc_name(handler)
            h_start = handler.lineno
            h_end = handler.end_lineno or h_start
            severity = _except_handler_severity(exc_name, handler)
            self._emit_block(
                "except", exc_name, handler, severity,
                span=(h_start, h_end),
                semantics=_BlockSemantics(
                    trigger_conditions=[
                        f"触发异常 {exc_name}",
                        f"建议: 构造非法输入、模拟网络错误、或 mock 依赖抛出 {exc_name}",
                    ],
                    suggested_inputs=[
                        f"mock 依赖使其 raise {exc_name}()",
                        "传入越界/非法参数",
                    ],
                ))
    def _visit_try_tail(self, node: ast.Try, try_start: int,
                        try_end: int) -> None:
        try_body_covered = _is_covered(
            self._scope, try_start, try_end,
            {stmt.lineno for stmt in node.body})
        if node.orelse:
            self._emit_clause_block(
                node, "try_else", "try...else", node.orelse, try_body_covered)
        if node.finalbody:
            self._emit_clause_block(
                node, "finally", "finally", node.finalbody, try_body_covered)
    def visit_Try(self, node: ast.Try) -> None:
        try_start, try_end = _stmt_span(node.body, node.lineno)
        self._emit_block(
            "try_body", "try block", node, Severity.HIGH,
            span=(try_start, try_end))
        self._visit_try_handlers(node)
        self._visit_try_tail(node, try_start, try_end)
        self.generic_visit(node)
    visit_TryStar = visit_Try
    def visit_With(self, node: ast.With) -> None:
        contexts = [
            text for text in (
                _safe_unparse(item.context_expr, "") for item in node.items)
            if text
        ]
        ctx_name = f"with {', '.join(contexts)}" if contexts else "with block"
        self._emit_block("with", ctx_name, node, Severity.INFO)
        self.generic_visit(node)
    visit_AsyncWith = visit_With
    def _visit_comprehension(self, node: ast.AST, comp_type: str):
        block = self._emit_block("comprehension", comp_type, node, Severity.LOW)
        if block is not None:
            block.trigger_conditions.append(
                "构造使可迭代对象至少产生一个元素"
                "（存在 if 子句时同时满足过滤条件）的输入")
        self.generic_visit(node)
    _COMPREHENSION_LABELS: ClassVar[dict[type, str]] = {
        ast.ListComp: "list comprehension",
        ast.SetComp: "set comprehension",
        ast.DictComp: "dict comprehension",
        ast.GeneratorExp: "generator expression",
    }
    def visit(self, node: ast.AST):
        label = self._COMPREHENSION_LABELS.get(type(node))
        if label is None:
            return super().visit(node)
        self._visit_comprehension(node, label)
        return None
    def visit_Lambda(self, node: ast.Lambda) -> None:
        self._emit_block("lambda", "lambda expression", node, Severity.LOW)
        self.generic_visit(node)
    def visit_Match(self, node: ast.Match) -> None:
        subject = _safe_unparse(node.subject, "subject")
        for case in node.cases:
            case_pattern = _format_pattern(case.pattern)
            c_start = getattr(case.pattern, "lineno", 0) or node.lineno
            c_end = _stmt_span(case.body, c_start)[1]
            self._emit_block(
                "match_case", f"case {case_pattern}", node, Severity.MEDIUM,
                span=(c_start, c_end),
                semantics=_BlockSemantics(
                    trigger_conditions=[
                        f"构造输入使 match {subject} 匹配模式 '{case_pattern}'"
                    ],
                    suggested_inputs=[f"提供匹配模式 '{case_pattern}' 的值"],
                ))
        self.generic_visit(node)
    def visit_Yield(self, node: ast.Yield) -> None:
        self._emit_block(
            "generator", "yield statement", node, Severity.LOW,
            span=(node.lineno, node.lineno),
            semantics=_BlockSemantics(
                trigger_conditions=["迭代生成器以触发此 yield"],
                suggested_inputs=["调用 next() 或 for 循环迭代生成器"],
            ))
        self.generic_visit(node)
    def visit_YieldFrom(self, node: ast.YieldFrom) -> None:
        target = _safe_unparse(node.value, "subgenerator")
        self._emit_block(
            "generator", f"yield from {target}", node, Severity.LOW,
            span=(node.lineno, node.lineno),
            semantics=_BlockSemantics(
                trigger_conditions=[f"迭代生成器以委托到 {target}"],
            ))
        self.generic_visit(node)

from __future__ import annotations

import ast
import importlib.util
import json
import logging
import os
import re
from collections import Counter, defaultdict
from collections.abc import Callable, Collection, Iterator
from dataclasses import dataclass, field
from functools import partial
from itertools import combinations, product
from typing import Any

from jwsgj.arch_coexistence_scan import (
    DEPRECATED_DOC_RE,
    SECONDS_PER_DAY,
    ArchCoexistenceItem,
    ArchCoexistenceReport,
    ArchScanContext,
    FuncInfo,
    ModuleInfo,
    _active_module_import_aliases,
    _declared_global_names,
    _declared_nonlocal_names,
    _local_binding_events,
    _local_binding_state_at,
    _node_position,
    _own_scope_bound_names,
    detect_dual_impl_a1,
    extract_name_stem,
    iter_module_scope_stmts,
    iter_own_scope,
    iter_skill_files,
    overlap_ratio_of,
    version_name_pairs,
)
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    call_tail_name,
    dotted_name,
    is_docstring_stmt,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import is_transient_module_name

__all__ = [
    'ARCH_STRATEGIES',
    'ConfigFileInfo',
    'ParadigmSpec',
    'build_paradigm_item',
    'collect_family_items',
    'detect_adapter_wall_a10',
    'detect_arch_shift_a5',
    'detect_bypass_a3',
    'detect_class_split_a7',
    'detect_config_coexistence_a14',
    'detect_datamodel_split_a11',
    'detect_decorator_conflict_a6',
    'detect_error_handling_conflict_a8',
    'detect_import_style_conflict_a13',
    'detect_logging_conflict_a9',
    'detect_state_conflict_a4',
    'detect_sync_async_mix_a2',
    'detect_type_annotation_conflict_a12',
    'family_conf',
    'family_stem',
    'iter_module_functions',
    'module_stems',
    'run_arch_strategies',
    'scan_config_files',
    'section_name_of',
    'side_symbols',
    'spans_files',
]
_log = logging.getLogger(__name__)
def detect_class_split_a7(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    name_to_classes = _collect_class_method_index(ctx)
    items = _detect_a7_same_name_split(name_to_classes, min_conf)
    items.extend(_detect_a7_version_suffix_split(name_to_classes, min_conf))
    return items
def _collect_class_method_index(ctx: ArchScanContext) -> dict[str, dict[str, list[FuncInfo]]]:
    name_to_classes: dict[str, dict[str, list[FuncInfo]]] = defaultdict(lambda: defaultdict(list))
    for mod_info in ctx.modules.values():
        for class_name, methods in mod_info.iter_class_groups():
            if class_name.startswith("_"):
                continue
            for fi in methods:
                name_to_classes[class_name][fi.file_path].append(fi)
    return name_to_classes
def _detect_a7_same_name_split(name_to_classes: dict[str, dict[str, list[FuncInfo]]],
                               min_conf: float) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for cls_name, file_groups in name_to_classes.items():
        files = list(file_groups.keys())
        if len(files) < 2:
            continue
        for f_a, f_b in combinations(files, 2):
            item = _a7_same_name_pair_item(
                cls_name, (f_a, f_b),
                (file_groups[f_a], file_groups[f_b]), min_conf)
            if item is not None:
                items.append(item)
    return items
@dataclass(frozen=True)
class _A7PairGate:
    overlap: set[str]
    overlap_ratio: float
    hash_diffs: int
    time_gap: float
    conf: float
def _a7_pair_gate(methods_a: list[FuncInfo], methods_b: list[FuncInfo], *,
                  min_conf: float, overlap_floor: float, base: float,
                  bonus: float) -> _A7PairGate | None:
    names_a = {fi.name for fi in methods_a}
    names_b = {fi.name for fi in methods_b}
    overlap_ratio = overlap_ratio_of(names_a, names_b)
    if overlap_ratio < overlap_floor:
        return None
    hash_diffs, time_gap = _class_compare_detail(methods_a, methods_b)
    conf = _a7_confidence(base, bonus, time_gap, hash_diffs)
    if conf < min_conf:
        return None
    return _A7PairGate(overlap=names_a & names_b, overlap_ratio=overlap_ratio,
                       hash_diffs=hash_diffs, time_gap=time_gap, conf=conf)
def _a7_same_name_pair_item(cls_name: str, files: tuple[str, str],
                            method_groups: tuple[list[FuncInfo], list[FuncInfo]],
                            min_conf: float) -> ArchCoexistenceItem | None:
    f_a, f_b = files
    methods_a, methods_b = method_groups
    gate = _a7_pair_gate(methods_a, methods_b, min_conf=min_conf,
                         overlap_floor=0.5, base=0.78, bonus=0.07)
    if gate is None:
        return None
    old_f, new_f = _judge_old_file(f_a, f_b, methods_a, methods_b)
    return _build_a7_split_item(_A7SplitSpec(
        summary=f"类分裂: 同名类 '{cls_name}' 在两个文件中存在，"
                f"方法重叠 {gate.overlap_ratio:.0%}，{gate.hash_diffs} 个方法实现不同",
        old_f=old_f, new_f=new_f,
        old_prefix=cls_name, new_prefix=cls_name,
        overlap=gate.overlap, conf=gate.conf, time_gap=gate.time_gap,
        old_desc=f"旧: {old_f}", new_desc=f"新: {new_f}",
        suggestion="确认两个类是否为新旧版本，合并后移除旧版类",
    ))
def _a7_confidence(base: float, time_gap_bonus: float, time_gap: float,
                   hash_diffs: int) -> float:
    conf = base
    if time_gap > 3 * SECONDS_PER_DAY:
        conf += time_gap_bonus
    if hash_diffs >= 2:
        conf += 0.05
    return conf
def _detect_a7_version_suffix_split(name_to_classes: dict[str, dict[str, list[FuncInfo]]],
                                    min_conf: float) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for (old_cls, new_cls) in version_name_pairs(name_to_classes).values():
        old_file_groups = name_to_classes[old_cls]
        new_file_groups = name_to_classes[new_cls]
        for (old_f, old_methods), (new_f, new_methods) in product(
                old_file_groups.items(), new_file_groups.items()):
            item = _a7_version_pair_item(
                (old_cls, new_cls), (old_f, new_f),
                (old_methods, new_methods), min_conf)
            if item is not None:
                items.append(item)
    return items
def _a7_version_pair_item(cls_pair: tuple[str, str], file_pair: tuple[str, str],
                          method_groups: tuple[list[FuncInfo], list[FuncInfo]],
                          min_conf: float) -> ArchCoexistenceItem | None:
    old_cls, new_cls = cls_pair
    old_f, new_f = file_pair
    old_methods, new_methods = method_groups
    if old_f == new_f:
        return None
    gate = _a7_pair_gate(old_methods, new_methods, min_conf=min_conf,
                         overlap_floor=0.4, base=0.80, bonus=0.05)
    if gate is None:
        return None
    return _build_a7_split_item(_A7SplitSpec(
        summary=f"类继承体系分裂: '{old_cls}' vs '{new_cls}'，"
                f"方法重叠 {gate.overlap_ratio:.0%}，{gate.hash_diffs} 个方法实现不同",
        old_f=old_f, new_f=new_f,
        old_prefix=old_cls, new_prefix=new_cls,
        overlap=gate.overlap, conf=gate.conf, time_gap=gate.time_gap,
        old_desc=f"旧类: {old_cls} in {old_f}",
        new_desc=f"新类: {new_cls} in {new_f}",
        suggestion=f"将 '{old_cls}' 的独有方法迁移到 '{new_cls}'，然后移除 '{old_cls}'",
    ))
@dataclass(frozen=True)
class _A7SplitSpec:
    summary: str
    old_f: str
    new_f: str
    old_prefix: str
    new_prefix: str
    overlap: set
    conf: float
    time_gap: float
    old_desc: str
    new_desc: str
    suggestion: str
def _build_a7_split_item(spec: _A7SplitSpec) -> ArchCoexistenceItem:
    conf = round(spec.conf, 2)
    return ArchCoexistenceItem(
        strategy="A7",
        summary=spec.summary,
        old_files=[spec.old_f],
        new_files=[spec.new_f],
        old_symbols=[f"{spec.old_prefix}.{m}" for m in sorted(spec.overlap)[:5]],
        new_symbols=[f"{spec.new_prefix}.{m}" for m in sorted(spec.overlap)[:5]],
        confidence=conf,
        evidence=[spec.old_desc, spec.new_desc,
                  f"共享方法: {sorted(spec.overlap)[:10]}"]
                 + ([f"mtime 差距: {spec.time_gap/SECONDS_PER_DAY:.1f} 天"]
                    if spec.time_gap > SECONDS_PER_DAY else []),
        suggestion=spec.suggestion,
        severity="high" if conf >= 0.85 else "warning",
    )
def _class_compare_detail(methods_a: list[FuncInfo], methods_b: list[FuncInfo]) -> tuple[int, float]:
    mtimes_a = {fi.mtime for fi in methods_a if fi.mtime > 0}
    mtimes_b = {fi.mtime for fi in methods_b if fi.mtime > 0}
    return (_count_body_hash_diffs(methods_a, methods_b),
            _activity_window_gap(mtimes_a, mtimes_b))
def _count_body_hash_diffs(methods_a: list[FuncInfo],
                           methods_b: list[FuncInfo]) -> int:
    return len({
        fi_a.name
        for fi_a in methods_a
        for fi_b in methods_b
        if (fi_a.name == fi_b.name
                and fi_a.body_hash and fi_b.body_hash
                and fi_a.body_hash != fi_b.body_hash)
    })
def _activity_window_gap(mtimes_a: set[float], mtimes_b: set[float]) -> float:
    if not mtimes_a or not mtimes_b:
        return 0.0
    return max(0.0,
               max(min(mtimes_a), min(mtimes_b))
               - min(max(mtimes_a), max(mtimes_b)))
def _judge_old_file(f_a: str, f_b: str, methods_a: list[FuncInfo], methods_b: list[FuncInfo]) -> tuple[str, str]:
    mtimes_a = [fi.mtime for fi in methods_a if fi.mtime > 0]
    mtimes_b = [fi.mtime for fi in methods_b if fi.mtime > 0]
    if _mtimes_separable(mtimes_a, mtimes_b):
        return (f_a, f_b) if min(mtimes_a) < min(mtimes_b) else (f_b, f_a)
    return (f_a, f_b) if f_a <= f_b else (f_b, f_a)
def _mtimes_separable(mtimes_a: list[float], mtimes_b: list[float]) -> bool:
    if not mtimes_a or not mtimes_b:
        return False
    return max(mtimes_a) < min(mtimes_b) or max(mtimes_b) < min(mtimes_a)
@dataclass(frozen=True)
class _DatamodelClassInfo:
    file: str
    is_dataclass: bool
    fields: set[str]
    mtime: float = 0.0
@dataclass(frozen=True)
class _DatamodelPair:
    old_name: str
    new_name: str
    old: _DatamodelClassInfo
    new: _DatamodelClassInfo
_ClassCandidates = dict[str, list[ast.ClassDef]]
def _collect_datamodel_class_info(
        ctx: ArchScanContext) -> dict[str, list[_DatamodelClassInfo]]:
    all_classes: dict[str, list[_DatamodelClassInfo]] = defaultdict(list)
    for mod_info in sorted(ctx.modules.values(), key=lambda m: m.file_path):
        candidates = _class_index_of_tree(_module_ast(ctx, mod_info))
        for storage_key, methods in mod_info.classes.items():
            cls_name = mod_info.class_names.get(storage_key, storage_key)
            if cls_name.startswith("_"):
                continue
            position = mod_info.class_positions.get(storage_key)
            anchor_lineno = (position[0] if position is not None
                             else methods[0].lineno if methods else None)
            is_dataclass, field_names = _class_datamodel_info(
                candidates, cls_name, methods, mod_info.import_aliases,
                anchor_lineno=anchor_lineno)
            all_classes[cls_name].append(_DatamodelClassInfo(
                file=mod_info.file_path,
                is_dataclass=is_dataclass,
                fields=field_names,
                mtime=mod_info.mtime,
            ))
    return dict(all_classes)
def _module_ast(ctx: ArchScanContext, mod_info: ModuleInfo) -> ast.AST | None:
    tree = ctx.file_tree_cache.get(mod_info.file_path)
    if tree is not None:
        return tree
    for class_funcs in mod_info.classes.values():
        if class_funcs:
            return ctx.get_node(class_funcs[0])
    return None
def _class_index_of_tree(tree: ast.AST | None) -> _ClassCandidates:
    index: _ClassCandidates = defaultdict(list)
    if tree is None:
        return index
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            index[node.name].append(node)
    return index
def _class_datamodel_info(
        candidates: _ClassCandidates, cls_name: str, methods: list[FuncInfo],
        import_aliases: dict[str, str],
        anchor_lineno: int | None = None) -> tuple[bool, set[str]]:
    try:
        anchor = (anchor_lineno if anchor_lineno is not None
                  else methods[0].lineno if methods else None)
        return _extract_class_fields(
            candidates, cls_name, anchor, import_aliases)
    except (OSError, SyntaxError, ValueError, RecursionError) as e:
        _log.warning("[ArchCoex] 收集dataclass信息失败,降级 %s: %s",
                     cls_name, e)
        return False, set()
def _extract_class_fields(
        tree: ast.AST | _ClassCandidates | None, cls_name: str,
        anchor_lineno: int | None = None,
        import_aliases: dict[str, str] | None = None) -> tuple[bool, set[str]]:
    candidates = (_class_index_of_tree(tree) if not isinstance(tree, dict)
                  else tree).get(cls_name, ())
    if not candidates:
        return False, set()
    chosen = min(candidates, key=lambda n: n.lineno)
    if anchor_lineno is not None:
        enclosing = [
            node for node in candidates
            if node.lineno <= anchor_lineno <= (node.end_lineno or node.lineno)
        ]
        if enclosing:
            chosen = max(enclosing, key=lambda n: n.lineno)
    return (_has_dataclass_decorator(chosen, import_aliases),
            _collect_class_field_names(chosen))
def _datamodel_pair_confidence(
        pair: _DatamodelPair) -> tuple[float, set[str], float] | None:
    old_is_dc = pair.old.is_dataclass
    new_is_dc = pair.new.is_dataclass
    if old_is_dc == new_is_dc:
        return None
    overlap = pair.old.fields & pair.new.fields
    overlap_ratio = overlap_ratio_of(pair.old.fields, pair.new.fields)
    if overlap_ratio < 0.4:
        return None
    conf = 0.74
    if new_is_dc and not old_is_dc:
        conf = 0.80
    if overlap_ratio >= 0.6:
        conf += 0.05
    return conf, overlap, overlap_ratio
def _build_datamodel_split_item(pair: _DatamodelPair,
                                min_conf: float) -> ArchCoexistenceItem | None:
    judged = _datamodel_pair_confidence(pair)
    if judged is None:
        return None
    conf, overlap, overlap_ratio = judged
    if conf < min_conf:
        return None
    old_name, new_name = pair.old_name, pair.new_name
    old_info, new_info = pair.old, pair.new
    old_is_dc = old_info.is_dataclass
    new_is_dc = new_info.is_dataclass
    dc_label = "dataclass" if new_is_dc else "普通类"
    old_label = "dataclass" if old_is_dc else "普通类"
    return ArchCoexistenceItem(
        strategy="A11",
        summary=f"数据模型分裂: '{old_name}'({old_label}) vs '{new_name}'({dc_label})，"
                f"字段重叠 {overlap_ratio:.0%}",
        old_files=[old_info.file],
        new_files=[new_info.file],
        old_symbols=[f"{old_name}.{f}" for f in sorted(overlap)[:5]],
        new_symbols=[f"{new_name}.{f}" for f in sorted(overlap)[:5]],
        confidence=round(conf, 2),
        evidence=[
            f"旧版: {old_name} ({old_label}) in {os.path.basename(old_info.file)}",
            f"新版: {new_name} ({dc_label}) in {os.path.basename(new_info.file)}",
            f"共享字段: {sorted(overlap)[:10]}",
        ],
        suggestion=f"确认 '{old_name}' 和 '{new_name}' 是否为新旧版本，迁移所有使用者到新版后移除旧版",
        severity="warning" if round(conf, 2) >= 0.80 else "info",
    )
def _order_same_name_datamodels(
        left: _DatamodelClassInfo, right: _DatamodelClassInfo,
) -> tuple[_DatamodelClassInfo, _DatamodelClassInfo]:
    if (left.mtime > 0 and right.mtime > 0
            and left.mtime != right.mtime):
        return (left, right) if left.mtime < right.mtime else (right, left)
    return (left, right) if left.file <= right.file else (right, left)
def _detect_a11_same_name_split(
        all_classes: dict[str, list[_DatamodelClassInfo]], min_conf: float,
) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for class_name, class_infos in all_classes.items():
        for left, right in combinations(class_infos, 2):
            if left.file == right.file:
                continue
            old_info, new_info = _order_same_name_datamodels(left, right)
            item = _build_datamodel_split_item(_DatamodelPair(
                old_name=class_name, new_name=class_name,
                old=old_info, new=new_info), min_conf)
            if item is not None:
                items.append(item)
    return items
def _detect_a11_version_name_split(
        all_classes: dict[str, list[_DatamodelClassInfo]], min_conf: float,
) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for old_name, new_name in version_name_pairs(all_classes).values():
        for old_info, new_info in product(
                all_classes[old_name], all_classes[new_name]):
            if old_info.file == new_info.file:
                continue
            item = _build_datamodel_split_item(_DatamodelPair(
                old_name=old_name, new_name=new_name,
                old=old_info, new=new_info), min_conf)
            if item is not None:
                items.append(item)
    return items
def detect_datamodel_split_a11(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    all_classes = _collect_datamodel_class_info(ctx)
    items = _detect_a11_same_name_split(all_classes, min_conf)
    items.extend(_detect_a11_version_name_split(all_classes, min_conf))
    return items
def _is_dataclass_decorator_target(
        target: ast.expr, import_aliases: dict[str, str] | None = None) -> bool:
    dotted = dotted_name(target)
    if not dotted:
        return False
    root, _, rest = dotted.partition('.')
    resolved_root = (import_aliases or {}).get(root, root)
    resolved = f"{resolved_root}.{rest}" if rest else resolved_root
    return resolved in {"dataclass", "dataclasses.dataclass"}
def _has_dataclass_decorator(
        class_node: ast.ClassDef,
        import_aliases: dict[str, str] | None = None) -> bool:
    return any(
        _is_dataclass_decorator_target(
            dec.func if isinstance(dec, ast.Call) else dec, import_aliases)
        for dec in class_node.decorator_list)
def _is_public_receiver_attr(target: ast.expr, receiver: str) -> bool:
    return (bool(receiver)
            and isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id == receiver
            and not target.attr.startswith("_"))
def _init_receiver_name(init_node) -> str:
    positional = (*init_node.args.posonlyargs, *init_node.args.args)
    return positional[0].arg if positional else ""
def _iter_target_leaves(targets) -> Iterator[ast.expr]:
    for target in targets:
        if isinstance(target, (ast.Tuple, ast.List)):
            yield from _iter_target_leaves(target.elts)
        elif isinstance(target, ast.Starred):
            yield from _iter_target_leaves((target.value,))
        else:
            yield target
def _collect_init_field_names(init_node) -> set[str]:
    names: set[str] = set()
    receiver = _init_receiver_name(init_node)
    for stmt in iter_own_scope(init_node):
        if isinstance(stmt, ast.Assign):
            for target in _iter_target_leaves(stmt.targets):
                if _is_public_receiver_attr(target, receiver):
                    names.add(target.attr)
        elif (isinstance(stmt, ast.AnnAssign)
              and _is_public_receiver_attr(stmt.target, receiver)):
            names.add(stmt.target.attr)
    return names
def _collect_public_name_targets(targets) -> set:
    return {target.id for target in _iter_target_leaves(targets)
            if isinstance(target, ast.Name) and not target.id.startswith("_")}
def _collect_class_field_names(class_node: ast.ClassDef) -> set[str]:
    field_names: set[str] = set()
    for item in iter_module_scope_stmts(class_node.body):
        if (isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name)
                and not item.target.id.startswith("_")):
            field_names.add(item.target.id)
        elif isinstance(item, ast.Assign):
            field_names |= _collect_public_name_targets(item.targets)
        elif (isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
              and item.name == "__init__"):
            field_names |= _collect_init_field_names(item)
    return field_names
_UTILITY_NAMES = frozenset({
    'get', 'set', 'add', 'run', 'build', 'make', 'load', 'save',
    'read', 'write', 'open', 'close', 'parse', 'format', 'log',
    'init', 'setup', 'reset', 'clear', 'update', 'check', 'scan',
    'detect', 'find', 'fix', 'create', 'delete', 'remove', 'append',
    'extend', 'insert', 'pop', 'keys', 'values', 'items',
})
_RE_A3_ORCHESTRATOR_KW = re.compile(
    r'(pipeline|orchestrat|dispatch|router|route|coordinator|workflow|'
    r'编排|调度|路由|分发|管道|流水线)',
    re.IGNORECASE
)
def detect_bypass_a3(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    orchestrators = _a3_find_orchestrators(ctx)
    if not orchestrators:
        return []
    callee_callers = _a3_callee_callers(ctx)
    orch_qnames = {o.qualified_name for o in orchestrators}
    items: list[ArchCoexistenceItem] = []
    for orch in orchestrators:
        items.extend(_a3_detect_bypass_for(
            orch, ctx, orch_qnames, callee_callers, min_conf))
    return items
def _a3_is_utility(qname: str) -> bool:
    return qname.rsplit('.', 1)[-1].split('@', 1)[0] in _UTILITY_NAMES
def _a3_find_orchestrators(ctx: ArchScanContext) -> list[FuncInfo]:
    return [fi for fi in ctx.all_functions.values()
            if _RE_A3_ORCHESTRATOR_KW.search(fi.name)]
def _a3_callee_callers(ctx: ArchScanContext) -> dict[str, set[str]]:
    callee_callers: dict[str, set[str]] = defaultdict(set)
    for qname in ctx.all_functions:
        for callee in ctx.call_graph.get(qname, set()):
            callee_callers[callee].add(qname)
    return callee_callers
def _a3_reachable_downstream(ctx: ArchScanContext,
                             orch: FuncInfo) -> set[str]:
    reachable: set[str] = set()
    pending = list(ctx.call_graph.get(orch.qualified_name, set()))
    while pending:
        qname = pending.pop()
        if qname in reachable:
            continue
        reachable.add(qname)
        pending.extend(ctx.call_graph.get(qname, set()) - reachable)
    return reachable
def _a3_detect_bypass_for(orch: FuncInfo, ctx: ArchScanContext,
                          orch_qnames: set[str],
                          callee_callers: dict[str, set[str]],
                          min_conf: float) -> list[ArchCoexistenceItem]:
    direct_downstream = set(ctx.call_graph.get(orch.qualified_name, set()))
    business_downstream = {q for q in direct_downstream if not _a3_is_utility(q)}
    if len(business_downstream) < 2:
        return []
    shared_callees = {q for q in business_downstream
                      if len(callee_callers.get(q, ())) >= 2}
    if not shared_callees:
        return []
    overlap_by_caller = _a3_collect_overlap(
        orch, orch_qnames, shared_callees, callee_callers,
        _a3_reachable_downstream(ctx, orch))
    return _a3_items_from_overlap(orch, ctx, overlap_by_caller, min_conf)
def _a3_collect_overlap(orch: FuncInfo, orch_qnames: set[str],
                        shared_callees: set[str],
                        callee_callers: dict[str, set[str]],
                        downstream: set[str]) -> dict[str, set[str]]:
    overlap_by_caller: dict[str, set[str]] = defaultdict(set)
    for callee in shared_callees:
        for caller in callee_callers.get(callee, ()):
            if (caller == orch.qualified_name or caller in orch_qnames
                    or caller in downstream):
                continue
            overlap_by_caller[caller].add(callee)
    return overlap_by_caller
def _a3_items_from_overlap(orch: FuncInfo, ctx: ArchScanContext,
                           overlap_by_caller: dict[str, set[str]],
                           min_conf: float) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for qname in sorted(overlap_by_caller):
        overlap = overlap_by_caller[qname]
        fi = ctx.all_functions.get(qname)
        if len(overlap) < 2 or fi is None or fi.file_path == orch.file_path:
            continue
        bypass_is_older, confidence = _a3_bypass_confidence(fi, orch)
        if confidence < min_conf:
            continue
        items.append(_a3_make_item(orch, _A3BypassSpec(
            qname=qname, fi=fi, overlap=overlap,
            bypass_is_older=bypass_is_older, confidence=confidence)))
    return items
def _a3_bypass_confidence(fi: FuncInfo, orch: FuncInfo) -> tuple[bool, float]:
    bypass_is_older = (fi.mtime > 0 and orch.mtime > 0
                       and fi.mtime < orch.mtime - SECONDS_PER_DAY)
    return bypass_is_older, (0.90 if bypass_is_older else 0.75)
@dataclass(frozen=True)
class _A3BypassSpec:
    qname: str
    fi: FuncInfo
    overlap: set[str]
    bypass_is_older: bool
    confidence: float
def _a3_make_item(orch: FuncInfo, spec: _A3BypassSpec) -> ArchCoexistenceItem:
    fi = spec.fi
    return ArchCoexistenceItem(
        strategy="A3",
        summary=f"旁路绕过编排入口: {fi.qualified_name} 直接调用了 "
                f"{len(spec.overlap)} 个业务核心函数，绕过 {orch.qualified_name}",
        old_files=[fi.file_path],
        new_files=[orch.file_path],
        old_symbols=[fi.name],
        new_symbols=[orch.name],
        confidence=spec.confidence,
        evidence=[
            f"编排入口: {orch.qualified_name}",
            f"旁路调用: {spec.qname}",
            f"共享业务下游: {sorted(spec.overlap)[:5]}",
        ] + (["旁路代码 mtime 更早"] if spec.bypass_is_older else []),
        suggestion="评估旁路是否为旧版直接调用，考虑统一走编排入口",
        severity="high" if spec.bypass_is_older else "warning",
    )
def _a10_delegate_target(call: ast.Call,
                         import_targets: dict[str, str]) -> str | None:
    func = call.func
    if isinstance(func, ast.Name):
        return import_targets.get(func.id)
    if isinstance(func, ast.Attribute):
        chain = dotted_name(func)
        if not chain:
            return None
        base, _, rest = chain.partition('.')
        target = import_targets.get(base)
        if target is None:
            return None
        return f"{target}.{rest}" if rest else target
    return None
def _a10_assign_targets(stmt: ast.stmt) -> list[ast.expr]:
    if isinstance(stmt, ast.Assign):
        return list(stmt.targets)
    if isinstance(stmt, ast.AnnAssign):
        return [stmt.target] if stmt.value is not None else []
    if isinstance(stmt, ast.AugAssign):
        return [stmt.target]
    return []
def _a10_target_rewrites_param(target: ast.expr, params: set[str]) -> bool:
    while isinstance(target, (ast.Attribute, ast.Subscript, ast.Starred)):
        target = target.value
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_a10_target_rewrites_param(elt, params)
                   for elt in target.elts)
    return isinstance(target, ast.Name) and target.id in params
def _a10_body_signature(
    body: list[ast.stmt], params: list[str]
) -> tuple[dict[str, str], bool, list[str]]:
    import_targets: dict[str, str] = {}
    has_param_transform = False
    delegate_calls: list[str] = []
    param_names = set(params)
    for stmt in body:
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            _collect_local_import_targets(stmt, import_targets)
            continue
        if (isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign))
                and not has_param_transform and any(
                    _a10_target_rewrites_param(target, param_names)
                    for target in _a10_assign_targets(stmt))):
            has_param_transform = True
        target = _a10_delegate_statement_target(stmt, import_targets)
        if target is not None and target not in delegate_calls:
            delegate_calls.append(target)
    return import_targets, has_param_transform, delegate_calls
def _collect_local_import_targets(stmt: ast.stmt, out: dict[str, str]) -> None:
    if isinstance(stmt, ast.ImportFrom):
        module = '.' * stmt.level + (stmt.module or '')
        separator = '' if module.endswith('.') else '.'
        for alias in stmt.names:
            local = alias.asname or alias.name
            out[local] = (
                f"{module}{separator}{alias.name}" if module else alias.name)
        return
    for alias in stmt.names:
        local = alias.asname or alias.name.split('.')[0]
        out[local] = alias.name if alias.asname else local
def _a10_delegate_statement_target(
    stmt: ast.stmt, import_targets: dict[str, str],
) -> str | None:
    if not isinstance(stmt, (ast.Return, ast.Expr, ast.Assign, ast.AnnAssign)):
        return None
    value = stmt.value
    if value is None:
        return None
    while isinstance(value, ast.Await):
        value = value.value
    if not isinstance(value, ast.Call):
        return None
    return _a10_delegate_target(value, import_targets)
def _a10_confidence(has_param_transform: bool, stmt_count: int,
                    import_count: int) -> float:
    conf = 0.72
    if has_param_transform:
        conf = 0.78
    if stmt_count <= 3:
        conf = min(conf + 0.06, 0.85)
    if import_count >= 2:
        conf = min(conf + 0.04, 0.85)
    return conf
def detect_adapter_wall_a10(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    items = []
    for fi in ctx.all_functions.values():
        try:
            item = _a10_analyze_function(fi, min_conf)
        except Exception as _e:  # noqa: BLE001
            _log.warning(
                "arch_coexistence_pairs:detect_adapter_wall_a10: %s: %s: %s",
                fi.qualified_name, type(_e).__name__, _e, exc_info=True)
            continue
        if item is not None:
            items.append(item)
    return items
def _a10_effective_body(func_node: ast.FunctionDef) -> list[ast.stmt] | None:
    body = func_node.body
    if body and is_docstring_stmt(body[0]):
        body = body[1:]
    return body if 2 <= len(body) <= 6 else None
def _a10_analyze_function(fi: FuncInfo, min_conf: float) -> ArchCoexistenceItem | None:
    if fi.complexity > 2 or not fi.is_public or fi.ast_node is None:
        return None
    body = _a10_effective_body(fi.ast_node)
    if body is None:
        return None
    stmt_count = len(body)
    import_targets, has_param_transform, delegate_calls = (
        _a10_body_signature(body, fi.params))
    if not delegate_calls:
        return None
    conf = _a10_confidence(has_param_transform, stmt_count,
                           len(import_targets))
    if conf < min_conf:
        return None
    return ArchCoexistenceItem(
        strategy="A10",
        summary=f"API适配器墙: '{fi.name}' 为薄包装函数，通过局部import委托调用 {delegate_calls}",
        old_files=[fi.file_path],
        new_files=[fi.file_path],
        old_symbols=[fi.name],
        new_symbols=delegate_calls,
        confidence=conf,
        evidence=[
            f"函数体仅 {stmt_count} 个语句，复杂度 {fi.complexity}",
            f"局部导入: {sorted(import_targets.values())}",
            f"委托调用: {delegate_calls[0]}(...)",
        ],
        suggestion=f"评估是否可以直接移除适配器 '{fi.name}'，让调用方直接使用目标函数",
        severity="info",
    )
ITEM_FILE_LIMIT = 3
_ITEM_SYMBOL_LIMIT = 5
_FAMILY_MIN_FUNCS = 4
@dataclass(frozen=True)
class ParadigmSpec:
    strategy: str
    summary: str
    old_funcs: list[FuncInfo]
    new_funcs: list[FuncInfo]
    evidence: tuple[str, str]
    conf: float
    is_cross: bool
    suggestion: str
    severity: str
    cross_evidence: str = ""
    extra_evidence: tuple[str, ...] = ()
def build_paradigm_item(spec: ParadigmSpec) -> ArchCoexistenceItem:
    evidence = [*spec.evidence]
    if spec.is_cross and spec.cross_evidence:
        evidence.append(spec.cross_evidence)
    evidence.extend(spec.extra_evidence)
    return ArchCoexistenceItem(
        strategy=spec.strategy,
        summary=spec.summary + (" [跨模块]" if spec.is_cross else ""),
        old_files=_side_files(spec.old_funcs),
        new_files=_side_files(spec.new_funcs),
        old_symbols=side_symbols(spec.old_funcs),
        new_symbols=side_symbols(spec.new_funcs),
        confidence=spec.conf,
        evidence=evidence,
        suggestion=spec.suggestion,
        severity=spec.severity,
    )
def collect_family_items(
        ctx: ArchScanContext,
        judge: Callable[..., ArchCoexistenceItem | None],
        *judge_args: object,
        min_funcs: int = _FAMILY_MIN_FUNCS,
) -> list[ArchCoexistenceItem]:
    all_funcs = iter_module_functions(ctx)
    items: list[ArchCoexistenceItem] = []
    if len(all_funcs) < min_funcs:
        return items
    for stem, group in _group_funcs_by_stem(all_funcs).items():
        item = judge(stem, group, *judge_args)
        if item is not None:
            items.append(item)
    return items
def _side_files(side: list[FuncInfo]) -> list[str]:
    files: list[str] = []
    for fi in side:
        if fi.file_path not in files:
            files.append(fi.file_path)
        if len(files) >= ITEM_FILE_LIMIT:
            break
    return files
def _sorted_files(side: list[FuncInfo]) -> list[str]:
    return sorted({fi.file_path for fi in side})
def _basenames(files: list[str]) -> list[str]:
    return [os.path.basename(f) for f in files[:ITEM_FILE_LIMIT]]
def side_symbols(side: list[FuncInfo]) -> list[str]:
    return [fi.name for fi in side[:_ITEM_SYMBOL_LIMIT]]
def _decorated_symbols(side: list[FuncInfo]) -> list[str]:
    return [f"{fi.name}({', '.join(fi.decorators)})"
            for fi in side[:_ITEM_SYMBOL_LIMIT]]
def iter_module_functions(ctx: ArchScanContext) -> list[FuncInfo]:
    funcs: list[FuncInfo] = []
    for mod_info in ctx.modules.values():
        funcs.extend(mod_info.functions.values())
    return funcs
_FAMILY_VARIANT_SUFFIX_RE = re.compile(r'_(?:[ab]|\d{1,2})$', re.IGNORECASE)
def family_stem(name: str) -> str:
    stem = extract_name_stem(name).lower()
    while True:
        stripped = _FAMILY_VARIANT_SUFFIX_RE.sub(
            '', extract_name_stem(stem).lower())
        if stripped == stem:
            return stem
        stem = stripped
def _group_funcs_by_stem(funcs: list[FuncInfo]) -> dict[str, list[FuncInfo]]:
    groups: dict[str, list[FuncInfo]] = defaultdict(list)
    for fi in funcs:
        groups[family_stem(fi.name)].append(fi)
    return groups
def module_stems(funcs: list[FuncInfo]) -> list[str]:
    return sorted({
        os.path.splitext(os.path.basename(fi.file_path))[0]
        for fi in funcs
    })
def spans_files(funcs: list[FuncInfo]) -> bool:
    return len({fi.file_path for fi in funcs}) > 1
_CROSS_BOOST = 0.06
_FAMILY_SIDE_BONUS = 0.06
_FAMILY_CONF_CAP = 0.85
def _cross_conf(base: float, is_cross: bool, boost: float) -> float:
    return base + boost if is_cross else base
def family_conf(base: float, is_cross: bool,
                 left: list[FuncInfo], right: list[FuncInfo], *,
                 boost: float = _CROSS_BOOST,
                 side_bonus: float = _FAMILY_SIDE_BONUS,
                 cap: float = _FAMILY_CONF_CAP) -> float:
    conf = _cross_conf(base, is_cross, boost)
    if len(left) >= 2 and len(right) >= 2:
        conf += side_bonus
    return min(conf, cap)
_A2_BASE_CONF = 0.75
def detect_sync_async_mix_a2(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    items = []
    for mod_name, mod_info in ctx.modules.items():
        if not (mod_info.has_async and mod_info.has_sync):
            continue
        item = _detect_a2_module(mod_name, mod_info, min_conf)
        if item is not None:
            items.append(item)
    return items
def _count_a2_stem_pairs(sync_funcs: dict[str, FuncInfo],
                         async_funcs: dict[str, FuncInfo]) -> int:
    async_stems = Counter(
        family_stem(fi.name) for fi in async_funcs.values())
    return sum(async_stems.get(family_stem(fi.name), 0)
               for fi in sync_funcs.values())
def _accessed_globals_of(funcs: dict[str, FuncInfo]) -> set[str]:
    return set().union(*(fi.accessed_globals for fi in funcs.values()))
def _a2_summary(mod_name: str, n_async: int, n_sync: int,
                pairs_found: int, shared_globals: set[str]) -> str:
    parts = [f"sync/async范式混用: {mod_name} 中 {n_async} async + {n_sync} sync 函数"]
    if pairs_found:
        parts.append(f"{pairs_found} 对同名函数")
    if shared_globals:
        parts.append(f"共享 {len(shared_globals)} 个全局变量")
    return "，".join(parts)
def _partition_a2_functions(mod_info: ModuleInfo
                           ) -> tuple[dict[str, FuncInfo], dict[str, FuncInfo], set[str]]:
    async_funcs = {n: fi for n, fi in mod_info.functions.items() if fi.is_async}
    sync_funcs = {n: fi for n, fi in mod_info.functions.items() if not fi.is_async}
    shared_globals = (_accessed_globals_of(async_funcs)
                      & _accessed_globals_of(sync_funcs)
                      & mod_info.global_vars)
    return async_funcs, sync_funcs, shared_globals
def _detect_a2_module(mod_name: str, mod_info: ModuleInfo,
                      min_conf: float) -> ArchCoexistenceItem | None:
    async_funcs, sync_funcs, shared_globals = _partition_a2_functions(mod_info)
    pairs_found = _count_a2_stem_pairs(sync_funcs, async_funcs)
    if pairs_found < 2 and len(shared_globals) < 2:
        return None
    if min_conf > _A2_BASE_CONF:
        return None
    return ArchCoexistenceItem(
        strategy="A2",
        summary=_a2_summary(mod_name, len(async_funcs), len(sync_funcs),
                            pairs_found, shared_globals),
        old_files=[mod_info.file_path],
        new_files=[],
        old_symbols=[fi.name for fi in sync_funcs.values()],
        new_symbols=[fi.name for fi in async_funcs.values()],
        confidence=_A2_BASE_CONF,
        evidence=[
            f"async 函数: {[fi.name for fi in async_funcs.values()][:10]}",
            f"sync 函数: {[fi.name for fi in sync_funcs.values()][:10]}",
        ] + ([f"共享全局变量: {sorted(shared_globals)[:10]}"] if shared_globals else []),
        suggestion="评估 sync/async 并存是否为过渡期残留，考虑统一异步模式或明确分层",
        severity="warning",
    )
_A4_STATE_PARAM_PREFIXES = ('state', 'ctx', 'context', 'config')
_A4_PARAM_WORD_CHARS = '_0123456789'
def _is_state_param_name(name: str) -> bool:
    lowered = name.lower()
    return any(
        lowered == prefix
        or (lowered.startswith(prefix)
            and lowered[len(prefix)] in _A4_PARAM_WORD_CHARS)
        for prefix in _A4_STATE_PARAM_PREFIXES
    )
def detect_state_conflict_a4(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    items = []
    for mod_name, mod_info in ctx.modules.items():
        if not mod_info.global_vars:
            continue
        item = _detect_a4_module(mod_name, mod_info, min_conf)
        if item is not None:
            items.append(item)
    return items
def _detect_a4_module(mod_name: str, mod_info: ModuleInfo,
                      min_conf: float) -> ArchCoexistenceItem | None:
    global_state_funcs, param_state_funcs = _partition_a4_functions(mod_info)
    overlap = global_state_funcs & param_state_funcs
    if len(overlap) < 2:
        return None
    fname = os.path.basename(mod_info.file_path)
    has_version_hint = bool(re.search(
        r'(?:^|[_\-.])(?:old|new|legacy|v\d+)(?:[_\-.]|$)',
        fname, re.IGNORECASE))
    conf = 0.80 if has_version_hint else 0.65
    if conf < min_conf:
        return None
    return ArchCoexistenceItem(
        strategy="A4",
        summary=f"状态管理模式冲突: {mod_name} 中 {len(overlap)} 个函数同时使用全局状态和参数传递",
        old_files=[mod_info.file_path],
        new_files=[],
        old_symbols=sorted(global_state_funcs),
        new_symbols=sorted(param_state_funcs),
        confidence=conf,
        evidence=[
            f"全局变量: {sorted(mod_info.global_vars)[:10]}",
            f"混合函数: {sorted(overlap)[:10]}",
        ] + (["文件名含版本标记"] if has_version_hint else []),
        suggestion="统一状态管理方式：选择全局状态或显式传递，避免混用增加维护难度",
        severity="warning",
    )
def _partition_a4_functions(mod_info: ModuleInfo) -> tuple[set[str], set[str]]:
    global_state_funcs: set[str] = set()
    param_state_funcs: set[str] = set()
    for fi in mod_info.functions.values():
        if fi.accessed_globals & mod_info.global_vars:
            global_state_funcs.add(fi.name)
        if any(_is_state_param_name(p) for p in fi.params):
            param_state_funcs.add(fi.name)
    return global_state_funcs, param_state_funcs
_GUARD_DECO_KW = re.compile(
    r'(guard|validate|verify|check_|auth|safe|sandbox|sanitize|'
    r'lock|rate_limit|retry|cache|log_|audit|require|enforce)',
    re.IGNORECASE
)
_REGISTER_DECO_KW = re.compile(
    r'(register|handler|route|hook|subscribe|listen|middleware)',
    re.IGNORECASE
)
def detect_decorator_conflict_a6(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    return collect_family_items(ctx, _detect_a6_stem_group, min_conf)
def _detect_a6_stem_group(stem: str, group: list[FuncInfo],
                          min_conf: float) -> ArchCoexistenceItem | None:
    guarded, unguarded = _partition_a6_group(group)
    if not guarded or not unguarded:
        return None
    is_cross_module = spans_files(guarded + unguarded)
    has_deprecated = _a6_has_deprecated_marker(unguarded)
    conf = _a6_confidence(guarded, unguarded, is_cross_module, has_deprecated)
    if conf < min_conf:
        return None
    return build_paradigm_item(ParadigmSpec(
        strategy="A6",
        summary=f"装饰器范式冲突: '{stem}' 函数族"
                f"（{', '.join(module_stems(group)[:ITEM_FILE_LIMIT])}）"
                f" {len(guarded)} 个带装饰器、{len(unguarded)} 个无装饰器",
        old_funcs=unguarded,
        new_funcs=guarded,
        evidence=(
            f"带装饰器: {_decorated_symbols(guarded)}",
            f"无装饰器: {side_symbols(unguarded)}",
        ),
        conf=conf,
        is_cross=is_cross_module,
        cross_evidence="跨模块冲突: 函数族分散在多个文件中",
        extra_evidence=("无装饰器函数含废弃标记",) if has_deprecated else (),
        suggestion="评估是否应为所有同类函数统一添加/移除装饰器，保持一致的防护级别",
        severity="warning" if not is_cross_module else "high",
    ))
def _partition_a6_group(group: list[FuncInfo]) -> tuple[list[FuncInfo], list[FuncInfo]]:
    guarded: list[FuncInfo] = []
    unguarded: list[FuncInfo] = []
    for fi in group:
        has_guard = any(
            _GUARD_DECO_KW.search(d) or _REGISTER_DECO_KW.search(d)
            for d in fi.decorators
        )
        if has_guard:
            guarded.append(fi)
        elif not fi.decorators:
            unguarded.append(fi)
    return guarded, unguarded
def _a6_has_deprecated_marker(unguarded: list[FuncInfo]) -> bool:
    return any(
        fi.docstring and DEPRECATED_DOC_RE.search(fi.docstring)
        for fi in unguarded
    )
def _a6_confidence(guarded: list[FuncInfo], unguarded: list[FuncInfo],
                   is_cross: bool, has_deprecated: bool) -> float:
    conf = family_conf(0.72, is_cross, guarded, unguarded)
    if has_deprecated:
        conf = min(conf + 0.10, 0.92)
    return conf
def detect_type_annotation_conflict_a12(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    return collect_family_items(ctx, _detect_a12_stem_group, min_conf)
def _a12_has_param_annotation(fi: FuncInfo) -> bool:
    args = getattr(fi.ast_node, "args", None)
    if args is None:
        return False
    params = [*args.posonlyargs, *args.args, *args.kwonlyargs]
    params.extend(p for p in (args.vararg, args.kwarg) if p is not None)
    return any(p.annotation is not None for p in params)
def _a12_is_typed(fi: FuncInfo) -> bool:
    return fi.return_annotation is not None or _a12_has_param_annotation(fi)
def _partition_a12_group(group: list[FuncInfo]) -> tuple[list[FuncInfo], list[FuncInfo]]:
    typed: list[FuncInfo] = []
    untyped: list[FuncInfo] = []
    for fi in group:
        if _a12_is_typed(fi):
            typed.append(fi)
        else:
            untyped.append(fi)
    return typed, untyped
def _detect_a12_stem_group(stem: str, group: list[FuncInfo],
                           min_conf: float) -> ArchCoexistenceItem | None:
    typed, untyped = _partition_a12_group(group)
    if not typed or not untyped:
        return None
    if not _a12_params_similar(typed, untyped):
        return None
    is_cross = spans_files(group)
    conf = family_conf(0.65, is_cross, typed, untyped,
                        boost=0.08, side_bonus=0.05, cap=0.82)
    if conf < min_conf:
        return None
    return build_paradigm_item(ParadigmSpec(
        strategy="A12",
        summary=f"类型注解范式冲突: '{stem}' 函数族 {len(typed)} 个有类型注解、"
                f"{len(untyped)} 个无类型注解",
        old_funcs=untyped,
        new_funcs=typed,
        evidence=(
            f"有注解: {side_symbols(typed)}",
            f"无注解: {side_symbols(untyped)}",
        ),
        conf=conf,
        is_cross=is_cross,
        cross_evidence=f"跨模块: {', '.join(module_stems(group)[:ITEM_FILE_LIMIT])}",
        suggestion="为无注解函数添加类型注解，保持代码库的类型安全一致性",
        severity="info",
    ))
def _a12_params_similar(typed: list[FuncInfo], untyped: list[FuncInfo]) -> bool:
    return any(
        _a12_param_pair_similar(fi_t, fi_u)
        for fi_t in typed for fi_u in untyped
    )
def _a12_param_pair_similar(fi_t: FuncInfo, fi_u: FuncInfo) -> bool:
    p_t, p_u = set(fi_t.params), set(fi_u.params)
    if not p_t and not p_u:
        return True
    if not (p_t and p_u):
        return False
    return len(p_t & p_u) / max(len(p_t | p_u), 1) >= 0.5
_A13_CONFIDENCE = 0.68
def detect_import_style_conflict_a13(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    file_import_style: dict[str, str] = {
        mod_info.file_path: _classify_import_style(mod_info)
        for mod_info in ctx.modules.values()
    }
    if len(file_import_style) < 2:
        return []
    return collect_family_items(
        ctx, _detect_a13_stem_group, file_import_style, min_conf, min_funcs=2)
def _detect_a13_stem_group(stem: str, group: list[FuncInfo],
                           file_import_style: dict[str, str],
                           min_conf: float) -> ArchCoexistenceItem | None:
    if len(group) < 2 or min_conf > _A13_CONFIDENCE:
        return None
    rel_funcs, abs_funcs = _partition_a13_group(group, file_import_style)
    if not rel_funcs or not abs_funcs:
        return None
    rel_files = _sorted_files(rel_funcs)
    abs_files = _sorted_files(abs_funcs)
    return ArchCoexistenceItem(
        strategy="A13",
        summary=f"导入路径范式冲突: '{stem}' 函数族跨 {len(rel_files)} 个相对导入模块"
                f"和 {len(abs_files)} 个绝对导入模块",
        old_files=rel_files[:ITEM_FILE_LIMIT],
        new_files=abs_files[:ITEM_FILE_LIMIT],
        old_symbols=side_symbols(rel_funcs),
        new_symbols=side_symbols(abs_funcs),
        confidence=_A13_CONFIDENCE,
        evidence=[
            f"相对导入模块: {_basenames(rel_files)}",
            f"绝对导入模块: {_basenames(abs_files)}",
        ],
        suggestion="统一使用绝对导入路径，提升代码可维护性和IDE支持",
        severity="info",
    )
def _classify_import_style(mod_info: ModuleInfo) -> str:
    abs_count = mod_info.abs_import_count
    if mod_info.rel_import_count > abs_count:
        return "relative"
    if abs_count > mod_info.rel_import_count:
        return "absolute"
    return ""
def _partition_a13_group(group: list[FuncInfo],
                         file_import_style: dict[str, str]
                         ) -> tuple[list[FuncInfo], list[FuncInfo]]:
    rel_funcs: list[FuncInfo] = []
    abs_funcs: list[FuncInfo] = []
    for fi in group:
        style = file_import_style.get(fi.file_path, "")
        if style == "relative":
            rel_funcs.append(fi)
        elif style == "absolute":
            abs_funcs.append(fi)
    return rel_funcs, abs_funcs
_CONFIG_EXTENSIONS = {
    ".json": "json",
    ".yml": "yaml",
    ".yaml": "yaml",
    ".toml": "toml",
    ".ini": "ini",
    ".cfg": "ini",
    ".conf": "ini",
}
@dataclass
class ConfigFileInfo:
    file_path: str
    format: str
    keys: set[str] = field(default_factory=set)
    sections: set[str] = field(default_factory=set)
    mtime: float = 0.0
    raw_content: str = ""
def _read_config_text(fpath: str) -> str:
    with open(fpath, encoding='utf-8-sig', errors='replace') as f:
        return f.read()
def _extract_json_keys(content: str) -> set[str]:
    try:
        data = json.loads(content)
    except (json.JSONDecodeError, ValueError) as e:
        _log.warning("arch_coexistence_pairs:_extract_json_keys: "
                     "JSON parse failed: %s", e)
        raise ValueError(f"JSON 解析失败: {e}") from e
    return _json_top_keys(data)
def _json_top_keys(data: Any) -> set[str]:
    if isinstance(data, dict):
        return set(data.keys())
    if isinstance(data, list):
        keys: set[str] = set()
        for item in data:
            if isinstance(item, dict):
                keys |= set(item.keys())
        return keys
    return set()
def _extract_yaml_keys(content: str) -> set[str]:
    keys: set[str] = set()
    for line in content.splitlines():
        stripped = _strip_inline_comment(line.strip(), ('#',))
        if not stripped:
            continue
        if not line[0].isspace() and stripped.startswith('- '):
            stripped = stripped[2:].lstrip()
            if stripped.startswith('- '):
                continue
        if not line[0].isspace():
            sep = _first_unquoted_separator(stripped, ':')
            if sep > 0:
                key = _normalize_config_key(stripped[:sep])
                if key:
                    keys.add(key)
    return keys
def _first_unquoted_separator(text: str, separators: str, *,
                              require_boundary: bool = False) -> int:
    quote = ''
    escaped = False
    for i, ch in enumerate(text):
        if quote:
            if escaped:
                escaped = False
            elif quote == '"' and ch == '\\':
                escaped = True
            elif ch == quote:
                quote = ''
        elif ch in ('"', "'"):
            quote = ch
        elif (ch in separators
              and (not require_boundary or i == 0
                   or text[i - 1].isspace())):
            return i
    return -1
def _strip_inline_comment(line: str, markers: tuple[str, ...], *,
                          require_boundary: bool = True) -> str:
    marker_at = _first_unquoted_separator(
        line, ''.join(markers), require_boundary=require_boundary)
    return line[:marker_at].rstrip() if marker_at >= 0 else line
def _normalize_config_key(key: str) -> str:
    key = key.strip()
    if len(key) >= 2 and key[0] == key[-1] and key[0] in ('"', "'"):
        return key[1:-1]
    return key
def section_name_of(stripped: str) -> str | None:
    stripped = _strip_inline_comment(stripped.strip(), ('#', ';')).strip()
    if not stripped.startswith('['):
        return None
    inner = stripped[1:].removeprefix('[')
    close = inner.find(']')
    if close < 0:
        return None
    return _normalize_config_key(inner[:close].strip()) or None
def _config_key_of_line(stripped: str, ini_style: bool,
                        current_section: str) -> str | None:
    separators = '=:' if ini_style else '='
    eq = _first_unquoted_separator(stripped, separators)
    if eq < 0 or (not ini_style and stripped.startswith('[')):
        return None
    key = _normalize_config_key(stripped[:eq])
    if not key:
        return None
    return f"{current_section}.{key}" if current_section else key
def _extract_config_keys(content: str, ini_style: bool = False) -> tuple[set[str], set[str]]:
    keys: set[str] = set()
    sections: set[str] = set()
    current_section = ""
    comment_starts = ('#', ';') if ini_style else ('#',)
    for line in content.splitlines():
        stripped = _strip_inline_comment(
            line.strip(), comment_starts, require_boundary=ini_style)
        if not stripped:
            continue
        section = section_name_of(stripped)
        if section is not None:
            current_section = section
            sections.add(section)
            continue
        key = _config_key_of_line(stripped, ini_style, current_section)
        if key is not None:
            keys.add(key)
    return keys, sections
_FORMAT_KEY_EXTRACTORS = {
    "json": lambda content: (_extract_json_keys(content), set()),
    "yaml": lambda content: (_extract_yaml_keys(content), set()),
    "toml": _extract_config_keys,
    "ini": partial(_extract_config_keys, ini_style=True),
}
def _parse_config_file(fpath: str) -> ConfigFileInfo:
    content = _read_config_text(fpath)
    fmt = _CONFIG_EXTENSIONS[os.path.splitext(fpath)[1].lower()]
    extractor = _FORMAT_KEY_EXTRACTORS.get(fmt)
    keys, sections = extractor(content) if extractor else (set(), set())
    return ConfigFileInfo(file_path=fpath, format=fmt, keys=keys,
                          sections=sections, mtime=os.path.getmtime(fpath),
                          raw_content=content)
def scan_config_files(skill_dir: str,
                      report: ArchCoexistenceReport | None = None
                      ) -> list[ConfigFileInfo]:
    config_files: list[ConfigFileInfo] = []
    for fname, fpath, rel in iter_skill_files(skill_dir):
        if os.path.splitext(fname)[1].lower() not in _CONFIG_EXTENSIONS:
            continue
        if is_transient_module_name(fname):
            continue
        try:
            config_files.append(_parse_config_file(fpath))
        except Exception as e:  # noqa: BLE001
            _log.warning("scan_config_files: parse_skipped %s: %s: %s",
                         rel, type(e).__name__, e, exc_info=True)
            if report is not None:
                report.errors.append(
                    f"解析配置 {rel} 失败: {type(e).__name__}: {e}")
    return config_files
_A14_FORMAT_CONF = 0.78
_A14_DUP_KEY_CONF = 0.72
_A14_STALE_REF_CONF = 0.68
_STALE_EXEMPT_LITERALS = frozenset({
    'true', 'false', 'none', 'null', 'yes', 'no', 'on', 'off',
    'enabled', 'disabled',
})
_CONFIG_KEY_PATTERN = re.compile(
    r'^(?:module|class|function|handler|service|plugin|command|entry|'
    r'component|provider|adapter|factory|middleware|backend|driver|'
    r'import|target|callback|hook|ref)(?:$|[_-])',
    re.IGNORECASE
)
_SYMBOL_REF_FILE_EXTS = frozenset({
    'py', 'pyi', 'json', 'yaml', 'yml', 'toml', 'ini', 'cfg', 'conf',
    'md', 'txt', 'rst', 'sh', 'bash', 'ps1', 'bat', 'cmd', 'exe', 'dll',
    'so', 'js', 'ts', 'tsx', 'jsx', 'html', 'htm', 'css', 'xml', 'csv',
    'log', 'db', 'sqlite', 'pem', 'key', 'crt', 'cer', 'env',
})
_SYMBOL_REF_TLDS = frozenset({
    'com', 'org', 'net', 'io', 'cn', 'dev', 'local', 'internal', 'ai',
    'co', 'me', 'info', 'biz', 'edu', 'gov', 'cloud', 'app', 'site',
    'online', 'tech',
})
_A14_NON_SYMBOL_KEY_SUFFIXES = (
    '_path', '_file', '_filename', '_dir', '_directory', '_url', '_uri',
    '_endpoint', '_host', '_hostname', '_port', '_address', '_addr',
    '_command', '_cmd', '_script', '_template', '_pattern', '_regex',
    '_glob',
)
def detect_config_coexistence_a14(ctx: ArchScanContext, min_conf: float,
                                  config_files: list[ConfigFileInfo]
                                  ) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    if len(config_files) >= 2:
        items.extend(_detect_config_format_coexistence(config_files, min_conf))
        items.extend(_detect_config_key_duplication(config_files, min_conf))
    items.extend(_detect_config_stale_references(ctx, config_files, min_conf))
    return items
def _detect_config_format_coexistence(config_files: list[ConfigFileInfo],
                                      min_conf: float) -> list[ArchCoexistenceItem]:
    if min_conf > _A14_FORMAT_CONF:
        return []
    groups = _a14_format_file_groups(config_files)
    if groups is None:
        return []
    old_files, new_files = groups
    return [ArchCoexistenceItem(
        strategy="A14",
        summary=f"配置格式共存: 旧格式(ini/cfg/conf) {len(old_files)} 个文件 "
                f"与新格式(toml/json) {len(new_files)} 个文件并存",
        old_files=old_files[:5],
        new_files=new_files[:5],
        old_symbols=[],
        new_symbols=[],
        confidence=_A14_FORMAT_CONF,
        evidence=[
            f"旧格式文件: {[os.path.basename(f) for f in old_files[:5]]}",
            f"新格式文件: {[os.path.basename(f) for f in new_files[:5]]}",
        ],
        suggestion="统一配置格式，迁移旧 ini/cfg/conf 配置到 toml/json，移除旧格式文件",
        severity="warning",
    )]
def _a14_format_file_groups(config_files: list[ConfigFileInfo]
                           ) -> tuple[list[str], list[str]] | None:
    old_files = [cf.file_path for cf in config_files if cf.format == "ini"]
    new_files = [cf.file_path for cf in config_files
                 if cf.format in {"toml", "json"}]
    if not old_files or not new_files:
        return None
    return old_files, new_files
def _detect_config_key_duplication(config_files: list[ConfigFileInfo],
                                   min_conf: float) -> list[ArchCoexistenceItem]:
    if min_conf > _A14_DUP_KEY_CONF:
        return []
    cross_format_dupes = _a14_cross_format_dupes(config_files)
    if not cross_format_dupes:
        return []
    return [ArchCoexistenceItem(
        strategy="A14",
        summary=f"配置键跨格式重复: {len(cross_format_dupes)} 个键在多个配置文件中重复定义",
        old_files=sorted({f for files in cross_format_dupes.values() for f in files})[:5],
        new_files=[],
        old_symbols=sorted(cross_format_dupes)[:10],
        new_symbols=[],
        confidence=_A14_DUP_KEY_CONF,
        evidence=_a14_dup_evidence(cross_format_dupes),
        suggestion="合并重复配置键，确保每个配置项只在一个文件中定义，通过导入/引用机制共享",
        severity="warning",
    )]
def _a14_keys_compatible(left: str, right: str) -> bool:
    return left == right or '.' not in left or '.' not in right
def _a14_key_entries(config_files: list[ConfigFileInfo]) -> dict[str, list[tuple[str, str, str]]]:
    entries: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    for cf in config_files:
        for key in cf.keys:
            entries[_short_key_of(key)].append((key, cf.file_path, cf.format))
    return entries
def _a14_cross_format_dupes(config_files: list[ConfigFileInfo]) -> dict[str, list[str]]:
    duplicates: dict[str, list[str]] = {}
    format_by_file = {cf.file_path: cf.format for cf in config_files}
    for short_key, entries in _a14_key_entries(config_files).items():
        matched_files: set[str] = set()
        for index, left in enumerate(entries):
            for right in entries[index + 1:]:
                left_key, left_file, left_format = left
                right_key, right_file, right_format = right
                if (left_file == right_file or left_format == right_format
                        or not _a14_keys_compatible(left_key, right_key)):
                    continue
                matched_files.update((left_file, right_file))
        if matched_files:
            duplicates[short_key] = sorted(
                matched_files,
                key=lambda path: (format_by_file[path] != "ini", path))
    return duplicates
def _short_key_of(key: str) -> str:
    return key.rsplit('.', 1)[-1]
def _a14_dup_evidence(cross_format_dupes: dict[str, list[str]]) -> list[str]:
    return [
        f"键 '{key}' 在 {len(set(files))} 个文件中定义: "
        f"{[os.path.basename(f) for f in sorted(set(files))[:3]]}"
        for key, files in sorted(cross_format_dupes.items())[:5]
    ]
def _is_config_comment_line(line: str) -> bool:
    s = line.lstrip()
    return s.startswith(('#', ';'))
def _locate_config_value_lines(
        raw_content: str, key: str, short_key: str) -> list[tuple[str, int]]:
    all_lines = [ln for ln in raw_content.splitlines()
                if not _is_config_comment_line(ln)]
    located = _match_full_key_lines(all_lines, key)
    if not located and '.' in key:
        located = _match_section_leaf_lines(all_lines, key)
    if not located:
        located = _match_short_key_lines(all_lines, short_key)
    return located
def _match_full_key_lines(all_lines: list[str], key: str) -> list[tuple[str, int]]:
    bare_re = re.compile(rf'^\s*(?P<key>{re.escape(key)})\s*[=:]')
    quoted_re = re.compile(
        rf'(?:^\s*|[\{{,}}]\s*)["\'](?P<key>{re.escape(key)})["\']\s*[=:]')
    located: list[tuple[str, int]] = []
    for ln in all_lines:
        bare = bare_re.match(ln)
        if bare is not None:
            located.append((ln, bare.end('key')))
            continue
        located.extend((ln, match.end('key'))
                       for match in quoted_re.finditer(ln))
    return located
def _match_section_leaf_lines(
        all_lines: list[str], key: str) -> list[tuple[str, int]]:
    key_section, leaf_key = key.rsplit('.', 1)
    leaf_re = re.compile(
        rf'^\s*["\']?{re.escape(leaf_key)}["\']?\s*[=:]')
    current_section = ''
    located: list[tuple[str, int]] = []
    for ln in all_lines:
        header = section_name_of(ln.strip())
        if header is not None:
            current_section = header
            continue
        if current_section == key_section and leaf_re.match(ln):
            located.append((ln, 0))
    return located
def _match_short_key_lines(
        all_lines: list[str], short_key: str) -> list[tuple[str, int]]:
    short_key_re = re.compile(
        rf'(?:^|[^.\w]){re.escape(short_key)}["\']?\s*[=:]')
    return [(ln, match.start()) for ln in all_lines
            for match in short_key_re.finditer(ln)]
def _truncate_unquoted_comment(value_part: str, *,
                               require_boundary: bool = True) -> str:
    marker_at = _first_unquoted_separator(
        value_part, '#;', require_boundary=require_boundary)
    return value_part[:marker_at].rstrip() if marker_at >= 0 else value_part
def _clean_config_value(hit_line: str, key_start: int = 0, *,
                        comment_requires_boundary: bool = True) -> str:
    sep_positions = [p for p in (hit_line.find('=', key_start),
                                hit_line.find(':', key_start))
                     if p >= 0]
    value_part = (hit_line[min(sep_positions) + 1:] if sep_positions
                  else hit_line)
    value_part = value_part.strip()
    value_part = _truncate_unquoted_comment(
        value_part, require_boundary=comment_requires_boundary)
    quoted = re.match(r'''^["'](.+?)["']\s*,?\s*$''', value_part)
    if quoted:
        return quoted.group(1)
    return value_part.split(',')[0].strip('{}[]() ').strip('"\'')
def _split_symbol_path(value_part: str) -> list[str]:
    return [t for t in re.split(r'[.:]', value_part) if t]
def _a14_key_is_non_symbol(short_key: str) -> bool:
    low = short_key.lower()
    return any(low.endswith(suffix) for suffix in _A14_NON_SYMBOL_KEY_SUFFIXES)
def _looks_like_symbol_ref(value_part: str) -> bool:
    value = value_part.strip()
    if (not value or '/' in value or '\\' in value or '://' in value
            or value.startswith('.')):
        return False
    tokens = _split_symbol_path(value)
    if not tokens or not all(t.isidentifier() for t in tokens):
        return False
    if tokens[-1].lower() in _SYMBOL_REF_FILE_EXTS:
        return False
    return tokens[-1].lower() not in _SYMBOL_REF_TLDS
def _detect_config_stale_references(ctx: ArchScanContext,
                                    config_files: list[ConfigFileInfo],
                                    min_conf: float) -> list[ArchCoexistenceItem]:
    if min_conf > _A14_STALE_REF_CONF:
        return []
    project_roots = {
        mod.module_name.partition('.')[0]
        for mod in ctx.modules.values() if mod.module_name
    }
    if ctx._package_prefix:
        project_roots.add(ctx._package_prefix.rstrip('.').partition('.')[0])
    stale_refs = _a14_collect_stale_refs(
        config_files, _a14_code_symbols(ctx), project_roots)
    if not stale_refs:
        return []
    return [ArchCoexistenceItem(
        strategy="A14",
        summary=f"过期配置引用: {len(stale_refs)} 个配置键引用了代码中不存在的符号",
        old_files=sorted({path for path, _ in stale_refs})[:5],
        new_files=[],
        old_symbols=[],
        new_symbols=[],
        confidence=_A14_STALE_REF_CONF,
        evidence=[evidence for _, evidence in stale_refs][:5],
        suggestion="清理过期配置项，更新或移除引用已删除模块/函数的配置键",
        severity="info",
    )]
def _a14_code_symbols(ctx: ArchScanContext) -> set[str]:
    symbols = {mod.module_name for mod in ctx.modules.values()}
    for fi in ctx.all_functions.values():
        symbols.add(fi.name)
        symbols.add(fi.qualified_name.partition('@')[0])
    for mod in ctx.modules.values():
        for class_name, _ in mod.iter_class_groups():
            symbols.add(class_name)
            symbols.add(f"{mod.module_name}.{class_name}")
        symbols.update(mod.global_vars)
        symbols.update(f"{mod.module_name}.{name}" for name in mod.global_vars)
        symbols.update(mod.imports)
        symbols.update(mod.import_aliases)
        symbols.update(f"{mod.module_name}.{name}" for name in mod.import_aliases)
        symbols.update(mod.import_aliases.values())
    return symbols
def _a14_collect_stale_refs(config_files: list[ConfigFileInfo],
                            code_symbols: set[str],
                            project_roots: Collection[str]) -> list[tuple[str, str]]:
    stale_refs: list[tuple[str, str]] = []
    for cf in config_files:
        for key in sorted(cf.keys):
            evidence = _a14_stale_ref_evidence(
                cf, key, code_symbols, project_roots)
            if evidence is not None:
                stale_refs.append((cf.file_path, evidence))
    return stale_refs
def _a14_stale_ref_evidence(
        cf: ConfigFileInfo, key: str, code_symbols: set[str],
        project_roots: Collection[str] = frozenset()) -> str | None:
    short_key = _short_key_of(key)
    if _a14_key_is_non_symbol(short_key):
        return None
    if cf.format == "json":
        data = json.loads(cf.raw_content)
        records = data if isinstance(data, list) else [data]
        value_parts = [
            record[key] for record in records
            if isinstance(record, dict) and isinstance(record.get(key), str)
        ]
    else:
        value_parts = [
            _clean_config_value(
                hit_line, key_start,
                comment_requires_boundary=cf.format != "toml")
            for hit_line, key_start in _locate_config_value_lines(
                cf.raw_content, key, short_key)
        ]
    for value_part in value_parts:
        if not _looks_like_symbol_ref(value_part):
            continue
        if not (_CONFIG_KEY_PATTERN.match(short_key) or ':' in value_part):
            continue
        if (_a14_value_is_live_ref(
                    value_part, code_symbols, project_roots)
                or _a14_value_is_exempt(value_part)
                or _a14_value_is_external_ref(value_part, project_roots)):
            continue
        return (f"{os.path.basename(cf.file_path)}: 键 '{key}' "
                f"引用 '{value_part}' 在代码中不存在")
    return None
def _a14_value_is_external_ref(
        value_part: str, project_roots: Collection[str]) -> bool:
    tokens = _split_symbol_path(value_part)
    if not tokens or tokens[0] in project_roots:
        return False
    try:
        return importlib.util.find_spec(tokens[0]) is not None
    except (ImportError, AttributeError, ValueError) as e:
        _log.warning("arch_coexistence_pairs:A14: 外部模块定位失败 %s: %s",
                     tokens[0], e)
        return False
def _a14_value_is_live_ref(
        value_part: str, code_symbols: set[str],
        project_roots: Collection[str] = frozenset()) -> bool:
    tokens = _split_symbol_path(value_part)
    if not tokens:
        return False
    candidates = [tokens]
    if len(tokens) > 1 and tokens[0] in project_roots:
        candidates.append(tokens[1:])
    for candidate in candidates:
        joined = '.'.join(candidate)
        if joined in code_symbols:
            return True
        if len(candidate) == 1:
            continue
        suffix = f".{joined}"
        if any(symbol.endswith(suffix) for symbol in code_symbols):
            return True
    return False
def _a14_value_is_exempt(value_part: str) -> bool:
    return (value_part.lower() in _STALE_EXEMPT_LITERALS
            or len(value_part) <= 2
            or value_part.startswith('$'))
_A5_MIN_TIME_RANGE = 7 * SECONDS_PER_DAY
_A5_FEATURE_KEYWORDS: tuple = (
    ("has_registry", re.compile(r'(registry|register)', re.IGNORECASE)),
    ("has_pipeline", re.compile(r'(pipeline|stage|phase|step)', re.IGNORECASE)),
    ("has_factory", re.compile(r'(factory|create|build_|make_)', re.IGNORECASE)),
)
def _extract_batch_features(batch: list[ModuleInfo]) -> dict[str, Any]:
    features = {
        "has_registry": False,
        "has_pipeline": False,
        "has_factory": False,
        "avg_complexity": 0.0,
        "uses_global_state": 0,
        "func_per_file": 0.0,
    }
    total_complexity = 0
    total_funcs = 0
    for mod in batch:
        funcs = list(mod.functions.values())
        total_funcs += len(funcs)
        features['uses_global_state'] += len(mod.global_vars)
        total_complexity += sum(fi.complexity for fi in funcs)
        _a5_mark_feature_flags(features, funcs)
    features['avg_complexity'] = round(total_complexity / max(total_funcs, 1), 2)
    features['func_per_file'] = round(total_funcs / max(len(batch), 1), 1)
    return features
_A5_BOOL_FEATURE_DIFFS: tuple = (
    ('has_registry', "新版使用注册表模式，旧版不使用", "旧版使用注册表模式，新版不使用"),
    ('has_pipeline', "新版使用 Pipeline 模式，旧版不使用", "旧版使用 Pipeline 模式，新版不使用"),
    ('has_factory', "新版使用工厂模式，旧版不使用", "旧版使用工厂模式，新版不使用"),
)
_A5_RATIO_FEATURES: tuple = (
    ('avg_complexity', "平均复杂度", ""),
    ('func_per_file', "函数密度", "/文件"),
)
def _a5_mark_feature_flags(features: dict[str, Any], funcs: list[FuncInfo]) -> None:
    for fi in funcs:
        for key, kw in _A5_FEATURE_KEYWORDS:
            if not features[key] and (kw.search(fi.name)
                                      or kw.search(fi.docstring or "")):
                features[key] = True
def _a5_global_state_diff(old_f: dict[str, Any], new_f: dict[str, Any]) -> list[str]:
    old_n, new_n = old_f['uses_global_state'], new_f['uses_global_state']
    if old_n > 0 and new_n == 0:
        return [f"旧版使用 {old_n} 个全局变量，新版不使用"]
    if new_n > 0 and old_n == 0:
        return [f"新版使用 {new_n} 个全局变量，旧版不使用"]
    return []
def _compare_features(old_f: dict[str, Any], new_f: dict[str, Any]) -> list[str]:
    diffs = []
    for key, new_only_msg, old_only_msg in _A5_BOOL_FEATURE_DIFFS:
        if new_f[key] != old_f[key]:
            diffs.append(new_only_msg if new_f[key] else old_only_msg)
    diffs.extend(_a5_global_state_diff(old_f, new_f))
    for key, label, unit in _A5_RATIO_FEATURES:
        diffs.extend(_a5_ratio_diff(old_f[key], new_f[key], label, unit))
    return diffs
def _a5_ratio_diff(old_v: float, new_v: float, label: str, unit: str) -> list[str]:
    if old_v <= 0 or new_v <= 0:
        return []
    ratio = old_v / max(new_v, 0.1)
    if ratio > 2.0:
        return [f"旧版{label} ({old_v}{unit}) 是新版 ({new_v}{unit}) 的 {ratio:.1f} 倍"]
    if ratio < 0.5:
        return [f"新版{label} ({new_v}{unit}) 是旧版 ({old_v}{unit}) 的 {1/ratio:.1f} 倍"]
    return []
def detect_arch_shift_a5(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    batches = _a5_eligible_batches(ctx)
    if batches is None:
        return []
    old_batch, new_batch = batches
    diffs = _compare_features(_extract_batch_features(old_batch),
                              _extract_batch_features(new_batch))
    if not diffs:
        return []
    conf = round(min(0.65 + 0.05 * len(diffs), 0.85), 2)
    if conf < min_conf:
        return []
    return [_a5_make_item(old_batch, new_batch, diffs, conf)]
def _a5_eligible_batches(ctx: ArchScanContext
                         ) -> tuple[list[ModuleInfo], list[ModuleInfo]] | None:
    if len(ctx.modules) < 3:
        return None
    split_time = _a5_split_time_of(ctx)
    if split_time is None:
        return None
    old_batch, new_batch = _a5_split_batches(ctx, split_time)
    if len(old_batch) < 2 or len(new_batch) < 2:
        return None
    return old_batch, new_batch
def _a5_split_time_of(ctx: ArchScanContext) -> float | None:
    mtimes = sorted(mod_info.mtime for mod_info in ctx.modules.values()
                    if mod_info.mtime > 0)
    if not mtimes:
        return None
    time_range = mtimes[-1] - mtimes[0]
    if time_range < _A5_MIN_TIME_RANGE:
        return None
    return _a5_choose_split_time(mtimes, time_range)
def _a5_choose_split_time(mtimes: list[float], time_range: float) -> float:
    mid = len(mtimes) // 2
    median_time = (mtimes[mid] if len(mtimes) % 2
                   else (mtimes[mid - 1] + mtimes[mid]) / 2)
    best_gap = 0
    best_split = median_time
    for k in range(1, len(mtimes)):
        gap = mtimes[k] - mtimes[k - 1]
        if gap > best_gap:
            best_gap = gap
            best_split = (mtimes[k - 1] + mtimes[k]) / 2
    if best_gap > time_range * 0.2 and best_gap > 3 * SECONDS_PER_DAY:
        return best_split
    return median_time
def _a5_split_batches(ctx: ArchScanContext, split_time: float
                      ) -> tuple[list[ModuleInfo], list[ModuleInfo]]:
    old_batch = [mod for mod in ctx.modules.values()
                 if mod.mtime <= split_time and mod.mtime > 0]
    new_batch = [mod for mod in ctx.modules.values()
                 if mod.mtime > split_time and mod.mtime > 0]
    return old_batch, new_batch
def _a5_make_item(old_batch: list[ModuleInfo],
                  new_batch: list[ModuleInfo], diffs: list[str],
                  conf: float) -> ArchCoexistenceItem:
    return ArchCoexistenceItem(
        strategy="A5",
        summary=f"架构模式突变: 代码分两批引入（旧 {len(old_batch)} 文件，"
                f"新 {len(new_batch)} 文件），检测到 {len(diffs)} 个架构特征差异",
        old_files=[m.file_path for m in old_batch[:5]],
        new_files=[m.file_path for m in new_batch[:5]],
        old_symbols=[],
        new_symbols=[],
        confidence=conf,
        evidence=diffs,
        suggestion="评估新旧两批代码的架构差异是否为有意重构，确认旧架构可退役后统一",
        severity="info",
    )
_RESULT_TYPE_RE = re.compile(r'(Result|Tuple|Union|Optional)', re.IGNORECASE)
def _is_result_type_annotation(annotation: str | None) -> bool:
    return bool(annotation) and bool(_RESULT_TYPE_RE.search(annotation))
_LOGGER_METHOD_TAILS = frozenset({
    "debug", "info", "warning", "error", "exception", "critical", "fatal", "log",
})
_PRINT_KW = frozenset({"print", "pprint"})
_LOGGER_MODS = frozenset({"logging", "logger", "_log", "_logger", "LOG", "LOGGER"})
_LOGGER_RECEIVER_NAMES = _LOGGER_MODS | {"log"}
_STDOUT_WRITE_CHAINS = frozenset({
    "sys.stdout.write", "sys.stderr.write",
})
def detect_error_handling_conflict_a8(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    items = []
    all_funcs = iter_module_functions(ctx)
    if len(all_funcs) < _FAMILY_MIN_FUNCS:
        return items
    swallow, propagate, return_none, result_type = _classify_a8_functions(all_funcs)
    if swallow and propagate:
        _emit_a8_conflict_items(
            items, _find_conflict_groups(swallow, propagate),
            _A8_SWALLOW_VS_PROPAGATE, min_conf=min_conf)
    err_return = return_none + result_type
    if err_return and propagate:
        _emit_a8_conflict_items(
            items, _find_conflict_groups(err_return, propagate),
            _A8_ERR_RETURN_VS_RAISE, min_conf=min_conf)
    return items
def _a8_profile_of(fi: FuncInfo) -> dict[str, bool] | None:
    if (not fi.has_try and not fi.has_raise
            and not _is_result_type_annotation(fi.return_annotation)):
        return None
    return _analyze_error_profile(fi)
def _classify_a8_functions(all_funcs: list[FuncInfo]) -> tuple[
        list[FuncInfo], list[FuncInfo], list[FuncInfo], list[FuncInfo]]:
    swallow: list[FuncInfo] = []
    propagate: list[FuncInfo] = []
    return_none: list[FuncInfo] = []
    result_type: list[FuncInfo] = []
    for fi in all_funcs:
        profile = _a8_profile_of(fi)
        if profile is None:
            continue
        if profile.get("swallows_exception"):
            swallow.append(fi)
        if profile.get("raises_explicitly"):
            propagate.append(fi)
        if profile.get("returns_none_on_error"):
            return_none.append(fi)
        if profile.get("returns_result_type"):
            result_type.append(fi)
    return swallow, propagate, return_none, result_type
@dataclass(frozen=True)
class _A8ConflictKind:
    head: str
    left_label: str
    right_label: str
    base_conf: float
    suggestion: str
    severity: str
_A8_SWALLOW_VS_PROPAGATE = _A8ConflictKind(
    head="错误处理冲突", left_label="吞异常", right_label="显式传播",
    base_conf=0.70, suggestion="统一错误处理策略：选择吞异常、显式传播或 Result 类型",
    severity="warning")
_A8_ERR_RETURN_VS_RAISE = _A8ConflictKind(
    head="错误返回策略冲突", left_label="返回错误值", right_label="抛异常",
    base_conf=0.68, suggestion="统一错误返回策略：全部使用异常或全部使用 Result 类型",
    severity="info")
def _emit_a8_conflict_items(items: list[ArchCoexistenceItem],
                            groups: list[tuple[str, list[FuncInfo], list[FuncInfo]]],
                            kind: _A8ConflictKind,
                            min_conf: float) -> None:
    for stem, l_list, r_list in groups:
        item = _detect_a8_conflict_group(stem, l_list, r_list, kind, min_conf)
        if item is not None:
            items.append(item)
def _detect_a8_conflict_group(stem: str, l_list: list[FuncInfo],
                              r_list: list[FuncInfo], kind: _A8ConflictKind,
                              min_conf: float) -> ArchCoexistenceItem | None:
    is_cross = spans_files(l_list + r_list)
    conf = family_conf(kind.base_conf, is_cross, l_list, r_list,
                       side_bonus=0.0, cap=1.0)
    if conf < min_conf:
        return None
    return build_paradigm_item(ParadigmSpec(
        strategy="A8",
        summary=f"{kind.head}: '{stem}' 函数族"
                f" {len(l_list)} 个{kind.left_label} vs {len(r_list)} 个{kind.right_label}",
        old_funcs=l_list,
        new_funcs=r_list,
        evidence=(
            f"{kind.left_label}: {side_symbols(l_list)}",
            f"{kind.right_label}: {side_symbols(r_list)}",
        ),
        conf=conf,
        is_cross=is_cross,
        cross_evidence=f"跨模块: {', '.join(module_stems(l_list + r_list)[:ITEM_FILE_LIMIT])}",
        suggestion=kind.suggestion,
        severity=kind.severity,
    ))
def _scan_error_constructs(func_node: ast.AST) -> tuple[bool, bool, bool, bool]:
    has_swallow = False
    has_raise = False
    has_return_none = False
    has_try = False
    for child in iter_own_scope(func_node):
        if isinstance(child, TRY_NODE_TYPES):
            has_try = True
            for handler in child.handlers:
                handler_swallow, handler_ret_none = _analyze_handler_body(handler)
                has_swallow = has_swallow or handler_swallow
                has_return_none = has_return_none or handler_ret_none
        if isinstance(child, ast.Raise):
            has_raise = True
    return has_swallow, has_raise, has_return_none, has_try
def _analyze_error_profile(fi: FuncInfo) -> dict[str, bool]:
    profile: dict[str, bool] = {}
    try:
        func_node = fi.ast_node
        if func_node is None:
            return profile
        has_swallow, has_raise, has_return_none, has_try = (
            _scan_error_constructs(func_node))
        if _is_result_type_annotation(fi.return_annotation):
            profile["returns_result_type"] = True
        profile["swallows_exception"] = has_swallow
        profile["raises_explicitly"] = has_raise and not has_swallow
        profile["returns_none_on_error"] = has_return_none and has_try
    except (ValueError, TypeError, AttributeError) as e:
        _log.warning("_analyze_error_profile: %s: %s: %s",
                     fi.qualified_name, type(e).__name__, e, exc_info=True)
    return profile
def _handler_return_signals(value: ast.expr | None) -> tuple[bool, bool]:
    if value is None or (isinstance(value, ast.Constant) and value.value is None):
        return True, True
    if (isinstance(value, ast.Dict) and not value.keys) or (
            isinstance(value, ast.List) and not value.elts):
        return True, False
    return False, False
def _handler_stmt_signals(stmt: ast.stmt) -> tuple[bool, bool]:
    if isinstance(stmt, ast.Pass):
        return True, False
    if isinstance(stmt, ast.Return):
        return _handler_return_signals(stmt.value)
    if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
        call = stmt.value
        if isinstance(call.func, ast.Name) and call.func.id in _PRINT_KW:
            return True, False
        if _is_logger_attribute_call(call):
            return True, False
        if dotted_name(call.func) in _STDOUT_WRITE_CHAINS:
            return True, False
    return False, False
def _analyze_handler_body(handler: ast.ExceptHandler) -> tuple[bool, bool]:
    if any(isinstance(n, ast.Raise) for n in iter_own_scope(handler)):
        return False, False
    has_swallow = handler.type is None
    has_return_none = False
    for stmt in iter_own_scope(handler):
        if not isinstance(stmt, ast.stmt):
            continue
        stmt_swallow, stmt_ret_none = _handler_stmt_signals(stmt)
        has_swallow = has_swallow or stmt_swallow
        has_return_none = has_return_none or stmt_ret_none
    return has_swallow, has_return_none
def _find_conflict_groups(list_a: list[FuncInfo], list_b: list[FuncInfo]
                          ) -> list[tuple[str, list[FuncInfo], list[FuncInfo]]]:
    a_by_stem: dict[str, list[FuncInfo]] = defaultdict(list)
    for fi_a in _unique_functions(list_a):
        a_by_stem[family_stem(fi_a.name)].append(fi_a)
    b_by_stem: dict[str, list[FuncInfo]] = defaultdict(list)
    for fi_b in _unique_functions(list_b):
        b_by_stem[family_stem(fi_b.name)].append(fi_b)
    groups: list[tuple[str, list[FuncInfo], list[FuncInfo]]] = []
    for stem, a_list in a_by_stem.items():
        b_list = b_by_stem.get(stem)
        if not b_list:
            continue
        a_keys = {_func_identity(fi_a) for fi_a in a_list}
        matching = [fi_b for fi_b in b_list
                    if _func_identity(fi_b) not in a_keys]
        if matching:
            groups.append((stem, a_list, matching))
    return groups
def _func_identity(fi: FuncInfo) -> tuple[str, str]:
    return fi.file_path, fi.qualified_name
def _unique_functions(funcs: list[FuncInfo]) -> list[FuncInfo]:
    seen: set[tuple[str, str]] = set()
    unique: list[FuncInfo] = []
    for fi in funcs:
        identity = _func_identity(fi)
        if identity in seen:
            continue
        seen.add(identity)
        unique.append(fi)
    return unique
def _calls_unstructured_console(fi: FuncInfo) -> bool:
    func_node = fi.ast_node
    if func_node is None:
        return False
    for child in iter_own_scope(func_node):
        if (isinstance(child, ast.Call)
                and dotted_name(child.func) in _STDOUT_WRITE_CHAINS):
            return True
    return False
_LOGGING_MODULE_ROOT = "logging"
@dataclass(frozen=True)
class _LoggingBindings:
    receivers: frozenset[str]
    direct_functions: frozenset[str]
_EMPTY_LOGGING_BINDINGS = _LoggingBindings(
    receivers=frozenset(), direct_functions=frozenset())
def _logging_import_roles(
        import_aliases: dict[str, str]) -> tuple[set[str], set[str]]:
    receivers: set[str] = set()
    direct_functions: set[str] = set()
    for local, target in import_aliases.items():
        if not (target == _LOGGING_MODULE_ROOT
                or target.startswith(f"{_LOGGING_MODULE_ROOT}.")):
            continue
        receivers.add(local)
        if target.rsplit('.', 1)[-1] in _LOGGER_METHOD_TAILS:
            direct_functions.add(local)
    return receivers, direct_functions
def _logging_bindings_of(mod_info: ModuleInfo) -> _LoggingBindings:
    receivers, direct_functions = _logging_import_roles(
        _active_module_import_aliases(mod_info))
    return _LoggingBindings(
        receivers=frozenset(receivers),
        direct_functions=frozenset(direct_functions),
    )
def _all_local_logging_import_roles(
        func_node: ast.AST) -> tuple[set[str], set[str]]:
    imports: dict[str, str] = {}
    for child in iter_own_scope(func_node):
        if isinstance(child, (ast.Import, ast.ImportFrom)):
            _collect_local_import_targets(child, imports)
    return _logging_import_roles(imports)
def detect_logging_conflict_a9(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    logging_bindings = {
        module.file_path: _logging_bindings_of(module)
        for module in ctx.modules.values()
    }
    return collect_family_items(
        ctx, _detect_a9_stem_group, logging_bindings, min_conf)
def _detect_a9_stem_group(
        stem: str, group: list[FuncInfo],
        logging_bindings: dict[str, _LoggingBindings],
        min_conf: float) -> ArchCoexistenceItem | None:
    print_users, logger_users = _partition_a9_logging_group(
        group, logging_bindings)
    if not print_users or not logger_users:
        return None
    is_cross = spans_files(print_users + logger_users)
    conf = family_conf(0.68, is_cross, print_users, logger_users,
                        boost=0.08, side_bonus=0.05)
    if conf < min_conf:
        return None
    return build_paradigm_item(ParadigmSpec(
        strategy="A9",
        summary=f"日志范式冲突: '{stem}' 函数族 {len(print_users)} 个使用print()、"
                f"{len(logger_users)} 个使用结构化日志",
        old_funcs=print_users,
        new_funcs=logger_users,
        evidence=(
            f"print()输出: {side_symbols(print_users)}",
            f"结构化日志: {side_symbols(logger_users)}",
        ),
        conf=conf,
        is_cross=is_cross,
        cross_evidence=f"跨模块: {', '.join(module_stems(group)[:ITEM_FILE_LIMIT])}",
        suggestion="统一日志方案：全部迁移到结构化日志（如标准 logging 或 loguru），移除 print() 调试输出",
        severity="warning",
    ))
def _uses_unstructured_output(fi: FuncInfo) -> bool:
    output_names = _PRINT_KW & fi.called_functions
    if fi.ast_node is not None:
        local_values = _own_scope_bound_names(
            fi.ast_node, include_imports=False)
        output_names -= local_values
    return bool(output_names) or _calls_unstructured_console(fi)
def _calls_structured_logger(
        fi: FuncInfo, bindings: _LoggingBindings) -> bool:
    if fi.ast_node is None:
        return False
    events = _local_binding_events(fi.ast_node, fi.file_path)
    external_names = (
        _declared_global_names(fi.ast_node)
        | _declared_nonlocal_names(fi.ast_node))
    for child in iter_own_scope(fi.ast_node):
        if not isinstance(child, ast.Call):
            continue
        position = _node_position(child)
        local_imports = _local_binding_state_at(
            events, external_names, position)
        local_receivers, local_direct_functions = _logging_import_roles(
            local_imports)
        active_local_names = local_receivers | local_direct_functions
        local_values = {
            name
            for event_position, name, target in events
            if (event_position <= position and target is None
                and name not in external_names)
        }
        local_values.update(set(local_imports) - active_local_names)
        local_values.difference_update(active_local_names)
        imported_names = (
            _LOGGER_RECEIVER_NAMES | bindings.receivers
            | bindings.direct_functions | local_receivers
            | local_direct_functions)
        shadowed_names = local_values & imported_names
        receivers = (
            _LOGGER_RECEIVER_NAMES | bindings.receivers | local_receivers
        ) - shadowed_names
        direct_functions = (
            bindings.direct_functions | local_direct_functions) - shadowed_names
        if _is_logger_attribute_call(child, receivers):
            return True
        if (isinstance(child.func, ast.Name)
                and child.func.id in direct_functions):
            return True
    return False
def _is_logger_attribute_call(call: ast.Call,
                             receivers: Collection[str] = _LOGGER_RECEIVER_NAMES) -> bool:
    if not isinstance(call.func, ast.Attribute):
        return False
    if call_tail_name(call) not in _LOGGER_METHOD_TAILS:
        return False
    dotted = dotted_name(call.func)
    segments = dotted.split('.') if dotted else []
    receiver = segments[-2] if len(segments) >= 2 else ''
    root = segments[0] if segments else ''
    if receiver in receivers or root in receivers:
        return True
    return (isinstance(call.func.value, ast.Call)
            and call_tail_name(call.func.value) == 'getLogger')
def _partition_a9_logging_group(
        group: list[FuncInfo],
        logging_bindings: dict[str, _LoggingBindings],
) -> tuple[list[FuncInfo], list[FuncInfo]]:
    print_users: list[FuncInfo] = []
    logger_users: list[FuncInfo] = []
    for fi in group:
        bindings = logging_bindings.get(fi.file_path, _EMPTY_LOGGING_BINDINGS)
        uses_logger = _calls_structured_logger(fi, bindings)
        if not uses_logger and _uses_unstructured_output(fi):
            print_users.append(fi)
        elif uses_logger:
            logger_users.append(fi)
    return print_users, logger_users
ARCH_STRATEGIES: tuple[
    tuple[str, Callable[..., list[ArchCoexistenceItem]], bool], ...
] = (
    ("A3", detect_bypass_a3, False),
    ("A1", detect_dual_impl_a1, False),
    ("A7", detect_class_split_a7, False),
    ("A4", detect_state_conflict_a4, False),
    ("A6", detect_decorator_conflict_a6, False),
    ("A2", detect_sync_async_mix_a2, False),
    ("A8", detect_error_handling_conflict_a8, False),
    ("A5", detect_arch_shift_a5, False),
    ("A9", detect_logging_conflict_a9, False),
    ("A10", detect_adapter_wall_a10, False),
    ("A11", detect_datamodel_split_a11, False),
    ("A12", detect_type_annotation_conflict_a12, False),
    ("A13", detect_import_style_conflict_a13, False),
    ("A14", detect_config_coexistence_a14, True),
)
def run_arch_strategies(ctx: ArchScanContext, min_conf: float,
                        config_files: list[ConfigFileInfo],
                        errors: list[str]) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for strategy_id, detect_fn, needs_config in ARCH_STRATEGIES:
        try:
            if needs_config:
                items.extend(detect_fn(ctx, min_conf, config_files=config_files))
            else:
                items.extend(detect_fn(ctx, min_conf))
        except Exception as e:  # noqa: BLE001
            _log.warning("arch strategy %s failed: %s", strategy_id, e, exc_info=True)
            errors.append(f"策略 {strategy_id} 检测异常: {type(e).__name__}: {e}")
    return items

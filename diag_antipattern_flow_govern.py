from __future__ import annotations

import ast
import logging
import math
import os
import time
from collections.abc import Callable, Iterator, Mapping
from pathlib import Path
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_antipattern import (
    DeadCodeEliminator,
    DegradationEliminator,
    DynamicImportConverter,
    FacadeOptimizer,
    LazyImportEliminator,
    PassthroughLayerDetector,
    StubEliminator,
    fallback_scan_file,
)
from jwsgj.diag_antipattern_flow_detect import (
    _AP_CATEGORY_MAP,
    CrossSkillDetector,
    DefaultParamDuplicationDetector,
    DuplicateCodeDetector,
    SignalDetector,
    _antipattern_detail,
    _category_issue,
    _coerce_bool,
    _coerce_categories,
    _coerce_py_files,
    _coerce_root_arg,
    _coerce_str_seq,
    _confidence_or_none,
    _dict_category_detail,
    _finding_issues,
    _group_files_by_parent_dir,
    _norm_issue_line,
    _norm_issue_str,
    _path_identity,
    _slot_needs_attention,
    _text_or_fspath,
)
from jwsgj.diag_detector_findings import (
    RETIRED_RULE_IDS,
)
from jwsgj.diag_detector_findings import (
    map_external_severity as _map_severity,
)
from jwsgj.diag_detectors_registry import (
    run_bounded_channel,
)
from jwsgj.diag_merge_safety import (
    _GRAPH_DEFAULT_OPTIONS,
    FragmentConsolidator,
    _iter_project_modules,
    build_normalized_import_graph,
    detect_circular_imports_stratified,
    enumerate_all_cycles,
    find_graph_cycles,
    parse_py_file,
)
from jwsgj.diag_shared_ast_bindings import (
    ScopeNameResolver,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.refactor_api_contract import (
    check_import_edge_removed,
    diff_module_signatures,
    load_module_signatures,
    normalize_prev_signatures,
)
from jwsgj.runtime_scope import (
    is_scan_py_name,
    iter_scan_py_files,
)

__all__ = [
    'AntiPatternEliminator',
    'CircularDependencyResolver',
    'list_cycle_capabilities',
    'module_name_under_root',
    'real_antipattern_scan',
    'run_antipattern_detector',
    'run_boundary_coupling_diagnostics',
    'scan_anti_patterns',
    'suggest_circular_fixes',
]
logger = logging.getLogger(__name__)
logger.info(
    "diag_antipattern_flow_govern 已加载: %d 项导出"
    "（反模式消除与循环耦合治理）", len(__all__))
_META_RESULT_KEYS = frozenset({"summary", "ai_execution"})
def _existing_root_arg(value: Any) -> str | None:
    root = _coerce_root_arg(value)
    return root if root is not None and os.path.isdir(root) else None
def _root_or_stored(root_dir: Any, stored_root: str | None) -> str | None:
    if root_dir is not None:
        return _existing_root_arg(root_dir)
    return _existing_root_arg(stored_root) if stored_root is not None else None
def _slot_issues(category: str, findings: Any, parent_dir: str,
                 file_set: set) -> list[dict]:
    if isinstance(findings, Mapping):
        if not _slot_needs_attention(findings):
            return []
        return [_category_issue(
            category, parent_dir, 0,
            _dict_category_detail(dict(findings), category))]
    if not isinstance(findings, list):
        return []
    issues: list[dict] = []
    for finding in findings:
        if isinstance(finding, dict):
            issues.extend(
                _finding_issues(category, finding, parent_dir, file_set))
    return issues
def _scan_result_issues(scan_result: dict, parent_dir: str,
                        file_set: set) -> list[dict]:
    issues: list[dict] = []
    for category, findings in scan_result.items():
        if (category in _META_RESULT_KEYS
                or category not in _ANTIPATTERN_CATEGORIES):
            continue
        issues.extend(_slot_issues(category, findings, parent_dir, file_set))
    return issues
class AntiPatternEliminator:
    def __init__(self):
        self.facade_optimizer = FacadeOptimizer()
        self.lazy_import_eliminator = LazyImportEliminator()
        self.regression_eliminator = DegradationEliminator()
        self.circular_resolver = CircularDependencyResolver()
        self.dead_code_eliminator = DeadCodeEliminator()
        self.duplicate_detector = DuplicateCodeDetector()
        self.default_duplication_detector = DefaultParamDuplicationDetector()
        self.passthrough_layer_detector = PassthroughLayerDetector()
        self.stub_eliminator = StubEliminator()
        self.dynamic_import_converter = DynamicImportConverter()
        self.fragment_consolidator = FragmentConsolidator()
        self._file_detectors = (
            ("C2_lazy_import", self.lazy_import_eliminator),
            ("C4_regression", self.regression_eliminator),
            ("C8_dead_code", self.dead_code_eliminator),
            ("C16_stubs", self.stub_eliminator),
            ("C19_passthrough_layer", self.passthrough_layer_detector),
        )
    _LIST_CATEGORIES: ClassVar[tuple[str, ...]] = (
        "C1_facade",
        "C2_lazy_import",
        "C4_regression",
        "C6_circular",
        "C8_dead_code",
        "C11_duplicates",
        "C16_stubs",
        "C17_dynamic_import",
        "C18_default_duplication",
        "C19_passthrough_layer",
    )
    @classmethod
    def _init_scan_results(cls) -> dict:
        return {category: [] for category in cls._LIST_CATEGORIES}
    def _scan_file_categories(self, fpath: str, fname: str,
                              results: dict,
                              on: Callable[[str], bool]) -> None:
        if on("C1_facade") and fname == '__init__.py':
            _c1 = self.facade_optimizer.check(fpath)
            if isinstance(_c1, Mapping):
                if _slot_needs_attention(_c1):
                    results["C1_facade"].append(dict(_c1))
            elif _c1 is not None:
                logger.debug(
                    "[Antipattern] C1 检测器返回异形容器 %s: %r",
                    fpath, type(_c1).__name__)
        for category, detector in self._file_detectors:
            if not on(category):
                continue
            _found = detector.detect(fpath)
            if isinstance(_found, (list, tuple)):
                results[category].extend(_found)
            elif _found is not None:
                logger.debug(
                    "[Antipattern] %s 检测器返回异形容器 %s: %r",
                    category, fpath, type(_found).__name__)
        if on("C17_dynamic_import"):
            _found = self.dynamic_import_converter.detect(fpath)
            if not isinstance(_found, (list, tuple)):
                if _found is not None:
                    logger.debug(
                        "[Antipattern] C17 检测器返回异形容器 %s: %r",
                        fpath, type(_found).__name__)
                return
            for _v in _found:
                if not isinstance(_v, dict):
                    logger.debug("[Antipattern] C17 条目非 dict: %r", _v)
                    continue
                _v["suggestion"] = self.dynamic_import_converter.suggest_static_import(_v)
                results["C17_dynamic_import"].append(_v)
    def _scan_c10_fragments(self, root_dir: str,
                            on: Callable[[str], bool]) -> dict:
        if on("C10_fragments"):
            frag_stats = self.fragment_consolidator.detect(root_dir)
            if not isinstance(frag_stats, Mapping):
                logger.warning(
                    "[Antipattern] 碎片化检测返回异形容器，按空统计降级: %r",
                    type(frag_stats).__name__)
                frag_stats = {}
            c10 = dict(frag_stats)
            c10["disabled"] = False
            _needs = _coerce_bool(
                frag_stats.get("needs_consolidation"), False)
            c10["needs_consolidation"] = _needs
            c10["ok"] = not _needs
            if _needs:
                try:
                    c10["merge_plan"] = self.fragment_consolidator.generate_merge_plan(
                        root_dir, stats=frag_stats)
                except (OSError, ValueError, TypeError, KeyError) as e:
                    logger.warning(
                        "[Antipattern] 合并计划生成失败（保留统计）: %s", e)
                    c10["merge_plan"] = []
        else:
            c10 = {
                "disabled": True,
                "ok": True,
                "needs_consolidation": False,
                "small_file_list": [],
                "fragmentation_rate": 0.0,
                "total_files": 0,
                "total_lines": 0,
                "small_file_count": 0,
            }
        c10["small_file_threshold_hint"] = self.fragment_consolidator.SMALL_FILE_THRESHOLD
        _small = c10.get("small_file_list")
        c10["small_file_list"] = (
            list(_small)[:200] if isinstance(_small, (list, tuple)) else [])
        return c10
    @staticmethod
    def _iter_scan_files(root_dir: str) -> Iterator[tuple[str, str]]:
        for fpath in iter_scan_py_files(root_dir):
            yield fpath, os.path.basename(fpath)
    def full_scan(self, root_dir: str, categories=None) -> dict:
        root = _existing_root_arg(root_dir)
        if not root:
            logger.warning("[Antipattern] 反模式全量扫描跳过：根目录缺失/非法")
            results = self._init_scan_results()
            results["C10_fragments"] = self._scan_c10_fragments(
                "", lambda _cat: False)
            results["summary"] = {
                "total_violations": 0,
                "ok": False,
                "error": "missing_root_dir",
            }
            return results
        _categories = _coerce_categories(categories)
        def _on(cat: str) -> bool:
            return _categories is None or cat in _categories
        results = self._init_scan_results()
        for fpath, fname in self._iter_scan_files(root):
            self._scan_file_categories(fpath, fname, results, _on)
        if _on("C6_circular"):
            _cycles = self.circular_resolver.detect(root)
            results["C6_circular"] = (
                list(_cycles) if isinstance(_cycles, (list, tuple)) else [])
        results["C10_fragments"] = self._scan_c10_fragments(root, _on)
        if _on("C11_duplicates"):
            _dups = self.duplicate_detector.detect_duplicate_functions(root)
            results["C11_duplicates"] = (
                list(_dups) if isinstance(_dups, (list, tuple)) else [])
        if _on("C18_default_duplication"):
            _defaults = self.default_duplication_detector.detect(root)
            results["C18_default_duplication"] = (
                list(_defaults) if isinstance(_defaults, (list, tuple)) else [])
        total_violations = sum(len(results[cat]) for cat in self._LIST_CATEGORIES) + (
            1 if results["C10_fragments"]["needs_consolidation"] else 0)
        results["summary"] = {
            "total_violations": total_violations,
            "ok": total_violations == 0,
        }
        return results
    def verify_all_eliminated(self, root_dir: str) -> dict[str, bool]:
        scan = self.full_scan(root_dir)
        if scan.get("summary", {}).get("error"):
            categories = (*self._LIST_CATEGORIES, "C10_fragments")
            return {category: False for category in categories}
        status = {
            category: not scan[category]
            for category in self._LIST_CATEGORIES
        }
        status["C10_fragments"] = bool(scan["C10_fragments"].get("ok", True))
        return status
    def verify_eliminated(self, root_dir: str) -> bool:
        results = self.verify_all_eliminated(root_dir)
        return all(results.values())
def scan_anti_patterns(root_dir: str,
                       categories: set[str] | frozenset[str] | None = None) -> dict:
    eliminator = AntiPatternEliminator()
    result = eliminator.full_scan(root_dir, categories=categories)
    if isinstance(result, dict):
        result.setdefault("ai_execution", {
            "next_action": "review_and_execute_antipattern_fixes",
            "instruction": (
                "逐项审核各消除器产出的 concrete_transforms/合并计划；审核通过后调用 "
                "本技能的重构执行入口 run_refactor_execution(root_dir) 执行落盘并跑回归验证，"
                "不通过的变换按 reason 驳回。"
                "禁止补丁方式修复（P0 强制行为，与 AI 审核编排器 "
                "fix_scope.no_patch_fix、编写时门禁 NO_PATCH_FIX、"
                "编写前 B35 约束三层同口径）：每个变换须以根因消除方式落地"
                "（SSOT 归口/契约对齐/结构校正），吞异常遮蔽/特判绕过/"
                "副本对冲/宽捕获重试/表层归一等补丁形态变换一律驳回重写，"
                "症状消失而根因仍在视为未修复"
            ),
        })
    return result
_DEFAULT_MAX_CYCLES = 20
_MODULE_OBJECT_REFERENCE = "<module-object>"
_WILDCARD_IMPORT_REFERENCE = "<wildcard-import>"
_MODULE_METADATA_REFERENCES = frozenset({
    "__all__", "__annotations__", "__builtins__", "__cached__",
    "__class__", "__dict__", "__doc__", "__file__", "__loader__",
    "__name__", "__package__", "__path__", "__spec__",
})
_RESCAN_PARSE_ERROR = "rescan_failed: source_parse_failed"
_DEFAULT_DETECT_KWARGS: dict[str, bool] = {
    "include_tests": _GRAPH_DEFAULT_OPTIONS["include_tests"],
    "allow_bare": _GRAPH_DEFAULT_OPTIONS["allow_bare"],
    "full_cycles": False,
}
_FIX_BODY_KEYS: tuple[str, ...] = (
    "one_line_summary", "cycle_nodes", "cycle_length", "strategy",
    "new_module_suggestion", "weakest_link", "edge_strengths",
    "symbol_analysis", "migration_plan", "risk_assessment",
    "concrete_transforms", "strategies_ranked",
)
class _CycleFixRequest(NamedTuple):
    unique_nodes: list
    cycle_len: int
    cycle_edges: list
    all_symbols: list
    new_module: str
    symbol_map: dict
def _fix_body(**payload: Any) -> dict:
    missing = [k for k in _FIX_BODY_KEYS if k not in payload]
    extra = [k for k in payload if k not in _FIX_BODY_KEYS]
    if missing or extra:
        raise ValueError(
            f"修复建议体键集漂移: missing={missing} extra={extra}")
    return {key: payload[key] for key in _FIX_BODY_KEYS}
def _strategy(name: str, score: int, risk: str, desc: str, reason: str,
              **extra: Any) -> dict:
    entry: dict[str, Any] = {
        "name": name, "score": score, "risk": risk,
        "desc": desc, "reason": reason,
    }
    entry.update(extra)
    return entry
def _weakest_link_strategy(weakest_link: dict, *, desc: str,
                           how_to: str) -> dict:
    return _strategy(
        "断最弱链接（推荐）", 92, "low", desc,
        f"最弱链接仅 {weakest_link['symbol_count']} 符号,中断代价最小",
        edge=weakest_link["edge"], how_to=how_to,
    )
def _extract_api_strategy(new_module: str, to_move: int, score: int,
                          reason: str) -> dict:
    return _strategy("提取公共接口", score, "medium",
                     f"创建 {new_module},移入 {to_move} 个交叉依赖符号", reason)
def _inline_symbols_strategy() -> dict:
    return _strategy("符号内联", 70, "medium",
                     "仅被一方使用的符号直接内联到使用方",
                     "可减少需移动的符号数")
def _merge_modules_strategy(reason: str) -> dict:
    return _strategy("合并模块", 60, "medium",
                     "将两个模块合并为一个", reason)
def _cycle_nodes(cycle) -> list:
    if not isinstance(cycle, (list, tuple)):
        return []
    _raw = list(cycle)
    if any(not isinstance(node, str) or not node for node in _raw):
        return []
    if len(_raw) > 1 and _raw[-1] == _raw[0]:
        _raw.pop()
    if not _raw or len(set(_raw)) != len(_raw):
        return []
    return _raw
def _normalize_cycle_limit(value) -> int:
    if isinstance(value, bool):
        return _DEFAULT_MAX_CYCLES
    if isinstance(value, str):
        try:
            value = int(value.strip())
        except (TypeError, ValueError):
            return _DEFAULT_MAX_CYCLES
    if isinstance(value, float) and not math.isfinite(value):
        return _DEFAULT_MAX_CYCLES
    if not isinstance(value, (int, float)):
        return _DEFAULT_MAX_CYCLES
    return max(0, int(value))
def _count_cycle_symbols(cycle: list[str], symbol_map: dict) -> int:
    nodes = _cycle_nodes(cycle)
    total = 0
    for i in range(len(nodes)):
        _next = nodes[(i + 1) % len(nodes)]
        total += len(symbol_map.get(nodes[i], {}).get(_next, []))
    return total
def _pure_import_break_strategy(weakest_link: dict, new_module: str,
                                cycle_len: int) -> dict:
    return _weakest_link_strategy(
        weakest_link,
        desc=f"在 {weakest_link['edge']} 处中断（纯 import 边,无符号级依赖）",
        how_to=(
            f"1. 找到 {weakest_link['from']} 中 'import {weakest_link['to']}' 语句并删除\n"
            f"2. {weakest_link['from']} 对 {weakest_link['to']} 的模块级使用改为经 {new_module} 单向引用\n"
            f"3. 其余 {cycle_len - 1} 条边保持单向依赖"
        ),
    )
def _rank_self_ref_strategies(used: bool = False) -> list:
    action = ("先把自模块属性访问改成直接符号引用，再删除自引用导入"
              if used else "删除未被使用的自引用导入")
    return [_strategy(
        "消除自引用导入", 90, "low", action,
        ("自模块属性可直接绑定本地符号；须先改引用再删导入"
         if used else "未使用的自引用没有绑定收益；延迟导入仅掩盖问题"),
        how_to=("1. 在该模块中定位导入自身及其属性访问\n"
                "2. 将 模块.符号 改为直接使用本模块符号"
                "（未使用导入时无需替换）\n"
                "3. 删除自引用导入并用 verify_cycle_resolved 验证"),
    )]
def _rank_pure_import_strategies(weakest_link: dict, new_module: str,
                                 cycle_len: int, to_move: int) -> list:
    ranked = [_pure_import_break_strategy(weakest_link, new_module, cycle_len)]
    if cycle_len == 2:
        if to_move > 0:
            ranked.append(_extract_api_strategy(
                new_module, to_move, 80, "备选:迁移另一条边符号到共享模块"))
            ranked.append(_inline_symbols_strategy())
        ranked.append(_merge_modules_strategy(
            "纯 import 互导属模块级紧耦合,合并可整体消除环"))
    else:
        if to_move > 0:
            ranked.append(_extract_api_strategy(
                new_module, to_move, 85, "备选:一次性消除所有交叉依赖"))
        ranked.append(_strategy(
            "定向提取（仅最弱边）", 78, "low",
            (f"仅处理 {weakest_link['edge']} 纯 import 边"
             f"（删除语句或改经 {new_module}）"),
            "比全量提取更轻量"))
    return ranked
def _rank_two_node_strategies(new_module: str, to_move: int) -> list:
    return [
        _strategy("提取公共接口", 95, "low",
                  f"创建 {new_module},移入 {to_move} 个交叉依赖符号",
                  "2节点循环最优解"),
        _strategy("依赖反转", 80, "low",
                  "定义 Protocol/ABC 在独立模块",
                  "如交叉依赖涉及类继承可考虑"),
        _inline_symbols_strategy(),
        _merge_modules_strategy("模块均<500行且紧耦合时可用"),
    ]
def _rank_weak_link_strategies(weakest_link: dict, new_module: str,
                               cycle_len: int, to_move: int) -> list:
    _wl_syms = weakest_link["symbols"]
    _interrupt = (f"在 {weakest_link['edge']} 处中断（仅 "
                  f"{weakest_link['symbol_count']} 符号: "
                  f"{', '.join(_wl_syms[:3])}）")
    _how_to = (
        f"1. 找到 {weakest_link['from']} 中 'from {weakest_link['to']} import {', '.join(_wl_syms)}'\n"
        f"2. 将这 {weakest_link['symbol_count']} 个符号移入 {new_module}.py\n"
        f"3. {weakest_link['from']} 改为 from {new_module} import ...\n"
        f"4. 其余 {cycle_len - 1} 条边保持单向依赖"
    )
    return [
        _weakest_link_strategy(weakest_link, desc=_interrupt, how_to=_how_to),
        _extract_api_strategy(
            new_module, to_move, 85, "备选:一次性消除所有交叉依赖"),
        _strategy("定向提取（仅最弱边）", 78, "low",
                  (f"仅提取 {weakest_link['edge']} 涉及的 "
                   f"{weakest_link['symbol_count']} 个符号到 {new_module}"),
                  "比全量提取更轻量"),
    ]
def _rank_heavy_cycle_strategies(new_module: str, cycle_len: int,
                                 to_move: int, weakest_link) -> list:
    ranked = [
        _strategy("提取公共接口", 88, "medium",
                  f"创建 {new_module},提取 {to_move} 个交叉依赖符号",
                  f"{cycle_len}节点循环,{to_move}个符号需统一管理"),
        _strategy("依赖反转", 75, "medium",
                  "通过依赖反转打破长链循环",
                  "适用于分层架构"),
    ]
    if weakest_link:
        ranked.append(_strategy(
            "断最弱链接", 65, "medium",
            f"在 {weakest_link['edge']} 处中断（{weakest_link['symbol_count']} 符号）",
            f"符号数较多（{weakest_link['symbol_count']}）,不如全量提取"))
    return ranked
def _rank_cycle_strategies(cycle_len: int, new_module: str, to_move: int,
                           weakest_link) -> list:
    if cycle_len == 1:
        ranked = _rank_self_ref_strategies(
            bool(weakest_link and weakest_link["symbols"]))
    elif weakest_link and not weakest_link["symbols"]:
        ranked = _rank_pure_import_strategies(weakest_link, new_module,
                                              cycle_len, to_move)
    elif cycle_len == 2:
        ranked = _rank_two_node_strategies(new_module, to_move)
    elif cycle_len >= 3 and weakest_link and weakest_link["symbol_count"] <= 3:
        ranked = _rank_weak_link_strategies(weakest_link, new_module,
                                            cycle_len, to_move)
    else:
        ranked = _rank_heavy_cycle_strategies(new_module, cycle_len,
                                              to_move, weakest_link)
    ranked.append(_strategy(
        "延迟导入（不推荐）", 30, "high",
        "将循环 import 移入函数体",
        "最后手段,会掩盖真实依赖关系"))
    return ranked
def _imported_symbol_name(reference: str) -> str:
    return reference.split(" as ", 1)[0]
def _build_concrete_transforms(new_module: str, unique_nodes: list, all_symbols: list,
                               migration_plan: list, weakest_link: dict | None = None) -> list:
    transforms = []
    transforms.append(
        f"# new module: {new_module}.py  (解除 {' <-> '.join(unique_nodes[:4])} 循环)\n"
        f"# symbols: {', '.join(dict.fromkeys(_imported_symbol_name(s) for s in all_symbols))}\n"
    )
    if weakest_link is not None and not weakest_link["symbols"]:
        transforms.append(
            f"# {weakest_link['from']} (断最弱链接,推荐策略):\n"
            f"#   BEFORE: import {weakest_link['to']}\n"
            f"#   AFTER : 删除该语句（纯 import 边,无符号级依赖;"
            f"模块级使用改为经 {new_module} 单向引用）\n"
        )
    by_importer = {}
    for p in migration_plan:
        by_importer.setdefault(
            p["imported_by"], {}).setdefault(
                p["from_module"], []).append(p["reference"])
    for importer, from_map in by_importer.items():
        for from_mod, syms in from_map.items():
            transforms.append(
                f"# {importer}:\n"
                f"#   BEFORE: from {from_mod} import {', '.join(syms)}\n"
                f"#   AFTER:  from {new_module} import {', '.join(syms)}"
            )
    return transforms
def _build_degenerate_fix(
        cycle: list,
        summary: str = "退化环输入(无有效模块名),无修复建议") -> dict:
    _degen_nodes = _cycle_nodes(cycle)
    return _fix_body(
        one_line_summary=summary,
        cycle_nodes=_degen_nodes,
        cycle_length=len(_degen_nodes),
        strategy="none",
        new_module_suggestion=None,
        weakest_link=None,
        edge_strengths=[],
        symbol_analysis=_build_symbol_analysis([], 0),
        migration_plan=[],
        risk_assessment=_build_risk_assessment("low", 0, {}),
        concrete_transforms=[],
        strategies_ranked=[],
    )
def _collect_cycle_edges(unique_nodes: list, graph: dict,
                         symbol_map: dict) -> tuple[list, list]:
    cycle_edges: list = []
    all_symbols: list[str] = []
    for i in range(len(unique_nodes)):
        src = unique_nodes[i]
        dst = unique_nodes[(i + 1) % len(unique_nodes)]
        if dst in graph.get(src, set()):
            syms = list(symbol_map.get(src, {}).get(dst, []))
            cycle_edges.append({"from": src, "to": dst, "symbols": syms})
            all_symbols.extend(syms)
    return cycle_edges, all_symbols
def _build_symbol_analysis(cycle_edges: list, total_refs: int) -> dict:
    return {"cycle_edges": cycle_edges, "total_cross_references": total_refs}
def _build_risk_assessment(overall_risk: str, to_move: int,
                           per_impact: dict) -> dict:
    return {
        "overall_risk": overall_risk,
        "symbols_to_move": to_move,
        "per_symbol_impact": per_impact,
    }
def _collect_symbol_consumers(symbol_map: dict, sym: str,
                              provider: str) -> set[str]:
    consumers: set[str] = set()
    for mod, deps in symbol_map.items():
        dep_syms = deps.get(provider, ())
        if any(_imported_symbol_name(ds) == sym for ds in dep_syms):
            consumers.add(mod)
    return consumers
def _build_self_ref_transforms(self_mod: str, cycle_edges: list) -> list:
    transforms = [
        (f"# self-reference removal in {self_mod}.py"
         f" (解除 {self_mod} -> {self_mod} 自引用环)\n")
    ]
    for e in cycle_edges:
        if e["symbols"]:
            for s in dict.fromkeys(e["symbols"]):
                transforms.append(
                    f"BEFORE: import {self_mod} 并使用 {self_mod}.{s}"
                    f"（或 from {self_mod} import {s}）\n"
                    f"AFTER : 改为直接使用本模块符号 {s}，再删除自引用导入\n"
                )
        else:
            transforms.append(
                f"BEFORE: import {self_mod}"
                f"  (未使用的 import 自边,位于 {self_mod})\n"
                f"AFTER : 删除该语句（没有属性或模块对象使用证据）\n"
            )
    return transforms
def _suggest_self_ref_fix(unique_nodes: list, cycle_edges: list,
                          new_module: str) -> dict:
    self_mod = unique_nodes[0]
    self_syms = list(dict.fromkeys(
        _imported_symbol_name(s)
        for e in cycle_edges for s in e["symbols"]))
    edge_strengths = ([_edge_strength(cycle_edges[0], self_syms)]
                      if cycle_edges else [])
    ranked = _rank_cycle_strategies(
        1, new_module, 0, edge_strengths[0] if edge_strengths else None)
    wl_info = (f",自边 {len(self_syms)} 符号" if self_syms
               else ",纯 import 自边")
    action = ("先改自模块属性为直接符号引用，再删除自引用导入"
              if self_syms else "删除未使用的自引用导入")
    summary = (
        f"自引用环 {self_mod} -> {self_mod}{wl_info}:"
        f"{action},风险 low,"
        f"推荐 {ranked[0]['name']}（评分 {ranked[0]['score']}）"
    )
    transforms = _build_self_ref_transforms(self_mod, cycle_edges)
    return _fix_body(
        one_line_summary=summary,
        cycle_nodes=unique_nodes,
        cycle_length=len(unique_nodes),
        strategy=ranked[0]["name"],
        new_module_suggestion=None,
        weakest_link=edge_strengths[0] if edge_strengths else None,
        edge_strengths=edge_strengths,
        symbol_analysis=_build_symbol_analysis(
            cycle_edges, sum(len(edge["symbols"]) for edge in cycle_edges)),
        migration_plan=[],
        risk_assessment=_build_risk_assessment("low", 0, {}),
        concrete_transforms=transforms,
        strategies_ranked=ranked,
    )
def _build_migration_plan(cycle_edges: list, new_module: str,
                          symbol_map: dict | None = None) -> list:
    migration_plan = []
    for edge in cycle_edges:
        for sym in edge["symbols"]:
            migration_plan.append({
                "symbol": _imported_symbol_name(sym),
                "reference": sym,
                "from_module": edge["to"],
                "imported_by": edge["from"],
                "suggested_destination": new_module,
            })
    if symbol_map is not None:
        covered = {
            (p["imported_by"], p["from_module"], p["reference"])
            for p in migration_plan
        }
        for plan in tuple(migration_plan):
            sym = plan["symbol"]
            provider = plan["from_module"]
            for importer in sorted(
                    _collect_symbol_consumers(symbol_map, sym, provider)):
                for reference in symbol_map.get(importer, {}).get(provider, ()):
                    if _imported_symbol_name(reference) != sym:
                        continue
                    key = (importer, provider, reference)
                    if key in covered:
                        continue
                    covered.add(key)
                    migration_plan.append({
                        "symbol": sym,
                        "reference": reference,
                        "from_module": provider,
                        "imported_by": importer,
                        "suggested_destination": new_module,
                    })
    return migration_plan
def _edge_strength(edge: dict, symbols: list | None = None) -> dict:
    _syms = edge["symbols"] if symbols is None else symbols
    return {
        "edge": f"{edge['from']} -> {edge['to']}",
        "from": edge["from"],
        "to": edge["to"],
        "symbol_count": len({_imported_symbol_name(s) for s in _syms}),
        "symbols": _syms,
    }
def _rank_edge_strengths(cycle_edges: list) -> tuple[list, dict | None]:
    edge_strengths = [_edge_strength(edge) for edge in cycle_edges]
    edge_strengths.sort(key=lambda x: (x["symbol_count"], x["edge"]))
    weakest_link = edge_strengths[0] if edge_strengths else None
    return edge_strengths, weakest_link
def _build_per_symbol_impact(migration_plan: list, symbol_map: dict) -> dict:
    providers_by_name: dict[str, set[str]] = {}
    for plan in migration_plan:
        providers_by_name.setdefault(plan["symbol"], set()).add(
            plan["from_module"])
    consumer_sets: dict[str, set[str]] = {}
    for plan in migration_plan:
        sym = plan["symbol"]
        provider = plan["from_module"]
        key = (f"{provider}.{sym}"
               if len(providers_by_name[sym]) > 1 else sym)
        consumer_sets.setdefault(key, set()).update(
            _collect_symbol_consumers(symbol_map, sym, provider))
    return {
        key: {
            "consumer_count": len(consumers),
            "consumers": sorted(consumers)[:10],
        }
        for key, consumers in consumer_sets.items()
    }
def _summarize_multi_node(fix: _CycleFixRequest, to_move: int,
                          overall_risk: str, ranked: list, weakest_link) -> str:
    cycle_len = fix.cycle_len
    new_module = fix.new_module
    if weakest_link and not weakest_link["symbols"]:
        return (
            f"循环 {cycle_len} 节点,最弱链接 {weakest_link['edge']} 为纯 import 边:"
            f"删除该 import 语句即断环,风险 {overall_risk},"
            f"推荐 {ranked[0]['name']}（评分 {ranked[0]['score']}）"
        )
    wl_info = ""
    if weakest_link:
        wl_info = f",最弱链接 {weakest_link['edge']} ({weakest_link['symbol_count']}符号)"
    return (
        f"循环 {cycle_len} 节点{wl_info}"
        f" -> {new_module}:移动 {to_move} 个符号,风险 {overall_risk},"
        f"推荐 {ranked[0]['name']}（评分 {ranked[0]['score']}）"
    )
def _suggest_multi_node_fix(fix: _CycleFixRequest) -> dict:
    unique_nodes = fix.unique_nodes
    cycle_len = fix.cycle_len
    cycle_edges = fix.cycle_edges
    all_symbols = fix.all_symbols
    new_module = fix.new_module
    symbol_map = fix.symbol_map
    migration_plan = _build_migration_plan(cycle_edges, new_module, symbol_map)
    edge_strengths, weakest_link = _rank_edge_strengths(cycle_edges)
    to_move = len({
        (plan["from_module"], plan["symbol"]) for plan in migration_plan
    })
    overall_risk = "low" if to_move <= 3 else ("medium" if to_move <= 8 else "high")
    per_impact = _build_per_symbol_impact(migration_plan, symbol_map)
    ranked = _rank_cycle_strategies(cycle_len, new_module, to_move, weakest_link)
    transforms = _build_concrete_transforms(new_module, unique_nodes, all_symbols,
                                            migration_plan, weakest_link)
    summary = _summarize_multi_node(
        fix, to_move, overall_risk, ranked, weakest_link)
    return _fix_body(
        one_line_summary=summary,
        cycle_nodes=unique_nodes,
        cycle_length=cycle_len,
        strategy=ranked[0]["name"],
        new_module_suggestion=new_module,
        weakest_link=weakest_link,
        edge_strengths=edge_strengths,
        symbol_analysis=_build_symbol_analysis(
            cycle_edges, len(migration_plan)),
        migration_plan=migration_plan,
        risk_assessment=_build_risk_assessment(overall_risk, to_move, per_impact),
        concrete_transforms=transforms,
        strategies_ranked=ranked,
    )
def _common_parent(*modules: str) -> str:
    if not modules:
        return ""
    parts_list = [m.split(".") for m in modules if m]
    if not parts_list:
        return ""
    common: list[str] = []
    for parts in zip(*parts_list, strict=False):
        first = parts[0]
        if all(p == first for p in parts):
            common.append(first)
        else:
            break
    return ".".join(common)
def _match_still_existing(current_cycles: list, unique_cycle: list) -> tuple[bool, dict | None]:
    target_key = _normalize_cycle_key(unique_cycle)
    for c in current_cycles:
        if _normalize_cycle_key(c["cycle"]) == target_key:
            return True, c
    return False, None
def _edge_status_checks(unique_cycle: list, graph: dict, symbol_map: dict) -> list:
    edge_checks = []
    for i in range(len(unique_cycle)):
        src = unique_cycle[i]
        dst = unique_cycle[(i + 1) % len(unique_cycle)]
        edge_exists = dst in graph.get(src, set())
        syms = symbol_map.get(src, {}).get(dst, [])
        edge_checks.append({
            "edge": f"{src} -> {dst}",
            "exists": edge_exists,
            "remaining_symbols": syms if edge_exists else [],
            "status": "still_present" if edge_exists else "removed",
        })
    return edge_checks
def _normalize_cycle_key(cycle) -> tuple:
    seq = _cycle_nodes(cycle)
    if len(seq) <= 1:
        return tuple(seq)
    return min(tuple(seq[i:] + seq[:i]) for i in range(len(seq)))
def _invalid_cycle_verdict(
        current_cycles: list, started_at: float,
        error: str = "invalid_cycle: 至少需要一个有效模块名") -> dict:
    return {
        "resolved": False,
        "still_exists": False,
        "matched_cycle": None,
        "current_total_cycles": len(current_cycles),
        "edge_checks": [],
        "removed_edges": 0,
        "remaining_edges": 0,
        "fully_resolved": False,
        "partially_resolved": False,
        "delta": {
            "edges_before": 0,
            "edges_removed": 0,
            "edges_remaining": 0,
            "removed_list": [],
            "remaining_list": [],
        },
        "error": error,
        "verification_time": round(time.time() - started_at, 3),
    }
def module_name_under_root(fpath: str, skill_root: Path) -> str | None:
    try:
        rel = Path(fpath).resolve().relative_to(Path(skill_root).resolve())
    except (ValueError, OSError) as e:
        log_swallowed(
            __name__, e, context=f"module_name_under_root:{type(e).__name__}")
        return None
    suffixless = rel.with_suffix("") if rel.name else rel
    parts = suffixless.parts
    root_name = Path(skill_root).resolve().name
    if not parts:
        return root_name or None
    if parts[-1] == "__init__":
        parts = parts[:-1]
        if not parts:
            return root_name or None
    return ".".join(parts)
def _attribute_access_chain(
        node: ast.Attribute) -> tuple[list[str], ast.Name] | None:
    parts: list[str] = []
    cur: ast.AST = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if not isinstance(cur, ast.Name):
        return None
    parts.append(cur.id)
    parts.reverse()
    return parts, cur
def _import_destination_candidates(raw: str, destinations) -> list[str]:
    return sorted(
        dest for dest in destinations
        if (dest == raw or dest.endswith(f".{raw}")
            or raw.endswith(f".{dest}")))
def _import_destination(raw: str, destinations: set[str]) -> str | None:
    if raw in destinations:
        return raw
    candidates = _import_destination_candidates(raw, destinations)
    return candidates[0] if len(candidates) == 1 else None
def _record_bound_module_usage(
        symbols: list, binding: str, prefix: tuple[str, ...],
        import_path: str, chains: list, attribute_bases: set[int],
        tree: ast.AST, name_resolver: ScopeNameResolver,
        plain_import_prefixes: dict[str, set[tuple[str, ...]]]) -> None:
    module_object_used = False
    for parts, base in chains:
        if (not parts or parts[0] != binding
                or name_resolver.import_path(base) != import_path):
            continue
        chain_prefix = tuple(parts[:len(prefix)])
        if chain_prefix != prefix:
            consumed_by_sibling = any(
                sibling != prefix
                and tuple(parts[:len(sibling)]) == sibling
                for sibling in plain_import_prefixes.get(binding, ()))
            if not consumed_by_sibling:
                module_object_used = True
            continue
        # 同一顶层绑定可有多条非别名点式导入；最长匹配前缀
        # 才是属性链所有者，短前缀不能把子模块名记作业务符号。
        if any(
                len(sibling) > len(prefix)
                and tuple(parts[:len(sibling)]) == sibling
                for sibling in plain_import_prefixes.get(binding, ())):
            continue
        if len(parts) == len(prefix):
            module_object_used = True
            continue
        symbol = parts[len(prefix)]
        if symbol not in symbols:
            symbols.append(symbol)
    if module_object_used and _MODULE_OBJECT_REFERENCE not in symbols:
        symbols.append(_MODULE_OBJECT_REFERENCE)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, ast.Load)
                and node.id == binding
                and id(node) not in attribute_bases
                and name_resolver.import_path(node) == import_path):
            if _MODULE_OBJECT_REFERENCE not in symbols:
                symbols.append(_MODULE_OBJECT_REFERENCE)
            break
def _from_import_source(statement: ast.ImportFrom) -> str:
    if statement.level:
        return "." * statement.level + (statement.module or "")
    return statement.module or ""
def _record_from_module_usage(
        statement: ast.ImportFrom, module: str, import_graph: dict,
        symbol_map: dict, chains: list, attribute_bases: set[int],
        tree: ast.AST, name_resolver: ScopeNameResolver,
        plain_import_prefixes: dict[str, set[tuple[str, ...]]]) -> None:
    """记录 ``from <pkg> import <submodule>`` 的模块属性使用证据。

    ``ast.ImportFrom`` 的别名同样可能绑定**子模块对象**（``from . import y``、
    ``from pkg import sub``），只统计 ``ast.Import`` 会让这些边在符号图上恒为空，
    进而被 ``suggest_fix`` 误判为「纯 import 边、无符号级依赖」并建议删除仍在
    使用的导入。这里按图边确认别名确实指向项目内模块后，复用与 ``import``
    相同的属性链归集；无法确定归属时保持空证据（保守）。
    """
    source = _from_import_source(statement)
    separator = "" if source.endswith(".") else "."
    destinations = import_graph.get(module, set())
    for alias in statement.names:
        if alias.name == "*":
            continue
        destination = _import_destination(alias.name, destinations)
        if destination is None or destination not in import_graph:
            continue
        binding = alias.asname or alias.name
        symbols = symbol_map.setdefault(module, {}).setdefault(
            destination, [])
        _record_bound_module_usage(
            symbols, binding, (binding,),
            f"{source}{separator}{alias.name}",
            chains, attribute_bases, tree, name_resolver,
            plain_import_prefixes)
def _merge_module_import_usage(
        root: str, import_graph: dict, symbol_map: dict, *,
        include_tests: bool,
        parse_failures: list[str] | None = None) -> dict:
    for fpath, module, _pkg_segs in _iter_project_modules(
            root, include_tests=include_tests):
        if module not in import_graph:
            continue
        _content, tree = parse_py_file(fpath)
        if tree is None:
            if parse_failures is not None:
                parse_failures.append(fpath)
            continue
        name_resolver = ScopeNameResolver(_content, fpath, tree, set())
        attribute_nodes = [
            node for node in walk_nodes(tree) if isinstance(node, ast.Attribute)]
        nested_attributes = {
            id(node.value) for node in attribute_nodes
            if isinstance(node.value, ast.Attribute)
        }
        attribute_bases: set[int] = set()
        chains: list[tuple[list[str], ast.Name]] = []
        for node in attribute_nodes:
            chain = _attribute_access_chain(node)
            if chain is None:
                continue
            attribute_bases.add(id(chain[1]))
            if id(node) not in nested_attributes:
                chains.append(chain)
        plain_import_prefixes: dict[str, set[tuple[str, ...]]] = {}
        for statement in walk_nodes(tree):
            if isinstance(statement, ast.Import):
                for alias in statement.names:
                    if alias.asname is None:
                        prefix = tuple(alias.name.split("."))
                        plain_import_prefixes.setdefault(
                            prefix[0], set()).add(prefix)
        for statement in walk_nodes(tree):
            if isinstance(statement, ast.ImportFrom):
                if any(alias.name == "*" for alias in statement.names):
                    destinations = symbol_map.get(module, {})
                    if statement.module:
                        wildcard_targets = _import_destination_candidates(
                            statement.module, destinations)
                    elif statement.level > 0:
                        package_parts = module.split(".")
                        if os.path.basename(fpath) != "__init__.py":
                            package_parts.pop()
                        target_len = len(package_parts) - statement.level + 1
                        raw_target = (".".join(package_parts[:target_len])
                                      if target_len > 0 else "")
                        wildcard_targets = _import_destination_candidates(
                            raw_target, destinations)
                    else:
                        wildcard_targets = []
                    for destination in wildcard_targets:
                        symbols = symbol_map[module][destination]
                        if _WILDCARD_IMPORT_REFERENCE not in symbols:
                            symbols.append(_WILDCARD_IMPORT_REFERENCE)
                    continue
                _record_from_module_usage(
                    statement, module, import_graph, symbol_map, chains,
                    attribute_bases, tree, name_resolver,
                    plain_import_prefixes)
                continue
            if not isinstance(statement, ast.Import):
                continue
            for alias in statement.names:
                destinations = import_graph.get(module, set())
                destination = _import_destination(alias.name, destinations)
                if destination is None:
                    for candidate in _import_destination_candidates(
                            alias.name, destinations):
                        symbols = symbol_map.setdefault(module, {}).setdefault(
                            candidate, [])
                        if _MODULE_OBJECT_REFERENCE not in symbols:
                            symbols.append(_MODULE_OBJECT_REFERENCE)
                    continue
                import_path = (alias.name if alias.asname
                               else alias.name.split(".", 1)[0])
                prefix = ((alias.asname,) if alias.asname
                          else tuple(alias.name.split(".")))
                symbols = symbol_map.setdefault(module, {}).setdefault(
                    destination, [])
                _record_bound_module_usage(
                    symbols, prefix[0], prefix, import_path, chains,
                    attribute_bases, tree, name_resolver,
                    plain_import_prefixes)
    return symbol_map
class CircularDependencyResolver:
    def __init__(self) -> None:
        self._root_dir: str | None = None
        self._import_graph = {}
        self._symbol_import_map = {}
        self._source_parse_failures: list[str] = []
        self._prev_cycles = []
        self._prev_cycles_root: str | None = None
        self._prev_cycles_kwargs: dict | None = None
        self._prev_signatures = {}
        self._prev_signatures_root = None
        self._detect_kwargs: dict = dict(_DEFAULT_DETECT_KWARGS)
    def detect(self, root_dir: str,
               include_tests: bool = _DEFAULT_DETECT_KWARGS["include_tests"],
               allow_bare: bool = _DEFAULT_DETECT_KWARGS["allow_bare"],
               full_cycles: bool = _DEFAULT_DETECT_KWARGS["full_cycles"]) -> list[dict]:
        root = _existing_root_arg(root_dir)
        if not root:
            logger.warning(
                "[Antipattern] 循环依赖检测跳过：根目录缺失/非法 %r", root_dir)
            self._symbol_import_map = {}
            self._import_graph = {}
            self._source_parse_failures = []
            self._root_dir = None
            return []
        include_tests = _coerce_bool(
            include_tests, _DEFAULT_DETECT_KWARGS["include_tests"])
        allow_bare = _coerce_bool(
            allow_bare, _DEFAULT_DETECT_KWARGS["allow_bare"])
        full_cycles = _coerce_bool(
            full_cycles, _DEFAULT_DETECT_KWARGS["full_cycles"])
        import_graph, normalized_symbol_map = build_normalized_import_graph(
            root, include_tests=include_tests, allow_bare=allow_bare)
        parse_failures: list[str] = []
        normalized_symbol_map = _merge_module_import_usage(
            root, import_graph, normalized_symbol_map,
            include_tests=include_tests, parse_failures=parse_failures)
        cycles = (find_graph_cycles(import_graph) if not full_cycles
                  else enumerate_all_cycles(import_graph))
        self._symbol_import_map = normalized_symbol_map
        self._import_graph = import_graph
        self._source_parse_failures = parse_failures
        self._root_dir = root
        self._detect_kwargs = {
            "include_tests": include_tests,
            "allow_bare": allow_bare,
            "full_cycles": full_cycles,
        }
        return [{"cycle": c,
                 "length": len(set(c)),
                 "symbol_count": _count_cycle_symbols(c, normalized_symbol_map)}
                for c in cycles]
    def _rescan(self, root_dir: str | None, *,
                full_cycles: bool | None = None) -> list[dict]:
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            logger.warning("[Antipattern] 环复扫跳过：无可用根目录")
            return []
        kwargs = dict(self._detect_kwargs)
        if full_cycles is not None:
            kwargs["full_cycles"] = full_cycles
        return self.detect(root, **kwargs)
    def _resolve_analysis_state(
            self, root_dir: str | None,
            parse_failures: list[str] | None = None) -> tuple[dict, dict]:
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            logger.warning("[Antipattern] 环修复建议跳过：无可用导入图")
            return {}, {}
        if (self._root_dir
                and os.path.normpath(root) == os.path.normpath(self._root_dir)):
            if parse_failures is not None:
                parse_failures.extend(self._source_parse_failures)
            return self._import_graph, self._symbol_import_map
        graph, symbol_map = build_normalized_import_graph(
            root,
            include_tests=self._detect_kwargs["include_tests"],
            allow_bare=self._detect_kwargs["allow_bare"])
        return graph, _merge_module_import_usage(
            root, graph, symbol_map,
            include_tests=self._detect_kwargs["include_tests"],
            parse_failures=parse_failures)
    def suggest_fix(self, cycle: list[str], root_dir: str | None = None) -> dict:
        unique_nodes = _cycle_nodes(cycle)
        if not unique_nodes:
            return _build_degenerate_fix(unique_nodes)
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            return _build_degenerate_fix(
                unique_nodes,
                summary="无导入图证据（需先 detect 或提供 root_dir），"
                        "不产出修复建议")
        parse_failures: list[str] = []
        _graph, symbol_map = self._resolve_analysis_state(
            root, parse_failures=parse_failures)
        if not _graph and not symbol_map:
            return _build_degenerate_fix(
                unique_nodes,
                summary="无导入图证据（需先 detect 或提供 root_dir），"
                        "不产出修复建议")
        if parse_failures:
            return _build_degenerate_fix(
                unique_nodes,
                summary=f"源码解析失败 {len(parse_failures)} 个文件，"
                        "符号消费者证据不完整，不产出修复建议")
        cycle_len = len(unique_nodes)
        parent = _common_parent(*unique_nodes)
        new_module = f"{parent}._shared" if parent else "_shared_interface"
        cycle_edges, all_symbols = _collect_cycle_edges(
            unique_nodes, _graph, symbol_map)
        if len(cycle_edges) != cycle_len:
            return _build_degenerate_fix(
                unique_nodes,
                summary="环边证据不完整或环已消除,不产出修复建议")
        if any(_WILDCARD_IMPORT_REFERENCE in edge["symbols"]
               for edge in cycle_edges):
            return _build_degenerate_fix(
                unique_nodes,
                summary="通配符导入缺少可枚举的符号级依赖证据，"
                        "不产出删除导入或自动迁移建议")
        if any(_MODULE_OBJECT_REFERENCE in edge["symbols"]
               for edge in cycle_edges):
            return _build_degenerate_fix(
                unique_nodes,
                summary="模块对象被整体引用，缺少安全的符号级迁移证据，"
                        "不产出删除导入或自动迁移建议")
        if any(_imported_symbol_name(symbol) in _MODULE_METADATA_REFERENCES
               for edge in cycle_edges for symbol in edge["symbols"]):
            return _build_degenerate_fix(
                unique_nodes,
                summary="模块元数据属性不是可迁移业务符号，"
                        "不产出删除导入或自动迁移建议")
        providers_by_symbol: dict[str, set[str]] = {}
        for edge in cycle_edges:
            for reference in edge["symbols"]:
                providers_by_symbol.setdefault(
                    _imported_symbol_name(reference), set()).add(edge["to"])
        conflicting_symbols = sorted(
            symbol for symbol, providers in providers_by_symbol.items()
            if len(providers) > 1)
        if conflicting_symbols:
            return _build_degenerate_fix(
                unique_nodes,
                summary=("同名符号来自不同模块（"
                         f"{', '.join(conflicting_symbols)}），"
                         "缺少无冲突迁移证据，不产出自动迁移建议"))
        if cycle_len == 1:
            return _suggest_self_ref_fix(unique_nodes, cycle_edges, new_module)
        return _suggest_multi_node_fix(_CycleFixRequest(
            unique_nodes, cycle_len, cycle_edges,
            all_symbols, new_module, symbol_map))
    def verify_cycle_resolved(self, cycle: list[str], root_dir: str | None = None) -> dict:
        t0 = time.time()
        unique_cycle = _cycle_nodes(cycle)
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            return _invalid_cycle_verdict(
                [], t0,
                error="missing_import_graph: 需先 detect 或提供 root_dir")
        try:
            current_cycles = self._rescan(root)
        except (OSError, SyntaxError, ValueError, TypeError,
                RecursionError) as e:
            logger.warning("[Antipattern] 环复扫失败: %s", e)
            return _invalid_cycle_verdict(
                [], t0, error=f"rescan_failed: {type(e).__name__}")
        if not unique_cycle:
            return _invalid_cycle_verdict(current_cycles, t0)
        if self._source_parse_failures:
            return _invalid_cycle_verdict(
                current_cycles, t0, error=_RESCAN_PARSE_ERROR)
        still_exists, matched_cycle = _match_still_existing(
            current_cycles, unique_cycle)
        edge_checks = _edge_status_checks(
            unique_cycle, self._import_graph, self._symbol_import_map)
        removed_edges = [e for e in edge_checks if not e["exists"]]
        remaining_edges = [e for e in edge_checks if e["exists"]]
        if edge_checks and not removed_edges:
            still_exists = True
        return {
            "resolved": not still_exists,
            "still_exists": still_exists,
            "matched_cycle": matched_cycle,
            "current_total_cycles": len(current_cycles),
            "edge_checks": edge_checks,
            "removed_edges": len(removed_edges),
            "remaining_edges": len(remaining_edges),
            "fully_resolved": not remaining_edges,
            "partially_resolved": len(removed_edges) > 0 and len(remaining_edges) > 0,
            "delta": {
                "edges_before": len(unique_cycle),
                "edges_removed": len(removed_edges),
                "edges_remaining": len(remaining_edges),
                "removed_list": [e["edge"] for e in removed_edges],
                "remaining_list": [e["edge"] for e in remaining_edges],
            },
            "verification_time": round(time.time() - t0, 3),
        }
    def snapshot_cycles(self, root_dir: str | None = None) -> dict:
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            logger.warning("[Antipattern] 环快照跳过：无可用根目录")
            return {"snapshot_cycles": 0, "error": "missing_root_dir"}
        current_cycles = self._rescan(root, full_cycles=True)
        if self._source_parse_failures:
            return {"snapshot_cycles": 0, "error": _RESCAN_PARSE_ERROR}
        self._prev_cycles = current_cycles
        self._prev_cycles_root = root
        self._prev_cycles_kwargs = dict(self._detect_kwargs)
        return {'snapshot_cycles': len(self._prev_cycles)}
    def verify_no_new_cycles(self, root_dir: str | None = None) -> dict:
        prev_cycles = self._prev_cycles
        root = _root_or_stored(
            root_dir, self._prev_cycles_root or self._root_dir)
        if not root:
            return {
                "no_new_cycles": False,
                "new_cycles": [],
                "resolved_cycles": [],
                "prev_total": len(prev_cycles),
                "curr_total": 0,
                "delta": 0,
                "error": "missing_root_dir",
            }
        if self._prev_cycles_root is None or self._prev_cycles_kwargs is None:
            return {
                "no_new_cycles": False,
                "new_cycles": [],
                "resolved_cycles": [],
                "prev_total": len(prev_cycles),
                "curr_total": 0,
                "delta": 0,
                "error": "missing_cycle_snapshot",
            }
        if _path_identity(root) != _path_identity(self._prev_cycles_root):
            return {
                "no_new_cycles": False,
                "new_cycles": [],
                "resolved_cycles": [],
                "prev_total": len(prev_cycles),
                "curr_total": 0,
                "delta": 0,
                "error": "cycle_snapshot_root_mismatch",
            }
        self._detect_kwargs = dict(self._prev_cycles_kwargs)
        current_cycles = self._rescan(root, full_cycles=True)
        if self._source_parse_failures:
            return {
                "no_new_cycles": False,
                "new_cycles": [],
                "resolved_cycles": [],
                "prev_total": len(prev_cycles),
                "curr_total": 0,
                "delta": 0,
                "error": _RESCAN_PARSE_ERROR,
            }
        prev_set = {_normalize_cycle_key(c["cycle"]) for c in prev_cycles}
        curr_set = {_normalize_cycle_key(c["cycle"]) for c in current_cycles}
        new_cycles = sorted(curr_set - prev_set)
        resolved_cycles = sorted(prev_set - curr_set)
        return {
            "no_new_cycles": not new_cycles,
            "new_cycles": [list(c) for c in new_cycles],
            "resolved_cycles": [list(c) for c in resolved_cycles],
            "prev_total": len(prev_cycles),
            "curr_total": len(current_cycles),
            "delta": len(current_cycles) - len(prev_cycles),
        }
    def snapshot_signatures(self, modules: list[str], root_dir: str | None = None) -> dict:
        _modules = _coerce_str_seq(modules)
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            logger.warning("[Antipattern] 签名快照跳过：无可用根目录")
            return {"snapshot_modules": 0, "signatures": {},
                    "error": "missing_root_dir"}
        sigs = {}
        for module in _modules:
            module_sigs, _err = load_module_signatures(root, module)
            if module_sigs is None:
                continue
            sigs[module] = module_sigs
        self._prev_signatures = sigs
        self._prev_signatures_root = root
        return {'snapshot_modules': len(sigs), 'signatures': sigs}
    def _resolve_verify_root(self, root_dir: str | None) -> str | None:
        if root_dir is not None:
            return _existing_root_arg(root_dir)
        return self._prev_signatures_root or self._root_dir
    def verify_public_signatures(self, modules: list[str], root_dir: str | None = None,
                                  prev_signatures: dict | None = None) -> dict:
        _modules = _coerce_str_seq(modules)
        root = self._resolve_verify_root(root_dir)
        if not root:
            logger.warning("[Antipattern] 公面签名核验跳过：无可用根目录")
            return {
                "signatures_intact": False,
                "changed": [],
                "unchanged_count": 0,
                "modules_checked": len(_modules),
                "error": "missing_root_dir",
            }
        prev_sigs = normalize_prev_signatures(
            prev_signatures if prev_signatures is not None
            else self._prev_signatures)
        changed: list[dict] = []
        unchanged_count = 0
        for module in _modules:
            module_changed, module_unchanged = diff_module_signatures(
                module, prev_sigs, root)
            changed.extend(module_changed)
            unchanged_count += module_unchanged
        return {
            "signatures_intact": not changed,
            "changed": changed,
            "unchanged_count": unchanged_count,
            "modules_checked": len(_modules),
        }
    def verify_edge_removed(self, from_module: str, to_module: str, root_dir: str | None = None) -> dict:
        root = _root_or_stored(root_dir, self._root_dir)
        if not root:
            logger.warning("[Antipattern] 导入边核验跳过：无可用根目录")
            return {"removed": False, "still_imports": [],
                    "source_file": None, "import_count": 0,
                    "error": "missing_root_dir"}
        return check_import_edge_removed(from_module, to_module, root)
def suggest_circular_fixes(root_dir: str,
                           max_cycles: int = _DEFAULT_MAX_CYCLES) -> list[dict]:
    root = _existing_root_arg(root_dir)
    if not root:
        logger.warning("[Antipattern] 循环修复建议跳过：根目录缺失/非法")
        return []
    resolver = CircularDependencyResolver()
    cycles = resolver.detect(root)
    results = []
    for item in cycles[:_normalize_cycle_limit(max_cycles)]:
        suggestion = resolver.suggest_fix(item["cycle"], root)
        results.append({
            "cycle": item["cycle"],
            "cycle_length": suggestion["cycle_length"],
            "suggestion": suggestion,
        })
    return results
def _read_boundary_caches(analyzer: Any) -> tuple[Any, Any, Any, Any]:
    try:
        src_cache, ast_cache = analyzer.get_shared_caches()
        import_edges, import_nodes = analyzer.get_import_indexes()
    except (AttributeError, OSError, SyntaxError, ValueError, TypeError) as e:
        logger.warning(
            "[Boundary] 共享缓存获取失败（检测方回退自行解析）: %s", e)
        return None, None, None, None
    return src_cache, ast_cache, import_edges, import_nodes
def _suggest_cycle_fixes(context: dict[str, Any], skill_dir: str) -> None:
    _circular = context.get("circular_imports")
    if (not isinstance(_circular, Mapping)
            or not _circular.get("module_level_cycles")):
        return
    try:
        _suggestions = suggest_circular_fixes(str(skill_dir))
        if _suggestions:
            context["circular_fix_suggestions"] = _suggestions
        logger.info("[Boundary] 已生成 %d 条循环依赖修复建议",
                  len(_suggestions))
    except (ImportError, OSError, SyntaxError, RecursionError,
            ValueError, TypeError) as e:
        logger.warning("[Boundary] 循环修复建议生成失败: %s", e)
def _report_cross_skill_imports(skill_dir: str, ast_cache: Any,
                                import_nodes: Any,
                                context: dict[str, Any]) -> None:
    try:
        cross = CrossSkillDetector().detect(
            str(skill_dir), ast_cache=ast_cache,
            import_nodes=import_nodes)
        if isinstance(cross, list) and cross:
            context["cross_skill_imports"] = cross
            logger.warning("[Boundary] 检测到 %d 处跨技能导入（C7 边界违规）",
                         len(cross))
    except (OSError, SyntaxError, ValueError, TypeError) as e:
        logger.warning("[Boundary] 跨技能导入检测失败: %s", e)
def _detect_cycle_reports(analyzer: Any, skill_dir: str,
                          context: dict[str, Any], src_cache: Any,
                          ast_cache: Any, import_edges: Any) -> None:
    try:
        stratified = detect_circular_imports_stratified(
            analyzer.file_analyses,
            source_cache=src_cache,
            ast_cache=ast_cache,
            import_edges=import_edges,
        )
        if not isinstance(stratified, Mapping):
            logger.warning(
                "[Boundary] 分层环检测返回异形容器，按空结果降级: %r",
                type(stratified).__name__)
            return
        context["circular_imports"] = dict(stratified)
        _module_cycles = stratified.get("module_level_cycles") or []
        if _module_cycles:
            logger.warning(
                "[Boundary] 检测到 %d 个模块级循环导入（危险环，必须消除）",
                len(_module_cycles))
    except (AttributeError, OSError, SyntaxError, ValueError, KeyError,
            TypeError) as e:
        logger.warning("[Boundary] 循环导入检测失败: %s", e)
        return
    _suggest_cycle_fixes(context, skill_dir)
def run_boundary_coupling_diagnostics(analyzer: Any, skill_dir: str,
                                      context: dict[str, Any]) -> None:
    if not isinstance(context, dict):
        logger.warning(
            "[Boundary] 边界耦合诊断跳过：context 非 dict %r",
            type(context).__name__)
        return
    root = _existing_root_arg(skill_dir)
    if not root:
        logger.warning("[Boundary] 边界耦合诊断：技能根缺失/非法 %r", skill_dir)
    src_cache, ast_cache, import_edges, import_nodes = (
        _read_boundary_caches(analyzer))
    _detect_cycle_reports(
        analyzer, root or "", context, src_cache, ast_cache, import_edges)
    _report_cross_skill_imports(root or "", ast_cache, import_nodes, context)
_CYCLE_CAPABILITIES: tuple[tuple[str, str, str, str], ...] = (
    ("diag_antipattern_flow_govern", "CircularDependencyResolver.detect",
     "扫描入口",
     "目录级全量环扫描：include_tests/allow_bare 开审计模式，full_cycles=True 全量枚举简单环"),
    ("diag_antipattern_flow_govern", "suggest_circular_fixes",
     "修复建议",
     "对检出环逐个产出符号级修复建议（策略排序/迁移计划/风险评估，只产建议不自动改码，供 AI 审核执行）"),
    ("diag_merge_safety", "find_graph_cycles",
     "拓扑域检测",
     "已归一化邻接表的 SCC 代表环检出（每 SCC 一条确定性代表路径，供 D20/拓扑环键消费）"),
    ("diag_merge_safety", "enumerate_all_cycles",
     "全量枚举",
     "简单环全量枚举（指数级；仅 full_cycles 审计模式使用）"),
    ("diag_merge_safety", "detect_circular_imports",
     "重构域检测",
     "基于 FileAnalysis 导入图的 SCC 完备环检出（每环一条确定性代表路径）"),
    ("diag_merge_safety", "detect_circular_imports_stratified",
     "分层检测",
     "模块级危险环与函数级懒导入安全环分层输出（module_level_cycles / lazy_only_cycles）"),
    ("diag_merge_safety", "choose_cycle_fix_priority",
     "优先级决策",
     "按环消除收益选定修复方案优先级常量（结构重排/类型检查/共享抽取/懒导入）"),
    ("build_import_reference", "guard_circular",
     "写前守卫",
     "G12 循环导入守卫：ADD_IMPORT/MODIFY_CODE/REFACTOR 操作前拦截（GuardResult），防引入新环"),
    ("diag_dependency_analyzer", "DependencyAnalyzer.cycle_detection",
     "分析通道",
     "依赖分析域 Tarjan SCC 环检出 → D9-CYCLE findings + 环数据（供依赖健康度评分消费）"),
    ("runtime_scope", "tarjan_scc",
     "算法底座",
     "运行时范围 L0 底座迭代版 Tarjan 强连通分量算法；环判定经 DependencyGraph.has_cycle（多节点 SCC 或自环）"),
)
def list_cycle_capabilities() -> list[dict[str, str]]:
    return [
        {"module": mod, "symbol": sym, "kind": kind, "summary": summary}
        for mod, sym, kind, summary in _CYCLE_CAPABILITIES
    ]
def _fallback_scan_issues(files: list, detector: SignalDetector) -> list[dict]:
    issues: list[dict] = []
    _seen_paths: set[str] = set()
    for fpath in files:
        if not is_scan_py_name(os.path.basename(fpath)):
            continue
        _path_key = _path_identity(fpath)
        if _path_key in _seen_paths:
            continue
        _seen_paths.add(_path_key)
        _t0 = time.perf_counter()
        file_issues = fallback_scan_file(fpath)
        if not isinstance(file_issues, (list, tuple)):
            if file_issues is not None:
                logger.debug(
                    "real_antipattern_scan: 回退扫描器返回异形容器 %s: %r",
                    fpath, type(file_issues).__name__)
            continue
        _elapsed_ms = (time.perf_counter() - _t0) * 1000
        detector.check_performance(fpath, _elapsed_ms)
        issues.extend(file_issues)
    return issues
def _scan_engine_roots(files: list, detector: SignalDetector) -> list[dict] | None:
    issues: list[dict] = []
    try:
        for parent_dir, file_set in _group_files_by_parent_dir(files).items():
            _t0 = time.perf_counter()
            scan_result = scan_anti_patterns(parent_dir)
            if not isinstance(scan_result, dict):
                logger.debug(
                    "real_antipattern_scan: 引擎返回非 dict 结果 %s，回退到本地扫描器",
                    type(scan_result).__name__)
                return None
            _elapsed_ms = (time.perf_counter() - _t0) * 1000
            detector.check_performance(parent_dir, _elapsed_ms)
            issues.extend(_scan_result_issues(scan_result, parent_dir, file_set))
    except (ImportError, AttributeError, OSError, SyntaxError, ValueError,
            TypeError, KeyError, RecursionError) as _e:
        log_swallowed(
            __name__, _e, context="real_antipattern_scan:engine_fallback")
        return None
    return issues
_SCAN_DETECTOR = SignalDetector()
def _report_performance_signals(detector: SignalDetector) -> None:
    for signal in detector.drain_triggered():
        logger.warning(
            "[AntipatternScanner] %s (source=%s, strength=%.2f)",
            signal.description, signal.source, signal.strength,
        )
def real_antipattern_scan(files: list) -> list[dict]:
    detector = _SCAN_DETECTOR
    _files = _coerce_py_files(files)
    issues = _scan_engine_roots(_files, detector)
    if issues is None:
        issues = _fallback_scan_issues(_files, detector)
    _report_performance_signals(detector)
    return issues
_ANTIPATTERN_CATEGORIES = (
    frozenset(AntiPatternEliminator._LIST_CATEGORIES) | {"C10_fragments"})
def _issue_first_function_field(iss: dict, key: str):
    funcs = iss.get("functions")
    if isinstance(funcs, list) and funcs:
        f0 = funcs[0]
        if isinstance(f0, dict):
            return f0.get(key)
    return None
def _normalize_antipattern_list_item(iss: dict, cat: str,
                                     skill_dir: str = "") -> None:
    iss["file"] = (_text_or_fspath(iss.get("file"))
                   or _text_or_fspath(iss.get("filepath"))
                   or _text_or_fspath(
                       _issue_first_function_field(iss, "file")))
    if not iss["file"] and isinstance(iss.get("cycle"), (list, tuple)):
        iss["file"] = _text_or_fspath(skill_dir)
    iss["line"] = _norm_issue_line(
        iss.get("line"), _issue_first_function_field(iss, "line"))
    iss["rule_id"] = _norm_issue_str(iss.get("rule_id")) or cat
    iss["severity"] = _map_severity(iss.get("severity"))
    if not _norm_issue_str(iss.get("message")):
        iss["message"] = _antipattern_detail(iss, cat)
    _conf = _confidence_or_none(iss.get("confidence"))
    iss["confidence"] = 0.75 if _conf is None else _conf
    iss["category"] = _norm_issue_str(iss.get("category")) or "antipattern"
def _fragment_category_issue(items: dict, cat: str,
                             skill_dir: str) -> dict | None:
    if not _slot_needs_attention(items):
        return None
    _msg = (f"目录碎片化率 {items.get('fragmentation_rate')} 超阈值，"
            f"小文件 {items.get('small_file_count', 0)} 个")
    _merge_plan = items.get("merge_plan")
    if isinstance(_merge_plan, (list, tuple)) and _merge_plan:
        _msg += f"，待审合并计划 {len(_merge_plan)} 组"
    return {
        "file": skill_dir,
        "line": 0,
        "rule_id": cat,
        "severity": _AP_CATEGORY_MAP.get(cat, (None, "P2", None))[1],
        "message": _msg,
        "confidence": 0.8,
        "category": "antipattern",
        "suggestion": (f"微型文件 ≤{items.get('small_file_threshold_hint', '?')} 行 "
                        "可按 merge_plan 合并（由 AI 审核并执行相关操作）"),
    }
def _normalize_antipattern_category(items, cat: str, skill_dir: str,
                                    issues: list) -> None:
    if isinstance(items, list):
        for iss in items:
            if isinstance(iss, dict):
                _normalize_antipattern_list_item(iss, cat, skill_dir)
                issues.append(iss)
    elif isinstance(items, Mapping):
        if cat != "C10_fragments":
            logger.debug(
                "[Antipattern] 非碎片化类别返回字典槽位，按畸形跳过 %s: %r",
                cat, type(items).__name__)
            return
        _issue = _fragment_category_issue(dict(items), cat, skill_dir)
        if _issue is not None:
            issues.append(_issue)
def run_antipattern_detector(skill_dir: str) -> list[dict]:
    root = _existing_root_arg(skill_dir)
    _active_cats = _ANTIPATTERN_CATEGORIES - RETIRED_RULE_IDS
    def _produce() -> list:
        if not root:
            raise ValueError("skill_dir 缺失/非法")
        result = scan_anti_patterns(root, categories=_active_cats)
        issues: list[dict] = []
        if isinstance(result, dict):
            for cat, items in result.items():
                if cat in _active_cats:
                    _normalize_antipattern_category(items, cat, root, issues)
        return issues
    return run_bounded_channel(
        "diag_antipattern_flow_govern", "run_antipattern_detector", _produce, count_key="issues",
        extra={"active_categories": len(_active_cats)},
        label="D8 antipattern", propagate_errors=True)

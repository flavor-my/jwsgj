from __future__ import annotations

import ast
import json
import logging
import os
import re
import time
from collections import Counter, defaultdict
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass, field
from itertools import permutations
from pathlib import Path
from typing import Any, cast

from jwsgj.build_refactor_policy import (
    ALL_CONSTRAINTS,
    COHESION_STRONG_SIGNAL,
    FIX_APPROACH_ROOT_CAUSE,
    PHASE_ORDER,
    BoundaryAnalysisResult,
    FileAnalysis,
    ModuleBoundary,
    RefactoringRoute,
    SplitMergeAction,
    _bool_field,
    normalize_executed_action_ids,
)
from jwsgj.diag_guard_io import (
    atomic_write_text,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    serialize_json,
)
from jwsgj.diag_merge_safety import (
    detect_circular_imports_stratified,
    tarjan_scc,
)
from jwsgj.diag_types_normalize import (
    finite_float_or_none,
    int_metric,
    int_or,
    signal_bool,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_TASK_TYPE,
    LINE_LIMIT,
    SHARED_BASE_CONSUMER_THRESHOLD,
    TASK_BUDGETS,
)
from jwsgj.log_config import log_swallowed, write_module_run
from jwsgj.runtime_paths import get_temp_base

_PHASE_VALUES: tuple[str, ...] = tuple(p.value for p in PHASE_ORDER)
def _coercible_phase_container(value: Any) -> bool:
    return isinstance(value, (str, list, tuple, set, frozenset))
def _normalize_phase_list(completed_phases: Any, entry: str) -> list[str]:
    if not _coercible_phase_container(completed_phases):
        _log.warning(
            "[RefactorState] %s completed_phases 形状非法,已归一为空列表: %r",
            entry, completed_phases)
        return []
    raw = ([completed_phases] if isinstance(completed_phases, str)
           else list(completed_phases))
    phases = [p for p in raw if isinstance(p, str) and p]
    if len(phases) != len(raw):
        _log.warning(
            "[RefactorState] %s completed_phases 含非 str/空条目,已过滤: %d -> %d 条",
            entry, len(raw), len(phases))
    phase_index = {phase: position for position, phase in enumerate(_PHASE_VALUES)}
    unknown = sorted({p for p in phases if p not in phase_index})
    if unknown:
        _log.warning(
            "[RefactorState] %s completed_phases 含未知阶段,已丢弃: %s",
            entry, unknown)
    return sorted(dict.fromkeys(p for p in phases if p in phase_index),
                  key=phase_index.__getitem__)
def _phase_prefix_error(phases: Iterable[Any]) -> str | None:
    present = {phase for phase in phases if isinstance(phase, str)}
    completed = [phase for phase in _PHASE_VALUES if phase in present]
    if completed != list(_PHASE_VALUES[:len(completed)]):
        return "completed_phases 不是 PHASE_ORDER 的顺序前缀"
    return None
def _default_refactor_state() -> dict[str, Any]:
    return {"completed_phases": [], "actions_executed": 0, "started_at": ""}
def _normalize_actions_executed(value: Any, entry: str,
                               *, allow_absent: bool) -> int | None:
    if value is None and allow_absent:
        return None
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    _log.warning(
        "[RefactorCount] %s 已执行计数载荷形状非法,已归一为 0: %r",
        entry, value)
    return 0
def _state_corruption_reason(parsed: Any) -> str | None:
    if not isinstance(parsed, dict):
        return f"非 dict 形状: {type(parsed).__name__}"
    phases = parsed.get("completed_phases", [])
    if not _coercible_phase_container(phases):
        return f"completed_phases 形状非法: {type(phases).__name__}"
    raw = [phases] if isinstance(phases, str) else list(phases)
    return _phase_prefix_error(raw)
class RefactoringStateManager:
    def __init__(self, skill_dir: str) -> None:
        self.skill_dir = Path(os.path.abspath(os.fspath(skill_dir)))
        self.state_dir = Path(get_temp_base(str(self.skill_dir))) / ".refactor_state"
        self._state_file = self.state_dir / "state.json"
    def _read_state_file(self) -> dict[str, Any] | None:
        self._state_read_failure = None
        if not self._state_file.exists():
            return None
        try:
            parsed = json.loads(
                self._state_file.read_bytes().decode("utf-8-sig"))
        except (json.JSONDecodeError, UnicodeDecodeError, RecursionError) as e:
            self._state_read_failure = ValueError(
                f"重构状态 JSON 损坏: {self._state_file}: {e}")
            _log.warning("[RefactorState] %s", self._state_read_failure)
            return None
        except OSError:
            raise
        reason = _state_corruption_reason(parsed)
        if reason is not None:
            self._state_read_failure = ValueError(
                f"重构状态形状损坏({reason}): {self._state_file}")
            _log.warning("[RefactorState] %s", self._state_read_failure)
            return None
        self._state_read_failure = None
        return cast(dict[str, Any], parsed)
    def _state_read_failure_reason(self) -> ValueError | None:
        reason = getattr(self, "_state_read_failure", None)
        return reason if isinstance(reason, ValueError) else None
    def _load_state(self, *, strict: bool) -> dict[str, Any]:
        try:
            parsed = self._read_state_file()
        except OSError as e:
            action = "终止操作" if strict else "回退默认"
            _log.warning("[RefactorState] 加载重构状态失败,%s: %s: %s",
                         action, self._state_file, e)
            if strict:
                raise
            return _default_refactor_state()
        failure = self._state_read_failure_reason()
        if failure is not None:
            if strict:
                raise failure
            self.clear_state()
            return _default_refactor_state()
        if parsed is None:
            return _default_refactor_state()
        started_at = parsed.get("started_at", "")
        if not isinstance(started_at, str):
            _log.warning(
                "[RefactorState] %s started_at 形状非法,已归一为空字符串: %r",
                self._state_file, started_at)
            started_at = ""
        parsed["started_at"] = started_at
        parsed["completed_phases"] = _normalize_phase_list(
            parsed.get("completed_phases", []),
            f"load_state({self._state_file})")
        executed = _normalize_actions_executed(
            parsed.get("actions_executed"),
            f"load_state({self._state_file})", allow_absent=True)
        parsed["actions_executed"] = max(0, 0 if executed is None else executed)
        return parsed
    def load_state(self) -> dict[str, Any]:
        return self._load_state(strict=False)
    def load_state_for_resume(self) -> dict[str, Any]:
        return self._load_state(strict=True)
    def save_state(self, completed_phases: list[str], actions_executed: int = 0) -> None:
        phases = _normalize_phase_list(completed_phases, "save_state")
        phase_error = _phase_prefix_error(phases)
        if phase_error is not None:
            raise ValueError(f"拒绝保存损坏的重构状态: {phase_error}")
        executed = max(0, cast(int, _normalize_actions_executed(
            actions_executed, "save_state", allow_absent=False)))
        state = self._load_state(strict=True)
        state["completed_phases"] = phases
        state["actions_executed"] = executed
        if not state.get("started_at"):
            state["started_at"] = time.strftime("%Y%m%d_%H%M%S")
        state["updated_at"] = time.strftime("%Y%m%d_%H%M%S")
        self.state_dir.mkdir(parents=True, exist_ok=True)
        content = serialize_json(state, indent=2)
        atomic_write_text(str(self._state_file), content,
                          tag="refactor_state")
        write_module_run(
            "build_refactor_plan", "RefactoringStateManager.save_state",
            phases=len(phases), executed=executed)
    def clear_state(self) -> None:
        if self._state_file.exists():
            if not safe_delete(str(self._state_file)):
                _log.warning("[RefactorState] 清除重构状态失败: %s",
                             self._state_file)
                return
            _log.info("[RefactorState] 重构状态已清除: %s", self._state_file)
        try:
            if not os.listdir(self.state_dir):
                if safe_delete(str(self.state_dir)):
                    _log.info("[RefactorState] 空状态目录已移除: %s", self.state_dir)
                else:
                    _log.debug("[RefactorState] 状态目录移除失败（safe_delete 返 False）: %s", self.state_dir)
            else:
                _log.debug("[RefactorState] 状态目录非空，未移除: %s", self.state_dir)
        except OSError:
            _log.debug("[RefactorState] 状态目录未移除（不存在或不可读）: %s", self.state_dir)
    def get_pending_phases(self, completed_phases: list[str]) -> list[str]:
        phases = _normalize_phase_list(completed_phases, "get_pending_phases")
        return [p for p in _PHASE_VALUES if p not in phases]
    def get_next_phase(self, completed_phases: list[str]) -> str | None:
        pending = self.get_pending_phases(completed_phases)
        return pending[0] if pending else None
def _mark_actions_done(context: dict[str, Any], action_type: str,
                        ledger_key: str, kind: str,
                        count: int | None) -> None:
    if not isinstance(context, dict):
        _log.warning("[RefactorProgress] %s 增量确认跳过: 上下文非 dict", kind)
        return
    route = _coerce_typed(
        context, "refactoring_route", RefactoringRoute, "桥接")
    if route is None:
        return
    actions = [a for a in _iter_route_actions(route)
               if _route_action_type(a) == action_type]
    count = _normalize_actions_executed(
        count, f"{kind}增量确认", allow_absent=True)
    total = count if count is not None else len(actions)
    total = _clamp_executed_count(total, len(actions), kind)
    context[ledger_key] = list(range(total))
    _log.info("[RefactorProgress] 已确认%s完成: %d/%d", kind, total, len(actions))
def mark_migrations_done(context: dict[str, Any], count: int | None = None) -> None:
    _mark_actions_done(context, "migrate", "executed_migrations", "迁移", count)
def mark_rewrites_done(context: dict[str, Any], count: int | None = None) -> None:
    _mark_actions_done(context, "rewrite", "executed_rewrites", "重写", count)
def mark_step_validations(context: dict[str, Any],
                          validations: list[dict] | None = None) -> None:
    if not isinstance(context, dict):
        _log.warning("[RefactorProgress] 步骤验证登记跳过: 上下文非 dict")
        return
    raw = [] if validations is None else validations
    if isinstance(raw, (list, tuple)):
        records = [v for v in raw if isinstance(v, dict)]
        if len(records) != len(raw):
            _log.warning(
                "[RefactorProgress] 步骤验证记录形状非法,已过滤: %d -> %d 条",
                len(raw), len(records))
    else:
        records = []
        _log.warning(
            "[RefactorProgress] 步骤验证记录容器形状非法,已归一为空清单: %s",
            type(raw).__name__)
    context["step_validations"] = records
    _log.info("[RefactorProgress] 已登记步骤验证记录: %d 条", len(records))
def _clamp_executed_count(count: int, total_actions: int, kind: str) -> int:
    clamped = max(0, min(count, total_actions))
    if clamped != count:
        _log.warning("[RefactorProgress] %s 已执行计数越界（%d），"
                     "按 %d 归一（动作总数 %d）",
                     kind, count, clamped, total_actions)
    return clamped
__all__ = [
    'MERGE_GROUPS_PER_CHAIN',
    'MERGE_GROUP_MAX',
    'MIGRATE_IN',
    'MIGRATE_MERGE',
    'MIGRATE_OUT',
    'CrossGroupMigrationVerdict',
    'MergeEvidence',
    'MergeSimulationResult',
    'MigrationEvidence',
    'RefactoringStateManager',
    'SharedBaseVerdict',
    'SplitEstimate',
    'SplitTriggerResult',
    'build_refactor_diagnosis_report',
    'build_refactor_treatment_execution',
    'build_refactor_treatment_plan',
    'check_split_trigger',
    'cluster_merge_groups',
    'compute_optimal_boundaries',
    'estimate_splits',
    'find_merge_candidates',
    'find_migrate_candidates',
    'find_rewrite_candidates',
    'find_split_candidates',
    'group_merge_creates_cycle',
    'infer_responsibility',
    'infer_responsibility_domains',
    'is_shared_base',
    'judge_cross_group_migration',
    'mark_migrations_done',
    'mark_rewrites_done',
    'mark_step_validations',
    'merge_group_into_graph',
    'place_cycle_group',
    'place_to_primary_consumer',
    'rel_to_skill_dir',
    'resolve_boundary_conflicts',
    'resolve_stratified_cycles',
    'simulate_merge',
]
_log = logging.getLogger(__name__)
_log.info("build_refactor_plan 已加载: %d 项导出", len(__all__))
@dataclass
class SplitEstimate:
    needs_split: bool
    estimated_lines: int
    recommended_modules: int
    module_plan: list[dict] = field(default_factory=list)
    risk: str = "low"
    advice: str = ""
_DEFAULT_COMPLEXITY = "medium"
_COMPLEXITY_FUNC_LINES: dict[str, int] = {"low": 25, _DEFAULT_COMPLEXITY: 45, "high": 70}
_MODULE_OVERHEAD_LINES = 15
_DEFAULT_MAX_FILE = 3000
def _resolve_max_file(task_type: str) -> int:
    if not isinstance(TASK_BUDGETS, dict):
        return _DEFAULT_MAX_FILE
    budget = TASK_BUDGETS.get(task_type) if isinstance(task_type, str) else None
    if not isinstance(budget, dict):
        budget = TASK_BUDGETS.get("general")
    if not isinstance(budget, dict):
        return _DEFAULT_MAX_FILE
    return max(1, int_or(budget.get("max_file"), _DEFAULT_MAX_FILE))
def _first_present(item: dict, *keys: str):
    for key in keys:
        if key in item and item[key] not in (None, ""):
            return item[key]
    return None
def _func_count_value(value: Any) -> int:
    if isinstance(value, (list, tuple, set, frozenset)):
        return len(value)
    return max(0, int_or(value, 1))
def _estimate_module(item: dict) -> tuple[dict, int]:
    raw_name = _first_present(item, "name", "module")
    name = raw_name.strip() if isinstance(raw_name, str) and raw_name.strip() else "unknown.py"
    func_count = _func_count_value(
        _first_present(item, "func_count", "functions"))
    raw_complexity = _first_present(
        item, "estimated_complexity", "complexity")
    complexity = (raw_complexity.strip().lower()
                  if isinstance(raw_complexity, str) else "")
    if complexity not in _COMPLEXITY_FUNC_LINES:
        if raw_complexity not in (None, ""):
            _log.warning(
                "[SplitEstimate] 模块 %s 复杂度档位未知,按 %s 估算: %r",
                name, _DEFAULT_COMPLEXITY, raw_complexity)
        complexity = _DEFAULT_COMPLEXITY
    declared_lines = int_or(_first_present(
        item, "estimated_lines", "est_lines"), -1)
    est_lines = declared_lines if declared_lines >= 0 else (
        func_count * _COMPLEXITY_FUNC_LINES.get(
            complexity, _COMPLEXITY_FUNC_LINES[_DEFAULT_COMPLEXITY])
        + _MODULE_OVERHEAD_LINES)
    responsibility = _first_present(
        item, "description", "purpose", "responsibility") or ""
    plan = {
        "name": name,
        "responsibility": str(responsibility),
        "est_lines": est_lines,
        "func_count": func_count,
        "complexity": complexity,
    }
    return plan, est_lines
def _decide_split(module_plan: list[dict], total_est: int,
                  max_file: int) -> tuple[bool, int, str, str]:
    overflows = [m for m in module_plan if m["est_lines"] > max_file]
    if not overflows:
        return False, len(module_plan), "low", (
            f"预估 {total_est} 行，{len(module_plan)} 个模块均在 "
            f"{max_file} 行限制内,可安全编写.")
    added = 0
    worst = 0
    for module in overflows:
        sub_modules = max(
            2, (module["est_lines"] + max_file - 1) // max_file)
        added += sub_modules - 1
        worst = max(worst, module["est_lines"])
    recommended = len(module_plan) + added
    names = "、".join(m["name"] for m in overflows[:3])
    if worst > max_file * 2:
        return True, recommended, "high", (
            f"模块 {names} 预估行数远超 {max_file} 行限制,必须拆分;"
            f"计划内共 {len(module_plan)} 个模块,需扩展为 {recommended} 个.")
    return True, recommended, "medium", (
        f"模块 {names} 预估行数可能超标;"
        f"计划内共 {len(module_plan)} 个模块,推荐扩展为 {recommended} 个.")
def estimate_splits(outline: list[dict],
                    task_type: str = DEFAULT_TASK_TYPE) -> SplitEstimate:
    max_file = _resolve_max_file(task_type)
    if isinstance(outline, (list, tuple)):
        raw = outline
    else:
        _log.warning("[SplitEstimate] 大纲容器形状非法,按空处理: %s",
                     type(outline).__name__)
        raw = []
    items = [i for i in raw if isinstance(i, dict)]
    if len(items) != len(raw):
        _log.warning("[SplitEstimate] 大纲跳过 %d 个非 dict 条目",
                     len(raw) - len(items))
    total_est = 0
    module_plan: list[dict] = []
    for item in items:
        plan, est_lines = _estimate_module(item)
        total_est += est_lines
        module_plan.append(plan)
    if not items:
        return SplitEstimate(
            needs_split=False, estimated_lines=0, recommended_modules=1,
            module_plan=[], risk="unknown",
            advice="未提供可估算的模块大纲，无法判定拆分风险。")
    needs_split, rec_modules, risk, advice = _decide_split(
        module_plan, total_est, max_file)
    return SplitEstimate(
        needs_split=needs_split,
        estimated_lines=total_est,
        recommended_modules=rec_modules,
        module_plan=module_plan,
        risk=risk,
        advice=advice,
    )
def _valid_line_count(value: Any) -> int | None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        return None
    return value
_SCORE_MAX = 10.0
def _stable_items(value: Any) -> Any:
    return sorted(value, key=str) if isinstance(value, (set, frozenset)) else value
def _bounded_finite_or_none(
    value: Any, *, minimum: float = 0.0, maximum: float | None = None,
) -> float | None:
    number = finite_float_or_none(value)
    if number is None or number < minimum:
        return None
    if maximum is not None and number > maximum:
        return None
    return number
def _positive_finite_or_none(value: Any) -> float | None:
    number = _bounded_finite_or_none(value)
    return number if number is not None and number > 0 else None
def _name_entries(value: Any, field: str) -> tuple[str, ...]:
    if not isinstance(value, (list, tuple, set, frozenset)):
        _log.warning("[RefactorGuard] 名称证据 %s 非集合形状,按空处理: %s",
                     field, type(value).__name__)
        return ()
    names = tuple(item for item in _stable_items(value) if isinstance(item, str))
    if len(names) != len(value):
        _log.warning(
            "[RefactorGuard] 名称证据 %s 含非 str 元素,已过滤: %d -> %d 条",
            field, len(value), len(names))
    return names
_MIN_MERGE_MEMBERS = 2
_MIN_NAME_TOKENS = 2
_MIN_STRUCTURAL_DOMAIN_DEFS = 2
_MIN_MIXED_DOMAINS = 2
_TOP_DEF_ENTRY_ARITY = 2
_SIZE_THRESHOLD_BYTES = 100 * 1024
_FRAGMENT_MERGE_MAX_BYTES = 13 * 1024
_COHESION_HEALTHY_MIN = 4.0
_COHESION_MERGE_MIN = _COHESION_HEALTHY_MIN
_HIGH_COUPLING_THRESHOLD = 7.0
@dataclass(frozen=True)
class _MergeGroupContext:
    chain_id: str
    module_graph: dict[str, set[str]]
    evidence: MergeEvidence
    file_analyses: dict[str, FileAnalysis]
@dataclass(frozen=True)
class _MigrationGuard:
    top_defs: list[tuple[str, set[str]]]
    module_refs: set[str]
    all_decls: set[str]
    sibling: set[str]
    test_consumed: set[str]
    def allows(self, block_name: str) -> bool:
        rejected = (
            not self._is_known_block(block_name),
            not self._is_private_block(block_name),
            self._is_declared(block_name),
            self._is_referenced_elsewhere(block_name),
            block_name in self.module_refs,
            self._has_sibling_dependency(block_name),
            block_name in self.test_consumed,
        )
        return not any(rejected)
    def _is_known_block(self, block_name: str) -> bool:
        return any(name == block_name for name, _refs in self.top_defs)
    def _is_private_block(self, block_name: str) -> bool:
        return block_name.startswith("_")
    def _is_declared(self, block_name: str) -> bool:
        return not block_name or block_name in self.all_decls
    def _is_referenced_elsewhere(self, block_name: str) -> bool:
        return any(block_name in refs
                   for name, refs in self.top_defs if name != block_name)
    def _own_refs(self, block_name: str) -> set[str]:
        return next(
            (refs for name, refs in self.top_defs if name == block_name),
            set())
    def _has_sibling_dependency(self, block_name: str) -> bool:
        return bool(self._own_refs(block_name)
                    & (self.sibling - {block_name}))
def _drop_guarded_member(
    merge_members: list[str],
    is_guarded: Callable[[str, set[str]], bool],
) -> str | None:
    if len(merge_members) < _MIN_MERGE_MEMBERS:
        return None
    group_set = set(merge_members)
    victim = next((m for m in merge_members
                   if is_guarded(m, group_set)), None)
    if victim is not None:
        merge_members.remove(victim)
    return victim
def _off_group_consumers(
    member: str,
    group_set: set[str],
    reverse_import_only_graph: dict[str, set[str]],
) -> set[str]:
    return set(_name_entries(reverse_import_only_graph.get(member, ()),
                             "reverse_import_only_graph")) - group_set
def _apply_m04_shared_base_guard(
    merge_members: list[str],
    reverse_import_only_graph: dict[str, set[str]],
) -> None:
    while (preserved := _drop_guarded_member(
            merge_members,
            lambda m, group_set: is_shared_base(len(_off_group_consumers(
                m, group_set, reverse_import_only_graph))).is_shared_base
    )) is not None:
        _log.info("[Boundary] M-04 共享底座保护: %s 被 %d+ 组外"
                  "模块共享, 移出合并组保留为 L0 底座",
                  Path(preserved).name, SHARED_BASE_CONSUMER_THRESHOLD)
def _absorb_blocked(
    member: str,
    group_set: set[str],
    reverse_import_only_graph: dict[str, set[str]],
    file_analyses: dict[str, FileAnalysis],
) -> bool:
    if _off_group_consumers(member, group_set, reverse_import_only_graph):
        return True
    analysis = file_analyses.get(member)
    if analysis is None:
        return True
    size_bytes = _bounded_finite_or_none(analysis.size_bytes)
    if size_bytes is None:
        _log.warning("[Boundary] M-06 尺寸证据非法,按非碎片域处理: %s: %r",
                     Path(member).name, analysis.size_bytes)
        return True
    return size_bytes >= _FRAGMENT_MERGE_MAX_BYTES
def _apply_m06_absorb_guard(
    merge_members: list[str],
    reverse_import_only_graph: dict[str, set[str]],
    file_analyses: dict[str, FileAnalysis],
) -> None:
    while (exposed := _drop_guarded_member(
            merge_members,
            lambda m, group_set: _absorb_blocked(
                m, group_set, reverse_import_only_graph, file_analyses)
    )) is not None:
        _log.info("[Boundary] M-06 吸收保护: %s 有组外消费方或非碎片域尺寸,"
                  " 移出合并组", Path(exposed).name)
def find_merge_candidates(
    execution_chains: dict[str, list[str]],
    file_analyses: dict[str, FileAnalysis],
    evidence: MergeEvidence,
) -> list[SplitMergeAction]:
    evidence = _coerce_evidence(
        evidence, MergeEvidence, "find_merge_candidates", "合并证据")
    if evidence is None:
        return []
    evidence = MergeEvidence(
        weighted_graph=evidence.weighted_graph,
        reverse_import_graph=_coerce_module_graph(
            evidence.reverse_import_graph,
            "find_merge_candidates.reverse_import_graph"),
        reverse_import_only_graph=_coerce_module_graph(
            evidence.reverse_import_only_graph,
            "find_merge_candidates.reverse_import_only_graph"),
        weight_threshold=evidence.weight_threshold,
    )
    analyses = _coerce_analysis_mapping(
        file_analyses, "find_merge_candidates")
    chains = _coerce_chain_mapping(execution_chains, "find_merge_candidates")
    module_graph: dict[str, set[str]] = {
        fp: set(_name_entries(fa.imports_in, "imports_in"))
        for fp, fa in analyses.items()
    }
    candidates: list[SplitMergeAction] = []
    for chain_id, members in chains.items():
        candidates.extend(_merge_candidates_for_chain(
            chain_id, members, module_graph, evidence, analyses))
    return candidates
def _merge_candidates_for_chain(
    chain_id: str,
    members: list[str],
    module_graph: dict[str, set[str]],
    evidence: MergeEvidence,
    file_analyses: dict[str, FileAnalysis],
) -> list[SplitMergeAction]:
    if len(members) < _MIN_MERGE_MEMBERS:
        return []
    valid_analyses = _mergeable_chain_analyses(members, file_analyses)
    if len(valid_analyses) < _MIN_MERGE_MEMBERS:
        return []
    merge_groups = _merge_groups_for_chain(
        chain_id, valid_analyses, evidence)
    if not merge_groups:
        return []
    context = _MergeGroupContext(
        chain_id=chain_id, module_graph=module_graph,
        evidence=evidence, file_analyses=file_analyses)
    actions: list[SplitMergeAction] = []
    for raw_members in merge_groups:
        action = _merge_action_for_group(list(raw_members), context)
        if action is not None:
            actions.append(action)
    return actions
def _mergeable_chain_analyses(
    members: list[str],
    file_analyses: dict[str, FileAnalysis],
) -> list[FileAnalysis]:
    valid_analyses: list[FileAnalysis] = []
    for member in members:
        analysis = file_analyses.get(member)
        if not analysis:
            continue
        if (not isinstance(analysis.filepath, str)
                or analysis.filepath != member):
            _log.warning(
                "[Boundary] 跳过合并 %s: 分析对象路径与链成员不一致 %r",
                Path(member).name, analysis.filepath)
            continue
        if _valid_line_count(analysis.line_count) is None:
            _log.warning("[Boundary] 跳过合并 %s: 行数证据非法 %r",
                         Path(member).name, analysis.line_count)
            continue
        size_bytes = _bounded_finite_or_none(analysis.size_bytes)
        if size_bytes is None:
            _log.warning("[Boundary] 跳过合并 %s: 尺寸证据非法 %r",
                         Path(member).name, analysis.size_bytes)
            continue
        if size_bytes >= _SIZE_THRESHOLD_BYTES:
            continue
        cohesion_score = _bounded_finite_or_none(
            analysis.cohesion_score, maximum=_SCORE_MAX)
        if cohesion_score is None:
            _log.warning("[Boundary] 跳过合并 %s: 内聚度证据非法 %r",
                         Path(member).name, analysis.cohesion_score)
            continue
        if cohesion_score < _COHESION_MERGE_MIN:
            _log.info("[Boundary] 跳过合并 %s: 内聚度 %.1f 较低，合并会引入噪音",
                      Path(member).name, cohesion_score)
            continue
        valid_analyses.append(analysis)
    return valid_analyses
def _merge_groups_for_chain(
    chain_id: str,
    valid_analyses: list[FileAnalysis],
    evidence: MergeEvidence,
) -> list[list[str]]:
    total_lines = sum(m.line_count for m in valid_analyses)
    if (total_lines <= LINE_LIMIT
            and len(valid_analyses) <= MERGE_GROUP_MAX):
        return [[m.filepath for m in valid_analyses]]
    merge_groups = cluster_merge_groups(
        valid_analyses, evidence.weighted_graph, evidence.weight_threshold)
    if not merge_groups:
        _log.info("[Boundary] 链 %s 整链 %d 成员 %d 行超限且无强互连小组，跳过",
                  chain_id, len(valid_analyses), total_lines)
    return merge_groups
def _group_survives_prune(
    merge_members: list[str],
    chain_id: str,
    stage: str,
    before_members: list[str] | None = None,
) -> bool:
    if len(merge_members) >= _MIN_MERGE_MEMBERS:
        return True
    survivors = set(merge_members)
    composition = list(before_members or merge_members)
    pruned_names = [m for m in composition if m not in survivors]
    detail = (
        f" [{'、'.join(Path(m).name for m in composition)}]"
        if composition else ""
    )
    _log.info("[Boundary] %s后链 %s 组%s 剩余成员不足 2, 跳过合并%s",
              stage, chain_id, detail,
              (f"（移出 [{'、'.join(Path(m).name for m in pruned_names)}]）"
               if pruned_names else ""))
    return False
def _prune_group(
    merge_members: list[str],
    context: _MergeGroupContext,
) -> bool:
    before_m04 = list(merge_members)
    _apply_m04_shared_base_guard(
        merge_members, context.evidence.reverse_import_only_graph)
    if not _group_survives_prune(
            merge_members, context.chain_id, "M-04 共享底座保护",
            before_m04):
        return False
    before_m06 = list(merge_members)
    _apply_m06_absorb_guard(
        merge_members, context.evidence.reverse_import_only_graph,
        context.file_analyses)
    return _group_survives_prune(
        merge_members, context.chain_id, "M-06 吸收保护", before_m06)
def _merge_action_for_group(
    merge_members: list[str],
    context: _MergeGroupContext,
) -> SplitMergeAction | None:
    if not _prune_group(merge_members, context):
        return None
    threshold = _positive_finite_or_none(context.evidence.weight_threshold)
    if threshold is None:
        _log.warning("[Boundary] 跳过合并组 [%s]: 权重阈值证据非法 %r",
                     "、".join(Path(m).name for m in merge_members),
                     context.evidence.weight_threshold)
        return None
    total_weight = sum(
        _edge_weight(context.evidence.weighted_graph, source, target)
        for source, target in permutations(merge_members, 2))
    if total_weight < threshold:
        _log.info("[Boundary] 跳过合并组 [%s]: 组总权重 %.1f 低于阈值 %.1f",
                  "、".join(Path(m).name for m in merge_members),
                  total_weight, threshold)
        return None
    total_lines = sum(
        context.file_analyses[member].line_count
        for member in merge_members
        if member in context.file_analyses)
    action = _build_merge_action(
        merge_members, context.chain_id, total_weight, total_lines)
    if not _merge_simulation_passes(merge_members, context):
        return None
    _annotate_primary_shared_base(
        action, merge_members, context.evidence.reverse_import_only_graph)
    return action
def _build_merge_action(
    merge_members: list[str],
    chain_id: str,
    total_weight: float,
    total_lines: int,
) -> SplitMergeAction:
    member_count = len(merge_members)
    remaining = max(0, LINE_LIMIT - total_lines)
    return SplitMergeAction(
        action_type="merge",
        source_files=list(merge_members),
        target_files=[merge_members[0]],
        reason=f"同一运行链路 ({chain_id}) 中有 {len(merge_members)} 个"
               f"高内聚文件，合并目标 {Path(merge_members[0]).name}"
               f"（文件大小仅作辅助参考）",
        boundary_justification=f"基于运行链路内聚性: 文件属于同一导入链"
                              f"{chain_id}，内聚度均 ≥ {_COHESION_MERGE_MIN:.1f}，"
                              f"组总权重 {total_weight:.1f}，"
                              f"合并的唯一依据是运行链路内聚性足够高，"
                              f"文件大小仅作辅助参考",
        is_size_based=False,
        pros=(
            (f"同一运行链路 {chain_id} 内 {member_count} 个文件"
             f"内聚度均 ≥ {_COHESION_MERGE_MIN}"),
            (f"组内双向权重合计 {total_weight:.1f}，"
             "达到高内聚阈值，合并减少跨文件跳转"),
        ),
        cons=(
            f"合并后单文件约 {total_lines} 行，评审面积增大",
            (f"模块边界由 {member_count} 个收敛为 1 个，"
             "消费者导入路径需定向回归"),
        ),
        net_benefit="positive",
        risk=(
            f"合并后距行数上限仅余 {remaining} 行；"
            "需定向回归公开签名、导入链与运行链路行为"
        ),
    )
def _annotate_primary_shared_base(
    action: SplitMergeAction,
    merge_members: list[str],
    reverse_import_only_graph: dict[str, set[str]],
) -> None:
    primary_consumer = merge_members[0]
    consumer_count = len(
        set(_name_entries(
            reverse_import_only_graph.get(primary_consumer, ()),
            "reverse_import_only_graph"))
        - set(merge_members))
    shared = is_shared_base(consumer_count)
    if shared.is_shared_base:
        _log.info("[Boundary] M-04 共享底座 %s: %s",
                  Path(primary_consumer).stem, shared.reason)
        action.boundary_justification += (
            f" | M-04 共享底座识别: {shared.reason}"
        )
def _merge_simulation_passes(
    merge_members: list[str],
    context: _MergeGroupContext,
) -> bool:
    line_counts = {
        m: context.file_analyses[m].line_count
        for m in merge_members if m in context.file_analyses
    }
    sim = simulate_merge(merge_members, line_counts, context.module_graph)
    if sim.can_merge:
        return True
    _log.info("[Boundary] M-02 合并模拟拦截组 %s: %s",
              context.chain_id, sim.suggestion)
    if sim.will_create_cycle:
        place_cycle_group(merge_members,
                          context.evidence.reverse_import_graph,
                          context.chain_id)
    if sim.exceeds_line_limit:
        _log.info("[Boundary] M-02 合并超限: 合并后 %s 行 > %s 行上限",
                  sim.merged_line_count, LINE_LIMIT)
    return False
def find_migrate_candidates(
    file_analyses: dict[str, FileAnalysis],
    evidence: MigrationEvidence,
) -> list[SplitMergeAction]:
    evidence = _coerce_evidence(
        evidence, MigrationEvidence, "find_migrate_candidates", "迁移证据")
    if evidence is None:
        return []
    candidates: list[SplitMergeAction] = []
    seen: set[tuple[str, str, str]] = set()
    analyses = _coerce_analysis_mapping(
        file_analyses, "find_migrate_candidates")
    for fpath, analysis in analyses.items():
        candidates.extend(
            _migration_candidates_for_file(fpath, analysis, evidence, seen))
    return candidates
def _migration_candidates_for_file(
    fpath: str,
    analysis: FileAnalysis,
    evidence: MigrationEvidence,
    seen: set[tuple[str, str, str]],
) -> list[SplitMergeAction]:
    if not analysis.unrelated_code_blocks:
        return []
    guard = _migration_guard_for(fpath, evidence)
    actions: list[SplitMergeAction] = []
    for block_name in _iter_unrelated_block_names(
            analysis.unrelated_code_blocks):
        action = _migration_action_if_allowed(
            fpath, block_name, guard, evidence.import_index)
        if action is None:
            continue
        key = (fpath, block_name, action.target_files[0])
        if key in seen:
            continue
        seen.add(key)
        actions.append(action)
    return actions
def _coerce_analysis_mapping(
    value: Any, scope: str,
) -> dict[str, FileAnalysis]:
    if not isinstance(value, dict):
        if value is not None:
            _log.warning(
                "[RefactorGuard] %s file_analyses 非 dict 形状,按空处理: %s",
                scope, type(value).__name__)
        return {}
    valid: dict[str, FileAnalysis] = {}
    dropped = 0
    duplicates = 0
    for fp, analysis in value.items():
        if not isinstance(analysis, FileAnalysis) or not isinstance(
                fp, (str, os.PathLike)):
            dropped += 1
            continue
        try:
            key = os.fspath(fp)
        except TypeError as exc:
            log_swallowed(
                __name__, exc,
                context=(f"_coerce_analysis_mapping:{scope}:"
                         f"{type(exc).__name__}"))
            dropped += 1
            continue
        if not isinstance(key, str) or not key.strip():
            dropped += 1
            continue
        if (not isinstance(analysis.filepath, str)
                or analysis.filepath != key):
            dropped += 1
            _log.warning(
                "[RefactorGuard] %s 丢弃路径身份错位的 file_analyses 条目: "
                "键 %r != filepath %r", scope, key, analysis.filepath)
            continue
        if key in valid:
            duplicates += 1
        valid[key] = analysis
    if dropped:
        _log.warning(
            "[RefactorGuard] %s 丢弃 %d 个非法 file_analyses 条目（键/值形状脏）",
            scope, dropped)
    if duplicates:
        _log.warning(
            "[RefactorGuard] %s file_analyses 有 %d 个键归一后重复,已后者覆盖",
            scope, duplicates)
    return valid
def _coerce_evidence(
    value: Any, expected: type, scope: str, label: str,
) -> Any | None:
    if isinstance(value, expected):
        return value
    _log.warning(
        "[RefactorGuard] %s %s 缺失或形状非法,按无候选处理: %s",
        scope, label, type(value).__name__)
    return None
def _coerce_chain_mapping(
    value: Any, scope: str,
) -> dict[str, list[str]]:
    if not isinstance(value, dict):
        if value is not None:
            _log.warning(
                "[RefactorGuard] %s execution_chains 非 dict 形状,按空处理: %s",
                scope, type(value).__name__)
        return {}
    chains: dict[str, list[str]] = {}
    dropped = 0
    invalid_members = 0
    for chain_id, members in value.items():
        if not isinstance(chain_id, str) or not chain_id.strip():
            dropped += 1
            continue
        if not isinstance(members, (list, tuple, set, frozenset)):
            invalid_members += 1
            continue
        raw = [m for m in _stable_items(members)
               if isinstance(m, str) and m.strip()]
        names = list(dict.fromkeys(raw))
        if len(names) != len(members):
            invalid_members += 1
        chains[chain_id] = names
    if dropped:
        _log.warning(
            "[RefactorGuard] %s 丢弃 %d 个非法执行链条目（链名非 str/空白）",
            scope, dropped)
    if invalid_members:
        _log.warning(
            "[RefactorGuard] %s 有 %d 条执行链成员形状非法或含脏成员,已跳过/过滤",
            scope, invalid_members)
    return chains
def _coerce_module_graph(value: Any, scope: str) -> dict[str, set[str]]:
    if not isinstance(value, dict):
        if value is not None:
            _log.warning(
                "[RefactorGuard] %s module_graph 非 dict 形状,按空处理: %s",
                scope, type(value).__name__)
        return {}
    graph: dict[str, set[str]] = {}
    dropped_nodes = 0
    for node, dependencies in value.items():
        if not isinstance(node, str) or not node.strip():
            dropped_nodes += 1
            continue
        names = _name_entries(
            dependencies, f"{scope}.module_graph[{node}]")
        graph[node] = {name for name in names if name.strip()}
        if len(graph[node]) != len(names):
            _log.warning(
                "[RefactorGuard] %s 模块 %s 的空白依赖已过滤: %d -> %d 条",
                scope, node, len(names), len(graph[node]))
    if dropped_nodes:
        _log.warning(
            "[RefactorGuard] %s module_graph 丢弃 %d 个非法节点键",
            scope, dropped_nodes)
    return graph
def _coerce_group_members(group: Any, scope: str) -> list[str]:
    if group is None:
        return []
    if isinstance(group, str):
        return [group.strip()] if group.strip() else []
    if not isinstance(group, (list, tuple, set, frozenset)):
        _log.warning(
            "[RefactorGuard] %s 合并组非清单形状,按空处理: %s",
            scope, type(group).__name__)
        return []
    raw = [m for m in _stable_items(group) if isinstance(m, str) and m.strip()]
    names = list(dict.fromkeys(raw))
    if len(names) != len(group):
        _log.warning(
            "[RefactorGuard] %s 合并组含非法/重复成员,已归一: %d -> %d 条",
            scope, len(group), len(names))
    return names
def _edge_weight(
    weighted_graph: Any, source: str, target: str,
) -> float:
    if not isinstance(weighted_graph, dict):
        return 0.0
    row = weighted_graph.get(source)
    if not isinstance(row, dict):
        return 0.0
    weight = finite_float_or_none(row.get(target, 0))
    return 0.0 if weight is None or weight < 0 else weight
def _evidence_map(value: Any, scope: str) -> dict:
    if isinstance(value, dict):
        return value
    if value is not None:
        _log.warning(
            "[RefactorGuard] 迁移证据 %s 非 dict 形状,按空处理: %s",
            scope, type(value).__name__)
    return {}
def _migration_guard_for(
    fpath: str, evidence: MigrationEvidence,
) -> _MigrationGuard:
    top_level_refs = _evidence_map(
        evidence.top_level_refs, "top_level_refs")
    module_state_names = _evidence_map(
        evidence.module_state_names, "module_state_names")
    module_level_refs = _evidence_map(
        evidence.module_level_refs, "module_level_refs")
    all_declarations = _evidence_map(
        evidence.all_declarations, "all_declarations")
    test_symbol_consumers = _evidence_map(
        evidence.test_symbol_consumers, "test_symbol_consumers")
    raw_defs = top_level_refs.get(fpath) or []
    if not isinstance(raw_defs, (list, tuple)):
        _log.warning(
            "[RefactorGuard] 迁移证据 top_level_refs[%s] 非清单形状,按空处理: %s",
            Path(fpath).name, type(raw_defs).__name__)
        raw_defs = []
    top_defs = [
        (entry[0], entry[1]) for entry in raw_defs
        if (isinstance(entry, (tuple, list))
                and len(entry) == _TOP_DEF_ENTRY_ARITY)
        and isinstance(entry[0], str)
        and isinstance(entry[1], (set, frozenset))
    ]
    if len(top_defs) != len(raw_defs):
        _log.warning(
            "[RefactorGuard] 迁移证据 top_level_refs 含非法条目,已过滤: %d -> %d 条",
            len(raw_defs), len(top_defs))
    sibling = ({nm for nm, _ in top_defs}
               | set(_name_entries(
                   module_state_names.get(fpath, ()),
                   "module_state_names")))
    return _MigrationGuard(
        top_defs=top_defs,
        module_refs=set(_name_entries(
            module_level_refs.get(fpath, ()),
            "module_level_refs")),
        all_decls=set(_name_entries(
            all_declarations.get(fpath, ()),
            "all_declarations")),
        sibling=sibling,
        test_consumed=set(_name_entries(
            test_symbol_consumers.get(fpath, ()),
            "test_symbol_consumers")),
    )
def _migration_action_if_allowed(
    fpath: str,
    block_name: str,
    guard: _MigrationGuard,
    import_index: dict[str, set[str]],
) -> SplitMergeAction | None:
    if not guard.allows(block_name):
        return None
    target = _find_best_migration_target(fpath, block_name, import_index)
    if not target:
        return None
    return _build_migrate_action(fpath, block_name, target)
def _iter_unrelated_block_names(
    unrelated_code_blocks: list[str],
) -> Iterator[str]:
    if not isinstance(unrelated_code_blocks,
                      (list, tuple, set, frozenset)):
        _log.warning(
            "[RefactorGuard] 迁移证据 unrelated_code_blocks 非清单形状,"
            "按空处理: %s", type(unrelated_code_blocks).__name__)
        return
    for block in _stable_items(unrelated_code_blocks):
        if not isinstance(block, str) or " ↔ " not in block:
            continue
        for part in block.split(" ↔ "):
            name = part.strip()
            if name:
                yield name
def _build_migrate_action(
    fpath: str, block_name: str, target: str,
) -> SplitMergeAction:
    return SplitMergeAction(
        action_type="migrate",
        source_files=[fpath],
        target_files=[target],
        reason=(f"孤儿符号 '{block_name}' 不被本文件其他代码引用，"
                f"仅被目标文件 import（唯一消费者）"),
        boundary_justification=(f"基于模块边界: '{block_name}' 为私有孤儿符号且被 "
                                f"{Path(target).name} 唯一真实 import，"
                                "迁移到消费点提升内聚；迁移后移除旧依赖，"
                                "消费方不再从源文件导入该符号"),
        is_size_based=False,
        code_elements=[block_name],
    )
def _find_best_migration_target(source_file: str, code_name: str,
                               import_index: dict[str, set[str]]) -> str | None:
    source_aware = getattr(import_index, "consumers_for", None)
    if callable(source_aware):
        raw_consumers = source_aware(source_file, code_name)
    elif isinstance(import_index, dict):
        raw_consumers = import_index.get(code_name, ())
    else:
        _log.warning(
            "[RefactorGuard] 迁移消费索引形状非法,按无消费者处理: %s",
            type(import_index).__name__)
        return None
    consumers = {
        fpath for fpath in _name_entries(raw_consumers, "import_index")
        if fpath != source_file
    }
    if len(consumers) == 1:
        target = next(iter(consumers))
        if Path(target).name == "__init__.py":
            return None
        return target
    return None
def compute_optimal_boundaries(
    execution_chains: dict[str, list[str]],
    file_analyses: dict[str, FileAnalysis],
) -> list[ModuleBoundary]:
    analyses = _coerce_analysis_mapping(
        file_analyses, "compute_optimal_boundaries")
    chains = _coerce_chain_mapping(
        execution_chains, "compute_optimal_boundaries")
    return [
        _boundary_for_chain(chain_id, members, analyses)
        for chain_id, members in chains.items()
    ]
def _boundary_for_chain(
    chain_id: str,
    members: list[str],
    file_analyses: dict[str, FileAnalysis],
) -> ModuleBoundary:
    total_size = 0
    responsibilities: set[str] = set()
    imports_in: set[str] = set()
    imports_out: set[str] = set()
    for member in members:
        analysis = file_analyses.get(member)
        if analysis is None:
            continue
        size_bytes = _bounded_finite_or_none(analysis.size_bytes)
        if size_bytes is None:
            _log.warning("[RefactorGuard] 边界聚合跳过 %s 的尺寸证据: %r",
                         Path(member).name, analysis.size_bytes)
        else:
            total_size += int(size_bytes)
        if isinstance(analysis.module_responsibility, str) and analysis.module_responsibility:
            responsibilities.add(analysis.module_responsibility)
        imports_in.update(_name_entries(analysis.imports_in, "imports_in"))
        imports_out.update(_name_entries(analysis.imports_out, "imports_out"))
    return ModuleBoundary(
        name=chain_id,
        member_files=members,
        responsibility=", ".join(sorted(responsibilities)),
        imports_in=imports_in,
        imports_out=imports_out,
        execution_chain_id=chain_id,
        total_size_bytes=total_size,
    )
_RESPONSIBILITY_WORDS: dict[str, tuple[str, ...]] = {
    "诊断": ("diag", "diagnose", "diagnoses", "diagnosed", "diagnosing",
             "diagnosis", "diagnostic", "diagnostics", "diagnoser",
             "diagnosers"),
    "构建": ("build", "builds", "built", "builder", "builders",
             "building"),
    "修复": ("fix", "fixes", "fixed", "fixing", "fixer", "fixers",
             "fixate", "fixates", "fixated", "fixation", "fixations",
             "fixpoint", "fixpoints", "fixup", "fixups", "fixable"),
    "交叉验证": ("xv", "xvs", "xvr"),
    "治疗": ("treatment", "treatments"),
    "测试": ("test", "tests", "tested", "testing", "testable", "tester",
             "testers", "testcase", "testcases", "testtriage", "fixture",
             "fixtures"),
    "扫描": ("scan", "scans", "scanned", "scanning", "scanner", "scanners",
             "scannable", "scandebt"),
    "检测": ("detect", "detects", "detected", "detecting", "detection",
             "detections", "detector", "detectors"),
    "分析": ("analyze", "analyzes", "analyzed", "analyzing", "analyzer",
             "analyzers", "analyse", "analyses", "analysed", "analysing",
             "analysis"),
    "渲染": ("render", "renders", "rendered", "rendering", "renderer",
             "renderers"),
    "生成": ("generate", "generates", "generated", "generating", "generation",
             "generations", "generator", "generators"),
    "验证": ("validate", "validates", "validated", "validating", "validation",
             "validations", "validator", "validators"),
    "重构": ("refactor", "refactors", "refactored", "refactoring",
             "refactorer", "refactorers", "refactorings"),
    "清理": ("clean", "cleans", "cleaned", "cleaning", "cleaner", "cleaners",
             "cleanable", "cleanup", "cleanups"),
    "审计": ("audit", "audits", "audited", "auditing", "auditor",
             "auditors"),
    "安全": ("security", "securities"),
    "质量": ("quality", "qualities"),
    "覆盖": ("coverage", "coverages"),
    "报告": ("report", "reports", "reported", "reporting", "reporter",
             "reporters", "reportable"),
    "反馈": ("feedback", "feedbacks"),
    "编排": ("orchestrat", "orchestrate", "orchestrates", "orchestrated",
             "orchestrating", "orchestration", "orchestrator", "orchestrators"),
    "管道": ("pipeline", "pipelines"),
    "守卫": ("guard", "guards", "guarded", "guarding", "guardian",
             "guardians"),
    "约束": ("constraint", "constraints"),
}
_RESPONSIBILITY_FORM_SETS: tuple[tuple[str, frozenset[str]], ...] = tuple(
    (domain, frozenset(forms))
    for domain, forms in _RESPONSIBILITY_WORDS.items()
)
_GENERIC_NAME_TOKENS: frozenset[str] = frozenset({
    "a", "an", "the", "and", "or", "not", "self", "cls",
    "get", "set", "run", "do", "make", "handle", "process",
    "main", "init", "new", "load", "save", "read", "write",
    "parse", "create", "update", "delete", "add", "remove",
    "check", "is", "has", "to", "from", "of", "by", "with",
    "util", "utils", "helper", "helpers", "base", "core",
    "common", "misc", "impl", "internal", "manager", "handler",
})
def _name_tokens(name: str) -> list[str]:
    if not isinstance(name, str):
        return []
    tokens: list[str] = []
    for part in name.split("_"):
        tokens.extend(
            tok.lower() for tok in re.findall(
                r"[A-Z]+(?![a-z])|[A-Z][a-z]+|[a-z]+|\d+", part))
    return tokens
def _structural_domain(name: str) -> str:
    tokens = _name_tokens(name)
    if len(tokens) < _MIN_NAME_TOKENS:
        return ""
    return next((tok for tok in tokens
                 if tok not in _GENERIC_NAME_TOKENS and not tok.isdigit()),
                "")
def infer_responsibility(name: str) -> str:
    tokens = set(_name_tokens(name))
    for domain, forms in _RESPONSIBILITY_FORM_SETS:
        if tokens & forms:
            return domain
    return ""
def _responsibility_domains_ordered(names: Iterable[str]) -> list[str]:
    domains: list[str] = []
    structural: Counter[str] = Counter()
    for name in _stable_items(names):
        known = infer_responsibility(name)
        if known:
            if known not in domains:
                domains.append(known)
            continue
        domain = _structural_domain(name)
        if domain:
            structural[domain] += 1
    for domain, count in structural.items():
        if (count >= _MIN_STRUCTURAL_DOMAIN_DEFS
                and domain not in domains):
            domains.append(domain)
    return domains
def infer_responsibility_domains(names: Iterable[str]) -> set[str]:
    return set(_responsibility_domains_ordered(names))
MIGRATE_OUT = "migrate_out"
MIGRATE_IN = "migrate_in"
MIGRATE_MERGE = "migrate_merge"
@dataclass
class MergeSimulationResult:
    can_merge: bool
    will_create_cycle: bool
    exceeds_line_limit: bool
    merged_line_count: int = 0
    cycle_members: list[str] = field(default_factory=list)
    suggestion: str = ""
@dataclass
class SplitTriggerResult:
    triggered: bool
    line_count: int = 0
    top_level_domain_count: int = 0
    domains: list[str] = field(default_factory=list)
    reason: str = ""
@dataclass
class SharedBaseVerdict:
    is_shared_base: bool
    reason: str = ""
    consumer_count: int = 0
@dataclass
class CrossGroupMigrationVerdict:
    allowed: bool
    action: str = ""
    reason: str = ""
def _merge_group_label(
    graph: dict[str, set[str]], group_set: set[str],
) -> str:
    occupied: set[str] = set(graph)
    for deps in graph.values():
        if deps:
            occupied.update(deps)
    occupied -= group_set
    label = "group"
    suffix = 0
    while label in occupied:
        suffix += 1
        label = f"group#{suffix}"
    return label
def merge_group_into_graph(
    graph: dict[str, set[str]],
    group: list[str],
) -> dict[str, set[str]]:
    graph = _coerce_module_graph(graph, "merge_group_into_graph")
    members = _coerce_group_members(group, "merge_group_into_graph")
    if not members:
        return {node: set(deps or ()) for node, deps in graph.items()}
    group_set = set(members)
    label = _merge_group_label(graph, group_set)
    merged = {
        node: {label if dep in group_set else dep for dep in (deps or ())}
        for node, deps in graph.items()
        if node not in group_set
    }
    merged[label] = _external_group_dependencies(graph, group_set)
    return merged
def _external_group_dependencies(
    graph: dict[str, set[str]], group_set: set[str],
) -> set[str]:
    out: set[str] = set()
    for node in group_set:
        out.update(dep for dep in (graph.get(node) or ())
                   if dep not in group_set)
    return out
def group_merge_creates_cycle(
    graph: dict[str, set[str]],
    group: list[str],
) -> list[str]:
    graph = _coerce_module_graph(graph, "group_merge_creates_cycle")
    members = _coerce_group_members(group, "group_merge_creates_cycle")
    group_set = set(members)
    label = _merge_group_label(graph, group_set)
    merged = merge_group_into_graph(graph, members)
    sccs = tarjan_scc(merged)
    for scc in sccs:
        if len(scc) > 1 and label in scc:
            return scc
    return []
def _merge_simulation(
    can_merge: bool,
    merged_lines: int,
    cycle_members: list[str],
    suggestion: str,
) -> MergeSimulationResult:
    return MergeSimulationResult(
        can_merge=can_merge,
        will_create_cycle=bool(cycle_members),
        exceeds_line_limit=merged_lines > LINE_LIMIT,
        merged_line_count=merged_lines,
        cycle_members=cycle_members,
        suggestion=suggestion,
    )
def simulate_merge(
    group: list[str],
    line_counts: dict[str, int],
    module_graph: dict[str, set[str]],
) -> MergeSimulationResult:
    group = _coerce_group_members(group, "simulate_merge")
    if not group:
        return _merge_simulation(
            False, 0, [], "合并组为空，不生成合并动作")
    counts = line_counts if isinstance(line_counts, dict) else {}
    module_graph = module_graph if isinstance(module_graph, dict) else {}
    measured = {m: _valid_line_count(counts.get(m)) for m in group}
    missing = [m for m, lines in measured.items() if lines is None]
    merged_lines = sum(lines for lines in measured.values() if lines is not None)
    cycle_members = group_merge_creates_cycle(module_graph, group)
    if missing:
        suggestion = (
            f"缺少 {len(missing)} 个成员的行数证据，无法判定合并规模，放弃直接合并")
        if cycle_members:
            suggestion += "；且合并后将引入循环依赖"
        return _merge_simulation(False, merged_lines, cycle_members, suggestion)
    if merged_lines > LINE_LIMIT:
        suggestion = (
            f"合并后 {merged_lines} 行超过单文件上限 {LINE_LIMIT} 行，放弃直接合并")
        if cycle_members:
            suggestion += "；且合并后将引入循环依赖"
        return _merge_simulation(False, merged_lines, cycle_members, suggestion)
    if cycle_members:
        return _merge_simulation(
            False, merged_lines, cycle_members,
            "合并后将引入循环依赖，改用「归位到主要使用方」策略："
            "按 AST 使用次数把符号放回消费最多的模块，沿既有单向依赖边导入")
    return _merge_simulation(
        True, merged_lines, [], f"可合并：不超 {LINE_LIMIT} 行上限且不引入新环")
def place_to_primary_consumer(
    usage_counts: dict[str, int],
    candidates: list[str],
) -> str:
    counts = usage_counts if isinstance(usage_counts, dict) else {}
    names = _coerce_group_members(candidates, "place_to_primary_consumer")
    ranking = sorted(
        (m for m in names if int_metric(counts.get(m, 0), 0) > 0),
        key=lambda m: int_metric(counts.get(m, 0), 0),
        reverse=True,
    )
    return ranking[0] if ranking else (names[0] if names else "")
_MODULE_LEVEL_BLOCK_NODES: tuple[type[ast.AST], ...] = tuple(
    block for block in (ast.If, ast.Try, ast.ExceptHandler, ast.With,
                        ast.AsyncWith, ast.For, ast.AsyncFor, ast.While,
                        getattr(ast, "TryStar", None))
    if block is not None)
_MATCH_STMT_NODE = getattr(ast, "Match", None)
def _iter_module_level_defs(
    tree: ast.AST,
) -> Iterator[ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef]:
    stack: list[ast.AST] = list(reversed(getattr(tree, "body", ())))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            yield node
            continue
        if _MATCH_STMT_NODE is not None and isinstance(node, _MATCH_STMT_NODE):
            for case in reversed(node.cases):
                stack.extend(reversed(case.body))
            continue
        if isinstance(node, _MODULE_LEVEL_BLOCK_NODES):
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
def check_split_trigger(
    line_count: int,
    tree: ast.AST | None = None,
) -> SplitTriggerResult:
    line_count = int_or(line_count, 0)
    domains: list[str] = []
    if tree is not None:
        domains = _responsibility_domains_ordered(
            node.name for node in _iter_module_level_defs(tree))
    domain_count = len(domains)
    triggered = (line_count > LINE_LIMIT
                 and domain_count >= _MIN_MIXED_DOMAINS)
    reason = ""
    if triggered:
        reason = (f"硬触发治理候选：{line_count} 行 > {LINE_LIMIT} 行上限 且 "
                  f"功能域混杂 {domain_count} 类（≥{_MIN_MIXED_DOMAINS}）→ "
                  "按 GOV-01 简化逻辑/"
                  "消除重复/收敛依赖/迁移代码/提取同模块私有实现，禁止直接拆分")
    return SplitTriggerResult(
        triggered=triggered,
        line_count=line_count,
        top_level_domain_count=domain_count,
        domains=domains,
        reason=reason,
    )
def is_shared_base(
    consumer_count: int,
    source_deleted: bool = False,
    merge_creates_hub_cycle: bool = False,
) -> SharedBaseVerdict:
    consumer_count = int_metric(consumer_count, 0)
    source_deleted = signal_bool(source_deleted)
    merge_creates_hub_cycle = signal_bool(merge_creates_hub_cycle)
    if source_deleted:
        return SharedBaseVerdict(True, "来源已删，无法归位，保留为 L0 底座", consumer_count)
    if merge_creates_hub_cycle:
        return SharedBaseVerdict(True, "合回会制造 hub 自依赖大环，保留为 L0 底座", consumer_count)
    if consumer_count >= SHARED_BASE_CONSUMER_THRESHOLD:
        return SharedBaseVerdict(
            True,
            f"符号被 {consumer_count} 个模块共享（≥{SHARED_BASE_CONSUMER_THRESHOLD}），"
            "保留为 L0 共享底座",
            consumer_count,
        )
    return SharedBaseVerdict(
        False,
        f"符号消费方 {consumer_count} 个低于共享底座阈值",
        consumer_count,
    )
def judge_cross_group_migration(
    action: str,
    strong_coupling: bool,
    bidirectional: bool = False,
) -> CrossGroupMigrationVerdict:
    strong_coupling = _bool_field(strong_coupling)
    bidirectional = _bool_field(bidirectional)
    if action not in (MIGRATE_OUT, MIGRATE_IN, MIGRATE_MERGE):
        return CrossGroupMigrationVerdict(False, action, f"未知跨组迁移动作: {action}")
    if action == MIGRATE_MERGE:
        if strong_coupling and bidirectional:
            return CrossGroupMigrationVerdict(
                True, MIGRATE_MERGE,
                "双向强耦合 → 允许合并入本批（因上下文消费需要）")
        return CrossGroupMigrationVerdict(
            False, MIGRATE_MERGE,
            "双向强耦合未成立，不合并，仅只读补上下文")
    if strong_coupling:
        kind = "迁出" if action == MIGRATE_OUT else "迁入"
        return CrossGroupMigrationVerdict(
            True, action, f"{kind}：强耦合目标其他批，因上下文消费需要允许跨组迁移")
    return CrossGroupMigrationVerdict(
        False, action, "仅弱依赖，不跨组迁移，只读补上下文并备注引用事实")
@dataclass(frozen=True)
class MergeEvidence:
    weighted_graph: dict[str, dict[str, float]]
    reverse_import_graph: dict[str, set[str]]
    reverse_import_only_graph: dict[str, set[str]]
    weight_threshold: float
@dataclass(frozen=True)
class MigrationEvidence:
    top_level_refs: dict[str, list[tuple[str, set[str]]]]
    module_level_refs: dict[str, set[str]]
    all_declarations: dict[str, set[str]]
    module_state_names: dict[str, set[str]]
    import_index: dict[str, set[str]]
    test_symbol_consumers: dict[str, set[str]] | None = None
_REWRITE_MIN_ISSUES = 3
_REWRITE_STRONG_ISSUES = 5
_DENSITY_REWRITE_MIN = 1.0
_DENSITY_SYSTEMATIC = 3.0
_COHESION_REWRITE_SAFE = 6.0
@dataclass(frozen=True)
class _RewriteSignals:
    total_issues: int
    density: float
    coupling: float
    is_systematic: bool
def _issue_values(issues: Iterable[str] | None) -> tuple[str, ...]:
    if not isinstance(issues, (list, tuple, set, frozenset)):
        return ()
    return tuple(item for item in _stable_items(issues) if isinstance(item, str))
def _issue_count(analysis: FileAnalysis) -> int:
    return (len(_issue_values(analysis.quality_issues))
            + len(_issue_values(analysis.logic_issues)))
def _rewrite_signals(
    fpath: str,
    analysis: FileAnalysis,
) -> _RewriteSignals | None:
    total_issues = _issue_count(analysis)
    if total_issues < _REWRITE_MIN_ISSUES:
        return None
    line_count = _bounded_finite_or_none(analysis.line_count)
    if line_count is None:
        _log.warning("[Boundary] 跳过重写 %s: 行数证据非法 %r",
                     Path(fpath).name, analysis.line_count)
        return None
    density = total_issues * 100 / max(1.0, line_count)
    cohesion_score = _bounded_finite_or_none(
            analysis.cohesion_score, maximum=_SCORE_MAX)
    if cohesion_score is None:
        _log.warning("[Boundary] 跳过重写 %s: 内聚度证据非法 %r",
                     Path(fpath).name, analysis.cohesion_score)
        return None
    coupling_score = _bounded_finite_or_none(
            analysis.coupling_score, maximum=_SCORE_MAX)
    if coupling_score is None:
        _log.warning("[Boundary] 跳过重写 %s: 耦合度证据非法 %r",
                     Path(fpath).name, analysis.coupling_score)
        return None
    if density < _DENSITY_REWRITE_MIN and cohesion_score >= _COHESION_REWRITE_SAFE:
        _log.info("[Boundary] 跳过重写 %s: 问题密度 %.1f 较低且内聚度 %.1f",
                  Path(fpath).name, density, cohesion_score)
        return None
    return _RewriteSignals(
        total_issues=total_issues,
        density=density,
        coupling=coupling_score,
        is_systematic=_is_systematic_rewrite(analysis, density),
    )
def _is_systematic_rewrite(analysis: FileAnalysis, density: float) -> bool:
    return (density >= _DENSITY_SYSTEMATIC
            or _issues_contain(_issue_values(analysis.logic_issues), "值冲突")
            or _has_vars_and_god_class(analysis))
def _issues_contain(issues: Iterable[str], marker: str) -> bool:
    return any(marker in issue for issue in issues)
def _has_vars_and_god_class(analysis: FileAnalysis) -> bool:
    quality_issues = _issue_values(analysis.quality_issues)
    return (_issues_contain(quality_issues, "上帝类")
            and _issues_contain(quality_issues, "模块级变量过多"))
def find_rewrite_candidates(
    file_analyses: dict[str, FileAnalysis],
) -> list[SplitMergeAction]:
    candidates: list[SplitMergeAction] = []
    analyses = _coerce_analysis_mapping(
        file_analyses, "find_rewrite_candidates")
    for fpath, analysis in analyses.items():
        signals = _rewrite_signals(fpath, analysis)
        if signals is None:
            continue
        if not signals.is_systematic:
            _log.info("[Boundary] %s 问题密度 %.1f 但非系统性结构问题，"
                      "不产 rewrite 候选（走精确修复路径）",
                      Path(fpath).name, signals.density)
            continue
        candidates.append(_rewrite_action(fpath, analysis, signals))
    return candidates
def _rewrite_action(
    fpath: str, analysis: FileAnalysis, signals: _RewriteSignals,
) -> SplitMergeAction:
    quality_issues = _issue_values(analysis.quality_issues)
    logic_issues = _issue_values(analysis.logic_issues)
    functions = (_stable_items(analysis.functions)
                 if isinstance(analysis.functions,
                               (list, tuple, set, frozenset)) else ())
    signatures = [f"{func} 签名须保持不变" for func in functions]
    return SplitMergeAction(
        action_type="rewrite",
        source_files=[fpath],
        reason=f"文件存在 {len(quality_issues)} 个质量问题 "
               f"和 {len(logic_issues)} 个逻辑问题"
               f"（密度 {signals.density:.1f}/百行，系统性结构问题）",
        boundary_justification=f"基于代码质量分析: 问题密度 {signals.density:.1f}/百行，"
                              f"耦合度 {signals.coupling:.1f}/10，"
                              f"({signals.total_issues} 个问题/{analysis.line_count} 行)，"
                              f"需要重写解决质量和逻辑问题，"
                              f"重写前确认所有公开函数签名不变",
        is_systematic=signals.is_systematic,
        is_size_based=False,
        code_elements=[*quality_issues, *logic_issues, *signatures],
        fix_approach=FIX_APPROACH_ROOT_CAUSE,
    )
def resolve_boundary_conflicts(
    result: BoundaryAnalysisResult,
    file_analyses: dict[str, FileAnalysis],
) -> BoundaryAnalysisResult:
    if not isinstance(result, BoundaryAnalysisResult):
        _log.warning(
            "[Boundary] 仲裁跳过: 边界结果非 BoundaryAnalysisResult 形状: %s",
            type(result).__name__)
        return BoundaryAnalysisResult()
    file_analyses = _coerce_analysis_mapping(
        file_analyses, "resolve_boundary_conflicts")
    conflicting = _conflicting_file_types(result)
    if not conflicting:
        return result
    _log.info("[Boundary] 发现 %d 个冲突文件，开始仲裁", len(conflicting))
    for fpath in conflicting:
        analysis = file_analyses.get(fpath)
        if not analysis:
            continue
        _arbitrate_file_conflicts(fpath, analysis, result)
    return result
def _conflicting_file_types(
    result: BoundaryAnalysisResult,
) -> dict[str, set[str]]:
    file_types: dict[str, set[str]] = defaultdict(set)
    for attr in _ACTION_CANDIDATE_ATTR.values():
        for action in _iter_action_items(
                getattr(result, attr, ()), f"boundary_result.{attr}"):
            action_type = _route_action_type(action)
            for src in _action_path_field(action, "source_files"):
                file_types[src].add(action_type)
    return {f: types for f, types in file_types.items() if len(types) > 1}
_ACTION_CANDIDATE_ATTR: dict[str, str] = {
    "split": "split_candidates",
    "merge": "merge_candidates",
    "migrate": "migrate_candidates",
    "rewrite": "rewrite_candidates",
}
def _has_action(
    result: BoundaryAnalysisResult, fpath: str, action_type: str,
) -> bool:
    attr = _ACTION_CANDIDATE_ATTR[action_type]
    return any(
        fpath in _action_path_field(action, "source_files")
        for action in _iter_action_items(
            getattr(result, attr, ()), f"boundary_result.{attr}"))
def _drop_candidates_for_file(
    result: BoundaryAnalysisResult, action_type: str, fpath: str,
) -> None:
    attr = _ACTION_CANDIDATE_ATTR[action_type]
    kept = [
        action for action in _iter_action_items(
            getattr(result, attr, ()), f"boundary_result.{attr}")
        if fpath not in _action_path_field(action, "source_files")
    ]
    setattr(result, attr, kept)
def _rule_keep(
    fpath: str,
    result: BoundaryAnalysisResult,
    left_type: str,
    right_type: str,
    winner: str,
) -> None:
    loser = right_type if winner == left_type else left_type
    _log.info("[Boundary] 仲裁 %s: %s↔%s → 保留 %s",
              Path(fpath).name, left_type, right_type, winner)
    _drop_candidates_for_file(result, loser, fpath)
def _rule_split_vs_rewrite(
    fpath: str, analysis: FileAnalysis, result: BoundaryAnalysisResult,
) -> None:
    if _issue_count(analysis) >= _REWRITE_STRONG_ISSUES:
        _log.info("[Boundary] 仲裁 %s: split↔rewrite → 保留 rewrite (问题多)",
                  Path(fpath).name)
        _drop_candidates_for_file(result, "split", fpath)
        return
    cohesion_score = _bounded_finite_or_none(
            analysis.cohesion_score, maximum=_SCORE_MAX)
    if cohesion_score is not None and cohesion_score < COHESION_STRONG_SIGNAL:
        _log.info("[Boundary] 仲裁 %s: split↔rewrite → 保留 split (低内聚)",
                  Path(fpath).name)
        _drop_candidates_for_file(result, "rewrite", fpath)
        return
    _log.info("[Boundary] 仲裁 %s: split↔rewrite → 保留并存待人工确认"
              "（内聚度 %s，问题数 %d）", Path(fpath).name,
              "未度量" if cohesion_score is None else f"{cohesion_score:.2f}",
              _issue_count(analysis))
_ARBITRATION_RULES: tuple[tuple[str, str, str | None], ...] = (
    ("split", "merge", "split"),
    ("split", "migrate", "split"),
    ("split", "rewrite", None),
    ("merge", "migrate", "merge"),
    ("merge", "rewrite", "rewrite"),
    ("migrate", "rewrite", "rewrite"),
)
def _arbitrate_file_conflicts(
    fpath: str,
    analysis: FileAnalysis,
    result: BoundaryAnalysisResult,
) -> None:
    for left, right, winner in _ARBITRATION_RULES:
        if not (_has_action(result, fpath, left)
                and _has_action(result, fpath, right)):
            continue
        if winner is None:
            _rule_split_vs_rewrite(fpath, analysis, result)
            continue
        _rule_keep(fpath, result, left, right, winner)
MERGE_GROUP_MAX = 4
MERGE_GROUPS_PER_CHAIN = 8
_COHESION_CONTRACT_ONLY = 2.0
_COHESION_SPLIT_EXEMPT = 5.0
_PAIR_EDGE_THRESHOLD_FACTOR = 3
def _split_candidate(
    fpath: str, reason: str, justification: str,
    code_elements: list[str],
) -> SplitMergeAction:
    return SplitMergeAction(
        action_type='split',
        source_files=[fpath],
        reason=reason,
        boundary_justification=justification,
        is_size_based=False,
        code_elements=code_elements,
    )
def find_split_candidates(
    file_analyses: dict[str, FileAnalysis],
    get_tree: Callable[[str], ast.AST | None],
) -> list[SplitMergeAction]:
    candidates: list[SplitMergeAction] = []
    analyses = _coerce_analysis_mapping(
        file_analyses, "find_split_candidates")
    for fpath, analysis in analyses.items():
        line_count = _valid_line_count(analysis.line_count)
        if line_count is None:
            _log.warning("[Boundary] 跳过拆分 %s: 行数证据非法 %r",
                         Path(fpath).name, analysis.line_count)
            continue
        try:
            tree = get_tree(fpath) if line_count > LINE_LIMIT else None
        except Exception as e:  # noqa: BLE001 — 单文件 AST 失败不阻断全量扫描
            _log.warning(
                "[Boundary] 拆分候选 AST 获取失败,按无 AST 降级 %s: %s",
                Path(fpath).name, e)
            tree = None
        hard = check_split_trigger(line_count, tree)
        candidate = _governance_candidate(fpath, analysis, hard)
        if candidate is not None:
            candidates.append(candidate)
    return candidates
def _governance_candidate(
    fpath: str,
    analysis: FileAnalysis,
    hard: SplitTriggerResult,
) -> SplitMergeAction | None:
    if hard.triggered:
        return _hard_trigger_candidate(fpath, analysis, hard)
    return _mixed_responsibility_candidate(fpath, analysis)
def _hard_trigger_candidate(
    fpath: str,
    analysis: FileAnalysis,
    hard: SplitTriggerResult,
) -> SplitMergeAction:
    return _split_candidate(
        fpath,
        "治理候选（M-03 硬触发）: " + hard.reason
        + "；须以非拆分手段治理，禁止直接拆分",
        f"M-03 治理候选定位: 文件 {hard.line_count} 行 > {LINE_LIMIT} 行上限 "
        f"且 AST 顶层功能域混杂 {hard.top_level_domain_count} 类"
        f"（>={_MIN_MIXED_DOMAINS}）；"
        "按功能内聚改为简化逻辑/消除重复/收敛依赖/迁移代码/"
        "提取同模块内私有实现，不新增文件边界",
        hard.domains,
    )
def _mixed_responsibility_candidate(
    fpath: str, analysis: FileAnalysis,
) -> SplitMergeAction | None:
    blocks = _fa_list_items(analysis, "substantial_unrelated_blocks")
    if not (_fa_flag(analysis, "has_mixed_responsibilities") and blocks):
        return None
    cohesion_score = _bounded_finite_or_none(
            analysis.cohesion_score, maximum=_SCORE_MAX)
    if cohesion_score is None:
        _log.warning("[Boundary] 跳过拆分 %s: 内聚度证据非法 %r",
                     Path(fpath).name, analysis.cohesion_score)
        return None
    if cohesion_score >= _COHESION_SPLIT_EXEMPT:
        _log.info("[Boundary] 跳过拆分 %s: 内聚度 %.1f 较高，暂不分",
                  Path(fpath).name, cohesion_score)
        return None
    if _shared_base_protected(fpath, analysis):
        return None
    split_strength = _split_signal_label(cohesion_score)
    return _split_candidate(
        fpath,
        f"治理候选（{split_strength}信号）: 文件包含混合职责 "
        f"({analysis.module_responsibility})，"
        f"存在 {len(blocks)} 组无关联代码块"
        f"（内聚度{cohesion_score:.2f}）；须非拆分治理",
        f"治理候选定位依据（非拆分授权）: 文件内存在多个不相关的"
        f"职责域 ({analysis.module_responsibility})，内聚度"
        f"{cohesion_score:.2f}/10，"
        f"非基于文件大小 ({analysis.size_bytes} bytes)；"
        f"治理手段限定为简化/去重/收敛/迁移/提取私有实现",
        blocks,
    )
def _split_signal_label(cohesion_score: float) -> str:
    return "强" if cohesion_score < COHESION_STRONG_SIGNAL else "弱"
def _shared_base_protected(fpath: str, analysis: FileAnalysis) -> bool:
    consumer_count = int_metric(analysis.shared_base_consumers, -1)
    if consumer_count < 0:
        _log.warning(
            "[Boundary] M-04 消费方计数证据非法，保守跳过拆分 %s: %r",
            Path(fpath).name, analysis.shared_base_consumers)
        return True
    shared = is_shared_base(consumer_count)
    if not shared.is_shared_base:
        return False
    cohesion_score = _bounded_finite_or_none(
            analysis.cohesion_score, maximum=_SCORE_MAX)
    if cohesion_score is None:
        _log.warning("[Boundary] M-04 共享底座保护跳过 %s: 内聚度证据非法 %r",
                     Path(fpath).name, analysis.cohesion_score)
        return False
    if cohesion_score > _COHESION_CONTRACT_ONLY:
        return False
    _log.info("[Boundary] M-04 共享底座保护: 跳过拆分 %s — %s"
              "（纯契约指纹: 内聚度 %.2f <= %.1f）",
              Path(fpath).name, shared.reason,
              cohesion_score, _COHESION_CONTRACT_ONLY)
    return True
class _GreedyClusterState:
    __slots__ = ('_by_path', '_next_gid', 'group_lines', 'groups', 'member_group')
    def __init__(self, by_path: dict[str, FileAnalysis]) -> None:
        self._by_path = by_path
        self.member_group: dict[str, int] = {}
        self.groups: dict[int, list[str]] = {}
        self.group_lines: dict[int, int] = {}
        self._next_gid = 0
    def try_join(self, a: str, b: str) -> None:
        if a == b:
            return
        ga = self.member_group.get(a)
        gb = self.member_group.get(b)
        if ga is not None:
            if gb is None:
                self._join_existing_group(ga, b)
            elif ga != gb:
                self._join_two_groups(ga, gb)
            return
        if gb is None:
            self._create_new_group(a, b)
            return
        self._join_existing_group(gb, a)
    def _create_new_group(self, a: str, b: str) -> None:
        lines = self._by_path[a].line_count + self._by_path[b].line_count
        if lines > LINE_LIMIT:
            return
        self._next_gid += 1
        gid = self._next_gid
        self.groups[gid] = [a, b]
        self.group_lines[gid] = lines
        self.member_group[a] = gid
        self.member_group[b] = gid
    def _join_existing_group(self, gid: int, other: str) -> None:
        if len(self.groups[gid]) >= MERGE_GROUP_MAX:
            return
        if self.group_lines[gid] + self._by_path[other].line_count > LINE_LIMIT:
            return
        self.groups[gid].append(other)
        self.group_lines[gid] += self._by_path[other].line_count
        self.member_group[other] = gid
    def _join_two_groups(self, ga: int, gb: int) -> None:
        big, small = (
            (ga, gb) if len(self.groups[ga]) >= len(self.groups[gb])
            else (gb, ga))
        if (len(self.groups[big]) + len(self.groups[small]) > MERGE_GROUP_MAX
                or self.group_lines[big] + self.group_lines[small] > LINE_LIMIT):
            return
        for x in self.groups[small]:
            self.member_group[x] = big
        self.groups[big].extend(self.groups.pop(small))
        self.group_lines[big] += self.group_lines.pop(small)
def _strong_pair_edges(
    paths: list[str],
    weighted_graph: dict[str, dict[str, float]],
    weight_threshold: float,
) -> list[tuple[float, str, str]]:
    edges: list[tuple[float, str, str]] = []
    paths = sorted(paths)
    for i, a in enumerate(paths):
        for b in paths[i + 1:]:
            weight = (_edge_weight(weighted_graph, a, b)
                      + _edge_weight(weighted_graph, b, a))
            if weight >= weight_threshold * _PAIR_EDGE_THRESHOLD_FACTOR:
                edges.append((weight, a, b))
    edges.sort(key=lambda edge: (-edge[0], edge[1], edge[2]))
    return edges
def _group_weight(members: list[str],
                  weighted_graph: dict[str, dict[str, float]]) -> float:
    return sum(
        _edge_weight(weighted_graph, m, o)
        for m in members for o in members if m != o)
def cluster_merge_groups(valid_members: list[FileAnalysis],
                         weighted_graph: dict[str, dict[str, float]],
                         weight_threshold: float) -> list[list[str]]:
    threshold = _positive_finite_or_none(weight_threshold)
    if threshold is None:
        _log.warning(
            "[Boundary] 合并聚类跳过: 权重阈值证据非法 %r", weight_threshold)
        return []
    by_path = {m.filepath: m for m in valid_members}
    edges = _strong_pair_edges(
        [m.filepath for m in valid_members],
        weighted_graph, threshold)
    cluster = _GreedyClusterState(by_path)
    for _weight, a, b in edges:
        cluster.try_join(a, b)
    result = [g for g in cluster.groups.values()
              if len(g) >= _MIN_MERGE_MEMBERS]
    result.sort(key=lambda g: (-_group_weight(g, weighted_graph), tuple(g)))
    if len(result) > MERGE_GROUPS_PER_CHAIN:
        _log.info("[Boundary] 单链合并组超过上限,截断 %d -> %d 组",
                  len(result), MERGE_GROUPS_PER_CHAIN)
    return result[:MERGE_GROUPS_PER_CHAIN]
def place_cycle_group(merge_members: list[str],
                      reverse_import_graph: dict[str, set[str]],
                      chain_id: str) -> None:
    merge_members = _coerce_group_members(
        merge_members, "place_cycle_group")
    if not merge_members:
        _log.warning("[Boundary] M-02 成环归位跳过: 空合并组 (chain %s)", chain_id)
        return
    reverse_import_graph = (reverse_import_graph
                            if isinstance(reverse_import_graph, dict) else {})
    usage: dict[str, int] = {}
    for member in merge_members:
        for importer in _name_entries(
                reverse_import_graph.get(member, ()),
                "reverse_import_graph"):
            if importer not in merge_members:
                usage[importer] = usage.get(importer, 0) + 1
    primary = place_to_primary_consumer(usage, sorted(usage))
    if primary:
        _log.info("[Boundary] M-02 成环，建议归位到主要使用方: %s", primary)
    else:
        _log.info("[Boundary] M-02 成环: 链 %s 合并组无组外消费方，"
                  "归位目标由上层决策", chain_id)
def resolve_stratified_cycles(
    context: dict[str, Any],
    file_analyses: dict[str, FileAnalysis],
) -> dict[str, Any] | None:
    context = _normalize_context(context, "循环导入检测")
    file_analyses = _coerce_analysis_mapping(
        file_analyses, "resolve_stratified_cycles")
    stratified = context.get("circular_imports")
    if stratified is not None and not isinstance(stratified, dict):
        _log.warning(
            "[Boundary] 诊断报告 circular_imports 非 dict 形状,按空处理: %s",
            type(stratified).__name__)
        stratified = None
    if not file_analyses or stratified:
        return stratified
    try:
        return detect_circular_imports_stratified(file_analyses)
    except Exception as e:  # noqa: BLE001 — 通道级软失败隔离
        _log.warning("[Boundary] 诊断报告循环导入检测失败: %s", e)
        return None
def _type_label(expected: type | tuple[type, ...]) -> str:
    if isinstance(expected, type):
        return expected.__name__
    return "/".join(t.__name__ for t in expected)
def _normalize_context(context: object, scope: str) -> dict[str, Any]:
    if isinstance(context, dict):
        return context
    _log.warning("[RefactorGuard] %s 顶层上下文非 dict 形状,按空处理: %s",
                 scope, type(context).__name__)
    return {}
def _coerce_typed(context: dict[str, Any], key: str,
                  expected: type | tuple[type, ...],
                  scope: str) -> Any:
    value = context.get(key)
    if value is not None and not isinstance(value, expected):
        _log.warning(
            "[RefactorGuard] %s %s 非 %s 形状,按空处理: %s",
            scope, key, _type_label(expected), type(value).__name__)
        return None
    return value
def _iter_action_items(actions: object, scope: str) -> Iterator[SplitMergeAction]:
    if not isinstance(actions, (list, tuple)):
        _log.warning("[RefactorGuard] %s 非清单形状,按空处理: %s",
                       scope, type(actions).__name__)
        return
    for index, action in enumerate(actions):
        if isinstance(action, SplitMergeAction):
            yield action
            continue
        _log.warning(
            "[RefactorGuard] %s[%d] 非 SplitMergeAction 形状,跳过: %s",
            scope, index, type(action).__name__)
def _iter_route_actions(route: RefactoringRoute) -> Iterator[SplitMergeAction]:
    yield from _iter_action_items(
        getattr(route, "actions", ()), "refactoring_route.actions")
def _coerce_file_analyses(context: dict[str, Any]) -> dict[str, FileAnalysis]:
    file_analyses = _coerce_typed(
        context, "file_analyses", dict, "诊断报告") or {}
    return _coerce_analysis_mapping(file_analyses, "诊断报告")
def _valid_stratified_cycle(cycle: Any, key: str) -> bool:
    if not isinstance(cycle, (list, tuple)):
        _log.warning(
            "[RefactorGuard] 分层环报告 %s 含非清单条目,跳过该条: %r",
            key, type(cycle).__name__)
        return False
    if not cycle:
        _log.warning("[RefactorGuard] 分层环报告 %s 含空环条目,跳过该环", key)
        return False
    if not all(isinstance(p, str) for p in cycle):
        _log.warning(
            "[RefactorGuard] 分层环报告 %s 环条目含非 str 路径元素,跳过该环: %r",
            key, [type(p).__name__ for p in cycle])
        return False
    if any(not p.strip() for p in cycle):
        _log.warning(
            "[RefactorGuard] 分层环报告 %s 环条目含空白路径元素,跳过该环", key)
        return False
    return True
def _iter_stratified_cycles(
    stratified: dict[str, Any],
    key: str,
) -> Iterator[list[str]]:
    cycles = stratified.get(key)
    if cycles is None:
        return
    if not isinstance(cycles, (list, tuple)):
        _log.warning(
            "[RefactorGuard] 分层环报告 %s 非清单形状,按空处理: %r",
            key, type(cycles).__name__)
        return
    for cycle in cycles:
        if _valid_stratified_cycle(cycle, key):
            yield cycle
class _FindingSink:
    def __init__(self) -> None:
        self.findings: list[dict[str, Any]] = []
        self.method_details: dict[str, Any] = {}
        self._seq = 0
    def add(self, category: str, severity: str, description: str,
            method_id: str, confidence: float = 0.9) -> None:
        self._seq += 1
        fid = f"RF-{self._seq:04d}"
        self.findings.append({
            "finding_id": fid,
            "category": category,
            "severity": severity,
            "conclusion": "confirmed",
            "confidence": confidence,
            "sources": [{"method_id": method_id, "confidence": confidence}],
            "description": description,
        })
        detail = self.method_details.setdefault(method_id, {
            "method_name": method_id,
            "findings": [],
            "status": "completed",
        })
        detail["findings"].append({
            "finding_id": fid, "category": category,
            "severity": severity, "description": description,
        })
_FA_FINDING_RULES: tuple[tuple[str, str, str, str], ...] = (
    ("unused_imports", "unused_import", "P2", "{fname}: 未使用导入 {item}"),
    ("reexport_bridges", "reexport_bridge", "P1", "{fname}: 重导出桥接 {item}"),
    ("dead_constants", "dead_constant", "P2", "{fname}: 死常量 {item}"),
    ("cascade_dead_candidates", "cascade_dead_code", "P2", "{fname}: 级联死代码候选 {item}"),
    ("cross_file_duplicates", "cross_file_duplicate", "P2", "{fname}: 跨文件重复定义 {item}"),
    ("quality_issues", "quality_issue", "P1", "{fname}: {item}"),
    ("logic_issues", "logic_issue", "P1", "{fname}: {item}"),
    ("unrelated_code_blocks", "unrelated_code", "P1", "{fname}: 无关联代码块 {item}"),
)
_FA_BOUNDARY_RULES = (
    ("mixed_responsibility", "{fname}: 职责混合", 0.9,
     lambda metrics: metrics["mixed"]),
    ("high_coupling", "{fname}: 耦合度 {coupling:.1f}", 0.85,
     lambda metrics: (metrics["coupling"] is not None
                      and metrics["coupling"] > _HIGH_COUPLING_THRESHOLD)),
    ("low_cohesion", "{fname}: 内聚度 {cohesion:.1f}", 0.85,
     lambda metrics: (metrics["cohesion"] is not None
                      and metrics["cohesion"] < _COHESION_HEALTHY_MIN)),
)
def _fa_list_items(fa: FileAnalysis, attr: str) -> list:
    value = getattr(fa, attr, None)
    if value is None:
        return []
    if isinstance(value, (list, tuple)):
        return list(value)
    if isinstance(value, (set, frozenset)):
        return sorted(value, key=str)
    _log.warning(
        "[RefactorGuard] 诊断报告 file_analyses.%s 非清单形状,按空处理: %r",
        attr, type(value).__name__)
    return []
def _fa_number(fa: FileAnalysis, attr: str) -> float | None:
    value = getattr(fa, attr, None)
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        _log.warning(
            "[RefactorGuard] 诊断报告 file_analyses.%s 非数值形状,按未知跳过: %r",
            attr, type(value).__name__)
        return None
    number = _bounded_finite_or_none(value, maximum=_SCORE_MAX)
    if number is None:
        _log.warning(
            "[RefactorGuard] 诊断报告 file_analyses.%s 非有限或超出 [0, 10],按未知跳过: %r",
            attr, type(value).__name__)
    return number
def _fa_flag(fa: FileAnalysis, attr: str) -> bool:
    value = getattr(fa, attr, False)
    if value is None:
        return False
    if isinstance(value, bool):
        return value
    _log.warning(
        "[RefactorGuard] 诊断报告 file_analyses.%s 非布尔形状,按 False 处理: %r",
        attr, type(value).__name__)
    return False
def _fa_boundary_metrics(fname: str, fa: FileAnalysis) -> dict:
    return {
        "fname": fname,
        "coupling": _fa_number(fa, "coupling_score"),
        "cohesion": _fa_number(fa, "cohesion_score"),
        "mixed": _fa_flag(fa, "has_mixed_responsibilities"),
    }
def _collect_file_analysis_findings(
    context: dict[str, Any],
    sink: _FindingSink,
) -> dict[str, FileAnalysis]:
    file_analyses = _coerce_file_analyses(context)
    for filepath, fa in file_analyses.items():
        fname = Path(filepath).name
        for attr, category, severity, fmt in _FA_FINDING_RULES:
            for item in _fa_list_items(fa, attr):
                sink.add(category, severity,
                             fmt.format(fname=fname, item=item), "deep_analysis")
        metrics = _fa_boundary_metrics(fname, fa)
        for category, fmt, confidence, matches in _FA_BOUNDARY_RULES:
            if matches(metrics):
                sink.add(category, "P1", fmt.format(**metrics),
                         "boundary_analysis", confidence)
    return file_analyses
_CYCLE_FINDING_RULES: tuple[tuple[str, str, str, str], ...] = (
    ("module_level_cycles", "circular_import", "P1", "模块级循环导入（危险环）"),
    ("lazy_only_cycles", "lazy_import_cycle", "P3", "仅函数级 lazy import 构成的安全环"),
)
def _collect_circular_import_findings(
    context: dict[str, Any],
    file_analyses: dict[str, FileAnalysis],
    sink: _FindingSink,
) -> None:
    stratified = resolve_stratified_cycles(context, file_analyses)
    if not stratified:
        return
    for key, category, severity, prefix in _CYCLE_FINDING_RULES:
        for cycle in _iter_stratified_cycles(stratified, key):
            names = " → ".join(Path(f).name for f in cycle)
            sink.add(category, severity,
                         f"{prefix}: {names}", "boundary_analysis")
def _coerce_cross_skill_items(
    context: dict[str, Any],
) -> list[dict[str, Any]]:
    raw = _coerce_typed(
        context, "cross_skill_imports",
        (list, tuple, set, frozenset), "诊断报告") or []
    valid = [vio for vio in raw if isinstance(vio, dict)]
    if len(valid) != len(raw):
        _log.warning(
            "[RefactorGuard] 诊断报告跳过 %d 个非 dict 跨技能导入项",
            len(raw) - len(valid))
    return valid
def _violation_file(vio: dict[str, Any]) -> str:
    file = vio.get("file")
    if file is None:
        return ""
    try:
        path = os.fspath(file)
    except TypeError as exc:
        log_swallowed(__name__, exc, context="_violation_file:TypeError")
        path = None
    if isinstance(path, str):
        return path
    _log.warning(
        "[RefactorGuard] 诊断报告 cross_skill_imports file 非路径形状,按空处理: %s",
        type(file).__name__)
    return ""
def _violation_imports(vio: dict[str, Any]) -> str:
    raw = vio.get("imports", "")
    if isinstance(raw, (set, frozenset)):
        raw = sorted(raw, key=str)
    if isinstance(raw, (list, tuple)):
        return ", ".join(str(item) for item in raw)
    return str(raw or "")
def _collect_cross_skill_findings(
    context: dict[str, Any],
    sink: _FindingSink,
) -> None:
    for vio in _coerce_cross_skill_items(context):
        fname = Path(_violation_file(vio)).name or "<unknown>"
        sink.add(
            "cross_skill_import", "P1",
            f"{fname}: 跨技能导入 {_violation_imports(vio)} "
            f"({vio.get('from_skill') or ''!s} → "
            f"{vio.get('to_skill') or ''!s})",
            "boundary_analysis")
_BOUNDARY_FINDING_RULES: tuple[tuple[str, str, str], ...] = (
    ("split_candidates", "split_candidate", "治理候选（非拆分）"),
    ("merge_candidates", "merge_candidate", "建议合并"),
    ("migrate_candidates", "migrate_candidate", "建议迁移"),
    ("rewrite_candidates", "rewrite_candidate", "建议重写"),
)
def _collect_boundary_findings(
    context: dict[str, Any],
    sink: _FindingSink,
) -> None:
    boundary: BoundaryAnalysisResult | None = _coerce_typed(
        context, "boundary_result", BoundaryAnalysisResult, "诊断报告")
    if not boundary:
        return
    for attr, category, default_reason in _BOUNDARY_FINDING_RULES:
        for action in _iter_action_items(
                getattr(boundary, attr), f"boundary_result.{attr}"):
            sink.add(
                category,
                _route_action_priority(_route_action_type(action)),
                str(action.reason or default_reason),
                "boundary_analysis")
def _route_action_type(action: SplitMergeAction) -> str:
    value = getattr(action, "action_type", "")
    return value if isinstance(value, str) else ""
def _route_action_priority(action_type: object) -> str:
    return "P1" if action_type in ("split", "merge", "governance") else "P2"
def _collect_route_findings(
    context: dict[str, Any],
    sink: _FindingSink,
) -> None:
    route: RefactoringRoute | None = _coerce_typed(
        context, "refactoring_route", RefactoringRoute, "桥接")
    if not route:
        return
    for action in _iter_route_actions(route):
        sink.add("refactor_action",
                 _route_action_priority(_route_action_type(action)),
                 f"{_route_action_type(action)}: {_route_action_reason(action)}",
                 "route_planning", 0.8)
def _methodology_constraint_payload() -> list[dict[str, str]]:
    return [
        {"name": c.name, "description": c.description,
         "error_message": c.error_message}
        for c in ALL_CONSTRAINTS
    ]
def build_refactor_diagnosis_report(context: dict[str, Any]) -> dict[str, Any]:
    context = _normalize_context(context, "诊断报告")
    sink = _FindingSink()
    file_analyses = _collect_file_analysis_findings(context, sink)
    _collect_circular_import_findings(context, file_analyses, sink)
    _collect_cross_skill_findings(context, sink)
    _collect_boundary_findings(context, sink)
    _collect_route_findings(context, sink)
    write_module_run(
        "build_refactor_plan", "build_refactor_diagnosis_report",
        findings=len(sink.findings))
    return {  # jwsgj:suppress RT-01 — 审计认可：复盘引擎诊断报告桥接格式，键面由目标报告契约（findings_index/summary 等）定义，非缺陷
        "summary": {
            "total_findings": len(sink.findings),
            "timestamp": timestamp_ms(),
            "source": "refactor_workflow",
        },
        "findings_index": sink.findings,
        "layers": {
            "layer2": {
                "method_details": sink.method_details,
            },
        },
        "rules_detail": [],
        "methodology_constraints": _methodology_constraint_payload(),
    }
_ROUTE_ACTION_RULE_PREFIX: dict[str, str] = {
    "migrate": "RF-MIG",
    "rewrite": "RF-RW",
    "split": "RF-SPLIT",
    "merge": "RF-MERGE",
    "governance": "RF-GOV",
}
def _route_action_rule_ids(
    route: RefactoringRoute,
) -> Iterator[tuple[SplitMergeAction, str, int]]:
    counters: dict[str, int] = defaultdict(int)
    for action in _iter_route_actions(route):
        action_type = _route_action_type(action)
        prefix = _ROUTE_ACTION_RULE_PREFIX.get(action_type, "RF-ACT")
        index = counters[prefix]
        counters[prefix] = index + 1
        yield action, f"{prefix}-{index:04d}", index
def rel_to_skill_dir(fpath: str, skill_dir: str) -> str:
    if fpath is None:
        return ""
    try:
        path = os.fspath(fpath)
    except TypeError:
        return str(fpath)
    if not isinstance(path, str):
        return str(fpath)
    if not path.strip():
        return ""
    if not os.path.isabs(path):
        return Path(path).as_posix()
    skill_root = ""
    if skill_dir is not None:
        try:
            skill_root = os.fspath(skill_dir) or ""
        except TypeError:
            skill_root = ""
    if not isinstance(skill_root, str) or not skill_root.strip():
        return Path(path).as_posix()
    try:
        return Path(os.path.relpath(path, skill_root)).as_posix()
    except (ValueError, OSError) as _e:
        log_swallowed(__name__, _e, context="rel_to_skill_dir:ValueError")
        return Path(path).as_posix()
def _action_path_field(action: SplitMergeAction, field: str) -> list[str]:
    values = getattr(action, field, ())
    action_type = getattr(action, "action_type", type(action).__name__)
    if isinstance(values, (str, os.PathLike)):
        values = [values]
    if not isinstance(values, (list, tuple)):
        _log.warning(
            "[RefactorGuard] 动作 %s 字段 %s 非清单形状,按空处理: %s",
            action_type, field, type(values).__name__)
        return []
    paths: list[str] = []
    dropped = 0
    for value in values:
        if isinstance(value, str):
            if value:
                paths.append(value)
            else:
                dropped += 1
            continue
        if not isinstance(value, os.PathLike):
            dropped += 1
            continue
        try:
            path = os.fspath(value)
        except TypeError as exc:
            log_swallowed(
                __name__, exc,
                context=f"_action_path_field:{field}:TypeError")
            dropped += 1
            continue
        if isinstance(path, str) and path:
            paths.append(path)
        else:
            dropped += 1
    if dropped:
        _log.warning("[RefactorGuard] 动作 %s 字段 %s 丢弃 %d 个非法路径元素",
                     action_type, field, dropped)
    return paths
def _route_action_locator(rule_id: str, source_files: list[str],
                          target_files: list[str]) -> str:
    path = (source_files[0] if source_files else
            target_files[0] if target_files else "")
    return f"{path}:0:{rule_id}" if path else rule_id
def _route_action_reason(action: SplitMergeAction) -> str:
    value = getattr(action, "reason", "")
    return value if isinstance(value, str) else str(value or "")
def _route_action_strategy(action: SplitMergeAction) -> str:
    for value in (getattr(action, "governance_method", None),
                  getattr(action, "action_type", None)):
        if isinstance(value, str) and value.strip():
            return value.strip()
        if isinstance(value, (list, tuple)):
            methods = [str(item).strip() for item in value
                       if isinstance(item, str) and item.strip()]
            if methods:
                return "/".join(methods)
    return "manual_confirm"
def _action_files(action: SplitMergeAction) -> list[str]:
    files: list[str] = []
    for field_name in ("source_files", "target_files"):
        files.extend(_action_path_field(action, field_name))
    return list(dict.fromkeys(files))
def _treatment_execution_details(
    context: dict[str, Any],
    route: RefactoringRoute | None,
) -> list[dict[str, Any]]:
    if not route:
        return []
    split_merge_executed = set(normalize_executed_action_ids(
        context.get("executed_split_merges")))
    spec_by_type = {
        "split": ("split", split_merge_executed),
        "merge": ("merge", split_merge_executed),
        "migrate": ("migration", set(normalize_executed_action_ids(
            context.get("executed_migrations")))),
        "rewrite": ("rewrite", set(normalize_executed_action_ids(
            context.get("executed_rewrites")))),
    }
    details: list[dict[str, Any]] = []
    split_merge_index = 0
    for action, rule_id, type_index in _route_action_rule_ids(route):
        action_type = _route_action_type(action)
        spec = spec_by_type.get(action_type)
        if spec is None:
            details.append({
                "rule_id": rule_id,
                # 明细状态须落在消费方（retrospective_audit._item_outcome_bucket）
                # 认可的治疗状态词表内；"pending" 不在词表中，会触发
                # 「未识别的非空执行状态」告警并被兜底归入 pending_confirm。
                "status": "pending_confirm",
                "method": action_type or "unknown",
                "files": _action_files(action),
            })
            continue
        method, executed = spec
        if action_type in ("split", "merge"):
            execution_index = split_merge_index
            split_merge_index += 1
        else:
            execution_index = type_index
        details.append({
            "rule_id": rule_id,
            "status": ("fixed" if execution_index in executed
                       else "pending_confirm"),
            "method": method,
            "files": _action_files(action),
        })
    return details
def build_refactor_treatment_execution(context: dict[str, Any]) -> dict[str, Any]:
    context = _normalize_context(context, "桥接")
    route = _coerce_typed(
        context, "refactoring_route", RefactoringRoute, "桥接")
    details = _treatment_execution_details(context, route)
    fixed_count = sum(1 for d in details if d["status"] == "fixed")
    pending_count = sum(
        1 for d in details if d["status"] == "pending_confirm")
    skipped_count = sum(1 for d in details if d["status"] == "skipped")
    write_module_run(
        "build_refactor_plan", "build_refactor_treatment_execution",
        total=len(details), fixed=fixed_count)
    return {
        "status": (
            "in_progress" if route is None or pending_count else "completed"),
        "details": details,
        "total": len(details),
        "fixed": fixed_count,
        "executed": fixed_count,
        "succeeded": fixed_count,
        "pending_confirm": pending_count,
        "failed": 0,
        "rolled_back": 0,
        "skipped": skipped_count,
        "fp_confirmed": 0,
        "suggestion": 0,
    }
def build_refactor_treatment_plan(context: dict[str, Any]) -> dict[str, Any]:
    context = _normalize_context(context, "桥接")
    route: RefactoringRoute | None = _coerce_typed(
        context, "refactoring_route", RefactoringRoute, "桥接")
    items: list[dict[str, Any]] = []
    if route:
        for i, (action, rule_id, _index) in enumerate(
                _route_action_rule_ids(route)):
            priority = _route_action_priority(_route_action_type(action))
            source_files = _action_path_field(action, "source_files")
            target_files = _action_path_field(action, "target_files")
            items.append({
                "item_id": f"RF-{i:04d}",
                "rule_id": rule_id,
                "locator": _route_action_locator(
                    rule_id, source_files, target_files),
                "severity": priority,
                "priority": priority,
                "strategy": _route_action_strategy(action),
                "action_type": _route_action_type(action),
                "reason": _route_action_reason(action),
                "source_files": source_files,
                "target_files": target_files,
            })
    execution_order = [
        item["locator"] for item in sorted(
            items, key=lambda item: 0 if item["priority"] == "P1" else 1)
    ]
    write_module_run(
        "build_refactor_plan", "build_refactor_treatment_plan",
        items=len(items))
    risk_level = "unknown"
    if route is not None:
        declared_risk = getattr(route, "risk_level", None)
        if isinstance(declared_risk, str) and declared_risk.strip():
            risk_level = declared_risk.strip()
    return {
        "items": items,
        "execution_order": execution_order,
        "total": len(items),
        "risk_level": risk_level,
    }

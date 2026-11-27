from __future__ import annotations

import logging
import os
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass
from itertools import chain
from pathlib import Path
from types import MappingProxyType
from typing import Any, NamedTuple, Self

from jwsgj.build_preflight_guard import attach_validation_result
from jwsgj.build_refactor_collect import ModuleBoundaryAnalyzer
from jwsgj.build_refactor_plan import RefactoringStateManager, rel_to_skill_dir
from jwsgj.build_refactor_policy import (
    ALL_CONSTRAINTS,
    CONSTRAINT_ALL_PY_ANALYZED,
    CONSTRAINT_BACKUP_BEFORE_MODIFY,
    CONSTRAINT_MERGE_ARGUMENT,
    CONSTRAINT_MERGE_COHESION_ONLY,
    CONSTRAINT_MIGRATION_DONE,
    CONSTRAINT_MIGRATION_NO_RESIDUAL,
    CONSTRAINT_NEXT_PHASE,
    CONSTRAINT_NO_BATCH_FIX,
    CONSTRAINT_NO_PATCH_FIX,
    CONSTRAINT_NO_SIZE_ONLY_MERGE,
    CONSTRAINT_NO_SIZE_ONLY_SPLIT,
    CONSTRAINT_NO_SPLIT_AS_GOVERNANCE,
    CONSTRAINT_PHASE_ORDER,
    CONSTRAINT_PLAN_BEFORE_EXECUTE,
    CONSTRAINT_REWRITE_DONE,
    CONSTRAINT_REWRITE_PRECONDITIONS,
    PHASE_ORDER,
    BoundaryAnalysisResult,
    RefactoringConstraint,
    RefactoringPhase,
    RefactoringRoute,
    RefactoringRoutePlanner,
    SplitMergeAction,
    _as_str_list,
    approved_split_actions,
    collect_modified_files,
    count_executed_actions,
    merge_argument_payload,
    read_modified_files,
    reconcile_governance_proposals,
    require_boundary_value,
    require_route_value,
    validate_refactoring_action,
)
from jwsgj.build_safe_write import BackupManager, quick_safe_backup
from jwsgj.build_skill_md_optimize import attach_best_practices
from jwsgj.build_skill_md_rewrite import (
    rebuild_skill_md,
    write_skill_md_text,
)
from jwsgj.build_text_document import write_markdown_text
from jwsgj.cleanup_file_hygiene import detect_new_compat_stubs
from jwsgj.diag_antipattern_flow_govern import (
    CircularDependencyResolver,
    module_name_under_root,
    run_boundary_coupling_diagnostics,
)
from jwsgj.pipeline_steps_phases import run_traced_entry
from jwsgj.refactor_decompose_actions import SplitExecutor
from jwsgj.refactor_write_actions import (
    DEFAULT_REFACTOR_DRY_RUN,
    BaseExecutor,
    ExecutorResult,
    MergeExecutor,
    MigrateExecutor,
    RewriteExecutor,
)
from jwsgj.retrospective_enhancer import run_retrospective_feedback
from jwsgj.shared_cache import ensure_entry_warmed
from jwsgj.skill_doc_refactor_guard import (
    compose_refactor_document,
    get_refactorer,
)

_log = logging.getLogger(__name__)
def _skill_dir_text(skill_dir: Any) -> str:
    raw = (os.fspath(skill_dir)
           if isinstance(skill_dir, (str, os.PathLike)) else "")
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError(
            f"无效的技能目录: {skill_dir!r}（须为非空字符串或路径对象）")
    return raw
def _finalize_workflow_reports(skill_dir: str,
                              context: dict[str, Any]) -> None:
    try:
        from jwsgj.build_refactor_plan import (
            build_refactor_diagnosis_report,
        )
        from jwsgj.pipeline_report_delivery import (
            finalize_completed_pipeline,
        )
        _diag = build_refactor_diagnosis_report(context)
        _findings = (_diag.get("findings_index")
                     if isinstance(_diag, dict) else None)
        if not isinstance(_findings, list):
            _findings = None
        finalize_completed_pipeline(
            skill_dir, dict(context),
            advance_phase=False, findings=_findings)
        _log.info(
            "[RefactorWorkflow] 最终汇总报告已收口（内存注入 %s 条发现）",
            len(_findings) if _findings else 0)
    except Exception as _fe:  # noqa: BLE001
        _log.warning(
            "[RefactorWorkflow] 最终汇总报告生成失败(不阻断): %s", _fe)
_ACTION_TYPE_KEYS: tuple[str, ...] = ("type", "action", "action_type")
def _first_action_type_value(container: Mapping) -> Any:
    for key in _ACTION_TYPE_KEYS:
        value = container.get(key)
        if value is None or (isinstance(value, str) and not value.strip()):
            continue
        return value
    return ""
def _action_type_of(action: object) -> str:
    if isinstance(action, Mapping):
        raw = _first_action_type_value(action)
    else:
        raw = getattr(action, "action_type", "")
    if isinstance(raw, str):
        return raw
    if raw is None:
        return ""
    _log.warning("[Dispatcher] 动作类型载荷形状非法(须为 str),已按 <%s> "
                 "类型标记并拒绝分发", type(raw).__name__)
    return f"<{type(raw).__name__}>"
_EXECUTOR_BY_ACTION: dict[str, type[BaseExecutor]] = {
    "split": SplitExecutor,
    "merge": MergeExecutor,
    "migrate": MigrateExecutor,
    "rewrite": RewriteExecutor,
}
def _is_positive_change_count(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0
class RefactoringExecutorDispatcher:
    def __init__(self, skill_dir: str,
                 dry_run: bool = DEFAULT_REFACTOR_DRY_RUN,
                 cache: Any = None) -> None:
        self.skill_dir = Path(_skill_dir_text(skill_dir))
        self.dry_run = bool(dry_run)
        self._cache = cache
        self.results: list[ExecutorResult] = []
    def dispatch(self, action: Any) -> ExecutorResult:
        action_type = _action_type_of(action)
        executor_cls = _EXECUTOR_BY_ACTION.get(action_type)
        if executor_cls is None:
            result = ExecutorResult(action_type=action_type, status="failed")
            result.error_message = f"不支持的操作类型: {action_type}"
            self.results.append(result)
            return result
        executor = executor_cls(str(self.skill_dir), self.dry_run,
                                cache=self._cache)
        result = executor.execute(action)
        self.results.append(result)
        return result
    def dispatch_all(self, actions: list[Any]) -> list[ExecutorResult]:
        if not isinstance(actions, (list, tuple)):
            _log.warning(
                "[Dispatcher] 批量派发载荷非序列(%s)，按空批次处理",
                type(actions).__name__)
            return []
        results = []
        for action in actions:
            result = self.dispatch(action)
            results.append(result)
        return results
    def summary(self) -> dict[str, Any]:
        total = len(self.results)
        success = sum(1 for r in self.results if r.status == "success")
        failed = sum(1 for r in self.results if r.status == "failed")
        changes = sum(
            r.changes_made for r in self.results
            if _is_positive_change_count(r.changes_made))
        no_change_actions = sum(
            1 for r in self.results
            if r.status == "success"
            and not _is_positive_change_count(r.changes_made))
        return {
            "total": total,
            "success": success,
            "failed": failed,
            "changes_made": changes,
            "no_change_actions": no_change_actions,
            "dry_run": self.dry_run,
        }
def _str_list(value: Any) -> list[str]:
    if isinstance(value, (str, os.PathLike)):
        raw_values = [value]
    elif isinstance(value, (list, tuple, set, frozenset)):
        raw_values = value
    else:
        return []
    normalized: list[Any] = []
    for item in raw_values:
        if isinstance(item, os.PathLike):
            try:
                item = os.fspath(item)
            except TypeError:
                continue
        normalized.append(item)
    if isinstance(value, (set, frozenset)):
        return _as_str_list(set(normalized))
    return _as_str_list(normalized)
_PAYLOAD_PATHS = "paths"
_PAYLOAD_TEXT = "text"
_PAYLOAD_TEXT_LIST = "text_list"
_PAYLOAD_TEXT_OR_LIST = "text_or_list"
_PAYLOAD_TEXT_OR_MAPPING = "text_or_mapping"
_PAYLOAD_BOOL = "bool"
_ACTION_PAYLOAD_SPEC: tuple[tuple[str, str, str], ...] = (
    ("type", "action_type", _PAYLOAD_TEXT),
    ("source", "source_files", _PAYLOAD_PATHS),
    ("target", "target_files", _PAYLOAD_PATHS),
    ("reason", "reason", _PAYLOAD_TEXT),
    ("boundary_justification", "boundary_justification", _PAYLOAD_TEXT),
    ("is_size_based", "is_size_based", _PAYLOAD_BOOL),
    ("code_elements", "code_elements", _PAYLOAD_TEXT_LIST),
    ("is_systematic", "is_systematic", _PAYLOAD_BOOL),
    ("precise_fix_attempted", "precise_fix_attempted", _PAYLOAD_BOOL),
    ("signature_preservation_confirmed", "signature_preservation_confirmed",
     _PAYLOAD_BOOL),
    ("new_code", "new_code", _PAYLOAD_TEXT),
    ("fix_approach", "fix_approach", _PAYLOAD_TEXT),
    ("governance_method", "governance_method", _PAYLOAD_TEXT_OR_LIST),
    ("governance_exception", "governance_exception",
     _PAYLOAD_TEXT_OR_MAPPING),
    ("exception_approved_by", "exception_approved_by", _PAYLOAD_TEXT),
    ("governance_decision_id", "governance_decision_id", _PAYLOAD_TEXT),
    ("pros", "pros", _PAYLOAD_TEXT_LIST),
    ("cons", "cons", _PAYLOAD_TEXT_LIST),
    ("net_benefit", "net_benefit", _PAYLOAD_TEXT),
    ("risk", "risk", _PAYLOAD_TEXT),
)
def _payload_value(action: Any, attr: str, kind: str,
                   skill_dir: str | None) -> Any:
    if kind == _PAYLOAD_PATHS:
        files = _str_list(getattr(action, attr, None))
        if skill_dir is None:
            return files
        return [rel_to_skill_dir(f, skill_dir) for f in files]
    if kind == _PAYLOAD_TEXT_LIST:
        return _str_list(getattr(action, attr, None))
    if kind == _PAYLOAD_TEXT_OR_LIST:
        raw = getattr(action, attr, "")
        return raw if isinstance(raw, str) else _str_list(raw)
    if kind == _PAYLOAD_TEXT_OR_MAPPING:
        raw = getattr(action, attr, "")
        return dict(raw) if isinstance(raw, dict) else _as_str(raw)
    if kind == _PAYLOAD_BOOL:
        return bool(getattr(action, attr, False))
    return _as_str(getattr(action, attr, ""))
def _p0_stub_findings(stub_findings: list[dict]) -> list[dict]:
    return [_f for _f in stub_findings if _f.get("severity") == "P0"]
def _detect_stub_findings(skill_dir: str, changed_files: Iterable[str] | None,
                          context: str) -> list[dict]:
    stub_findings = detect_new_compat_stubs(
        skill_dir, changed_files=changed_files)
    p0_count = len(_p0_stub_findings(stub_findings))
    if p0_count:
        _log.warning("%s: 检出 %d 个 P0 兼容桩/门户违规", context, p0_count)
    elif stub_findings:
        _log.warning("%s: 检出 %d 个门户/注释残留警告", context,
                     len(stub_findings))
    return stub_findings
def _apply_stub_detection(result: dict[str, Any], skill_dir: str,
                          modified_files: list[str] | None) -> None:
    if not modified_files:
        _log.debug("[RefactorWorkflow] 本次无有效写入证据，跳过落盘桩扫描")
        return
    stub_findings = _detect_stub_findings(
        skill_dir, modified_files, "[RefactorWorkflow]")
    if not stub_findings:
        return
    p0 = _p0_stub_findings(stub_findings)
    result["violations"].extend(
        f"{f.get('rule_id', 'S0?')}: {f.get('message', '')}"
        for f in p0
    )
    result["stub_findings"] = stub_findings
    if p0:
        result["status"] = WORKFLOW_STATUS_BLOCKED_STUB_GUARD
WORKFLOW_STATUS_OK = "ok"
WORKFLOW_STATUS_BLOCKED = "blocked"
WORKFLOW_STATUS_BLOCKED_STUB_GUARD = "blocked_stub_guard"
def _project_summary(context: dict[str, Any], route: Any) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "files_analyzed": len(context["analyzed_files"]),
        "files_backed_up": len(context["backed_up_files"]),
        "split_candidates": len(context.get(
            "split_detector_candidates", context.get("split_actions", []))),
        "split_exceptions": len(context.get("split_actions", [])),
        "governance_candidates": len(context.get("governance_actions", [])),
        "merge_candidates": len(context.get("merge_actions", [])),
        "migrate_candidates": len(context.get("migrate_actions", [])),
        "rewrite_candidates": len(context.get("rewrite_actions", [])),
        "completed_phases": list(context["completed_phases"]),
        "risk_level": route.risk_level if route else "unknown",
    }
    circular = context.get("circular_imports")
    if circular is not None:
        summary["module_level_cycles"] = len(circular.get("module_level_cycles", []))
        summary["lazy_only_cycles"] = len(circular.get("lazy_only_cycles", []))
    if route:
        summary["total_actions"] = len(route.actions)
        summary["validation_checkpoints"] = route.validation_checkpoints
    return summary
def _action_detail(action: Any, skill_dir: str) -> dict[str, Any]:
    return {
        key: _payload_value(action, attr, kind, skill_dir)
        for key, attr, kind in _ACTION_PAYLOAD_SPEC
    }
def _project_actions_detail(route: Any, skill_dir: str) -> list[dict[str, Any]]:
    if not route:
        return []
    return [_action_detail(action, skill_dir) for action in route.actions]
def _project_file_analyses(context: dict[str, Any],
                           skill_dir: str) -> dict[str, Any]:
    return {
        rel_to_skill_dir(fp, skill_dir): {
            "size_bytes": a.size_bytes,
            "line_count": a.line_count,
            "classes": a.classes,
            "functions": a.functions,
            "execution_chain": a.execution_chain_id,
            "responsibility": a.module_responsibility,
            "has_mixed_responsibilities": a.has_mixed_responsibilities,
            "cohesion_score": round(a.cohesion_score, 2),
            "shared_base_consumers": a.shared_base_consumers,
            "quality_issues": a.quality_issues,
            "logic_issues": a.logic_issues,
            "unrelated_code_blocks": a.unrelated_code_blocks,
            "unused_imports": a.unused_imports,
            "reexport_bridges": a.reexport_bridges,
            "dead_constants": a.dead_constants,
            "cascade_dead_candidates": a.cascade_dead_candidates,
            "cross_file_duplicates": a.cross_file_duplicates,
        }
        for fp, a in context.get("file_analyses", {}).items()
    }
def _rel_cycle_paths(cycles: list[list[str]], skill_dir: str) -> list[list[str]]:
    return [
        [rel_to_skill_dir(f, skill_dir) for f in cycle]
        for cycle in cycles
    ]
def _project_cross_skill_imports(entries: list[dict],
                                 skill_dir: str) -> list[dict]:
    return [
        {
            "file": rel_to_skill_dir(v.get("file", ""), skill_dir),
            "line": v.get("line", 0),
            "imports": v.get("imports", ""),
            "from_skill": v.get("from_skill", ""),
            "to_skill": v.get("to_skill", ""),
        }
        for v in entries
    ]
def _project_cycle_reports(context: dict[str, Any],
                           skill_dir: str) -> dict[str, list]:
    circular = context.get("circular_imports") or {}
    return {
        "circular_imports": {
            "module_level_cycles": _rel_cycle_paths(
                circular.get("module_level_cycles", []), skill_dir),
            "lazy_only_cycles": _rel_cycle_paths(
                circular.get("lazy_only_cycles", []), skill_dir),
        },
        "cross_skill_imports": _project_cross_skill_imports(
            context.get("cross_skill_imports") or [], skill_dir),
    }
def _planning_only_of_route(route: Any) -> list[Any]:
    """路由中仅作人工指引、不参与派发的动作（当前为 governance）。"""
    if not route:
        return []
    actions = getattr(route, "actions", ())
    if not isinstance(actions, (list, tuple)):
        return []
    return [action for action in actions
            if _action_type_of(action) in _PLANNING_ONLY_ACTION_TYPES]
def _build_workflow_result(context: dict[str, Any], violations: list[str],
                          dry_run: bool, skill_dir: str) -> dict[str, Any]:
    route = context.get("refactoring_route")
    cycle_reports = _project_cycle_reports(context, skill_dir)
    return {
        "status": (WORKFLOW_STATUS_BLOCKED if violations
                   else WORKFLOW_STATUS_OK),
        "dry_run": dry_run,
        "skill_dir": skill_dir,
        "summary": _project_summary(context, route),
        "violations": list(violations),
        "planning_only_count": len(_planning_only_of_route(route)),
        "actions": _project_actions_detail(route, skill_dir),
        "file_analyses": _project_file_analyses(context, skill_dir),
        "retrospective": context.get("retrospective_result"),
        "code_feedback": context.get("feedback_result"),
        "circular_imports": cycle_reports["circular_imports"],
        "cross_skill_imports": cycle_reports["cross_skill_imports"],
        "public_signature_snapshot": context.get("public_signature_snapshot"),
    }
def _refactor_execution_entry() -> str:
    package = __package__ or __name__.rpartition(".")[0]
    top = package.split(".", 1)[0]
    return f"{top}.run_refactor_execution" if top else "run_refactor_execution"
_REFACTOR_EXECUTION_ENTRY = _refactor_execution_entry()
def _execution_instruction(
    scope: _ExecutionScope, status: _ExecutionStatus,
) -> tuple[str, str]:
    entry = _REFACTOR_EXECUTION_ENTRY
    if status.dispatch_failed:
        stub_note = (
            f"；同一批落盘产物另有 {status.p0_stub_n} 个 P0 兼容桩/门户违规，"
            "须按 stub_findings 一并清除"
        ) if status.blocked_stub else ""
        return "review_failed_actions_and_rerun", (
            f"{status.failed_n} 个重构动作执行失败；根据执行器日志定位失败动作并根因修复，"
            f"随后通过同一 {entry} 入口重跑；"
            f"失败摘要不得视为完成{stub_note}"
        )
    if status.blocked_stub:
        return "fix_stub_findings_and_rerun", (
            "落盘产物检出 P0 兼容桩/门户违规（blocked_stub_guard）："
            "按 stub_findings 逐条清除桩/门户形态（S01 直接更新消费者 "
            "import 不加兼容桩、S02 删除纯门户文件、S03 清理历史注释），"
            "随后以 dry_run=False 重新调用 "
            f"{entry}(skill_dir, dry_run=False) 复检，"
            "落盘产物须零 P0 违规方为终态通过"
        )
    if status.principle_blocked:
        return "review_principle_violations_and_rerun", (
            f"{status.rejected_n} 个动作未通过核心原则校验，未参与派发；"
            "被拒绝或跳过的动作不得视为执行完成。请按 principle_violations "
            f"逐项修正后通过同一 {entry} 入口重跑"
        )
    if status.no_changes:
        return "review_no_changes_and_rerun", (
            f"本次真实执行有 {status.no_change_n} 个动作未产生可证实的文件变更"
            "（changes_made<=0 或证据非法）："
            "空操作不得报为已完成；逐项核对动作是否携带 new_code/可执行载荷，"
            f"补齐后通过同一 {entry} 入口重跑"
        )
    if status.executable_n == 0 and scope.planning_only:
        return "review_governance_actions", (
            f"本次规划只产出 {len(scope.planning_only)} 个治理建议（governance），"
            "没有可派发动作：按 governance_actions 逐项在既有模块内降复杂度"
            "（不新增文件/模块边界），处理完再以 dry_run=False 复跑本入口确认归零"
        )
    if scope.planning_only and not scope.dry_run:
        return "review_governance_actions", (
            f"本次 {status.executable_n} 个可派发动作已执行完成，另有 "
            f"{len(scope.planning_only)} 个治理建议（governance）未参与派发："
            "按 governance_actions 逐项在既有模块内降复杂度（不新增文件/模块边界），"
            "处理完再复跑本入口确认治理项归零；不得把人工待办视为已完成"
        )
    if not scope.dry_run:
        return "refactor_execution_completed", (
            "本次真实执行已完成且未检出阻断项，无需重复派发；"
            "保留 execution 与定向回归结果作为交付证据"
        )
    return "review_and_execute_refactor", (
        "逐项审核 execution 中各动作预览；审核通过后以 dry_run=False "
        f"重新调用 {entry}(skill_dir, dry_run=False) "
        "经同一入口（含核心原则校验链）落盘拆分/合并/迁移/重写并跑回归验证；"
        "quick_refactor(apply=True) 为等价备选入口；"
        "不通过的动作可按 principle_violations 口径驳回"
    )
def _execution_ai_continuation(
    scope: _ExecutionScope, status: _ExecutionStatus,
) -> dict[str, Any]:
    next_action, instruction = _execution_instruction(scope, status)
    compliant_n = len(scope.compliant_actions) + len(scope.planning_only)
    return {
        "next_action": next_action,
        "instruction": instruction,
        "compliant_actions": compliant_n,
        "skipped_actions": len(scope.principle_violations),
    }
@dataclass(frozen=True)
class _ExecutionScope:
    skill_dir: str
    dry_run: bool
    plan_status: str
    summary: dict[str, Any]
    compliant_actions: list[SplitMergeAction]
    principle_violations: list[dict]
    stub_findings: list[dict]
    planning_only: list[SplitMergeAction]
class _ExecutionStatus(NamedTuple):
    dispatch_failed: bool
    failed_n: int
    blocked_stub: bool
    p0_stub_n: int
    principle_blocked: bool
    rejected_n: int
    no_changes: bool
    no_change_n: int
    executable_n: int
    governance_blocked: bool
def _execution_status(scope: _ExecutionScope) -> _ExecutionStatus:
    failed_n = scope.summary.get("failed", 0)
    dispatch_failed = bool(failed_n)
    p0_stub_n = len(_p0_stub_findings(scope.stub_findings))
    rejected_n = len(scope.principle_violations)
    changes_made = scope.summary.get("changes_made")
    executable_n = len(scope.compliant_actions)
    no_change_n = scope.summary.get("no_change_actions")
    if no_change_n is None:
        no_change_n = (
            executable_n if not _is_positive_change_count(changes_made) else 0)
    elif (not isinstance(no_change_n, int) or isinstance(no_change_n, bool)
            or no_change_n < 0):
        no_change_n = executable_n
    no_changes = (
        not scope.dry_run and not dispatch_failed and executable_n > 0
        and (no_change_n > 0 or not _is_positive_change_count(changes_made))
    )
    return _ExecutionStatus(
        dispatch_failed, failed_n, bool(p0_stub_n), p0_stub_n,
        bool(rejected_n), rejected_n, no_changes, no_change_n, executable_n,
        not scope.dry_run and bool(scope.planning_only))
def _apply_execution_status(
    result: dict[str, Any], status: _ExecutionStatus,
) -> None:
    if status.dispatch_failed:
        result["ok"] = False
        result["status"] = "failed"
        error = f"{status.failed_n} 个重构动作执行失败，不能将本次派发视为成功"
        if status.blocked_stub:
            error += (
                f"；落盘产物另有 {status.p0_stub_n} 个 P0 兼容桩/门户违规"
                "（见 stub_findings）")
        result["error"] = error
    elif status.blocked_stub:
        result["ok"] = False
        result["status"] = WORKFLOW_STATUS_BLOCKED_STUB_GUARD
        result["error"] = (
            f"落盘产物检出 {status.p0_stub_n} 个 P0 兼容桩/门户违规"
            "（blocked_stub_guard），须按 stub_findings 逐条清除后重跑验证")
    elif status.principle_blocked:
        result["ok"] = False
        result["status"] = "blocked_principles"
        result["error"] = (
            f"{status.rejected_n} 个动作未通过核心原则校验且未参与派发，"
            "不得将本次执行视为完成"
        )
    elif status.no_changes:
        result["ok"] = False
        result["status"] = "no_changes"
        result["error"] = (
            f"{status.no_change_n} 个重构动作未产生可证实的文件变更"
            f"（本批共派发 {status.executable_n} 个动作；changes_made<=0 "
            "或证据非法），空操作不得视为执行完成")
    elif status.governance_blocked:
        result["ok"] = False
        result["status"] = WORKFLOW_STATUS_BLOCKED
        result["error"] = "仍有治理建议待处理，不得将本次执行或断点视为全部完成"
def _execution_result(scope: _ExecutionScope) -> dict[str, Any]:
    result = {
        "ok": True,
        "status": WORKFLOW_STATUS_OK,
        "skill_dir": scope.skill_dir,
        "dry_run": scope.dry_run,
        "plan_status": scope.plan_status,
        "execution": scope.summary,
    }
    if scope.planning_only:
        result["governance_actions"] = [
            _action_detail(action, scope.skill_dir)
            for action in scope.planning_only]
    if scope.principle_violations:
        result["principle_violations"] = scope.principle_violations
        result["skipped_actions"] = len(scope.principle_violations)
    if scope.stub_findings:
        result["stub_findings"] = scope.stub_findings
    status = _execution_status(scope)
    _apply_execution_status(result, status)
    result["ai_execution"] = _execution_ai_continuation(scope, status)
    return result
_MODE_PHASE_MAP: Mapping[str, tuple[str, ...]] = MappingProxyType({
    "analyze": ("deep_analysis", "backup", "boundary_analysis", "route_planning"),
    "execute": ("backup", "split_merge", "code_migration", "quality_rewrite"),
})
_PHASE_VALUES: tuple[str, ...] = tuple(p.value for p in PHASE_ORDER)
_PHASE_BY_VALUE: Mapping[str, RefactoringPhase] = MappingProxyType(
    {p.value: p for p in PHASE_ORDER})
_PHASE_HANDLERS: Mapping[RefactoringPhase, str] = MappingProxyType({
    RefactoringPhase.DEEP_ANALYSIS: "_phase_deep_analysis",
    RefactoringPhase.BACKUP: "_phase_backup",
    RefactoringPhase.BOUNDARY_ANALYSIS: "_phase_boundary_analysis",
    RefactoringPhase.ROUTE_PLANNING: "_phase_route_planning",
    RefactoringPhase.SPLIT_MERGE: "_phase_split_merge",
    RefactoringPhase.CODE_MIGRATION: "_phase_code_migration",
    RefactoringPhase.QUALITY_REWRITE: "_phase_quality_rewrite",
})
_VALID_WORKFLOW_MODES = frozenset({"full"}) | frozenset(_MODE_PHASE_MAP)
_EXECUTION_PHASE_VALUES = frozenset({
    RefactoringPhase.SPLIT_MERGE.value,
    RefactoringPhase.CODE_MIGRATION.value,
    RefactoringPhase.QUALITY_REWRITE.value,
})
def _validate_workflow_mode(mode: str) -> None:
    if mode not in _VALID_WORKFLOW_MODES:
        raise ValueError(
            f"无效的 mode 值: {mode!r}（合法值: full/analyze/execute）")
def _validate_phase_names(phase_names: list[str]) -> list[RefactoringPhase]:
    valid_phases: list[RefactoringPhase] = []
    for name in phase_names:
        p = _PHASE_BY_VALUE.get(name)
        if p is None:
            raise ValueError(
                f"无效阶段名: {name!r}（有效值: {', '.join(_PHASE_VALUES)}）")
        valid_phases.append(p)
    _phase_indices = [_PHASE_VALUES.index(p.value) for p in valid_phases]
    if _phase_indices != sorted(_phase_indices):
        _log.warning("[RefactorGuard] 阶段顺序异常: %s", [p.value for p in valid_phases])
    valid_phases.sort(key=lambda p: _PHASE_VALUES.index(p.value))
    return valid_phases
def _initial_context(skill_dir: str) -> dict[str, Any]:
    return {
        "skill_dir": skill_dir,
        "analyzed_files": [],
        "backed_up_files": [],
        "files_to_modify": [],
        "completed_phases": [],
        "refactoring_route": None,
        "split_actions": [],
        "merge_actions": [],
        "migrate_actions": [],
        "rewrite_actions": [],
        "executed_migrations": [],
        "executed_rewrites": [],
        "executed_split_merges": [],
        "file_analyses": {},
        "migration_results": [],
        "fix_records": [],
    }
def _display_name(files: list[str]) -> str:
    if not files:
        return "?"
    return Path(files[0]).name or "?"
def _successful_commit_data(result: Any) -> dict[str, Any] | None:
    extra = getattr(result, "extra", None)
    if not isinstance(extra, Mapping):
        return None
    commit = extra.get("commit")
    if not isinstance(commit, Mapping) or commit.get("status") != "ok":
        return None
    data = commit.get("data")
    if data is None:
        return {}
    return dict(data) if isinstance(data, Mapping) else None
_PHASE_GATES: Mapping[RefactoringPhase, tuple[RefactoringConstraint, ...]] = MappingProxyType({
    RefactoringPhase.DEEP_ANALYSIS: (CONSTRAINT_ALL_PY_ANALYZED,),
    RefactoringPhase.BACKUP: (CONSTRAINT_BACKUP_BEFORE_MODIFY,),
    RefactoringPhase.ROUTE_PLANNING: (
        CONSTRAINT_PLAN_BEFORE_EXECUTE,
        CONSTRAINT_NO_SIZE_ONLY_SPLIT,
        CONSTRAINT_NO_SIZE_ONLY_MERGE,
        CONSTRAINT_MERGE_COHESION_ONLY,
        CONSTRAINT_REWRITE_PRECONDITIONS,
    ),
    RefactoringPhase.CODE_MIGRATION: (CONSTRAINT_MIGRATION_NO_RESIDUAL,),
    RefactoringPhase.QUALITY_REWRITE: (
        CONSTRAINT_NO_BATCH_FIX,
        CONSTRAINT_NO_PATCH_FIX,
    ),
})
_PRE_PHASE_GATES: Mapping[RefactoringPhase, tuple[RefactoringConstraint, ...]] = MappingProxyType({
    RefactoringPhase.SPLIT_MERGE: (
        CONSTRAINT_NO_SPLIT_AS_GOVERNANCE,
        CONSTRAINT_MERGE_ARGUMENT,
    ),
})
_EXECUTION_GATES: Mapping[RefactoringPhase, tuple[RefactoringConstraint, ...]] = MappingProxyType({
    RefactoringPhase.CODE_MIGRATION: (CONSTRAINT_MIGRATION_DONE,),
    RefactoringPhase.QUALITY_REWRITE: (CONSTRAINT_REWRITE_DONE,),
})
def _phase_gate_transition(phase: RefactoringPhase,
                           context: dict[str, Any],
                           violations: list[str]) -> bool:
    if not CONSTRAINT_PHASE_ORDER.evaluate(context)[0]:
        violations.append(CONSTRAINT_PHASE_ORDER.error_message)
        return False
    context["next_phase"] = phase.value
    try:
        passed, msg = CONSTRAINT_NEXT_PHASE.evaluate(context)
        if not passed:
            violations.append(msg)
            return False
    finally:
        context.pop("next_phase", None)
    return True
def _phase_gate_pre(phase: RefactoringPhase, dry_run: bool,
                    context: dict[str, Any], violations: list[str]) -> bool:
    if dry_run:
        return True
    return _evaluate_phase_gates(_PRE_PHASE_GATES, phase, context, violations)
def _evaluate_phase_gates(
    gates: Mapping[RefactoringPhase, tuple[RefactoringConstraint, ...]],
    phase: RefactoringPhase, context: dict[str, Any], violations: list[str],
) -> bool:
    if not isinstance(phase, RefactoringPhase):
        return True
    constraints = gates.get(phase, ())
    return (not constraints or _constraints_all_pass(
        list(constraints), context, violations))
def _constraints_all_pass(constraints: list[RefactoringConstraint],
                          context: dict[str, Any],
                          violations: list[str]) -> bool:
    all_passed = True
    for constraint in constraints:
        passed, msg = constraint.evaluate(context)
        if not passed:
            violations.append(msg)
            all_passed = False
    return all_passed
def _dispatch_phase_handler(phase: RefactoringPhase, guard: Any) -> None:
    if not isinstance(phase, RefactoringPhase):
        return
    handler_name = _PHASE_HANDLERS.get(phase)
    if handler_name is None:
        raise NotImplementedError(f"阶段缺少处理器: {phase.value}")
    getattr(guard, handler_name)()
def _apply_boundary_candidates(result: BoundaryAnalysisResult,
                               context: dict[str, Any]) -> None:
    raw_splits = list(result.split_candidates)
    governance = reconcile_governance_proposals(
        raw_splits, result.governance_candidates)
    context["boundary_result"] = result
    context["split_detector_candidates"] = raw_splits
    context["split_actions"] = approved_split_actions(raw_splits)
    context["governance_actions"] = governance
    context["merge_actions"] = result.merge_candidates
    context["migrate_actions"] = result.migrate_candidates
    context["rewrite_actions"] = result.rewrite_candidates
def _extend_refactor_modified_files(
        context: dict[str, Any], files: Iterable[str]) -> None:
    modified = context.get("refactor_modified_files")
    if not isinstance(modified, list):
        modified = []
        context["refactor_modified_files"] = modified
    modified[:] = dict.fromkeys(chain(modified, files))
def _append_migration_result(result: Any, context: dict[str, Any]) -> None:
    data = _successful_commit_data(result)
    if data is None:
        return
    source_files = _str_list(data.get("source_files_updated"))
    consumer_files = _str_list(data.get("consumer_files_updated"))
    context["migration_results"].append({
        "references_updated": bool(source_files or consumer_files),
        "has_residual_forwarding": bool(data.get("symbols_left_in_source")),
        "source_files_updated": source_files,
        "consumer_files_updated": consumer_files,
    })
    _extend_refactor_modified_files(
        context, chain(source_files, consumer_files))
def _append_fix_record(action: SplitMergeAction, result: Any,
                       context: dict[str, Any]) -> None:
    if _successful_commit_data(result) is None:
        return
    context["fix_records"].append({
        "files_modified": _str_list(
            getattr(result, "source_files", None)),
        "issues_fixed": [_rewrite_issue_text(action)],
        "fix_approach": getattr(action, "fix_approach", "") or "",
    })
def _rewrite_issue_text(action: SplitMergeAction) -> str:
    return action.reason or action.boundary_justification or "质量重写"
class RefactoringWorkflowGuard:
    def __init__(self: Self, skill_dir: str,
                 dry_run: bool = DEFAULT_REFACTOR_DRY_RUN, cache=None,
                 resume_completed_phases: Iterable[str] | None = None) -> None:
        self.skill_dir = _skill_dir_text(skill_dir)
        self.dry_run = bool(dry_run)
        self._context: dict[str, Any] = _initial_context(self.skill_dir)
        self._backup_mgr = BackupManager(self.skill_dir)
        self._boundary_analyzer = ModuleBoundaryAnalyzer(
            self.skill_dir, cache=cache)
        self._cache = cache
        self._dispatcher = RefactoringExecutorDispatcher(
            self.skill_dir, dry_run=self.dry_run, cache=self._cache)
        self._violations: list[str] = []
        self._boundary_result: BoundaryAnalysisResult | None = None
        self._resume_completed_phases = frozenset(
            resume_completed_phases or ())
    def _run_prerequisite_phases(self: Self,
                                valid_phases: list[RefactoringPhase]) -> bool:
        completed = self._context.get("completed_phases", [])
        last_idx = max(_PHASE_VALUES.index(p.value) for p in valid_phases)
        for value in _PHASE_VALUES[:last_idx]:
            if value in completed:
                continue
            prereq_phase = _PHASE_BY_VALUE.get(value)
            if prereq_phase is None:
                continue
            if (value in _EXECUTION_PHASE_VALUES
                    and value in self._resume_completed_phases):
                completed.append(value)
                _log.info("[RefactorGuard] 断点已完成，跳过重复执行阶段: %s", value)
                continue
            _log.info("[RefactorGuard] 自动补全前置阶段: %s", value)
            if not self._execute_phase(prereq_phase):
                return False
        return True
    def execute_phases(self: Self, phase_names: list[str]) -> dict[str, Any]:
        self._violations.clear()
        valid_phases = _validate_phase_names(phase_names)
        if not valid_phases:
            return _build_workflow_result(
                self._context, self._violations, self.dry_run, self.skill_dir)
        if not self._run_prerequisite_phases(valid_phases):
            return _build_workflow_result(
                self._context, self._violations, self.dry_run, self.skill_dir)
        completed_now = self._context.get("completed_phases", [])
        ok, executed_phases = self._run_phase_sequence(
            valid_phases, completed_now)
        if not ok:
            return _build_workflow_result(
                self._context, self._violations, self.dry_run, self.skill_dir)
        if (executed_phases
                and executed_phases[-1] == RefactoringPhase.QUALITY_REWRITE):
            run_retrospective_feedback(self.skill_dir, self._context)
            _finalize_workflow_reports(self.skill_dir, self._context)
        return _build_workflow_result(
            self._context, self._violations, self.dry_run, self.skill_dir)
    def _run_phase_sequence(
        self: Self,
        phases: list[RefactoringPhase],
        completed: list[str],
    ) -> tuple[bool, list[RefactoringPhase]]:
        executed: list[RefactoringPhase] = []
        for phase in phases:
            if phase.value in completed:
                continue
            if not self._execute_phase(phase):
                return False, executed
            executed.append(phase)
        return True, executed
    def execute(self: Self) -> dict[str, Any]:
        self._violations.clear()
        completed = self._context.get("completed_phases", [])
        ok, _executed = self._run_phase_sequence(PHASE_ORDER, completed)
        if not ok:
            return _build_workflow_result(
                self._context, self._violations, self.dry_run, self.skill_dir)
        run_retrospective_feedback(self.skill_dir, self._context)
        _finalize_workflow_reports(self.skill_dir, self._context)
        return _build_workflow_result(
            self._context, self._violations, self.dry_run, self.skill_dir)
    def _execute_phase(self: Self, phase: RefactoringPhase) -> bool:
        if not _phase_gate_transition(
                phase, self._context, self._violations):
            return False
        if not _phase_gate_pre(
                phase, self.dry_run, self._context, self._violations):
            return False
        _log.info("[RefactorGuard] 执行阶段: %s", phase.value)
        violation_count = len(self._violations)
        _dispatch_phase_handler(phase, self)
        action_failed = len(self._violations) != violation_count
        if not _evaluate_phase_gates(
                _PHASE_GATES, phase, self._context, self._violations):
            return False
        if (not self.dry_run
                and not _evaluate_phase_gates(
                    _EXECUTION_GATES, phase, self._context, self._violations)):
            return False
        if action_failed:
            return False
        self._context["completed_phases"].append(phase.value)
        return True
    def _phase_deep_analysis(self: Self) -> None:
        self._boundary_analyzer.deep_analyze()
        self._context["analyzed_files"] = list(
            self._boundary_analyzer.file_analyses.keys())
        self._context["file_analyses"] = (
            self._boundary_analyzer.file_analyses)
    def _phase_backup(self: Self) -> None:
        files_to_modify = list(dict.fromkeys(
            self._context.get("analyzed_files", [])))
        self._context["files_to_modify"] = files_to_modify
        if self.dry_run:
            self._context["backed_up_files"] = list(files_to_modify)
            _log.info(
                "[RefactorGuard] 分析模式跳过磁盘备份（%d 个文件仅内存登记）",
                len(files_to_modify))
            return
        for fpath in files_to_modify:
            if Path(fpath).exists():
                self._backup_mgr.ensure_backed_up(fpath)
            else:
                _log.warning(
                    "[RefactorGuard] 备份跳过（文件不存在）: %s", fpath)
        self._context["backed_up_files"] = self._backup_mgr.backed_up_files
    def _phase_boundary_analysis(self: Self) -> None:
        result = self._boundary_analyzer.analyze_boundaries()
        self._boundary_result = result
        _apply_boundary_candidates(result, self._context)
        run_boundary_coupling_diagnostics(
            self._boundary_analyzer, self.skill_dir, self._context)
    def _phase_route_planning(self: Self) -> None:
        planner = RefactoringRoutePlanner(
            require_boundary_value(self._boundary_result))
        route = planner.plan()
        self._context["refactoring_route"] = route
        take_signature_snapshot(self.skill_dir, route, self._context)
    @property
    def _mode_label(self: Self) -> str:
        return "dry_run" if self.dry_run else "execute"
    def _run_action_batch(
        self: Self,
        actions: list[SplitMergeAction],
        execute: Callable[[SplitMergeAction], Any],
        describe: Callable[[SplitMergeAction, Any], str],
        on_success: Callable[[SplitMergeAction, Any], None] | None = None,
    ) -> list[int]:
        executed: list[int] = []
        for idx, action in enumerate(actions):
            result = execute(action)
            _log.info("[RefactorGuard] [%s] %s",
                      self._mode_label, describe(action, result))
            if result.status != "success":
                detail = getattr(result, "error_message", "") or "未提供错误详情"
                self._violations.append(
                    f"[执行失败] {action.action_type} 动作 "
                    f"{_display_name(action.source_files)}: "
                    f"{result.status}；{detail}")
                continue
            if (not self.dry_run
                    and not _is_positive_change_count(result.changes_made)):
                self._violations.append(
                    f"[执行失败] {action.action_type} 动作 "
                    f"{_display_name(action.source_files)}: 空操作；"
                    "成功状态缺少有效文件变更证据 "
                    f"(changes_made={result.changes_made!r})")
                continue
            if not self.dry_run:
                collect_modified_files(
                    self._context, action, result, self.dry_run)
                executed.append(idx)
                if on_success is not None:
                    on_success(action, result)
        return executed
    def _phase_split_merge(self: Self) -> None:
        route = require_route_value(self._context)
        actions = [a for a in route.actions if a.action_type in ("split", "merge")]
        split_count = sum(1 for a in actions if a.action_type == "split")
        _log.info("[RefactorGuard] [%s] 拆分例外: %d, 合并候选: %d",
                  self._mode_label, split_count, len(actions) - split_count)
        executed = self._run_action_batch(
            actions, self._dispatcher.dispatch,
            lambda _action, result: (
                f"{result.action_type}: {_display_name(result.source_files)}"
                f" ({result.status})"),
        )
        if not self.dry_run:
            self._context["executed_split_merges"] = executed
    def _phase_code_migration(self: Self) -> None:
        route = require_route_value(self._context)
        migrate_actions = [a for a in route.actions if a.action_type == "migrate"]
        _log.info("[RefactorGuard] [%s] 迁移候选: %d",
                  self._mode_label, len(migrate_actions))
        executed = self._run_action_batch(
            migrate_actions,
            self._dispatcher.dispatch,
            lambda action, result: (
                f"迁移 {_display_name(action.source_files)} → "
                f"{_display_name(action.target_files)}: {result.status}"),
            on_success=lambda _action, result: _append_migration_result(
                result, self._context),
        )
        if not self.dry_run:
            self._context["executed_migrations"] = executed
    def _phase_quality_rewrite(self: Self) -> None:
        route = require_route_value(self._context)
        rewrite_actions = [a for a in route.actions if a.action_type == "rewrite"]
        _log.info("[RefactorGuard] [%s] 重写候选: %d",
                  self._mode_label, len(rewrite_actions))
        executed_rw = self._run_action_batch(
            rewrite_actions,
            self._dispatcher.dispatch,
            lambda action, result: (
                f"重写 {_display_name(action.source_files)}: {result.status}"
                f" ({result.changes_made} 修复)"),
            on_success=lambda action, result: _append_fix_record(
                action, result, self._context),
        )
        if not self.dry_run:
            self._context["executed_rewrites"] = executed_rw
    @property
    def constraints(self: Self) -> list[RefactoringConstraint]:
        return list(ALL_CONSTRAINTS)
    def get_constraint(self: Self, name: str) -> RefactoringConstraint | None:
        for c in ALL_CONSTRAINTS:
            if c.name == name:
                return c
        return None
def _normalize_skill_dir(skill_dir: str) -> str:
    return os.path.abspath(_skill_dir_text(skill_dir))
def _resolve_phase_names(phases: list[str] | None,
                         mode: str) -> list[str] | None:
    if phases is not None:
        return [phase.value for phase in _validate_phase_names(phases)]
    mapped = _MODE_PHASE_MAP.get(mode)
    return list(mapped) if mapped is not None else None
def _consume_resume_state(
    state_mgr: RefactoringStateManager, dry_run: bool, skill_dir: str,
    requested_phases: list[str] | None,
) -> tuple[list[str] | None, dict[str, Any] | None, dict[str, Any]]:
    state = state_mgr.load_state_for_resume()
    completed = state.get("completed_phases", [])
    pending = state_mgr.get_pending_phases(completed)
    requested = (None if requested_phases is None
                 else frozenset(requested_phases))
    scoped_pending = [
        phase for phase in pending
        if requested is None or phase in requested
    ]
    if not scoped_pending:
        if not pending:
            if dry_run:
                _log.info(
                    "[RefactorWorkflow] 断点已全部完成，干跑确认后保留状态")
            else:
                state_mgr.clear_state()
                _log.info(
                    "[RefactorWorkflow] 断点已全部完成，状态消费后清理")
            message = "所有阶段已完成，无需继续"
        else:
            message = "本次请求的阶段均已完成，无需继续"
        result = _build_workflow_result(
            _initial_context(skill_dir), [], dry_run, skill_dir)
        result["summary"] = {
            "completed_phases": completed,
            "message": message,
        }
        return None, result, state
    _next_phase = state_mgr.get_next_phase(completed)
    _log.info("[RefactorWorkflow] 断点恢复: 已完成 %d 阶段, 全局待执行 %d 阶段, "
              "本次请求待执行 %d 阶段 (全局下一阶段: %s)；分析阶段将重放，"
              "已完成写盘阶段不会重复执行",
              len(completed), len(pending), len(scoped_pending),
              _next_phase or "无")
    return scoped_pending, None, state
def _persist_breakpoint_state(state_mgr: RefactoringStateManager,
                              guard: RefactoringWorkflowGuard,
                              result: dict[str, Any],
                              prior_executed_count: int = 0) -> None:
    if result.get("status") == WORKFLOW_STATUS_BLOCKED_STUB_GUARD:
        _log.warning(
            "[RefactorWorkflow] 落盘产物存在 P0 兼容桩/门户违规，"
            "本次不写断点、不清理状态（须清除后重跑至通过）")
        return
    completed = result.get("summary", {}).get("completed_phases", [])
    if not completed:
        return
    if not state_mgr.get_pending_phases(completed):
        state_mgr.clear_state()
        _log.info("[RefactorWorkflow] 全部阶段已完成，清理遗留断点状态（无新增落盘）")
        return
    executed_count = (
        max(0, prior_executed_count)
        + count_executed_actions(guard._context))
    state_mgr.save_state(completed, executed_count)
def run_refactor_workflow(skill_dir: str,
                          dry_run: bool = DEFAULT_REFACTOR_DRY_RUN,
                          mode: str = "full",
                          phases: list[str] | None = None, resume: bool = False,
                          cache: Any = None) -> dict[str, Any]:
    _validate_workflow_mode(mode)
    skill_dir = _normalize_skill_dir(skill_dir)
    state_mgr = RefactoringStateManager(skill_dir)
    requested_phases = _resolve_phase_names(phases, mode)
    resume_state: dict[str, Any] = {}
    if resume:
        phases, short_circuit, resume_state = _consume_resume_state(
            state_mgr, dry_run, skill_dir, requested_phases)
        if short_circuit is not None:
            return short_circuit
    else:
        phases = requested_phases
    cache = ensure_entry_warmed(skill_dir, cache, "重构工作流 run_refactor_workflow")
    guard = RefactoringWorkflowGuard(
        skill_dir, dry_run=dry_run, cache=cache,
        resume_completed_phases=resume_state.get("completed_phases", ()))
    result = (guard.execute_phases(phases) if phases is not None
              else guard.execute())
    if not dry_run:
        _apply_stub_detection(
            result, skill_dir, read_modified_files(guard._context))
        _persist_breakpoint_state(
            state_mgr, guard, result,
            prior_executed_count=resume_state.get("actions_executed", 0))
    return result
_PLANNING_ONLY_ACTION_TYPES = frozenset({"governance"})
def _principle_violation(action_type: str, source: list[str],
                         reason: str) -> dict[str, Any]:
    return {"type": action_type, "source": source, "reason": reason}
def _plan_action_items(plan: dict) -> tuple[list[Any], list[dict]]:
    raw = plan.get("actions")
    if raw is None:
        return [], []
    if isinstance(raw, (list, tuple)):
        return list(raw), []
    return [], [_principle_violation(
        "", [], f"actions 非序列（{type(raw).__name__}），拒绝派发")]
def _validate_dispatch_actions(
        plan: dict) -> tuple[list[SplitMergeAction], list[dict]]:
    action_items, container_violations = _plan_action_items(plan)
    principle_violations: list[dict] = list(container_violations)
    compliant_actions = []
    for _act_raw in action_items:
        if not isinstance(_act_raw, dict):
            principle_violations.append(_principle_violation(
                "", [], f"动作非 dict（{type(_act_raw).__name__}），拒绝派发"))
            continue
        _act = _dict_to_action(_act_raw, SplitMergeAction)
        _ok, _err = validate_refactoring_action(_act)
        if _ok:
            compliant_actions.append(_act)
            continue
        principle_violations.append(_principle_violation(
            getattr(_act, "action_type", ""),
            _str_list(getattr(_act, "source_files", None)), _err))
    if principle_violations:
        _log.warning(
            "run_refactor_execution: %d 个动作违反核心原则被拒绝派发",
            len(principle_violations))
    return compliant_actions, principle_violations
def _post_write_stub_check(skill_dir: str,
                           actions: list[SplitMergeAction],
                           dispatcher: RefactoringExecutorDispatcher,
                           dry_run: bool) -> list[dict]:
    if dry_run:
        return []
    written_files = _collect_dispatch_written_files(
        actions, dispatcher.results, skill_dir)
    return _detect_stub_findings(
        skill_dir, written_files, "run_refactor_execution")
def _partition_dispatch_actions(
        actions: list[SplitMergeAction],
) -> tuple[list[SplitMergeAction], list[SplitMergeAction]]:
    executable = [a for a in actions
                  if a.action_type not in _PLANNING_ONLY_ACTION_TYPES]
    planning_only = [a for a in actions
                     if a.action_type in _PLANNING_ONLY_ACTION_TYPES]
    return executable, planning_only
def run_refactor_execution(
        skill_dir: str,
        dry_run: bool = DEFAULT_REFACTOR_DRY_RUN) -> dict[str, Any]:
    target_dir = _normalize_skill_dir(skill_dir)
    def _body() -> dict[str, Any]:
        cache = ensure_entry_warmed(
            target_dir, None, "重构执行 run_refactor_execution")
        plan = _plan_refactor_or_raise(target_dir, dry_run, cache)
        plan_status = plan["status"]
        if plan_status != WORKFLOW_STATUS_OK:
            return _blocked_plan_result(
                target_dir, plan, plan_status, dry_run)
        dispatcher = RefactoringExecutorDispatcher(
            target_dir, dry_run=dry_run, cache=cache)
        compliant_actions, principle_violations = _validate_dispatch_actions(
            plan)
        dispatch_actions, planning_only = _partition_dispatch_actions(
            compliant_actions)
        if planning_only:
            _log.info(
                "run_refactor_execution: %d 个治理建议仅作人工指引，"
                "不参与执行派发", len(planning_only))
        dispatcher.dispatch_all(dispatch_actions)
        summary = dispatcher.summary()
        stub_findings = _post_write_stub_check(
            target_dir, dispatch_actions, dispatcher, dry_run)
        result = _execution_result(_ExecutionScope(
            skill_dir=target_dir,
            dry_run=dry_run,
            plan_status=plan_status,
            summary=summary,
            compliant_actions=dispatch_actions,
            principle_violations=principle_violations,
            stub_findings=stub_findings,
            planning_only=planning_only,
        ))
        if not dry_run and result.get("ok"):
            RefactoringStateManager(target_dir).save_state(
                list(_PHASE_VALUES), summary["success"])
        return result
    return run_traced_entry(
        "run_refactor_execution", "refactor_execution", target_dir, _body)
def _plan_refactor_or_raise(skill_dir: str, dry_run: bool,
                            cache: Any = None) -> dict[str, Any]:
    plan = run_refactor_workflow(
        skill_dir, dry_run=dry_run, mode="analyze", cache=cache)
    if not isinstance(plan, dict):
        raise TypeError(
            f"run_refactor_workflow 返回异常结构: {type(plan).__name__}")
    return plan
def _blocked_plan_result(skill_dir: str, plan: dict[str, Any],
                         plan_status: str, dry_run: bool) -> dict[str, Any]:
    result = {
        "ok": False,
        "status": WORKFLOW_STATUS_BLOCKED,
        "skill_dir": skill_dir,
        "error": f"重构规划被工作流守卫阻断（status={plan_status}），动作派发已终止",
        "plan_status": plan_status,
        "violations": plan.get("violations") or [],
        "dry_run": dry_run,
    }
    if "stub_findings" in plan:
        result["stub_findings"] = plan["stub_findings"]
    return result
def _as_str(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _dict_to_action(d: dict[str, Any], action_cls: type) -> Any:
    kwargs: dict[str, Any] = {}
    merge_values = merge_argument_payload(d)
    for key, attr, kind in _ACTION_PAYLOAD_SPEC:
        if key in merge_values:
            raw = merge_values[key]
        else:
            raw = _first_action_type_value(d) if key == "type" else d.get(key)
        if kind in (_PAYLOAD_PATHS, _PAYLOAD_TEXT_LIST):
            kwargs[attr] = _str_list(raw)
        elif kind == _PAYLOAD_TEXT_OR_LIST:
            kwargs[attr] = raw if isinstance(raw, str) else _str_list(raw)
        elif kind == _PAYLOAD_TEXT_OR_MAPPING:
            kwargs[attr] = dict(raw) if isinstance(raw, dict) else _as_str(raw)
        elif kind == _PAYLOAD_BOOL:
            kwargs[attr] = raw
        else:
            kwargs[attr] = _as_str(raw)
    return action_cls(**kwargs)
def _collect_dispatch_written_files(
        actions: list[SplitMergeAction], results: list[Any],
        skill_dir: str) -> list[str]:
    context: dict[str, Any] = {}
    for _act, _res in zip(actions, results, strict=True):
        if (getattr(_res, "status", "") != "success"
                or not _is_positive_change_count(_res.changes_made)):
            continue
        collect_modified_files(context, _act, _res, False)
        commit = _successful_commit_data(_res)
        if commit is not None:
            _extend_refactor_modified_files(context, chain(
                _str_list(commit.get("source_files_updated")),
                _str_list(commit.get("consumer_files_updated")),
            ))
    written: list[str] = []
    seen: set[str] = set()
    for _f in read_modified_files(context) or []:
        if not os.path.isabs(_f):
            _f = os.path.normpath(os.path.join(skill_dir, _f))
        _key = os.path.normcase(_f)
        if _key not in seen:
            seen.add(_key)
            written.append(_f)
    return written
class _SignatureLocation(NamedTuple):
    module_root: Path
    import_root: Path
    package: str
def _signature_location_for_file(fpath: str, root: Path) -> _SignatureLocation:
    if (root / "__init__.py").is_file() and root.name.isidentifier():
        return _SignatureLocation(root, root.parent, root.name)
    source_root = root / "src"
    if (source_root.is_dir()
            and module_name_under_root(fpath, source_root) is not None):
        return _SignatureLocation(source_root, source_root, "")
    if root.name.isidentifier():
        return _SignatureLocation(root, root.parent, root.name)
    return _SignatureLocation(root, root, "")
def _qualified_signature_module(fpath: str,
                                location: _SignatureLocation) -> str:
    if location.package and Path(fpath).name == "__init__.py":
        try:
            if (Path(fpath).resolve()
                    == (location.module_root / "__init__.py").resolve()):
                return location.package
        except (OSError, RuntimeError):
            return ""
    name = module_name_under_root(fpath, location.module_root)
    if name is None:
        return ""
    qualified = (f"{location.package}.{name}" if location.package and name
                 else location.package or name)
    if not qualified or not all(
            part.isidentifier() for part in qualified.split(".")):
        return ""
    return qualified
def _signature_modules_by_root(route: RefactoringRoute,
                               skill_root: Path) -> dict[Path, set[str]]:
    grouped: dict[Path, set[str]] = {}
    for action in route.actions:
        if action.action_type not in ("merge", "migrate"):
            continue
        for fpath in chain(
                _str_list(action.source_files), _str_list(action.target_files)):
            resolved = Path(fpath)
            if not resolved.is_absolute():
                resolved = skill_root / resolved
            resolved_text = os.fspath(resolved)
            location = _signature_location_for_file(resolved_text, skill_root)
            qualified = _qualified_signature_module(resolved_text, location)
            if qualified:
                grouped.setdefault(location.import_root, set()).add(qualified)
    return grouped
def _build_signature_snapshot(import_root: Path,
                              modules: list[str]) -> dict[str, Any]:
    snapshot = CircularDependencyResolver().snapshot_signatures(
        modules, str(import_root))
    return {
        "modules": modules,
        "root_dir": str(import_root),
        "snapshot_modules": snapshot.get("snapshot_modules", 0),
        "signatures": snapshot.get("signatures", {}),
        "verify_hint": (
            "AI 执行合并/迁移后：resolver = CircularDependencyResolver(); "
            "resolver.verify_public_signatures("
            "snapshot['modules'], snapshot['root_dir'], "
            "prev_signatures=snapshot['signatures'])"),
    }
def _combine_signature_snapshots(
        snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    if len(snapshots) == 1:
        return snapshots[0]
    signatures = {
        name: signature
        for snapshot in snapshots
        for name, signature in snapshot["signatures"].items()
    }
    return {
        "modules": sorted({
            name for snapshot in snapshots for name in snapshot["modules"]}),
        "root_dir": "",
        "snapshot_modules": sum(
            snapshot["snapshot_modules"] for snapshot in snapshots),
        "signatures": signatures,
        "groups": snapshots,
        "verify_hint": (
            "AI 执行合并/迁移后：resolver = CircularDependencyResolver(); "
            "遍历 snapshot['groups']，逐项调用 "
            "resolver.verify_public_signatures(group['modules'], "
            "group['root_dir'], prev_signatures=group['signatures'])"),
    }
def take_signature_snapshot(skill_dir: str, route: RefactoringRoute,
                            context: dict[str, Any]) -> None:
    try:
        grouped = _signature_modules_by_root(route, Path(skill_dir).resolve())
        snapshots = [
            _build_signature_snapshot(import_root, sorted(modules))
            for import_root, modules in sorted(
                grouped.items(), key=lambda item: str(item[0]))
        ]
        if snapshots:
            context["public_signature_snapshot"] = (
                _combine_signature_snapshots(snapshots))
    except Exception as e:  # noqa: BLE001
        _log.warning("[Boundary] 公开签名快照失败: %s", e)
def restore_skill_md_from_backup(md_path: str, backup_path: str) -> None:
    raw = Path(backup_path).read_bytes()
    write_markdown_text(
        Path(md_path), raw.decode("utf-8-sig"),
        raw.startswith(b"\xef\xbb\xbf"), newline="")
def backup_skill_md(md_path: str) -> str:
    if not os.path.isfile(md_path):
        return ""
    backup = quick_safe_backup(md_path, "skill_doc_refactor_guard:rebuild")
    if not backup:
        raise RuntimeError(f"SKILL.md 备份失败，已中止重建: {md_path}")
    return backup
def rebuild_skill_md_with_fallback(skill_dir: str) -> str:
    md_path = str(Path(skill_dir).resolve() / "SKILL.md")
    backup_path = backup_skill_md(md_path)
    try:
        result = rebuild_skill_md(skill_dir)
    except Exception as exc:  # noqa: BLE001
        _log.warning("代码驱动重建失败，回退章节增强路径: %s", exc)
        if backup_path:
            restore_skill_md_from_backup(md_path, backup_path)
        try:
            _refactor_fallback_writeback(md_path, backup_path)
        except Exception:
            if backup_path:
                restore_skill_md_from_backup(md_path, backup_path)
            raise
        return md_path
    if backup_path:
        _log.info("代码驱动重建完成，备份: %s", backup_path)
    else:
        _log.info("代码驱动重建完成（无存量文件，无备份需求）")
    return result
def _refactor_fallback_writeback(md_path: str, backup_path: str) -> None:
    new_content = compose_refactor_document(get_refactorer().refactor(md_path))
    write_skill_md_text(Path(md_path), new_content + "\n")
    _log.info("回退路径重建完成，备份: %s", backup_path)
def _attach_rebuild_result(result: dict, skill_dir: str) -> None:
    try:
        md_path = rebuild_skill_md_with_fallback(skill_dir)
        result["skill_md_rebuilt"] = True
        result["skill_md_path"] = md_path
    except Exception as e:  # noqa: BLE001
        _log.warning("SKILL.md 重建失败: %s", e)
        result["skill_md_rebuilt"] = False
        result["skill_md_error"] = str(e)
def _planning_only_count_of(workflow: Any) -> int:
    if not isinstance(workflow, dict):
        return 0
    raw = workflow.get("planning_only_count")
    if isinstance(raw, int) and not isinstance(raw, bool) and raw > 0:
        return raw
    return len(_planning_only_of_actions(workflow.get("actions")))
def _planning_only_of_actions(actions: Any) -> list[dict]:
    if not isinstance(actions, (list, tuple)):
        return []
    return [action for action in actions
            if isinstance(action, dict)
            and action.get("type") in _PLANNING_ONLY_ACTION_TYPES]
def _executable_actions_of(workflow: Any) -> list[dict]:
    if not isinstance(workflow, dict):
        return []
    actions = workflow.get("actions")
    if not isinstance(actions, (list, tuple)):
        return []
    return [action for action in actions
            if isinstance(action, dict)
            and action.get("type") not in _PLANNING_ONLY_ACTION_TYPES]
def quick_refactor(skill_dir: str, apply: bool = False,
                   rebuild_md: bool = False) -> dict:
    skill_dir = _normalize_skill_dir(skill_dir)
    try:
        workflow = run_refactor_workflow(skill_dir, dry_run=not apply)
    except Exception as e:  # noqa: BLE001
        _log.warning("重构工作流执行失败: %s", e)
        return {"ok": False, "error": f"重构工作流执行失败: {e}"}
    workflow_ok = workflow.get("status") == WORKFLOW_STATUS_OK
    planning_only = _planning_only_count_of(workflow)
    executable_actions = _executable_actions_of(workflow)
    governance_blocked = bool(
        apply and workflow_ok and planning_only and not executable_actions)
    result = {
        "ok": workflow_ok and not governance_blocked,
        "dry_run": not apply,
        "report": workflow.get("summary", {}),
        "actions": workflow.get("actions", []),
        "planning_only_count": planning_only,
        "violations": workflow.get("violations", []),
        "file_analyses": workflow.get("file_analyses", {}),
        "plan_applied": bool(apply and workflow_ok and not governance_blocked),
    }
    if governance_blocked:
        result["next_action"] = "review_governance_actions"
        result["message"] = (
            f"本次仅产出 {planning_only} 条治理建议（governance），"
            "未派发任何写盘动作，不得视为已完成；"
            "按 actions 逐项在既有模块内降复杂度后复跑本入口确认归零"
        )
    if workflow.get("stub_findings"):
        result["stub_findings"] = workflow["stub_findings"]
    if rebuild_md:
        _attach_rebuild_result(result, skill_dir)
    attach_best_practices(result, skill_dir)
    attach_validation_result(result, "post_refactor_validation", skill_dir, "重构后验证")
    return result
__all__ = [
    "WORKFLOW_STATUS_BLOCKED",
    "WORKFLOW_STATUS_BLOCKED_STUB_GUARD",
    "WORKFLOW_STATUS_OK",
    "RefactoringExecutorDispatcher",
    "RefactoringWorkflowGuard",
    "quick_refactor",
    "rebuild_skill_md_with_fallback",
    "run_refactor_execution",
    "run_refactor_workflow",
    "take_signature_snapshot",
]

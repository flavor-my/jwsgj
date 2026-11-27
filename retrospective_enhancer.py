from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import re
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
from typing import Any, NamedTuple

from jwsgj.ai_review_item_plan import (
    build_auto_enhancement_report,
    enqueue_adjustment_proposals,
    run_code_level_feedback,
    run_stage6d_auto_enhancements,
)
from jwsgj.build_refactor_plan import (
    build_refactor_diagnosis_report,
    build_refactor_treatment_execution,
    build_refactor_treatment_plan,
)
from jwsgj.build_safe_rollback import get_rollback_audit
from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_json_artifact,
)
from jwsgj.diag_solidify_rules import run_stage6d_solidify
from jwsgj.diag_types_defs import (
    default_feedback_history,
)
from jwsgj.diag_types_normalize import (
    as_count,
    as_dict,
    dict_or_empty,
    elapsed_seconds,
    finite_float_or_none,
    grade_from_score,
    integral_count,
    len_safe,
    meta_num,
    require_dict,
    signal_bool,
    str_or,
    timestamp_human,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    FIELD_CV_RULE_WEIGHTS,
    FIELD_DIAGNOSIS_METHOD,
    FIELD_EXPECTED_IMPACT,
    FIELD_METHOD_THRESHOLDS,
    FIELD_ROLLBACK_RECOMMENDED,
    FIELD_RULES_TRIGGERED,
    FIELD_SUGGESTED_VALUE,
    FIELD_THRESHOLD_ADJUST,
    FIELD_TOTAL_INPUT_FINDINGS,
    FMT_DATETIME,
    FMT_DATETIME_ISO,
    RETRO_SCORE_DIMENSIONS,
)
from jwsgj.hallucination_ledger import integrate_with_full_audit
from jwsgj.html_render_pipeline import (
    generate_html_report,
    html_report_path,
)
from jwsgj.log_config import locked_artifact, log_swallowed, write_module_run
from jwsgj.memory_bridge_ops import (
    apply_retrospective_memory_bridge,
    apply_review_memory_enhancements,
    enhance_stage6d_memory,
    integrate_fupan_capabilities,
    normalize_report_containers,
    sync_stage6d_feedback,
)
from jwsgj.retrospective_audit import (
    CrossValidationAudit,
    CrossValidationAuditResult,
    DiagnosisAudit,
    DiagnosisAuditResult,
    RetrospectiveReport,
    TreatmentAudit,
    TreatmentAuditResult,
    _materialize_audit_iterators,
)
from jwsgj.retrospective_ledger import (
    EnhancementEntryFactory,
    EnhancementTracker,
    append_enhancement_entry,
    append_pending_enhancements,
    augment_treatment_context,
    build_provenance,
    clean_enhancement_confidence,
    clean_enhancement_text,
    enhancement_dedup_key,
    enhancement_dict_items,
    get_retrospective_history,
    method_audit_digest_from_list,
    normalized_enhancement_entries,
    read_enhancement_log,
    save_enhancement_log,
    treatment_context_digest,
)
from jwsgj.runtime_paths import (
    evolution_report_path,
    evolution_state_path,
    feedback_enhancement_log_context,
    get_temp_base,
    read_evolution_section,
    write_evolution_section,
)

__all__ = [
    "EnhancementAction",
    "FeedbackEnhancer",
    "GoodPractice",
    "IssueFound",
    "RetrospectiveComposer",
    "RetrospectiveScore",
    "TreatmentEnhancer",
    "close_pending_snapshots",
    "compose_with_context",
    "effective_priority_correct_rate",
    "extract_stage5_cv_metrics",
    "find_latest_report",
    "has_treatment_activity",
    "inject_roi_snapshot",
    "inject_session_count",
    "load_retro_inputs",
    "load_stage_data",
    "persist_retrospective_report",
    "run_code_feedback_channel",
    "run_enhance_channels",
    "run_enhancer_channel",
    "run_retrospective",
    "run_retrospective_feedback",
    "run_stage5_review_engine",
    "run_stage6d_auto_enhance",
    "tracker_roi_inject",
    "write_retrospective_json",
]
logger = logging.getLogger(__name__)
_READ_ERRORS = (OSError, ValueError, RecursionError)
_FEEDBACK_WRITE_ERRORS = (OSError, ValueError, RecursionError, KeyError)
class _FeedbackHistoryShapeError(ValueError):
    pass
def _load_json_payload(path: str, *, log_tag: str) -> Any | None:
    if not path or not os.path.isfile(path):
        return None
    payload, status, error = read_json_artifact(path)
    if status == "ok":
        return payload
    logger.warning("[%s] JSON 加载失败 %s: %s",
                   log_tag, path, error or status)
    return None
@contextmanager
def _required_write_lock(skill_dir: str) -> Iterator[None]:
    if not skill_dir:
        raise OSError("技能根为空，拒绝获取历史写锁")
    lock_target = evolution_state_path(skill_dir)
    os.makedirs(os.path.dirname(os.path.abspath(lock_target)), exist_ok=True)
    with locked_artifact(lock_target) as locked:
        if not locked:
            raise OSError(f"反哺进化状态写锁不可用，拒绝无锁写盘: {skill_dir}")
        yield
_SEVERITY_THRESHOLD_FACTOR: dict[str, float] = {
    "P0": 0.15, "P1": 0.10, "P2": 0.05, "P3": 0.03}
_DEFAULT_ACTION_TYPE = "logic_enhance"
_TREATMENT_AUDIT_METHOD_ID = "treatment_engine"
_EXECUTION_ORDER_TARGET_ID = "execution_order"
_EXECUTION_ORDER_TARGET = f"treatment/{_EXECUTION_ORDER_TARGET_ID}"
_EXECUTION_ORDER_DESCRIPTION = "优化治疗执行顺序，确保高优先级问题优先处理"
_EXECUTION_ORDER_REMEDY = "按 P0→P1→P2 严格排序，同优先级内按影响面排序"
_EXECUTION_ORDER_IMPACT = "提高修复效率"
_EXECUTION_ORDER_PRIORITY = "P1"
_EXECUTION_ORDER_CONFIDENCE = 0.7
_TREATMENT_PROCESS_ACTION_TYPE = "process_improve"
_SEVERITY_DEFAULT_PRIORITY = "P2"
_DEFAULT_ACTION_LEVEL = "L2"
_ACTION_LEVEL_MAP: dict[str, str] = {
    FIELD_THRESHOLD_ADJUST: "L1", _DEFAULT_ACTION_TYPE: _DEFAULT_ACTION_LEVEL,
    "rule_refine": "L3", "new_check": _DEFAULT_ACTION_LEVEL,
    _TREATMENT_PROCESS_ACTION_TYPE: _DEFAULT_ACTION_LEVEL}
_CV_CODE_TARGETS: dict[str, tuple[str, str]] = {
    _DEFAULT_ACTION_TYPE: ("xv_core", "逻辑增强"),
    "rule_refine": ("xv_rules", "精化"),
}
_SUGGESTION_KEEP = 20
_CODE_FEEDBACK_MAX_ITEMS = 5
_CODE_FEEDBACK_MIN_CONFIDENCE = 0.7
_PENDING_ENTRY_STATUS = "pending"
def _is_pending_entry(entry: dict) -> bool:
    status = entry.get("status")
    return isinstance(status, str) and status.strip().lower() == _PENDING_ENTRY_STATUS
_ENTRY_CONTENT_FIELDS: tuple[str, ...] = (
    "timestamp", "round_start_ts", "target", "description", "action_type",
    FIELD_SUGGESTED_VALUE, FIELD_EXPECTED_IMPACT, "confidence",
)
def _entry_content_key(entry: dict) -> tuple[str, ...]:
    return tuple(_stable_identity(entry.get(key))
                 for key in _ENTRY_CONTENT_FIELDS)
def _load_feedback_history(skill_dir: str) -> dict:
    if not skill_dir:
        return default_feedback_history()
    history = read_evolution_section(skill_dir, "feedback_history", None)
    if history is None:
        return default_feedback_history()
    if not isinstance(history, dict):
        raise _FeedbackHistoryShapeError(
            "反馈历史顶层必须为 JSON 对象，"
            f"实际为 {type(history).__name__}")
    return history
def _save_feedback_history(skill_dir: str, history: dict) -> None:
    if not write_evolution_section(skill_dir, "feedback_history", history):
        raise OSError(
            f"反馈历史 section 落盘失败（evolution_state.json）: {skill_dir}")
def _subdict_guard(history: dict, key: str) -> dict:
    sub = history.setdefault(key, {})
    if sub is None:
        sub = {}
        history[key] = sub
    if not isinstance(sub, dict):
        raise _FeedbackHistoryShapeError(
            f"反馈历史分区 {key} 必须为 JSON 对象，"
            f"实际为 {type(sub).__name__}；拒绝覆盖原数据")
    return sub
def _dict_entry(mapping: dict, key: str) -> dict:
    entry = mapping.get(key)
    if entry is None:
        return {}
    if not isinstance(entry, dict):
        raise _FeedbackHistoryShapeError(
            f"反馈历史条目 {key} 必须为 JSON 对象，"
            f"实际为 {type(entry).__name__}；拒绝覆盖原数据")
    return entry
def _merge_provenance(sug: dict, provenance: dict | None) -> None:
    if isinstance(provenance, dict):
        for pk in ("phase", "rule_id", "source"):
            if provenance.get(pk):
                sug[pk] = provenance[pk]
def _append_suggestion(entry: dict, list_key: str, sug: dict) -> None:
    items = entry.get(list_key)
    if items is None:
        items = []
    elif not isinstance(items, list):
        raise _FeedbackHistoryShapeError(
            f"反馈历史建议列表 {list_key} 必须为 JSON 数组，"
            f"实际为 {type(items).__name__}；拒绝覆盖原数据")
    items.append(sug)
    entry[list_key] = items[-_SUGGESTION_KEEP:]
    entry["_last_updated"] = time.strftime(FMT_DATETIME)
def _stable_identity(value) -> str:
    if isinstance(value, dict):
        try:
            return json.dumps(value, sort_keys=True, ensure_ascii=False,
                              default=str)
        except (TypeError, ValueError) as _e:
            log_swallowed(__name__, _e, context="stable_identity:json")
    return repr(value)
def _merge_key(entry: dict) -> tuple:
    if _is_pending_entry(entry):
        return ("pending", enhancement_dedup_key(entry))
    return ("event", _stable_identity(entry))
def _session_sort_key(session) -> tuple[int, str]:
    timestamp = session.get("timestamp") if isinstance(session, dict) else None
    if not isinstance(timestamp, str):
        return (0, "")
    return (1, timestamp.replace("T", " "))
def _session_identity(session) -> str:
    if isinstance(session, dict):
        session_id = session.get("session_id")
        if isinstance(session_id, str) and session_id.strip():
            return f"id:{session_id.strip()}"
    return f"content:{_stable_identity(session)}"
def _sync_session_count(history: dict, disk: dict | None = None) -> None:
    identities: list[str] = []
    seen: set[str] = set()
    counts = [as_count(history.get("session_count"))]
    sources = (history,) if disk is None else (disk, history)
    for source in sources:
        counts.append(as_count(source.get("session_count")))
        raw_ids = source.get("session_ids")
        candidates = [item for item in raw_ids if isinstance(item, str)] \
            if isinstance(raw_ids, list) else []
        sessions = source.get("sessions")
        if isinstance(sessions, list):
            candidates.extend(_session_identity(session) for session in sessions)
        for identity in candidates:
            if identity and identity not in seen:
                seen.add(identity)
                identities.append(identity)
    history["session_ids"] = identities
    history["session_count"] = max([len(identities), *counts])
def _declared_multiplier(value) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, str):
        try:
            value = float(value.strip())
        except (TypeError, ValueError):
            return None
    number = finite_float_or_none(value)
    if number is None or not 0.5 <= number <= 1.0:
        return None
    return round(number, 2)
def _threshold_multiplier(action: dict, confidence: float) -> float:
    declared = _declared_multiplier(action.get(FIELD_SUGGESTED_VALUE))
    if declared is not None:
        return declared
    raw_severity = action.get("priority", _SEVERITY_DEFAULT_PRIORITY)
    severity = (raw_severity.strip().upper()
                if isinstance(raw_severity, str) else "")
    factor = _SEVERITY_THRESHOLD_FACTOR.get(
        severity, _SEVERITY_THRESHOLD_FACTOR[_SEVERITY_DEFAULT_PRIORITY])
    adjustment = max(0.5, 0.85 - factor)
    if confidence > 0.8:
        adjustment = max(0.5, adjustment - 0.05)
    return round(adjustment, 2)
class FeedbackEnhancer:
    def __init__(self, skill_dir: str):
        self.skill_dir, _ = feedback_enhancement_log_context(skill_dir)
        self._enhancement_history = self._load_history()
        self._tracker = EnhancementTracker(self.skill_dir)
    def _feedback_provenance(self, report: RetrospectiveReport,
                             action: dict | None = None) -> dict:
        action = action if isinstance(action, dict) else {}
        ta = report.treatment_audit if isinstance(report.treatment_audit, dict) else {}
        rid = clean_enhancement_text(action.get("target_id", "") or action.get("rule_id", ""))
        _dc = {
            "rule_id": rid,
            "severity": action.get("priority", ""),
            "target_type": action.get("target_type", ""),
            "description": action.get("description", ""),
            "current_value": clean_enhancement_text(
                action.get("current_value", "")),
            "suggested_value": clean_enhancement_text(
                action.get("suggested_value", "")),
        }
        _dc.update(method_audit_digest_from_list(report, rid))
        return build_provenance(
            report,
            phase=action.get("phase", "review"),
            rule_id=rid,
            diagnosis_context=_dc,
            treatment_context=augment_treatment_context(
                treatment_context_digest(ta, with_worsened=False),
                self.skill_dir, rid),
            source="feedback_enhancer",
        )
    @staticmethod
    def _normalize_actions(raw_actions) -> list[dict]:
        if not isinstance(raw_actions, list) and raw_actions is not None:
            logger.warning(
                "[FeedbackEnhancer] enhancement_actions 非 list(%s)，按空行动处理",
                type(raw_actions).__name__)
        actions = enhancement_dict_items(raw_actions)
        if isinstance(raw_actions, list) and len(actions) != len(raw_actions):
            logger.warning(
                "[FeedbackEnhancer] %d 项增强行动非 dict 条目，已跳过",
                len(raw_actions) - len(actions))
        return actions
    @staticmethod
    def _priority_batches(actions: list[dict]) -> list[list[dict]]:
        priority_order = ("P0", "P1", "P2", "P3")
        batches: dict[str, list[dict]] = {p: [] for p in priority_order}
        fallback_actions: list[dict] = []
        for action in actions:
            priority = action.get("priority")
            if isinstance(priority, str):
                priority = priority.strip().upper()
            if priority in priority_order:
                batches[priority].append(action)
            else:
                fallback_actions.append(action)
        if fallback_actions:
            logger.warning(
                "[FeedbackEnhancer] %d 项行动优先级非 P0-P3（如 %s），按末位兜底批次处理",
                len(fallback_actions),
                sorted({repr(a.get("priority")) for a in fallback_actions})[:3])
        return [batches[p] for p in priority_order] + [fallback_actions]
    def enhance(self, report: RetrospectiveReport,
                cv_report: dict | None = None,
                treatment_outcome: dict | None = None) -> list[dict]:
        actions = self._normalize_actions(report.enhancement_actions)
        enhancement_log: list[dict] = []
        seen_adj_ids: set[str] = set()
        for priority_actions in self._priority_batches(actions):
            for action in priority_actions:
                adj_id = self._unique_adjustment_id(action, seen_adj_ids)
                enhancement_log.append(self._snapshot_and_apply(
                    action, adj_id, report, cv_report, treatment_outcome))
        enhancement_log.extend(self._rollback_suggestions(report))
        self._record_session(report, len(actions), enhancement_log)
        logger.info("[FeedbackEnhancer] 增强完成: %d 项行动, %d 项已应用",
                    len(actions),
                    sum(1 for le in enhancement_log if le.get("applied")))
        return enhancement_log
    @staticmethod
    def _unique_adjustment_id(action: dict, seen_adj_ids: set) -> str:
        adj_id = action.get("action_id", "")
        if not isinstance(adj_id, str):
            adj_id = str(adj_id or "")
        if not adj_id:
            logger.warning(
                "[FeedbackEnhancer] 增强行动缺 action_id"
                "（target=%s），快照键以固定占位符代替",
                action.get("target_id", ""))
            adj_id = "anonymous"
        if adj_id in seen_adj_ids:
            suffix = 2
            while f"{adj_id}#{suffix}" in seen_adj_ids:
                suffix += 1
            logger.warning(
                "[FeedbackEnhancer] 同轮 action_id 重复（%s），"
                "快照键派生为 %s#%d",
                adj_id, adj_id, suffix)
            adj_id = f"{adj_id}#{suffix}"
        seen_adj_ids.add(adj_id)
        return adj_id
    @staticmethod
    def _snapshot_adjustment_id(report: RetrospectiveReport,
                              adj_id: str) -> str:
        anchor = str_or(report.round_start_ts).strip()
        if not anchor:
            anchor = str_or(report.session_id).strip()
        return f"{anchor}/{adj_id}" if anchor else adj_id
    def _snapshot_and_apply(self, action: dict, adj_id: str,
                            report: RetrospectiveReport,
                            cv_report: dict | None,
                            treatment_outcome: dict | None) -> dict:
        target = clean_enhancement_text(action.get("target_id", ""))
        action_type = action.get("action_type", "")
        if not isinstance(action_type, str):
            logger.warning(
                "[FeedbackEnhancer] 增强行动 action_type 非 str"
                "（%s），归空串走默认级别 L2（target=%s）",
                type(action_type).__name__, target)
            action_type = ""
        level = _ACTION_LEVEL_MAP.get(action_type, _DEFAULT_ACTION_LEVEL)
        snapshot_id = self._snapshot_adjustment_id(report, adj_id)
        result = self._apply_single_action(
            action, self._feedback_provenance(report, action))
        applied = bool(result.get("applied"))
        tracked = False
        if applied:
            try:
                capture_result = self._tracker.capture_before(
                    snapshot_id, level, target, action_type,
                    cv_report=cv_report, treatment_outcome=treatment_outcome)
            except Exception as track_err:
                logger.warning(
                    "[FeedbackEnhancer] 行动 %s 已应用，但 before 快照写入失败"
                    "（不阻断已落盘建议）: %s", adj_id, track_err)
            else:
                tracked = capture_result is not False
                if not tracked:
                    logger.warning(
                        "[FeedbackEnhancer] 行动 %s 已应用，但 before 快照未持久化"
                        "（不阻断已落盘建议）", adj_id)
        result["enhancement_tracked"] = tracked
        result["adjustment_id"] = snapshot_id
        return result
    def _rollback_suggestions(self, report: RetrospectiveReport) -> list[dict]:
        rb_entries = []
        rollback_targets = self._tracker.get_rollback_targets()
        for rt in rollback_targets:
            adj_id = rt.get("adjustment_id", "")
            if not self._tracker.should_rollback(adj_id):
                continue
            logger.warning("[FeedbackEnhancer] 调整 %s 建议回滚", adj_id)
            if rt.get("rollback_reason") == "single_large_degradation":
                reason = "单次大幅退化（precision 急剧下降）"
                rb_msg = f"{reason}，建议回滚"
            else:
                reason = "连续退化"
                rb_msg = (f"连续{rt.get('consecutive_degraded', 0)}次"
                          f" degraded，建议回滚")
            saved = self._write_code_suggestion(
                target=str(rt.get("target") or f"adjustment/{adj_id}"),
                description=f"[回滚建议] 调整 {adj_id}: {reason}，建议回滚",
                suggested_value=(
                    f"回滚调整 {adj_id}（目标 {rt.get('target', '')}）至基线值："
                    f"追踪器判定 {rt.get('verdict', '')}，{rb_msg}"),
                expected_impact="恢复退化前基线，防止调整持续劣化",
                confidence=0.8,
                action_type=_TREATMENT_PROCESS_ACTION_TYPE,
                provenance=self._feedback_provenance(report, {
                    "phase": "retrospective",
                    "target_id": adj_id,
                    "priority": "P1",
                    "target_type": "adjustment_rollback",
                    "description": rb_msg,
                }),
            )
            rb_entries.append({
                "action_id": adj_id,
                "target_id": rt.get("target"),
                "target_type": "adjustment_rollback",
                FIELD_ROLLBACK_RECOMMENDED: True,
                "verdict": rt.get("verdict"),
                "message": ("回滚建议已写入待审队列" if saved
                            else "回滚建议未落盘（详见日志）"),
                "applied": False,
                "persisted_to_review": saved,
            })
        return rb_entries
    def _record_session(self, report: RetrospectiveReport,
                        actions_count: int, enhancement_log: list[dict]) -> None:
        scores = report.scores if isinstance(report.scores, dict) else {}
        self._enhancement_history["sessions"].append({
            "timestamp": report.timestamp,
            "session_id": report.session_id,
            "overall_score": scores.get("overall", 0),
            "actions_generated": actions_count,
            "actions_applied": sum(1 for le in enhancement_log if le.get("applied")),
        })
        _sync_session_count(self._enhancement_history)
        if not self._save_history():
            logger.warning(
                "[FeedbackEnhancer] 本轮会话记录未落盘（增强历史不可读或写入失败），"
                "session 计数与 ROI 基线不会前进")
    def _apply_single_action(self, action: dict,
                             provenance: dict | None = None) -> dict:
        result = {
            "action_id": action.get("action_id"),
            "target_type": action.get("target_type"),
            "target_id": action.get("target_id"),
            "action_type": action.get("action_type"),
            "applied": False,
            "message": "",
        }
        target_type = action.get("target_type")
        handlers = {
            FIELD_DIAGNOSIS_METHOD: self._enhance_diagnosis_method,
            "cv_rule": self._enhance_cv_rule,
            "treatment_process": self._enhance_treatment_process,
        }
        handler = handlers.get(target_type) if isinstance(target_type, str) else None
        if handler is None:
            result["message"] = f"未知目标类型: {target_type}"
            return result
        try:
            result.update(handler(action, provenance))
        except Exception as e:
            result["message"] = f"增强失败: {e}"
            logger.warning("[FeedbackEnhancer] 行动 %s 失败: %s",
                           action.get("action_id"), e)
        return result
    @staticmethod
    def _action_context(action: dict) -> tuple[str, str, float]:
        return (action.get("action_type", ""),
                clean_enhancement_text(action.get("target_id", "")),
                clean_enhancement_confidence(action.get("confidence")))
    def _enhance_diagnosis_method(self, action: dict,
                                  provenance: dict | None = None) -> dict:
        action_type, target_id, confidence = self._action_context(action)
        if action_type == FIELD_THRESHOLD_ADJUST:
            return self._apply_threshold_adjust(
                action, target_id, confidence, provenance)
        if action_type == _DEFAULT_ACTION_TYPE:
            return self._persist_code_suggestion(
                action, target_id=target_id,
                subject=f"{target_id} 逻辑增强",
                confidence=confidence, action_type=action_type,
                provenance=provenance)
        if action_type == "new_check":
            return self._persist_code_suggestion(
                action, target_id=target_id,
                subject=f"{target_id} 新检测",
                confidence=confidence, desc_prefix="新增检测项: ",
                action_type=action_type, provenance=provenance)
        return {"applied": False, "message": f"未知的 action_type: {action_type}"}
    def _apply_threshold_adjust(self, action: dict, target_id: str,
                                confidence: float,
                                provenance: dict | None) -> dict:
        adjustment = _threshold_multiplier(action, confidence)
        saved = self._write_threshold_adjustment(
            container_key=FIELD_METHOD_THRESHOLDS,
            list_key="suggestions",
            item_id=target_id,
            param="confidence_multiplier",
            value=adjustment,
            description=clean_enhancement_text(action.get("description", "")),
            confidence=confidence,
            provenance=provenance,
            missing_label="方法调整建议缺 method_id，跳过写入",
            failure_label="写入方法调整失败",
        )
        return self._outcome(
            saved,
            f"已记录 {target_id} 阈值调整建议 (乘数={adjustment:.2f})",
            f"{target_id} 阈值调整建议未落盘"
            "（缺有效标识或写入失败，详见日志）")
    def _persist_code_suggestion(self, action: dict, *, target_id: str,
                                 subject: str, confidence: float,
                                 target_prefix: str = "",
                                 action_type: str,
                                 desc_prefix: str = "",
                                 provenance: dict | None = None) -> dict:
        target_id = clean_enhancement_text(target_id).strip()
        if not target_id:
            logger.warning("[FeedbackEnhancer] %s建议缺有效目标标识，跳过写入",
                           subject)
            return {"applied": False,
                    "message": f"{subject}建议缺有效目标标识，未落盘"}
        saved = self._write_code_suggestion(
            f"{target_prefix}{target_id}",
            f"{desc_prefix}{action.get('description', '')}",
            action.get(FIELD_SUGGESTED_VALUE, ""),
            action.get(FIELD_EXPECTED_IMPACT, ""),
            confidence,
            action_type=action_type,
            provenance=provenance,
        )
        return self._outcome(
            saved, f"已记录 {subject}建议", f"{subject}建议未落盘（详见日志）")
    @staticmethod
    def _outcome(saved: bool, success: str, failure: str) -> dict:
        return {"applied": bool(saved), "message": success if saved else failure}
    def _enhance_cv_rule(self, action: dict,
                         provenance: dict | None = None) -> dict:
        action_type, target_id, confidence = self._action_context(action)
        if action_type == FIELD_THRESHOLD_ADJUST:
            multiplier = _threshold_multiplier(action, confidence)
            desc = clean_enhancement_text(action.get("description", ""))
            saved = self._write_threshold_adjustment(
                container_key=FIELD_CV_RULE_WEIGHTS,
                list_key="adjustments",
                item_id=target_id,
                param="confidence_multiplier",
                value=multiplier,
                description=desc,
                confidence=confidence,
                provenance=provenance,
                missing_label="CV 调整建议缺 rule_id，跳过写入",
                failure_label="写入CV调整失败",
            )
            return self._outcome(
                saved,
                f"已记录 CV 规则 {target_id} 阈值调整 (乘数={multiplier:.2f})",
                f"CV 规则 {target_id} 阈值调整未落盘"
                "（缺有效标识或写入失败，详见日志）")
        code_target = (_CV_CODE_TARGETS.get(action_type)
                       if isinstance(action_type, str) else None)
        if code_target is None:
            return {"applied": False,
                    "message": f"未知的 action_type: {action_type}"}
        target_dir, label = code_target
        return self._persist_code_suggestion(
            action, target_id=target_id,
            target_prefix=f"{target_dir}/",
            subject=f"CV 规则 {target_id} {label}", confidence=confidence,
            action_type=action_type, provenance=provenance)
    def _enhance_treatment_process(self, action: dict,
                                   provenance: dict | None = None) -> dict:
        target_id = clean_enhancement_text(action.get("target_id", ""))
        entry_action_type = action.get("action_type")
        if not isinstance(entry_action_type, str) or not entry_action_type.strip():
            entry_action_type = _TREATMENT_PROCESS_ACTION_TYPE
        return self._persist_code_suggestion(
            action, target_id=target_id, target_prefix="treatment/",
            subject=f"治疗过程 {target_id} 增强",
            confidence=clean_enhancement_confidence(action.get("confidence")),
            action_type=entry_action_type, provenance=provenance)
    def _write_threshold_adjustment(self, *, container_key: str, list_key: str,
                                    item_id: str, param: str, value: float,
                                    description: str, confidence: float,
                                    provenance: dict | None,
                                    missing_label: str,
                                    failure_label: str) -> bool:
        description = clean_enhancement_text(description)
        return self._append_feedback_suggestion(
            container_key=container_key,
            list_key=list_key,
            item_id=item_id,
            description=description,
            confidence=confidence,
            suggestion={
                "timestamp": time.strftime(FMT_DATETIME_ISO),
                "feedback_type": "threshold_adjustment",
                "reason": description,
                FIELD_SUGGESTED_VALUE: {param: value},
            },
            provenance=provenance,
            missing_label=missing_label,
            failure_label=failure_label,
        )
    def _append_feedback_suggestion(self, *, container_key: str, list_key: str,
                                    item_id: str, description: str,
                                    confidence: float, suggestion: dict,
                                    provenance: dict | None,
                                    missing_label: str,
                                    failure_label: str) -> bool:
        item_id = (item_id if isinstance(item_id, str)
                   else str(item_id or "")).strip()
        if not item_id:
            logger.warning("[FeedbackEnhancer] %s", missing_label)
            return False
        try:
            with _required_write_lock(self.skill_dir):
                history = _load_feedback_history(self.skill_dir)
                section = _subdict_guard(history, container_key)
                entry = _dict_entry(section, item_id)
                previous_items = entry.get(list_key)
                previous_count = (len(previous_items)
                                  if isinstance(previous_items, list) else 0)
                entry["trigger_count"] = max(
                    as_count(entry.get("trigger_count")), previous_count) + 1
                suggestion.setdefault("confidence", confidence)
                _merge_provenance(suggestion, provenance)
                _append_suggestion(entry, list_key, suggestion)
                entry["_confidence"] = confidence
                entry["_description"] = description
                section[item_id] = entry
                _save_feedback_history(self.skill_dir, history)
            return True
        except _FEEDBACK_WRITE_ERRORS as e:
            logger.warning("[FeedbackEnhancer] %s: %s", failure_label, e)
            return False
    def _write_code_suggestion(self, target: str, description: str,
                               suggested_value: str, expected_impact: str,
                               confidence: float,
                               action_type: str,
                               provenance: dict | None = None) -> bool:
        entry = EnhancementEntryFactory(self.skill_dir).build(
            timestamp=time.strftime(FMT_DATETIME),
            target=target,
            description=description,
            suggested_value=suggested_value,
            expected_impact=expected_impact,
            confidence=confidence,
            action_type=action_type,
            provenance=provenance,
        )
        entries = normalized_enhancement_entries(self._enhancement_history)
        previous_count = len(entries)
        appended_entry = None
        try:
            append_enhancement_entry(entries, entry)
            if len(entries) > previous_count:
                appended_entry = entries[-1]
            if self._save_history():
                return True
        except Exception as e:
            logger.warning("[FeedbackEnhancer] 写入增强建议失败: %s", e)
        if appended_entry is not None:
            current_entries = normalized_enhancement_entries(
                self._enhancement_history)
            self._enhancement_history["entries"] = [
                item for item in current_entries if item is not appended_entry]
        return False
    def _load_history(self) -> dict:
        data, readable = read_enhancement_log(
            self.skill_dir, label="FeedbackEnhancer")
        if not readable or data is None:
            logger.warning(
                "[FeedbackEnhancer] 增强历史不可读（IO/内容损坏），本轮只读不写，"
                "保留原状态待人工修复: %s", self.skill_dir)
            return {"entries": [], "sessions": []}
        if not isinstance(data.get("sessions"), list):
            data["sessions"] = []
        return data
    def _save_history(self) -> bool:
        try:
            with _required_write_lock(self.skill_dir):
                disk = self._read_disk_history()
                if disk is None:
                    logger.warning(
                        "[FeedbackEnhancer] 增强历史不可读，放弃本轮落盘以保留原文件"
                        "（建议标记为未落盘，可修复后重跑）")
                    return False
                self._merge_disk_entries(disk)
                self._merge_disk_sessions(disk)
                save_enhancement_log(
                    self.skill_dir, self._enhancement_history)
            return True
        except _FEEDBACK_WRITE_ERRORS as e:
            logger.warning("[FeedbackEnhancer] 增强历史保存失败: %s", e)
            return False
    def _merge_disk_entries(self, disk: dict) -> None:
        disk_entries = [e for e in disk.get("entries", [])
                        if isinstance(e, dict)]
        if not disk_entries:
            return
        mem_entries = [
            e for e in normalized_enhancement_entries(self._enhancement_history)
            if isinstance(e, dict)]
        mem_by_key: dict[tuple, list[tuple[int, dict]]] = {}
        for index, entry in enumerate(mem_entries):
            mem_by_key.setdefault(_merge_key(entry), []).append((index, entry))
        used_mem_indices: set[int] = set()
        merged: list[dict] = []
        consumed_keys = self._consumed_entry_keys(disk_entries)
        mem_consumed_keys = self._consumed_entry_keys(mem_entries)
        for disk_entry in disk_entries:
            if (_is_pending_entry(disk_entry)
                    and _entry_content_key(disk_entry) in mem_consumed_keys):
                logger.info(
                    "[FeedbackEnhancer] 内存已完成消费，丢弃磁盘 pending 副本: %s",
                    enhancement_dedup_key(disk_entry)[0])
                continue
            candidates = mem_by_key.get(_merge_key(disk_entry), [])
            if not candidates:
                merged.append(disk_entry)
                continue
            index, _mem_entry = candidates.pop(0)
            used_mem_indices.add(index)
            merged.append(disk_entry)
        for index, entry in enumerate(mem_entries):
            if index in used_mem_indices:
                continue
            if (_is_pending_entry(entry)
                    and _entry_content_key(entry) in consumed_keys):
                logger.info(
                    "[FeedbackEnhancer] 同一条建议已被消费，丢弃内存 pending 副本: %s",
                    enhancement_dedup_key(entry)[0])
                continue
            merged.append(entry)
        self._enhancement_history["entries"] = merged
    @staticmethod
    def _consumed_entry_keys(disk_entries: list[dict]) -> set[tuple]:
        return {_entry_content_key(entry) for entry in disk_entries
                if not _is_pending_entry(entry)}
    def _read_disk_history(self) -> dict | None:
        if not self.skill_dir:
            logger.warning(
                "[FeedbackEnhancer] 增强日志落点未解析（无可用产物根），"
                "本轮不写盘")
            return None
        data, readable = read_enhancement_log(
            self.skill_dir, label="FeedbackEnhancer")
        return data if readable and data is not None else None
    def _merge_disk_sessions(self, disk: dict) -> None:
        disk_sessions = disk.get("sessions", [])
        if not isinstance(disk_sessions, list):
            disk_sessions = []
        mem_sessions = self._enhancement_history.get("sessions")
        if not isinstance(mem_sessions, list):
            mem_sessions = []
            self._enhancement_history["sessions"] = mem_sessions
        merged: list = []
        seen: set[str] = set()
        for session in (*disk_sessions, *mem_sessions):
            key = _session_identity(session)
            if key in seen:
                continue
            seen.add(key)
            merged.append(session)
        merged.sort(key=_session_sort_key)
        self._enhancement_history["sessions"] = merged
        _sync_session_count(self._enhancement_history, disk)
def _is_fixer_safety_candidate(entry: dict) -> bool:
    return (entry.get("target") == "treatment/fixer_safety"
            and clean_enhancement_confidence(entry.get("confidence")) >= 0.6)
_RULE_ID_PREFIX_PATTERN = (
    r'(?<![A-Za-z0-9_])([A-Z]{1,4}(?:[-\d][A-Za-z0-9_]*)+)'
    r'(?![A-Za-z0-9_])')
_RULE_ID_PATTERNS = (
    _RULE_ID_PREFIX_PATTERN,
    r'(?<![a-z0-9_])([a-z]{3,}(?:_[a-z]{3,})+)(?![a-z0-9_])',
)
_SEVERITY_TOKEN_PATTERN = re.compile(r"P\d")
def _extract_rule_id(entry: dict, desc: str) -> str | None:
    sources = [(desc, _RULE_ID_PATTERNS)]
    evidence = entry.get("evidence", [])
    if isinstance(evidence, list):
        sources.extend(
            (str(ev), (_RULE_ID_PREFIX_PATTERN,)) for ev in evidence)
    for text, patterns in sources:
        for pattern in patterns:
            for rule_match in re.finditer(pattern, text):
                candidate = rule_match.group(1)
                if (candidate != _TREATMENT_AUDIT_METHOD_ID
                        and not _SEVERITY_TOKEN_PATTERN.fullmatch(candidate)):
                    return candidate
    return None
def _issue_desc(issue: dict) -> str:
    desc = issue.get("description")
    return desc if isinstance(desc, str) else str(desc or "")
def _is_treatment_side_effect_issue(issue: dict) -> bool:
    if issue.get("phase") != "treatment":
        return False
    if (issue.get("method_id") == _TREATMENT_AUDIT_METHOD_ID
            and issue.get("impact") == "越修越坏"):
        return True
    return "引入新问题" in _issue_desc(issue)
class _EntryDraft(NamedTuple):
    action: str
    description: str
    severity: str
    remedy: str
    target: str
    impact: str
    confidence: float
    issue: dict | None = None
class TreatmentEnhancer:
    def __init__(self, skill_dir: str, enqueue_fn=None):
        self.skill_dir, _ = feedback_enhancement_log_context(skill_dir)
        self._enqueue_fn = enqueue_fn
    def _retro_provenance(self, report: RetrospectiveReport,
                          issue: dict | None = None) -> dict:
        issue = issue if isinstance(issue, dict) else {}
        _rid = clean_enhancement_text(
            issue.get("rule_id", "") or issue.get("target_id", "")
            or issue.get("method_id", ""))
        _dc = {
            "rule_id": _rid,
            "severity": issue.get("severity", ""),
            "location": issue.get("location", "") or issue.get("file", ""),
            "description": issue.get("description", ""),
        }
        _dc.update(method_audit_digest_from_list(report, _rid))
        return build_provenance(
            report,
            phase=issue.get("phase", ""),
            rule_id=_rid,
            diagnosis_context=_dc,
            treatment_context=augment_treatment_context(
                treatment_context_digest(report.treatment_audit, with_worsened=True),
                self.skill_dir, _rid),
            source="treatment_feedback_enhancer",
        )
    def enhance(self, report: RetrospectiveReport) -> list[dict]:
        log = []
        persistent_entries = []
        entry_factory = EnhancementEntryFactory(self.skill_dir)
        issues = enhancement_dict_items(report.issues_found)
        def _add(action: str, description: str, severity: str,
                 remedy: str, target: str, impact: str,
                 confidence: float, issue: dict | None = None) -> None:
            draft = _EntryDraft(action, description, severity, remedy,
                                target, impact, confidence, issue)
            log.append({
                "action": draft.action,
                "description": draft.description,
                "severity": draft.severity,
                "remedy": draft.remedy,
                "applied": True,
            })
            persistent_entries.append(
                self._build_entry(report, draft, entry_factory))
        self._apply_rollback_channel(issues, _add)
        self._apply_side_effect_channel(issues, _add)
        self._apply_execution_order_channel(report, _add)
        if persistent_entries:
            persisted = self._persist_entries(persistent_entries)
            if persisted:
                self._apply_to_adjustments(persistent_entries)
            else:
                for item in log:
                    if item.get("applied") and "action" in item:
                        item["applied"] = False
                        item["message"] = "增强条目未落盘（详见日志）"
        logger.info("[TreatmentEnhancer] 治疗增强: %d 项", len(log))
        return log
    def _build_entry(self, report: RetrospectiveReport, draft: _EntryDraft,
                     entry_factory: EnhancementEntryFactory) -> dict:
        entry = entry_factory.build(
            timestamp=report.timestamp,
            target=draft.target,
            description=draft.description,
            suggested_value=draft.remedy,
            expected_impact=draft.impact,
            confidence=draft.confidence,
            action_type=draft.action,
            provenance=self._retro_provenance(report, draft.issue),
        )
        evidence = (draft.issue.get("evidence")
                    if isinstance(draft.issue, dict) else None)
        if isinstance(evidence, list) and evidence:
            entry["evidence"] = evidence
        return entry
    @staticmethod
    def _apply_rollback_channel(issues: list[dict], add) -> None:
        for issue in issues:
            if issue.get("phase") == "treatment":
                desc = _issue_desc(issue)
                if "回滚" in desc:
                    add("recalibrate_fixer_safety", desc,
                        issue.get("severity", ""),
                        "将相关修复器的 auto_safe 标签降为 False",
                        "treatment/fixer_safety", "降低回滚率", 0.8, issue)
    @staticmethod
    def _apply_side_effect_channel(issues: list[dict], add) -> None:
        side_issue = next((i for i in issues
                           if _is_treatment_side_effect_issue(i)), None)
        if side_issue is not None:
            add("enhance_side_effect_detection", "增强修复后副作用检测",
                side_issue.get("severity", "P0"),
                "在 fix_safety_boundary 中增加 AST diff 检测",
                "treatment/side_effect_detection", "消除越修越坏", 0.9,
                side_issue)
    @staticmethod
    def _apply_execution_order_channel(report: RetrospectiveReport,
                                       add) -> None:
        treatment_audit = report.treatment_audit
        if not isinstance(treatment_audit, dict):
            return
        _has_activity = has_treatment_activity(
            treatment_audit.get("total_items", 0),
            treatment_audit.get("executed", 0))
        pcr = effective_priority_correct_rate(
            treatment_audit.get("priority_correct_rate"))
        priority_assessed = _priority_was_assessed(
            treatment_audit.get("priority_assessed"))
        if _has_activity and priority_assessed and pcr < 0.8:
            add("optimize_execution_order", _EXECUTION_ORDER_DESCRIPTION,
                _EXECUTION_ORDER_PRIORITY,
                _EXECUTION_ORDER_REMEDY, _EXECUTION_ORDER_TARGET,
                _EXECUTION_ORDER_IMPACT, _EXECUTION_ORDER_CONFIDENCE)
    def _apply_to_adjustments(self, entries: list) -> None:
        entries = enhancement_dict_items(entries)
        if self._enqueue_fn is None:
            if any(_is_fixer_safety_candidate(entry) for entry in entries):
                logger.warning(
                    "[TreatmentEnhancer] [AI审核] fixer_safety 降级建议未入待审队列"
                    "（enqueue_fn 未注入，仅日志留痕）；编排层应注入 "
                    "ai_review_item_plan.enqueue_adjustment_proposals")
            return
        for entry in entries:
            if not _is_fixer_safety_candidate(entry):
                continue
            desc = clean_enhancement_text(entry.get("description", ""))
            rule_id = _extract_rule_id(entry, desc)
            if rule_id is None:
                structured_rule_id = entry.get("rule_id")
                candidate = (structured_rule_id.strip()
                             if isinstance(structured_rule_id, str) else "")
                if (candidate
                        and candidate != _TREATMENT_AUDIT_METHOD_ID
                        and not _SEVERITY_TOKEN_PATTERN.fullmatch(candidate)):
                    rule_id = candidate
            if rule_id is None:
                logger.warning(
                    "[TreatmentEnhancer] [AI审核] fixer_safety 建议无可用规则号，"
                    "仅保留 enhancement_log 条目（无法生成修复器级覆盖）: %s",
                    desc[:80])
                continue
            self._enqueue_fixer_safety(entry, rule_id, desc)
    def _enqueue_fixer_safety(self, entry: dict, rule_id: str,
                              desc: str) -> None:
        try:
            prov = {k: entry[k] for k in (
                "phase", "rule_id", "diagnosis_context", "treatment_context",
                "retrospective_context", "source")
                if entry.get(k) not in (None, "", [], {})}
            prov["rule_id"] = rule_id
            enq = self._enqueue_fn(
                self.skill_dir,
                fixs={rule_id: {"auto_safe": False, "reason": desc[:200]}},
                reason=("[复盘]修复回滚信号：建议修复器 " + rule_id +
                        " auto_safe 降级为 False（" + desc[:150] + "）"),
                provenance=prov or None,
            )
            if enq.get("status") == "enqueued":
                logger.info(
                    "[TreatmentEnhancer] [AI审核] 修复器 %s auto_safe 降级建议已入待审队列(队列 pending=%s)，经 run_next_ai_review 审核后执行生效",
                    rule_id, enq.get("pending"))
            else:
                logger.info(
                    "[TreatmentEnhancer] [AI审核] 修复器 %s auto_safe 降级建议已在队列（幂等跳过），经 run_next_ai_review 审核后执行生效",
                    rule_id)
        except Exception as _eq:
            logger.warning(
                "[TreatmentEnhancer] [AI审核] 修复器 %s auto_safe 降级建议入队失败（仅日志留痕）: %s",
                rule_id, _eq)
    def _persist_entries(self, entries: list) -> bool:
        appended = append_pending_enhancements(self.skill_dir, entries)
        if appended >= len(entries):
            return True
        history = get_retrospective_history(self.skill_dir)
        history_entries = enhancement_dict_items(
            normalized_enhancement_entries(history))
        persisted = {enhancement_dedup_key(e) for e in history_entries}
        return all(enhancement_dedup_key(e) in persisted for e in entries
                   if isinstance(e, dict))
def inject_roi_snapshot(tracker, feedback_history: dict) -> None:
    try:
        roi = tracker.get_roi_report()
        if isinstance(roi, dict) and roi.get("total_adjustments"):
            feedback_history["enhancement_roi"] = roi
            logger.info("[Retrospective] 增强ROI: %d 项追踪, %d 改善, %d 退化, %d 建议回滚",
                        roi.get("total_adjustments", 0),
                        roi.get("improved", 0), roi.get("degraded", 0),
                        roi.get(FIELD_ROLLBACK_RECOMMENDED, 0))
        else:
            feedback_history.pop("enhancement_roi", None)
    except Exception as roi_err:
        logger.warning("[Retrospective] 增强ROI读取失败(不阻断): %s", roi_err)
def close_pending_snapshots(tracker, diagnosis_report: dict | None,
                             treatment_execution: dict | None) -> None:
    try:
        closed = tracker.capture_after_pending(
            diagnosis_report, treatment_execution)
        if closed:
            logger.info("[Retrospective] 闭合 %d 个上一轮 pending 增强快照", closed)
    except Exception as close_err:
        logger.warning("[Retrospective] pending 快照闭合失败(不阻断): %s", close_err)
def tracker_roi_inject(skill_dir: str, feedback_history: dict,
                        diagnosis_report: dict | None,
                        treatment_execution: dict | None) -> None:
    try:
        tracker = EnhancementTracker(skill_dir)
    except Exception as tracker_err:
        logger.warning("[Retrospective] 增强快照追踪器初始化失败(不阻断): %s",
                       tracker_err)
        return
    close_pending_snapshots(tracker, diagnosis_report, treatment_execution)
    inject_roi_snapshot(tracker, feedback_history)
def inject_session_count(skill_dir: str, feedback_history: dict) -> int:
    if not isinstance(feedback_history, dict):
        logger.warning(
            "[Retrospective] session_count 注入目标非 dict(%s)，跳过注入",
            type(feedback_history).__name__)
        return 0
    try:
        history = get_retrospective_history(skill_dir)
    except _READ_ERRORS as e:
        logger.warning("[Retrospective] 增强会话数读取失败(按 0 处理): %s", e)
        return 0
    sessions = history.get("sessions")
    retained = (len({_session_identity(session) for session in sessions})
                if isinstance(sessions, list) else 0)
    session_ids = history.get("session_ids")
    identified = len({
        item for item in session_ids
        if isinstance(item, str) and item
    }) if isinstance(session_ids, list) else 0
    observed = max(retained, identified, as_count(history.get("session_count")))
    count = max(observed, as_count(feedback_history.get("session_count")))
    feedback_history["session_count"] = count
    if count:
        logger.info("[Retrospective] 反馈闭环会话数: %d", count)
    return count
def run_enhancer_channel(label: str, runner) -> list:
    try:
        result = runner()
    except Exception as exc:
        logger.warning("[Retrospective] %s失败(降级为空): %s", label, exc)
        return []
    if not isinstance(result, list):
        logger.warning("[Retrospective] %s返回非 list(%s)，降级为空清单",
                       label, type(result).__name__)
        return []
    return result
@dataclass
class RetrospectiveScore:
    diagnosis_quality: float = 0.0
    cv_accuracy: float = 0.0
    treatment_effectiveness: float = 0.0
    side_effect_control: float = 0.0
    feedback_loop_quality: float = 0.0
    @property
    def overall(self) -> float:
        return round(sum(
            getattr(self, key) * weight
            for key, _label, weight in RETRO_SCORE_DIMENSIONS) * 100, 2)
    def to_dict(self) -> dict:
        data = asdict(self)
        data["overall"] = round(self.overall, 2)
        return data
@dataclass
class GoodPractice:
    phase: str = ""
    method_id: str = ""
    description: str = ""
    evidence: list[str] = field(default_factory=list)
    reusable: bool = True
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class IssueFound:
    phase: str = ""
    severity: str = ""
    method_id: str = ""
    description: str = ""
    impact: str = ""
    root_cause: str = ""
    remedy: str = ""
    evidence: list[str] = field(default_factory=list)
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class EnhancementAction:
    action_id: str = ""
    target_type: str = ""
    target_id: str = ""
    action_type: str = ""
    description: str = ""
    priority: str = ""
    confidence: float = 0.0
    current_value: str = ""
    suggested_value: str = ""
    expected_impact: str = ""
    applied: bool = False
    def to_dict(self) -> dict:
        return asdict(self)
def has_treatment_activity(total_items: object, executed: object) -> bool:
    return any(
        isinstance(value, int) and not isinstance(value, bool) and value > 0
        for value in (total_items, executed)
    )
def effective_priority_correct_rate(value: object) -> float:
    number = finite_float_or_none(value)
    if number is None or number < 0.0 or number > 1.0:
        return 1.0
    return number
def _priority_was_assessed(value: object) -> bool:
    return value is None or signal_bool(value)
_UNDERPERFORMING_SCORE = 60.0
_DIAGNOSIS_ISSUE_TIERS = (
    (40.0, "critical", "过低", "可能产生大量误报或漏报",
     "建议提升判定阈值或增加前置条件检查"),
    (_UNDERPERFORMING_SCORE, "high", "偏低", "精准度不足",
     "建议调整阈值或增强逻辑"),
)
def _feedback_adjustment_count(feedback_history: dict) -> int:
    total = 0
    for container_key, list_key in (
            (FIELD_METHOD_THRESHOLDS, "suggestions"),
            (FIELD_CV_RULE_WEIGHTS, "adjustments")):
        container = feedback_history.get(container_key)
        if not isinstance(container, dict):
            continue
        for entry in container.values():
            if not isinstance(entry, dict):
                continue
            records = entry.get(list_key)
            retained = len(records) if isinstance(records, list) else 0
            total += max(as_count(entry.get("trigger_count")), retained)
    return total
def _feedback_session_count(feedback_history: dict) -> float:
    explicit = meta_num(feedback_history.get("session_count"))
    if explicit > 0:
        return explicit
    sessions = feedback_history.get("sessions")
    return float(len(sessions)) if isinstance(sessions, list) else 0.0
def _has_treatment_side_effects(treatment: TreatmentAuditResult) -> bool:
    return treatment.introduced_new_issues > 0 or treatment.worsened_existing > 0
class RetrospectiveComposer:
    def compose(self,
                diagnosis_audits: list[DiagnosisAuditResult],
                cv_audit: CrossValidationAuditResult,
                treatment_audit: TreatmentAuditResult,
                feedback_history: dict | None = None,
                session_id: str = "",
                skill_dir: str = "") -> RetrospectiveReport:
        report = RetrospectiveReport(
            timestamp=time.strftime(FMT_DATETIME),
            session_id=session_id or hashlib.md5(
                str(time.time()).encode(), usedforsecurity=False).hexdigest()[:8],
            skill_dir=skill_dir,
            round_start_ts=(EnhancementEntryFactory(skill_dir).round_start_ts
                            if skill_dir else ""),
        )
        report.diagnosis_audit = [a.to_dict() for a in diagnosis_audits]
        report.cv_audit = cv_audit.to_dict()
        report.treatment_audit = treatment_audit.to_dict()
        scores = RetrospectiveScore()
        scores.diagnosis_quality = self._score_diagnosis(diagnosis_audits)
        scores.cv_accuracy = cv_audit.score / 100.0
        scores.treatment_effectiveness = treatment_audit.score / 100.0
        scores.side_effect_control = self._score_side_effects(treatment_audit)
        scores.feedback_loop_quality = self._score_feedback_loop(feedback_history)
        report.scores = scores.to_dict()
        report.good_practices = self._extract_good_practices(
            diagnosis_audits, cv_audit, treatment_audit)
        report.issues_found = self._extract_issues(
            diagnosis_audits, cv_audit, treatment_audit)
        report.enhancement_actions = self._generate_enhancements(
            diagnosis_audits, cv_audit, treatment_audit)
        report.summary = _compose_summary(scores, report)
        return report
    def _score_diagnosis(self, audits: list[DiagnosisAuditResult]) -> float:
        if not audits:
            return 0.0
        return sum(a.score for a in audits) / len(audits) / 100.0
    def _score_side_effects(self, treatment: TreatmentAuditResult) -> float:
        side_effect_count = (
            treatment.introduced_new_issues + treatment.worsened_existing)
        if treatment.executed <= 0:
            return 0.0 if side_effect_count > 0 else 0.5
        side_rate = side_effect_count / treatment.executed
        if side_rate == 0:
            return 1.0
        if side_rate < 0.1:
            return 0.8
        if side_rate < 0.3:
            return 0.5
        return max(0.0, 0.5 - (side_rate - 0.3) * 2.5)
    def _score_feedback_loop(self, feedback_history: dict | None = None) -> float:
        metrics = self._feedback_loop_metrics(feedback_history)
        if metrics is None:
            return 0.3
        session_count, total_adjustments, effectiveness, ineffectiveness = metrics
        base = self._feedback_loop_base(session_count)
        adj_penalty = min(total_adjustments * 0.02, 0.15)
        eff_bonus = effectiveness * 0.15
        ineff_penalty = ineffectiveness * 0.10
        score = base - adj_penalty + eff_bonus - ineff_penalty
        return max(0.0, min(1.0, score))
    @staticmethod
    def _feedback_loop_metrics(
        feedback_history: dict | None,
    ) -> tuple[float, int, float, float] | None:
        if not feedback_history:
            return None
        session_count = _feedback_session_count(feedback_history)
        total_adjustments = _feedback_adjustment_count(feedback_history)
        enhancement_roi = as_dict(feedback_history.get("enhancement_roi"))
        total_tracked = meta_num(enhancement_roi.get("total_adjustments"))
        if total_adjustments == 0 and total_tracked <= 0:
            return None
        if total_tracked > 0:
            effectiveness = meta_num(enhancement_roi.get("improved")) / total_tracked
            ineffectiveness = meta_num(enhancement_roi.get("degraded")) / total_tracked
        else:
            effectiveness = 0.5
            ineffectiveness = 0.2
        return session_count, total_adjustments, effectiveness, ineffectiveness
    @staticmethod
    def _feedback_loop_base(session_count: float) -> float:
        if session_count < 3:
            return 0.5
        if session_count < 10:
            return 0.7
        return min(0.8, 0.7 + session_count / 200.0)
    def _extract_good_practices(self,
                                diagnosis_audits: list[DiagnosisAuditResult],
                                cv_audit: CrossValidationAuditResult,
                                treatment_audit: TreatmentAuditResult) -> list[dict]:
        practices: list[dict] = []
        def _practice(phase: str, method_id: str, description: str,
                      evidence: list) -> None:
            practices.append(GoodPractice(
                phase=phase, method_id=method_id, description=description,
                evidence=evidence, reusable=True,
            ).to_dict())
        for audit in diagnosis_audits:
            if audit.score >= 80:
                _practice(
                    "diagnosis", audit.method_id,
                    f"诊断方法 {audit.method_name} 表现优秀 "
                    f"(评分{audit.score:.0f}, 精准度{audit.precision:.0%})",
                    [(f"总发现{audit.total_findings}, 确认{audit.confirmed_count}, "
                      f"抑制{audit.suppressed_count}")],
                )
        if cv_audit.confirmation_accuracy >= 0.8:
            _practice(
                "cv", "xv_core",
                f"交叉验证确认精度优秀 ({cv_audit.confirmation_accuracy:.0%})",
                [f"确认{cv_audit.confirmed}, 抑制{cv_audit.suppressed}"],
            )
        if (treatment_audit.net_improvement > 0
                and not _has_treatment_side_effects(treatment_audit)):
            _practice(
                "treatment", "treatment_engine",
                f"治疗净改善{treatment_audit.net_improvement}且无副作用",
                [f"成功{treatment_audit.succeeded}, 执行{treatment_audit.executed}"],
            )
        return practices
    def _extract_issues(self,
                        diagnosis_audits: list[DiagnosisAuditResult],
                        cv_audit: CrossValidationAuditResult,
                        treatment_audit: TreatmentAuditResult) -> list[dict]:
        issues: list[dict] = []
        issues.extend(_issues_from_diagnosis(diagnosis_audits))
        issues.extend(_issues_from_cv(cv_audit))
        issues.extend(_issues_from_treatment(treatment_audit))
        return issues
    def _generate_enhancements(self,
                                diagnosis_audits: list[DiagnosisAuditResult],
                                cv_audit: CrossValidationAuditResult,
                                treatment_audit: TreatmentAuditResult) -> list[dict]:
        actions: list[dict] = []
        action_counter = 0
        def _next_id() -> str:
            nonlocal action_counter
            action_counter += 1
            return f"ENH-{action_counter:03d}"
        def _add(target_type: str, target_id: str, action_type: str,
                 description: str, priority: str, confidence: float,
                 current_value: str, suggested_value: str,
                 expected_impact: str) -> None:
            actions.append(EnhancementAction(
                action_id=_next_id(),
                target_type=target_type,
                target_id=target_id,
                action_type=action_type,
                description=description,
                priority=priority,
                confidence=confidence,
                current_value=current_value,
                suggested_value=suggested_value,
                expected_impact=expected_impact,
            ).to_dict())
        _enhancements_from_diagnosis(diagnosis_audits, _add)
        _enhancements_from_cv(cv_audit, _add)
        _enhancements_from_treatment(treatment_audit, _add)
        return actions
def _make_issue(*, phase: str, severity: str, method_id: str,
               description: str, impact: str, cause: str, remedy: str,
               evidence: list) -> dict:
    return IssueFound(
        phase=phase, severity=severity, method_id=method_id,
        description=description, impact=impact, root_cause=cause,
        remedy=remedy, evidence=evidence,
    ).to_dict()
def _diagnosis_score_issue(audit: DiagnosisAuditResult) -> dict | None:
    for threshold, severity, wording, impact, remedy in _DIAGNOSIS_ISSUE_TIERS:
        if audit.score < threshold:
            return _make_issue(
                phase="diagnosis", severity=severity,
                method_id=audit.method_id,
                description=(f"诊断方法 {audit.method_name} 评分{wording} "
                             f"({audit.score:.0f})"),
                impact=impact,
                cause=(", ".join(audit.fp_indicators[:3])
                       if audit.fp_indicators else "待进一步分析"),
                remedy=remedy,
                evidence=audit.fp_indicators + audit.miss_indicators,
            )
    return None
def _issues_from_diagnosis(
        diagnosis_audits: list[DiagnosisAuditResult]) -> list[dict]:
    issues: list[dict] = []
    for audit in diagnosis_audits:
        score_issue = _diagnosis_score_issue(audit)
        if score_issue is not None:
            issues.append(score_issue)
        issues.extend(
            _make_issue(
                phase="diagnosis", severity="medium",
                method_id=audit.method_id,
                description=f"{audit.method_id} 存在{fp}",
                impact="浪费交叉验证资源",
                cause="诊断判定标准偏宽",
                remedy="收紧判定阈值",
                evidence=[fp],
            )
            for fp in audit.fp_indicators
            if "高抑制率" in fp
        )
    return issues
def _issues_from_cv(cv_audit: CrossValidationAuditResult) -> list[dict]:
    issues: list[dict] = []
    if cv_audit.contradictions_found > 5:
        issues.append(_make_issue(
            phase="cv", severity="high", method_id="xv_core",
            description=(f"交叉验证存在 {cv_audit.contradictions_found} "
                         "个矛盾决策"),
            impact="影响诊断结果的可信度",
            cause="多源信号冲突时仲裁逻辑不完善",
            remedy="增强矛盾消解逻辑或增加置信度权重校准",
            evidence=[str(e) for e in cv_audit.contradictions_examples[:5]],
        ))
    if cv_audit.confirmation_accuracy < 0.5 and cv_audit.confirmed > 3:
        issues.append(_make_issue(
            phase="cv", severity="critical", method_id="xv_core",
            description=(f"交叉验证确认精度过低 "
                         f"({cv_audit.confirmation_accuracy:.0%})"),
            impact="大量被确认的 finding 实际无法修复",
            cause="确认条件过宽松",
            remedy="提高确认所需的证据数量或置信度阈值",
            evidence=[f"确认{cv_audit.confirmed}个, 修复成功率低"],
        ))
    return issues
def _issues_from_treatment(treatment_audit: TreatmentAuditResult) -> list[dict]:
    issues: list[dict] = []
    if _has_treatment_side_effects(treatment_audit):
        issues.append(_make_issue(
            phase="treatment", severity="high",
            method_id=_TREATMENT_AUDIT_METHOD_ID,
            description=(f"治疗引入了 {treatment_audit.introduced_new_issues} "
                         f"个新问题，并恶化 "
                         f"{treatment_audit.worsened_existing} 个既有问题"),
            impact="越修越坏",
            cause="修复器缺乏副作用检测",
            remedy="增强修复器的安全验证（fix_safety_gate）",
            evidence=[(f"引入新问题{treatment_audit.introduced_new_issues}个, "
                       f"恶化既有问题{treatment_audit.worsened_existing}个")],
        ))
    if treatment_audit.rolled_back > treatment_audit.succeeded:
        issues.append(_make_issue(
            phase="treatment", severity="critical",
            method_id=_TREATMENT_AUDIT_METHOD_ID,
            description=(f"治疗回滚数({treatment_audit.rolled_back})"
                         f"超过成功数({treatment_audit.succeeded})"),
            impact="修复质量极差",
            cause="修复器不可靠或诊断误报率过高",
            remedy="检查修复器实现 + 回溯诊断误报",
            evidence=[(f"回滚{treatment_audit.rolled_back}, "
                       f"成功{treatment_audit.succeeded}")],
        ))
    return issues
def _is_zero_confirmation_miss(indicator: str) -> bool:
    return ("零确认" in indicator
            or ("全部" in indicator and "抑制" in indicator))
def _enh_diag_fp(audit: DiagnosisAuditResult, add) -> None:
    zero_confirmation = any(
        _is_zero_confirmation_miss(miss) for miss in audit.miss_indicators)
    for fp in audit.fp_indicators:
        if "高抑制率" in fp and not zero_confirmation:
            add(
                FIELD_DIAGNOSIS_METHOD, audit.method_id,
                FIELD_THRESHOLD_ADJUST,
                f"{audit.method_id}: 收紧判定阈值以降低误报",
                "P1", 0.7,
                "当前判定标准偏宽",
                "增加前置条件检查，提高判定阈值",
                "预计降低抑制率，提高精准度10-20%",
            )
        if "描述模糊" in fp:
            add(
                FIELD_DIAGNOSIS_METHOD, audit.method_id,
                _DEFAULT_ACTION_TYPE,
                f"{audit.method_id}: 增强finding描述的具体性",
                "P2", 0.6,
                "finding描述包含模糊词汇",
                "替换为具体的代码位置和问题描述",
                "提高交叉验证的匹配效率",
            )
        if "高回滚率" in fp:
            add(
                FIELD_DIAGNOSIS_METHOD, audit.method_id,
                _DEFAULT_ACTION_TYPE,
                f"{audit.method_id}: 修复高回滚率问题，"
                f"可能是诊断产出的路径/行号不准确",
                "P0", 0.8,
                "修复回滚率高",
                "增加路径规范化+行号精确验证",
                "预计降低回滚率至30%以下",
            )
def _enh_diag_miss(audit: DiagnosisAuditResult, add) -> None:
    for miss in audit.miss_indicators:
        if "零发现" in miss:
            add(
                FIELD_DIAGNOSIS_METHOD, audit.method_id,
                "new_check",
                f"{audit.method_id}: 方法产零发现，需检查扫描器是否真正执行",
                "P1", 0.7,
                "零发现",
                "添加空结果校验+扫描范围确认日志",
                "确保扫描器真正覆盖目标代码",
            )
        elif _is_zero_confirmation_miss(miss):
            add(
                FIELD_DIAGNOSIS_METHOD, audit.method_id,
                FIELD_THRESHOLD_ADJUST,
                f"{audit.method_id}: 发现零确认，判定标准可能偏差",
                "P0", 0.85,
                "确认率0%",
                "0.65",
                "置信度乘数x0.65，降低该方法findings的CV通过率",
            )
def _enhancements_from_diagnosis(diagnosis_audits: list[DiagnosisAuditResult],
                                 add) -> None:
    for audit in diagnosis_audits:
        if audit.score < _UNDERPERFORMING_SCORE:
            _enh_diag_fp(audit, add)
    for audit in diagnosis_audits:
        _enh_diag_miss(audit, add)
def _enhancements_from_cv(cv_audit: CrossValidationAuditResult, add) -> None:
    if cv_audit.confirmation_accuracy < 0.6 and cv_audit.confirmed >= 3:
        add(
            "cv_rule", "confirmation_threshold", FIELD_THRESHOLD_ADJUST,
            "提高交叉验证确认阈值，减少低质量确认",
            "P0", 0.85,
            f"当前确认精度: {cv_audit.confirmation_accuracy:.0%}",
            "提高确认所需的最小证据数和置信度",
            "预计提高确认精度20-30%",
        )
    if cv_audit.contradictions_found > 3:
        add(
            "cv_rule", "contradiction_resolution", _DEFAULT_ACTION_TYPE,
            "增强矛盾消解逻辑，处理高置信源被抑制的情况",
            "P1", 0.75,
            "矛盾决策未充分处理",
            "增加置信度权重校准 + 多源一致性检查",
            "预计减少矛盾决策50%以上",
        )
def _enhancements_from_treatment(treatment_audit: TreatmentAuditResult,
                                 add) -> None:
    if _has_treatment_side_effects(treatment_audit):
        add(
            "treatment_process", "fix_safety_gate", _DEFAULT_ACTION_TYPE,
            "增强修复安全验证，检测修复引入的新问题",
            "P0", 0.9,
            "修复器缺乏副作用检测",
            "在fix_safety_boundary中增加修复前后AST对比",
            "消除越修越坏问题",
        )
    _has_treatment_activity = has_treatment_activity(
        treatment_audit.total_items, treatment_audit.executed)
    _pcr = effective_priority_correct_rate(
        treatment_audit.priority_correct_rate)
    if (_has_treatment_activity
            and _priority_was_assessed(
                getattr(treatment_audit, "priority_assessed", None))
            and _pcr < 0.8):
        add(
            "treatment_process", _EXECUTION_ORDER_TARGET_ID,
            _TREATMENT_PROCESS_ACTION_TYPE,
            _EXECUTION_ORDER_DESCRIPTION,
            _EXECUTION_ORDER_PRIORITY, _EXECUTION_ORDER_CONFIDENCE,
            f"优先级正确率: {_pcr:.0%}",
            _EXECUTION_ORDER_REMEDY,
            _EXECUTION_ORDER_IMPACT,
        )
def _compose_summary(scores: RetrospectiveScore,
                     report: RetrospectiveReport) -> str:
    lines = []
    lines.append("## 复盘总结")
    lines.append("")
    lines.append(f"**总分: {scores.overall:.1f}/100**")
    lines.append("")
    dims = [(label, getattr(scores, key))
            for key, label, _weight in RETRO_SCORE_DIMENSIONS]
    for name, val in dims:
        lines.append(f"- {name}: {val:.0%} ({_score_status(val)})")
    lines.append("")
    _summary_block(lines, report.good_practices, "优质操作", tag_key="phase")
    _summary_issues(lines, report)
    _summary_actions(lines, report)
    return "\n".join(lines)
def _score_status(val: float) -> str:
    if val >= 0.8:
        return "优秀"
    if val >= 0.6:
        return "良好"
    if val >= 0.4:
        return "待改进"
    return "严重不足"
_SUMMARY_DETAIL_LIMIT = 5
def _count_field(items: list, key: str, value: str) -> int:
    return sum(1 for item in items
               if isinstance(item, dict) and item.get(key) == value)
def _summary_block(lines: list[str], items: list, title: str, *,
                   tag_key: str, count_lines: tuple[str, ...] = ()) -> None:
    entries = [item for item in items if isinstance(item, dict)]
    if not entries:
        return
    lines.append(f"### {title} ({len(entries)} 项)")
    lines.extend(count_lines)
    lines.extend(
        f"- [{item.get(tag_key, '')}] {item.get('description', '')}"
        for item in entries[:_SUMMARY_DETAIL_LIMIT]
    )
    lines.append("")
def _summary_issues(lines: list[str], report) -> None:
    critical = _count_field(report.issues_found, "severity", "critical")
    high = _count_field(report.issues_found, "severity", "high")
    _summary_block(
        lines, report.issues_found, "发现问题", tag_key="severity",
        count_lines=(f"- P0/critical: {critical} 项, P1/high: {high} 项",))
def _summary_actions(lines: list[str], report) -> None:
    p0 = _count_field(report.enhancement_actions, "priority", "P0")
    p1 = _count_field(report.enhancement_actions, "priority", "P1")
    _summary_block(
        lines, report.enhancement_actions, "增强行动", tag_key="priority",
        count_lines=(f"- P0: {p0} 项, P1: {p1} 项",))
def compose_with_context(skill_dir: str, diagnosis_audits: list,
                          cv_audit, treatment_audit,
                          feedback_history: dict) -> RetrospectiveReport:
    report = RetrospectiveComposer().compose(
        diagnosis_audits, cv_audit, treatment_audit, feedback_history,
        skill_dir=skill_dir)
    try:
        report.rollback_audit = get_rollback_audit(skill_dir)
    except Exception as _rba_e:
        logger.warning("[Retrospective] 回滚审计加载失败: %s", _rba_e)
        report.rollback_audit = {}
    return report
def _stage1_findings(ctx: Any) -> list:
    s1 = dict_or_empty(ctx.stages.get("stage1", {}))
    findings = s1.get("findings")
    if isinstance(findings, list):
        return findings
    raw = s1.get("raw_findings")
    return raw if isinstance(raw, list) else []
def run_stage6d_auto_enhance(ctx: Any, review_result: dict | None,
                             cv_report: dict, *,
                             method_adjustments: dict | None = None,
                             fanout_signal: dict | None = None) -> dict:
    stage_start = time.time()
    logger.info("[Stage6d] auto_enhance 开始: %s", timestamp_human())
    result = {"stage": "auto_enhance", "timestamp": timestamp_ms(),
              "status": "running"}
    _memory_context = getattr(ctx, "memory_context", None)
    enhance_stage6d_memory(ctx.stages, result, _memory_context)
    sync_stage6d_feedback(
        ctx.stages, result, _memory_context,
        dict_or_empty(method_adjustments))
    _stage6d_hallucination(ctx, result)
    _hallucination_blocked = result.get("_hallucination_blocked") is True
    if _hallucination_blocked:
        result["auto_enhancements"] = build_auto_enhancement_report(
            enqueue={"status": "blocked", "enqueued": 0})
    else:
        _stage6d_solidify(ctx, result)
        try:
            result["auto_enhancements"] = require_dict(
                run_stage6d_auto_enhancements(
                    ctx.skill_dir, ctx.stages, review_result, cv_report,
                    fanout_signal=dict_or_empty(fanout_signal)),
                "auto-enhancement 结果")
        except Exception as e:
            logger.warning("[Stage6d] Auto-enhancement failed: %s", e)
            result["auto_enhancements"] = {"error": str(e)[:200], "applied": 0}
    _apply_stage6d_outcome(result, blocked=_hallucination_blocked)
    result["elapsed_s"] = elapsed_seconds(stage_start)
    ctx.stages["stage6d"] = result
    logger.info("[Stage6d] auto_enhance结束: status=%s, auto_enh=%d, "
                 "memory_ops=%d, %.1fs",
                 result["status"],
                 dict_or_empty(result.get("auto_enhancements")).get(
                     "applied", 0),
                 len_safe(result.get("_memory_operations")),
                 result["elapsed_s"])
    return result
def _apply_stage6d_outcome(result: dict, *, blocked: bool) -> None:
    if blocked:
        _hall_err = result.get("_hallucination_error")
        _hall = dict_or_empty(result.get("_hallucination_pipeline", {}))
        result["status"] = "hallucination_blocked"
        _hall_findings = as_count(_hall.get("total_findings"))
        _hall_norms = as_count(_hall.get("total_norm_violations"))
        if _hall_err:
            result["error"] = f"幻觉防控不可用(扫描失败): {_hall_err}"
            result["next_action"] = "fix_hallucination_scan"
        elif _hall_findings <= 0 and _hall_norms <= 0:
            result["error"] = (
                "幻觉防控不可用(扫描未完成): 0 findings, 0 norm violations，"
                f"已扫描 {as_count(_hall.get('files_scanned'))} 个文件")
            result["next_action"] = "fix_hallucination_scan"
        else:
            result["error"] = (
                f"幻觉防控阻断: {_hall_findings} findings, "
                f"{_hall_norms} norm violations（已扫描 "
                f"{as_count(_hall.get('files_scanned'))} 个文件）")
            result["next_action"] = "resolve_hallucination_findings"
        return
    auto_enhancements = dict_or_empty(result.get("auto_enhancements"))
    if auto_enhancements.get("error"):
        result["status"] = "failed"
        result["error"] = str(auto_enhancements["error"])[:500]
        result["next_action"] = "repair_auto_enhancements"
        return
    enqueue = dict_or_empty(
        auto_enhancements.get("ai_review_enqueue"))
    if enqueue.get("status") == "error":
        result["status"] = "failed"
        result["error"] = str(
            enqueue.get("error") or "调整建议入队失败")[:500]
        result["next_action"] = "repair_auto_enhancements"
        return
    sync_errors = result.get("_feedback_sync_errors")
    if isinstance(sync_errors, list) and sync_errors:
        detail = "; ".join(str(error) for error in sync_errors[:3])
        result["status"] = "failed"
        result["error"] = (
            f"反馈双向同步部分失败({len(sync_errors)}项): {detail}")[:500]
        result["next_action"] = "repair_feedback_sync"
        return
    result["status"] = "completed"
def _stage6d_hallucination(ctx: Any, result: dict) -> None:
    try:
        _hall_result = require_dict(
            integrate_with_full_audit(ctx.skill_dir, session_id=ctx.pipeline_id),
            "幻觉防控结果")
        result["_hallucination_pipeline"] = _hall_result
        if _hall_result.get("is_blocked") is True:
            result["_hallucination_blocked"] = True
            logger.warning("[Stage6d] 幻觉防控阻断: %d findings, %d norm violations",
                          _hall_result.get("total_findings", 0),
                          _hall_result.get("total_norm_violations", 0))
        else:
            logger.info("[Stage6d] 幻觉防控完成: %d findings, %d norm violations, %d files",
                       _hall_result.get("total_findings", 0),
                       _hall_result.get("total_norm_violations", 0),
                       _hall_result.get("files_scanned", 0))
    except Exception as _hall_err:
        result["_hallucination_blocked"] = True
        result["_hallucination_error"] = str(_hall_err)[:200]
        logger.warning("[Stage6d] 幻觉防控不可用，按阻断处理(不写SSOT/不入队): %s",
                       _hall_err)
def _stage6d_solidify(ctx: Any, result: dict) -> None:
    try:
        findings = _stage1_findings(ctx)
    except Exception as sf_err:
        logger.warning("[Stage6d] stage1 诊断发现读取失败(按空发现降级): %s", sf_err)
        findings = []
    run_stage6d_solidify(ctx.skill_dir, result, findings)
def extract_stage5_cv_metrics(cv_result: dict) -> tuple[dict, int, int]:
    cv_result = dict_or_empty(cv_result)
    cv_report = dict_or_empty(cv_result.get("report"))
    stage_total = _valid_stage5_cv_metric(cv_result.get("total_findings"))
    if stage_total is None:
        stage_total = cv_report.get(FIELD_TOTAL_INPUT_FINDINGS, 0)
    cv_findings_total = as_count(stage_total)
    stage_rules = _valid_stage5_cv_metric(cv_result.get(FIELD_RULES_TRIGGERED))
    if stage_rules is None:
        stage_rules = cv_report.get("rules_applied_count", 0)
    cv_rules_total = as_count(stage_rules)
    return cv_report, cv_findings_total, cv_rules_total
def _valid_stage5_cv_metric(value) -> int | None:
    count = integral_count(value)
    return count if count is not None and count >= 0 else None
def run_stage5_review_engine(*, skill_dir: str, round_start_ts: str,
                             memory_context: Any, cv_report: dict,
                             cv_result: dict, plan_result: dict,
                             exec_result: dict, result: dict,
                             stage_start: float) -> dict:
    diagnosis_report_path = _existing_report_path(cv_result, "report_path")
    treatment_plan_path = _existing_report_path(plan_result, "plan_path")
    retro_report = _run_retro_engine(
        skill_dir, memory_context, cv_report, exec_result, plan_result,
        diagnosis_report_path, treatment_plan_path)
    retro_dict = _retro_to_dict(retro_report)
    _stage_timestamp = result.get("timestamp")
    result.update(retro_dict)
    result["timestamp"] = (
        _stage_timestamp if _stage_timestamp is not None else timestamp_ms())
    if not result.get("round_start_ts"):
        result["round_start_ts"] = round_start_ts
    if "status" in retro_dict:
        _retro_status = str_or(retro_dict.get("status")).strip()
    else:
        # 缺失状态不是成功证据，空/畸形报告必须停留待重试。
        _retro_status = "failed"
    if _retro_status != "completed":
        return _retro_not_run(result, retro_dict, _retro_status, stage_start)
    overall = _extract_overall_score(retro_dict)
    result["overall_score"] = overall
    result["overall_grade"] = grade_from_score(overall)
    result["engine_used"] = "retrospective_engine"
    result["status"] = "completed"
    result["elapsed_s"] = elapsed_seconds(stage_start)
    if memory_context:
        result = apply_review_memory_enhancements(result, memory_context)
    _ea = retro_dict.get("enhancement_actions")
    _ea_count = len(_ea) if isinstance(_ea, list) else 0
    logger.info("[Stage5] 六环复盘引擎完成: overall_score=%.1f, "
                 "enhancements=%d (耗时 %.1fs)",
                 result.get("overall_score", 0),
                 _ea_count,
                 result["elapsed_s"])
    return result
def _retro_not_run(result: dict, retro_dict: dict, retro_status: str,
                    stage_start: float) -> dict:
    result["status"] = retro_status or "skipped"
    result["reason"] = (str_or(retro_dict.get("summary"))
                        or ("复盘引擎未执行：缺少诊断/CV 报告输入"
                            if result["status"] == "skipped"
                            else f"复盘引擎未完成(status={result['status']})"))
    result["elapsed_s"] = elapsed_seconds(stage_start)
    logger.warning("[Stage5] 复盘引擎未完成(status=%s)，不判定为完成: %s",
                   result["status"], result["reason"])
    return result
_TREATMENT_SETTLED_STATUSES = frozenset({
    "completed", "failed", "error", "no_plan", "skipped", "rolled_back",
})
def _treatment_execution_settled(exec_result: Any) -> bool:
    if not isinstance(exec_result, dict):
        return False
    status = str_or(exec_result.get("status")).strip().lower()
    return status in _TREATMENT_SETTLED_STATUSES
def _run_retro_engine(skill_dir: str, memory_context: Any, cv_report: dict,
                      exec_result: dict, plan_result: dict,
                      diagnosis_report_path: str | None,
                      treatment_plan_path: str | None):
    # 空 dict 会短路 load_stage_data 的磁盘回退（`isinstance(mem, dict)`
    # 直接返回原值），导致「内存无输入但磁盘已有落盘产物」被读成空视图——
    # 复盘报告因此把 75 项治疗方案审计成 0 项、给出「治疗有效性 30%」的
    # 失实结论。这里用 None 表示「本次无内存输入」，由 load_stage_data
    # 按显式路径或最新落盘产物回退。
    # 治疗执行视图保持空 dict：治疗未结算时必须按「无执行证据」入账，
    # 不允许回退到历史执行报告（否则会把旧轮次的执行结果算进本轮复盘）。
    diagnosis_input = cv_report or None
    plan_input = plan_result.get("plan") or None
    execution_input = (
        exec_result if _treatment_execution_settled(exec_result) else {})
    return run_retrospective(
        skill_dir=skill_dir,
        diagnosis_report=diagnosis_input,
        treatment_execution=execution_input,
        treatment_plan=plan_input,
        diagnosis_report_path=diagnosis_report_path,
        treatment_plan_path=treatment_plan_path,
        memory_context=memory_context,
    )
def _retro_to_dict(retro_report) -> dict:
    to_dict = getattr(retro_report, "to_dict", None)
    if callable(to_dict):
        try:
            data = to_dict()
        except Exception as exc:
            logger.warning("[Stage5] 复盘报告 to_dict 失败(%s)，回退属性投影", exc)
        else:
            if isinstance(data, dict):
                return data
            logger.warning("[Stage5] 复盘报告 to_dict 返回非 dict(%s)，回退属性投影",
                           type(data).__name__)
    result = {
        key: getattr(
            retro_report, key,
            default.copy() if isinstance(default, (dict, list)) else default)
        for key, default in _RETRO_FALLBACK_FIELDS.items()
    }
    if hasattr(retro_report, "status"):
        result["status"] = retro_report.status
    return result
_RETRO_FALLBACK_FIELDS: dict[str, Any] = {
    "timestamp": "", "session_id": "", "skill_dir": "",
    "round_start_ts": "", "diagnosis_audit": [], "cv_audit": {},
    "treatment_audit": {}, "scores": {}, "good_practices": [],
    "issues_found": [], "enhancement_actions": [], "summary": "",
    "enhancement_log": [], "code_feedback_result": None,
    "rollback_audit": {}, "memory_operations": [],
    "quality_gate_result": {}, "pdca_tracking": {}, "overall_score": 0,
}
def _extract_overall_score(retro_dict: dict) -> int | float:
    _scores = dict_or_empty(retro_dict.get("scores"))
    _ov = _valid_score_value(_scores.get("overall"))
    if _ov is None:
        _ov = _valid_score_value(retro_dict.get("overall_score"))
    return 0 if _ov is None else _ov
def _valid_score_value(value: Any) -> int | float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, str):
        text = value.strip()
        if not text:
            return None
        try:
            value = float(text)
        except (TypeError, ValueError):
            return None
    elif not isinstance(value, (int, float)):
        return None
    try:
        if not math.isfinite(value) or value < 0 or value > 100:
            return None
    except OverflowError as _e:
        log_swallowed(__name__, _e, context='_valid_score_value:OverflowError')
        return None
    return value
def _existing_report_path(container: dict, key: str) -> str | None:
    raw = container.get(key, "")
    try:
        path = os.fspath(raw)
    except TypeError:
        return None
    if isinstance(path, bytes):
        path = os.fsdecode(path)
    if path and os.path.isfile(path):
        return path
    return None
def load_stage_data(mem: dict | None, path: str | None,
                    pattern: str, temp_dir: str) -> dict | None:
    if isinstance(mem, dict):
        return mem
    loaded = (_load_json_payload(path, log_tag="Retrospective") if path
              else find_latest_report(temp_dir, pattern))
    return loaded if isinstance(loaded, dict) else None
def load_retro_inputs(skill_dir: str, temp_dir: str, *,
                      diagnosis_report: dict | None,
                      diagnosis_report_path: str | None,
                      treatment_execution: dict | None,
                      treatment_execution_path: str | None,
                      treatment_plan: dict | None,
                      treatment_plan_path: str | None) -> tuple:
    diagnosis_report = load_stage_data(
        diagnosis_report, diagnosis_report_path, "report.json", temp_dir)
    treatment_execution = load_stage_data(
        treatment_execution, treatment_execution_path,
        "treatment_execution.json", temp_dir)
    treatment_plan = load_stage_data(
        treatment_plan, treatment_plan_path,
        "treatment_plan_latest.json", temp_dir)
    try:
        feedback_history = as_dict(
            read_evolution_section(skill_dir, "feedback_history"))
    except (OSError, ValueError, TypeError) as exc:
        logger.warning("[Retrospective] 反馈历史 section 读取失败: %s", exc)
        feedback_history = {}
    return diagnosis_report, treatment_execution, treatment_plan, feedback_history
def write_retrospective_json(report_dict: dict, output_dir: str) -> str:
    os.makedirs(output_dir, exist_ok=True)
    report_path = os.path.join(output_dir, "retrospective_report.json")
    write_json_artifact(report_path, report_dict, indent=2)
    return report_path
def run_retrospective(
    skill_dir: str,
    diagnosis_report_path: str | None = None,
    treatment_execution_path: str | None = None,
    treatment_plan_path: str | None = None,
    output_dir: str | None = None,
    memory_context: Any | None = None,
    diagnosis_report: dict | None = None,
    treatment_execution: dict | None = None,
    treatment_plan: dict | None = None,
    run_code_feedback: bool | None = None,
) -> RetrospectiveReport:
    skill_dir, _ = feedback_enhancement_log_context(skill_dir)
    temp_dir = get_temp_base(skill_dir)
    if output_dir is None:
        output_dir = os.path.dirname(evolution_report_path(skill_dir))
    (diagnosis_report, treatment_execution,
     treatment_plan, feedback_history) = load_retro_inputs(
        skill_dir, temp_dir,
        diagnosis_report=diagnosis_report,
        diagnosis_report_path=diagnosis_report_path,
        treatment_execution=treatment_execution,
        treatment_execution_path=treatment_execution_path,
        treatment_plan=treatment_plan,
        treatment_plan_path=treatment_plan_path,
    )
    if not diagnosis_report:
        logger.warning("[Retrospective] 未找到诊断报告，跳过复盘")
        return RetrospectiveReport(
            summary="未找到诊断报告，复盘跳过", skill_dir=skill_dir,
            status="skipped")
    logger.info("[Retrospective] === 复盘反哺开始 ===")
    _diag_summary = as_dict(diagnosis_report.get("summary"))
    _diag_total = _diag_summary.get("total_findings", 0)
    logger.info("[Retrospective] 诊断报告: %s findings", _diag_total)
    tracker_roi_inject(skill_dir, feedback_history,
                        diagnosis_report, treatment_execution)
    inject_session_count(skill_dir, feedback_history)
    diagnosis_audits, cv_audit, treatment_audit = _run_three_audits(
        diagnosis_report, treatment_execution,
        treatment_plan, treatment_plan_path)
    report = compose_with_context(
        skill_dir, diagnosis_audits, cv_audit, treatment_audit, feedback_history)
    normalize_report_containers(report)
    report_path = _finalize_report(
        skill_dir, report, diagnosis_report, treatment_execution,
        memory_context, output_dir, run_code_feedback)
    _log_completion(report, report_path)
    return report
def _log_completion(report: RetrospectiveReport, report_path: str) -> None:
    logger.info("[Retrospective] === 复盘反哺完成 ===")
    logger.info("[Retrospective] 总分: %.1f, 问题: %d, 优质操作: %d, "
                "增强行动: %d, 已应用: %d",
                report.scores.get("overall", 0),
                len(report.issues_found),
                len(report.good_practices),
                len(report.enhancement_actions),
                sum(1 for entry in report.enhancement_log
                    if isinstance(entry, dict) and entry.get("applied")))
    logger.info("[Retrospective] 报告: %s", report_path)
def _run_three_audits(diagnosis_report: dict,
                      treatment_execution: dict | None,
                      treatment_plan: dict | None,
                      treatment_plan_path: str | None) -> tuple:
    diagnosis_report = _materialize_audit_iterators(diagnosis_report)
    treatment_execution = _materialize_audit_iterators(treatment_execution)
    treatment_plan = _materialize_audit_iterators(treatment_plan)
    diagnosis_audits = DiagnosisAudit().audit(
        diagnosis_report, treatment_execution)
    cv_audit = CrossValidationAudit().audit(
        diagnosis_report, treatment_execution)
    treatment_audit = TreatmentAudit().audit(
        treatment_plan, treatment_execution, treatment_plan_path)
    return diagnosis_audits, cv_audit, treatment_audit
def persist_retrospective_report(report: Any, output_dir: str,
                                 skill_dir: str) -> str:
    report_dict = _to_payload(report)
    if not isinstance(report_dict, dict):
        raise TypeError(
            "复盘报告须可投影为非空 dict，"
            f"实际为 {type(report_dict).__name__}")
    if not report_dict:
        raise ValueError("复盘报告为空，拒绝覆盖既有报告")
    report_path = write_retrospective_json(report_dict, output_dir)
    try:
        html_result = generate_html_report(report_dict, skill_dir, "retro")
        html_path = html_report_path(html_result)
        if html_path:
            logger.info("[Retrospective] retro 富报告 HTML 已生成: %s", html_path)
        else:
            reason = (html_result.get("message", "")
                      if isinstance(html_result, dict) else html_result)
            logger.warning("[Retrospective] retro HTML 报告未落盘(不阻断): %s",
                           reason)
    except Exception as _rhe:
        logger.warning("[Retrospective] retro HTML 报告生成失败(不阻断): %s", _rhe)
    return report_path
def run_enhance_channels(skill_dir: str, report: RetrospectiveReport,
                          diagnosis_report: dict | None,
                          treatment_execution: dict | None) -> None:
    report.enhancement_log = run_enhancer_channel(
        "反馈增强",
        lambda: FeedbackEnhancer(skill_dir).enhance(
            report, cv_report=diagnosis_report,
            treatment_outcome=treatment_execution))
    report.enhancement_log.extend(run_enhancer_channel(
        "治疗增强",
        lambda: TreatmentEnhancer(
            skill_dir, enqueue_fn=enqueue_adjustment_proposals).enhance(report)))
def run_code_feedback_channel(skill_dir: str, report: RetrospectiveReport,
                               run_code_feedback: bool | None) -> None:
    if run_code_feedback is None:
        run_code_feedback = (
            os.environ.get("JWSGJ_PIPELINE_MODE", "") != "1")
    if run_code_feedback:
        try:
            report.code_feedback_result = run_code_level_feedback(
                skill_dir, max_items=_CODE_FEEDBACK_MAX_ITEMS,
                min_confidence=_CODE_FEEDBACK_MIN_CONFIDENCE)
            logger.info("[Retrospective] 独立调用模式：代码级反哺已执行")
            return
        except Exception as e:
            logger.warning("[Retrospective] 代码级反哺跳过: %s", e)
    report.code_feedback_result = None
def _finalize_report(skill_dir: str, report: RetrospectiveReport,
                     diagnosis_report: dict,
                     treatment_execution: dict | None,
                     memory_context, output_dir: str,
                     run_code_feedback: bool | None) -> str:
    run_enhance_channels(skill_dir, report,
                          diagnosis_report, treatment_execution)
    run_code_feedback_channel(skill_dir, report, run_code_feedback)
    if memory_context:
        apply_retrospective_memory_bridge(report, memory_context)
    try:
        integrate_fupan_capabilities(report, diagnosis_report,
                                     memory_context=memory_context)
    except Exception as fupan_err:
        logger.warning("[Retrospective] fupan 能力集成跳过: %s", fupan_err)
    return persist_retrospective_report(report, output_dir, skill_dir)
class _BridgeReports(NamedTuple):
    diagnosis: dict[str, Any]
    execution: dict[str, Any]
    plan: dict[str, Any]
    total_findings: int
@contextmanager
def _soft_fail_channel(label: str) -> Iterator[None]:
    try:
        yield
    except ImportError:
        raise
    except Exception as e:
        logger.warning("[RefactorGuard] %s异常: %s", label, e)
def _to_payload(result: Any) -> Any:
    to_dict = getattr(result, "to_dict", None)
    return to_dict() if callable(to_dict) else result
def _run_retrospective_channel(
    skill_dir: str,
    context: dict[str, Any],
    reports: _BridgeReports,
) -> None:
    with _soft_fail_channel("复盘引擎"):
        retro_result = run_retrospective(
            skill_dir=skill_dir,
            diagnosis_report=reports.diagnosis,
            treatment_execution=reports.execution,
            treatment_plan=reports.plan,
            run_code_feedback=False,
        )
        logger.info("[RefactorGuard] 复盘完成（内存输入，报告落 jinhua/ 归口）")
        context["retrospective_result"] = _to_payload(retro_result)
        write_module_run(
            "retrospective_enhancer",
            "run_retrospective_feedback.retrospective",
            findings=reports.total_findings)
def _render_feedback_step_html(skill_dir: str, context: dict[str, Any]) -> None:
    try:
        _fb_raw = context["feedback_result"]
        _fb_payload = (dict(_fb_raw) if isinstance(_fb_raw, dict)
                       else {"summary": str(_fb_raw)[:200]})
        _fb_payload["_step_name"] = "refactor_feedback"
        _fb_html = generate_html_report(_fb_payload, skill_dir, "step")
        _fb_path = html_report_path(_fb_html)
        if _fb_path:
            logger.info("[RefactorGuard] 代码级反哺 HTML 报告已生成: %s",
                        _fb_path)
        else:
            logger.warning("[RefactorGuard] 代码级反哺 HTML 报告未落盘"
                           "(不阻断)，阶段聚合未返回路径")
    except Exception as _fbe:
        logger.warning("[RefactorGuard] 代码级反哺 HTML 报告生成失败(不阻断): %s", _fbe)
def _run_step_code_feedback_channel(skill_dir: str, context: dict[str, Any]) -> None:
    with _soft_fail_channel("代码级反哺"):
        feedback_result = run_code_level_feedback(
            skill_dir=skill_dir, max_items=_CODE_FEEDBACK_MAX_ITEMS,
            min_confidence=_CODE_FEEDBACK_MIN_CONFIDENCE)
        logger.info("[RefactorGuard] 代码级反哺完成")
        context["feedback_result"] = _to_payload(feedback_result)
        write_module_run(
            "retrospective_enhancer",
            "run_retrospective_feedback.code_feedback")
        _render_feedback_step_html(skill_dir, context)
def run_retrospective_feedback(skill_dir: str, context: dict[str, Any]) -> None:
    try:
        diag_report = build_refactor_diagnosis_report(context)
        exec_report = build_refactor_treatment_execution(context)
        plan_report = build_refactor_treatment_plan(context)
        findings_index = (diag_report.get("findings_index")
                          if isinstance(diag_report, dict) else None)
        total_findings = (len(findings_index)
                          if isinstance(findings_index, (list, tuple)) else 0)
        if total_findings == 0:
            logger.info("[RefactorGuard] 重构未发现可复盘的信号，跳过复盘")
            return
        logger.info("[RefactorGuard] 启动复盘: %d 项发现（内存输入，不落盘）",
                  total_findings)
        _run_retrospective_channel(
            skill_dir, context,
            _BridgeReports(diag_report, exec_report, plan_report,
                           total_findings))
        _run_step_code_feedback_channel(skill_dir, context)
    except ImportError:
        logger.info("[RefactorGuard] 复盘/反哺模块未就绪，跳过")
    except Exception as e:
        logger.warning("[RefactorGuard] 复盘反哺异常: %s", e)
REPORT_EXCLUDE_DIRS = frozenset({"mutation", "mutant_batch",
                                  "__pycache__", "reports"})
REPORT_EXCLUDE_FILES = frozenset({"retrospective_report.json",
                                   "_fix_route_report.json",
                                   "leak_report.jsonl"})
def _is_excluded_report_file(filename: str) -> bool:
    normalized = filename.lower()
    return (normalized in REPORT_EXCLUDE_FILES
            or normalized.endswith((".tmp", ".bak"))
            or ".bak." in normalized)
def _report_recency_key(candidate: tuple[float, str]) -> tuple[float, str, str]:
    mtime, path = candidate
    return (mtime, os.path.basename(path), path)
def find_latest_report(temp_dir: str, name_pattern: str) -> dict | None:
    if not isinstance(name_pattern, str) or not name_pattern.strip():
        logger.warning("[Retrospective] 报告名模式为空，拒绝把任意 JSON 当报告")
        return None
    if not os.path.isdir(temp_dir):
        return None
    buckets: dict[str, list[tuple[float, str]]] = {"exact": [], "loose": []}
    for kind, mtime, path in _iter_report_candidates(temp_dir, name_pattern):
        buckets[kind].append((mtime, path))
    for bucket in buckets.values():
        for _mtime, path in sorted(
                bucket, key=_report_recency_key, reverse=True):
            loaded, status, err = read_json_artifact(path)
            if status == "parse_error":
                logger.warning("[Retrospective] JSON 加载失败 %s: %s", path, err)
            if isinstance(loaded, dict) and loaded:
                return loaded
    return None
def _report_file_mtime(file_path: str) -> float | None:
    try:
        return os.path.getmtime(file_path)
    except OSError:
        logger.warning("[Retrospective] 跳过无法读取 mtime 的文件: %s",
                       file_path, exc_info=True)
        return None
def _iter_report_candidates(temp_dir: str, name_pattern: str):
    for root, dirs, files in os.walk(temp_dir):
        dirs[:] = [d for d in dirs
                   if d.lower() not in REPORT_EXCLUDE_DIRS]
        for filename in files:
            if _is_excluded_report_file(filename):
                continue
            kind = _report_match_kind(filename, name_pattern)
            if kind is None:
                continue
            file_path = os.path.join(root, filename)
            mtime = _report_file_mtime(file_path)
            if mtime is None:
                continue
            yield kind, mtime, file_path
def _is_exact_report_name(filename: str, name_pattern: str) -> bool:
    stem = name_pattern.removesuffix(".json")
    return (filename == name_pattern
            or filename.endswith(("_" + name_pattern, "-" + name_pattern))
            or (filename.startswith(stem + "_")
                and filename.endswith(".json")))
def _report_match_kind(filename: str, name_pattern: str) -> str | None:
    if _is_exact_report_name(filename, name_pattern):
        return "exact"
    if name_pattern in filename:
        return "loose"
    return None

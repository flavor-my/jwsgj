from __future__ import annotations

import copy
import datetime
import hashlib
import json
import logging
import math
import os
import re
import time
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from typing import Protocol

from jwsgj.diag_types_normalize import (
    has_finding_entries,
    is_finite_num,
    plan_index,
    strip_cv_target_prefix,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CONCLUSION_V2_MAP,
    DEFAULT_CONFIDENCE_FALLBACK,
    FIELD_EXPECTED_IMPACT,
    FIELD_ROLLBACK_RECOMMENDED,
    FIELD_SUGGESTED_VALUE,
    FMT_DATETIME,
    TX_FAILED_STATUSES,
    TX_FIXED_STATUSES,
    TX_FP_CONFIRMED_STATUSES,
    TX_ROLLED_BACK_STATUSES,
)
from jwsgj.html_render_pipeline import emit_step_trace
from jwsgj.log_config import locked_artifact, log_swallowed, trace_module_run
from jwsgj.runtime_paths import (
    evolution_report_path,
    evolution_state_path,
    read_evolution_section,
    write_evolution_section,
)
from jwsgj.treatment_state import load_treatment_state
from jwsgj.xv_intermediate_store import (
    load_review_result_summary,
    peek_round_start_ts,
)

__all__ = [
    "EnhancementEntryFactory",
    "EnhancementTracker",
    "append_enhancement_entry",
    "append_pending_enhancements",
    "apply_treatment_fix_rate",
    "augment_treatment_context",
    "backfill_enhancement_round_anchor",
    "build_provenance",
    "clean_enhancement_confidence",
    "clean_enhancement_text",
    "dump_json_text",
    "enhancement_dedup_key",
    "enhancement_dict_items",
    "get_pending_enhancements",
    "get_retrospective_history",
    "global_diagnosis_digest",
    "load_enhancement_log",
    "load_retrospective_summary",
    "load_treatment_items_for_evidence",
    "mark_enhancement_applied",
    "method_audit_digest_from_list",
    "normalized_enhancement_entries",
    "persist_review_enhancements",
    "prune_enhancement_data",
    "read_enhancement_log",
    "retro_issues_digest",
    "retro_practices_digest",
    "save_enhancement_log",
    "target_treatment_evidence",
    "treatment_context_digest",
    "write_enhancement_log",
]
logger = logging.getLogger(__name__)
_READ_ERRORS = (OSError, ValueError, RecursionError)
# read_enhancement_log 仅在 IO 故障/内容损坏时返回 None（文件缺失走默认值）；
# 消费方（apply_enhancement_verdict / _link_resolve_entry）以 error 键判定失败并
# 保留待审，error 为空会被归为 already_absent（已消费态），导致批准的增强建议
# 在日志不可读时被静默销项。
_ENH_LOG_UNREADABLE_ERROR = (
    "enhancement_log 不可读（IO 故障或内容损坏），未标记任何条目，保留待审重试")
_JSON_DUMP_SPEC: dict = {"ensure_ascii": False, "indent": 2, "default": str}
@contextmanager
def _required_write_lock(skill_dir: str) -> Iterator[None]:
    if not skill_dir:
        raise OSError("技能根为空，拒绝获取增强台账写锁")
    lock_target = evolution_state_path(skill_dir)
    os.makedirs(os.path.dirname(os.path.abspath(lock_target)), exist_ok=True)
    with locked_artifact(lock_target) as locked:
        if not locked:
            raise OSError(f"增强台账写锁不可用，拒绝无锁写盘: {skill_dir}")
        yield
def dump_json_text(obj) -> str:
    return json.dumps(obj, **_JSON_DUMP_SPEC)
_ACTION_TYPE_RULES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("threshold_adjust", ("threshold", "阈值", "confidence", "置信度")),
    ("fp_suppression", ("fp", "false_positive", "误报", "suppression", "抑制")),
    ("logic_enhance", ("logic", "逻辑", "inject", "注入", "check", "检查")),
)
def _classify_action_type(*texts: str) -> str:
    hay = " ".join(t for t in texts if t).lower()
    for action_type, keywords in _ACTION_TYPE_RULES:
        if any(kw in hay for kw in keywords):
            return action_type
    return "improvement_suggestion"
_METHOD_AUDIT_DIGEST_KEYS: tuple[tuple[str, object], ...] = (
    ("total_findings", 0), ("confirmed_count", 0),
    ("suppressed_count", 0), ("fixed_successfully", 0),
    ("fixed_rolled_back", 0), ("fixed_failed", 0),
    ("precision", 0.0), ("fix_success_rate", 0.0),
    ("rollback_rate", 0.0), ("score", 0.0),
)
def _clip(value, limit: int) -> str:
    return ("" if value is None else str(value))[:limit]
def _numeric_or_zero(value):
    if isinstance(value, bool):
        return 0
    if isinstance(value, str):
        try:
            value = float(value.strip())
        except (TypeError, ValueError, OverflowError):
            return 0
    if not isinstance(value, (int, float)) or value < 0:
        return 0
    if isinstance(value, float):
        if not math.isfinite(value):
            return 0
        if value.is_integer():
            return int(value)
    return value
def _normalize_audits_carrier(audits):
    if isinstance(audits, (list, tuple)):
        return audits
    if isinstance(audits, dict):
        return audits.get("diagnosis_audit")
    return getattr(audits, "diagnosis_audit", None)
def method_audit_digest_from_list(audits, key: str) -> dict:
    if not key:
        return {}
    _audits = _normalize_audits_carrier(audits)
    if not isinstance(_audits, (list, tuple)):
        return {}
    for a in _audits:
        if not isinstance(a, dict):
            continue
        if str(a.get("method_id", "") or "").strip() != str(key).strip():
            continue
        return {k: _numeric_or_zero(a.get(k, d))
                for k, d in _METHOD_AUDIT_DIGEST_KEYS}
    return {}
def global_diagnosis_digest(audits) -> dict:
    audits = _normalize_audits_carrier(audits)
    if not isinstance(audits, (list, tuple)):
        return {}
    methods = 0
    total = 0
    confirmed = 0
    for a in audits:
        if not isinstance(a, dict):
            continue
        methods += 1
        total += _numeric_or_zero(a.get("total_findings", 0))
        confirmed += _numeric_or_zero(a.get("confirmed_count", 0))
    if not methods:
        return {}
    precision = 0.0
    if total:
        precision = (1.0 if confirmed >= total
                     else round(confirmed / total, 4))
    return {
        "method_count": methods,
        "total_findings": total,
        "confirmed_count": confirmed,
        "overall_precision": precision,
    }
_RETRO_ISSUE_DIGEST_MAX = 12
_RETRO_PRACTICE_DIGEST_MAX = 8
_RETRO_TEXT_FIELD_LIMIT = 200
_REVIEW_CONFIDENCE_DEFAULT = 0.7
_PENDING_ENTRY_STATUS = "pending"
def retro_issues_digest(issues) -> list[dict]:
    return _digest_items(issues, _RETRO_ISSUE_DIGEST_MAX, _issue_digest_item)
def retro_practices_digest(practices) -> list[dict]:
    return _digest_items(
        practices, _RETRO_PRACTICE_DIGEST_MAX, _practice_digest_item)
def _digest_items(container, max_items: int, build_item) -> list[dict]:
    if not isinstance(container, (list, tuple)):
        return []
    out: list[dict] = []
    for it in container:
        if not isinstance(it, dict):
            continue
        if len(out) >= max_items:
            break
        out.append(build_item(it))
    return out
def _issue_digest_item(it: dict) -> dict:
    return {
        "phase": _clip(it.get("phase", ""), 60),
        "severity": _clip(it.get("severity", ""), 20),
        "method_id": _clip(it.get("method_id", ""), 60),
        "description": _clip(it.get("description", ""), _RETRO_TEXT_FIELD_LIMIT),
        "root_cause": _clip(it.get("root_cause", ""), _RETRO_TEXT_FIELD_LIMIT),
        "remedy": _clip(it.get("remedy", ""), _RETRO_TEXT_FIELD_LIMIT),
    }
def _practice_digest_item(it: dict) -> dict:
    return {
        "phase": _clip(it.get("phase", ""), 60),
        "method_id": _clip(it.get("method_id", ""), 60),
        "description": _clip(it.get("description", ""), _RETRO_TEXT_FIELD_LIMIT),
    }
def _present_fields(source: dict, keys: tuple[str, ...]) -> dict:
    return {k: source[k] for k in keys if source.get(k) not in (None, "")}
def _overall_score_of(retro: dict):
    scores = retro.get("scores")
    overall = scores.get("overall") if isinstance(scores, dict) else None
    return retro.get("overall_score") if overall is None else overall
def _project_retrospective_report(rp) -> dict:
    if not isinstance(rp, dict):
        return {}
    overall = _overall_score_of(rp)
    summary = _present_fields(rp, ("timestamp", "risk_level"))
    if overall is not None:
        summary["overall_score"] = overall
    return summary
def _load_jinhua_retrospective_summary(skill_dir: str) -> dict:
    try:
        rp_path = evolution_report_path(skill_dir)
        if not os.path.isfile(rp_path):
            return {}
        return _project_retrospective_report(_read_log_file(rp_path))
    except Exception as _e:
        log_swallowed(
            __name__, _e,
            context=f'_load_jinhua_retrospective_summary:{type(_e).__name__}')
        return {}
def load_retrospective_summary(skill_dir: str) -> dict:
    summary = load_review_result_summary(skill_dir)
    if summary:
        return summary
    return _load_jinhua_retrospective_summary(skill_dir)
def _status_keys(statuses) -> frozenset[str]:
    return frozenset(str(s).strip().lower() for s in statuses)
_TX_FIXED_STATUS_KEYS: frozenset[str] = _status_keys(TX_FIXED_STATUSES)
_TX_FAILED_STATUS_KEYS: frozenset[str] = _status_keys(TX_FAILED_STATUSES)
_TX_ROLLED_BACK_KEYS: frozenset[str] = _status_keys(TX_ROLLED_BACK_STATUSES)
_TX_FP_CONFIRMED_KEYS: frozenset[str] = _status_keys(TX_FP_CONFIRMED_STATUSES)
_ATTEMPTED_STATUSES: frozenset[str] = (
    _TX_FIXED_STATUS_KEYS | _TX_FAILED_STATUS_KEYS | _TX_ROLLED_BACK_KEYS)
_TARGET_TX_SUCCEEDED = _TX_FIXED_STATUS_KEYS
_TARGET_TX_FAILURE_STATUSES: frozenset[str] = (
    _TX_FAILED_STATUS_KEYS | _TX_ROLLED_BACK_KEYS)
_TARGET_TX_FAILURE_BUCKET = {
    status: ("rolled_back" if status in _TX_ROLLED_BACK_KEYS else "failed")
    for status in _TARGET_TX_FAILURE_STATUSES
}
def load_treatment_items_for_evidence(skill_dir: str) -> list:
    try:
        state = load_treatment_state(skill_dir)
    except Exception:
        logger.warning("[Enhancer] 治疗状态读取失败，target 治疗实证降级为空",
                       exc_info=True)
        return []
    items = state.get("items") if isinstance(state, dict) else None
    return items if isinstance(items, list) else []
def _failure_reason(res) -> str:
    if not isinstance(res, dict):
        return ""
    reason = res.get("reason")
    if isinstance(reason, str) and reason:
        return reason
    error = res.get("error")
    return error if isinstance(error, str) else ""
def _classify_target_tx_status(out: dict, reasons: list, it: dict) -> None:
    _st = _tx_status_key(it) or "pending"
    if _st in _TARGET_TX_SUCCEEDED:
        out["succeeded"] += 1
        return
    if _st in _TARGET_TX_FAILURE_STATUSES:
        out[_TARGET_TX_FAILURE_BUCKET[_st]] += 1
        _reason = _failure_reason(it.get("result"))
        if _reason.strip():
            reasons.append(_reason[:120])
        return
    if _st in _TX_FP_CONFIRMED_KEYS:
        out["fp_confirmed"] += 1
        return
    if _st == "pending_confirm":
        out["pending_confirm"] += 1
def _aggregate_target_items(items: list, key: str, out: dict,
                            reasons: list) -> bool:
    matched = False
    for it in items:
        if not isinstance(it, dict):
            continue
        _rid = clean_enhancement_text(it.get("rule_id")).strip()
        if _rid != key:
            continue
        matched = True
        out["total"] += 1
        _classify_target_tx_status(out, reasons, it)
    return matched
_TARGET_TREATMENT_TARGET_PREFIXES = ("fp_suppression/",)
def _target_treatment_candidates(target_key) -> list[str]:
    """把审核条目 target 归一为治疗项可匹配的规则身份候选。

    审核条目 target 可能是通道复合键：``fp_suppression/{rule_id}``（误报抑制
    桥接）与 ``CV-CONFIDENCE-{rule_id}``（CV 规则反馈）都会进入审核证据链，
    而治疗项 ``rule_id`` 存放裸规则身份。不归一前缀时
    ``target_treatment_evidence`` 对这两类 target 恒返回空，审核四维中的
    目标级治疗实证静默断链。原样身份优先，命中失败才回退剥离前缀的候选。
    """
    _key = clean_enhancement_text(target_key).strip()
    if not _key:
        return []
    candidates = [_key]
    for _prefix in _TARGET_TREATMENT_TARGET_PREFIXES:
        if not _key.startswith(_prefix):
            continue
        _stripped = _key[len(_prefix):].strip()
        if _stripped and _stripped not in candidates:
            candidates.append(_stripped)
    _cv_stripped = strip_cv_target_prefix(_key).strip()
    if _cv_stripped and _cv_stripped not in candidates:
        candidates.append(_cv_stripped)
    return candidates
def _empty_target_treatment_evidence(key: str) -> dict:
    return {
        "rule_id": key,
        "total": 0,
        "succeeded": 0,
        "failed": 0,
        "rolled_back": 0,
        "fp_confirmed": 0,
        "pending_confirm": 0,
    }
def target_treatment_evidence(skill_dir: str, target_key) -> dict:
    _candidates = _target_treatment_candidates(target_key)
    if not _candidates:
        return {}
    items = load_treatment_items_for_evidence(skill_dir)
    if not items:
        return {}
    for _key in _candidates:
        out = _empty_target_treatment_evidence(_key)
        reasons: list[str] = []
        if not _aggregate_target_items(items, _key, out, reasons):
            continue
        if reasons:
            out["sample_failure_reasons"] = reasons[-2:]
        return out
    return {}
def augment_treatment_context(tctx: dict, skill_dir: str,
                              target_key) -> dict:
    tctx = tctx if isinstance(tctx, dict) else {}
    try:
        _tte = target_treatment_evidence(skill_dir, target_key)
    except Exception:
        logger.warning("[Enhancer] target 治疗实证下钻异常(不阻断): %r",
                       target_key, exc_info=True)
        return tctx
    if _tte:
        tctx["target_treatment_evidence"] = _tte
    return tctx
def treatment_context_digest(ta: dict, with_worsened: bool) -> dict:
    ta = ta if isinstance(ta, dict) else {}
    ctx = {
        "total_items": ta.get("total_items", 0),
        "executed": ta.get("executed", 0),
        "succeeded": ta.get("succeeded", 0),
        "failed": ta.get("failed", 0),
        "rolled_back": ta.get("rolled_back", 0),
        "pending_confirm": ta.get("pending_confirm", 0),
        "skipped": ta.get("skipped", 0),
        "fp_confirmed": ta.get("fp_confirmed", 0),
        "suggestion": ta.get("suggestion", 0),
        "introduced_new_issues": ta.get("introduced_new_issues", 0),
    }
    if with_worsened:
        ctx["worsened_existing"] = ta.get("worsened_existing", 0)
    ctx["net_improvement"] = ta.get("net_improvement", 0)
    ctx["priority_correct_rate"] = ta.get("priority_correct_rate", 0.0)
    ctx["strategy_effectiveness"] = ta.get("strategy_effectiveness", 0.0)
    ctx["score"] = ta.get("score", 0.0)
    return ctx
def _report_field(report, name: str, default):
    if isinstance(report, dict):
        return report.get(name, default)
    return getattr(report, name, default)
def build_provenance(report, phase: str, rule_id: str,
                     diagnosis_context: dict, treatment_context: dict,
                     source: str) -> dict:
    summary = _report_field(report, "summary", "")
    scores = _report_field(report, "scores", {})
    return {
        "phase": phase,
        "rule_id": rule_id,
        "diagnosis_context": diagnosis_context,
        "treatment_context": treatment_context,
        "retrospective_context": {
            "session_id": _report_field(report, "session_id", ""),
            "timestamp": _report_field(report, "timestamp", ""),
            "scores": scores if isinstance(scores, dict) else {},
            "summary": summary[:200] if isinstance(summary, str) else "",
            "issues_found": retro_issues_digest(
                _report_field(report, "issues_found", [])),
            "good_practices": retro_practices_digest(
                _report_field(report, "good_practices", [])),
        },
        "source": source,
    }
def _build_retro_prov(review_result: dict) -> dict:
    _scores = review_result.get("scores") if isinstance(review_result.get("scores"), dict) else {}
    _tsum = (review_result.get("treatment_summary")
             if isinstance(review_result.get("treatment_summary"), dict) else {})
    _summary_raw = review_result.get("summary", "")
    return {
        "phase": "review",
        "source": "review_enhancements",
        "treatment_context": {
            "total_items": _tsum.get("total_items", 0),
            "executed": _tsum.get("executed", 0),
            "succeeded": _tsum.get("succeeded", 0),
            "ai_fixed": _tsum.get("ai_fixed", 0),
            "failed": _tsum.get("failed", 0),
            "rolled_back": _tsum.get("rolled_back", 0),
            "fp_confirmed": _tsum.get("fp_confirmed", 0),
        },
        "retrospective_context": {
            "overall_score": _overall_score_of(review_result),
            "overall_grade": review_result.get("overall_grade"),
            "risk_level": review_result.get("risk_level"),
            "quality_level": review_result.get("quality_level"),
            "timestamp": review_result.get("timestamp", ""),
            "scores": _scores,
            "summary": (_summary_raw[:200]
                        if isinstance(_summary_raw, str) else ""),
            "issues_found": retro_issues_digest(
                review_result.get("issues_found")),
            "good_practices": retro_practices_digest(
                review_result.get("good_practices")),
        },
    }
def _diagnosis_context(diag_audits, target: str,
                       description: str) -> dict:
    ctx = method_audit_digest_from_list(diag_audits, target)
    if ctx:
        ctx["diagnosis_scope"] = "method"
    else:
        ctx = global_diagnosis_digest(diag_audits)
        ctx["diagnosis_scope"] = "global"
    ctx["target"] = target
    ctx["description"] = description
    return ctx
def _review_field_value(enh: dict, primary: str, legacy: str):
    value = enh.get(primary)
    return enh.get(legacy) if value is None or value == "" else value
def _review_entry_dict(enh: dict, retro_prov: dict, diag_audits,
                       skill_dir: str) -> dict:
    _retro_target = clean_enhancement_text(
        _review_field_value(enh, "target", "area"))
    _retro_desc = clean_enhancement_text(
        _review_field_value(enh, "description", "action"))
    _raw_action_type = enh.get("action_type")
    _retro_action = (_raw_action_type.strip()
                     if isinstance(_raw_action_type, str) else "")
    if not _retro_action:
        _retro_action = _classify_action_type(_retro_target, _retro_desc)
    _retro_suggested = enh.get(FIELD_SUGGESTED_VALUE)
    if _retro_suggested is None or _retro_suggested == "":
        _retro_suggested = _review_field_value(enh, "remedy", "suggestion")
    _dc = _diagnosis_context(diag_audits, _retro_target, _retro_desc)
    _tc = augment_treatment_context(
        dict(retro_prov["treatment_context"]), skill_dir, _retro_target)
    return {
        **_base_enhancement_entry(
            timestamp=timestamp_ms(), target=_retro_target,
            description=_retro_desc,
            suggested_value=_retro_suggested,
            expected_impact=enh.get(FIELD_EXPECTED_IMPACT),
            confidence=enh.get("confidence"),
            confidence_default=_REVIEW_CONFIDENCE_DEFAULT,
            action_type=_retro_action),
        "diagnosis_context": _dc,
        "phase": retro_prov["phase"],
        "source": retro_prov["source"],
        "treatment_context": _tc,
        "retrospective_context": retro_prov["retrospective_context"],
    }
def read_enhancement_log(skill_dir: str, *,
                          label: str = "Stage6") -> tuple[dict | None, bool]:
    try:
        return _coerce_enhancement_history(
            read_evolution_section(skill_dir, "enhancement_log",
                                   _empty_enhancement_history())), True
    except OSError as log_err:
        logger.warning("[%s] 增强日志读取IO故障，保留原状态并跳过本轮操作: %s (%s)",
                       label, skill_dir, log_err, exc_info=True)
        return None, False
    except (ValueError, RecursionError) as log_err:
        logger.warning("[%s] 增强日志内容损坏，保留原状态并跳过本轮操作: %s (%s)",
                       label, skill_dir, log_err, exc_info=True)
        return None, False
def _review_enhancement_entries(review_result, skill_dir: str) -> list:
    if not isinstance(review_result, dict):
        return []
    retro_enhancements = enhancement_dict_items(
        review_result.get("enhancement_actions"))
    if not retro_enhancements:
        return []
    _diag_audits = review_result.get("diagnosis_audit")
    _retro_prov = _build_retro_prov(review_result)
    return [
        _review_entry_dict(enh, _retro_prov, _diag_audits, skill_dir)
        for enh in retro_enhancements
    ]
class _PipelineContextLike(Protocol):
    skill_dir: str
def persist_review_enhancements(ctx: _PipelineContextLike, review_result):
    enhancements = _review_enhancement_entries(review_result, ctx.skill_dir)
    if not enhancements:
        return
    try:
        with _required_write_lock(ctx.skill_dir):
            existing_data, _readable = read_enhancement_log(ctx.skill_dir)
            if not _readable or existing_data is None:
                return
            entries_list = normalized_enhancement_entries(existing_data)
            _round_ts = peek_round_start_ts(ctx.skill_dir)
            _appended = _append_entries_with_dedup(
                entries_list, enhancements,
                _pending_dedup_keys(entries_list), _round_ts)
            _flush_enh_log(existing_data, ctx.skill_dir, _appended)
    except _READ_ERRORS as exc:
        logger.warning("[Stage6] 增强建议持久化失败: %s", exc)
def _is_pending_entry(entry) -> bool:
    if not isinstance(entry, dict):
        return False
    status = entry.get("status")
    return (isinstance(status, str)
            and status.strip().lower() == _PENDING_ENTRY_STATUS)
def _pending_dedup_keys(entries: list) -> set:
    return {
        enhancement_dedup_key(e)
        for e in entries
        if _is_pending_entry(e)
    }
def _append_entries_with_dedup(entries_list: list, enhancements,
                               existing_keys: set, round_ts: str) -> int:
    appended = 0
    for entry in enhancements:
        prepared = _prepare_new_entry(entry, existing_keys, round_ts)
        if prepared is None:
            continue
        entries_list.append(prepared)
        appended += 1
        if _is_pending_entry(prepared):
            existing_keys.add(enhancement_dedup_key(prepared))
    return appended
def _flush_enh_log(existing_data, skill_dir: str, appended: int) -> None:
    try:
        save_enhancement_log(skill_dir, existing_data)
    except (OSError, ValueError, RecursionError) as e:
        logger.warning("[Stage6] 增强建议持久化失败: %s", e)
        return
    if appended:
        logger.info("[Stage6] 复盘增强建议持久化: %d 条写入 evolution_state.json"
                    "(enhancement_log)", appended)
_MAX_ENHANCEMENT_ENTRIES = 200
_MAX_ENHANCEMENT_SESSIONS = 50
_MAX_ENHANCEMENT_PENDING_ENTRIES = 300
def _prune_entries(data: dict) -> list:
    entries = data.get("entries", [])
    if isinstance(entries, tuple):
        entries = list(entries)
    elif not isinstance(entries, list):
        logger.warning("[EnhLog] entries 非法类型(%s)，重置为空", type(entries).__name__)
        entries = []
    normalized = [entry for entry in entries if isinstance(entry, dict)]
    pending_idx = [
        index for index, entry in enumerate(normalized)
        if _is_pending_entry(entry)
    ]
    consumed_idx = [
        index for index, entry in enumerate(normalized)
        if not _is_pending_entry(entry)
    ]
    dropped: set[int] = set()
    if len(consumed_idx) > _MAX_ENHANCEMENT_ENTRIES:
        dropped.update(
            consumed_idx[:len(consumed_idx) - _MAX_ENHANCEMENT_ENTRIES])
    if len(pending_idx) > _MAX_ENHANCEMENT_PENDING_ENTRIES:
        _overflow = len(pending_idx) - _MAX_ENHANCEMENT_PENDING_ENTRIES
        logger.warning(
            "[EnhLog] pending 超限（AI 审核通道停滞），裁剪最旧 %d 条: "
            "保留最近 %d 条",
            _overflow,
            _MAX_ENHANCEMENT_PENDING_ENTRIES)
        dropped.update(pending_idx[:_overflow])
    return [entry for index, entry in enumerate(normalized)
            if index not in dropped]
def _prune_sessions(data: dict) -> None:
    sessions = data.get("sessions")
    if isinstance(sessions, tuple):
        sessions = list(sessions)
        data["sessions"] = sessions
    elif not isinstance(sessions, list):
        data["sessions"] = []
        return
    if len(sessions) > _MAX_ENHANCEMENT_SESSIONS:
        data["sessions"] = sessions[-_MAX_ENHANCEMENT_SESSIONS:]
def prune_enhancement_data(data: dict) -> dict:
    data["entries"] = _prune_entries(data)
    _prune_sessions(data)
    return data
def normalized_enhancement_entries(history: dict) -> list:
    if not isinstance(history, dict):
        logger.warning(
            "[EnhLog] 增强历史容器非 dict 形状,按空条目集处理: %s",
            type(history).__name__)
        return []
    raw = history.setdefault("entries", [])
    entries = raw if isinstance(raw, list) else (
        list(raw) if isinstance(raw, tuple) else [])
    entries = [entry for entry in entries if isinstance(entry, dict)]
    history["entries"] = entries
    return entries
def enhancement_dict_items(value) -> list[dict]:
    if isinstance(value, dict):
        value = value.get("entries")
    if value is None or isinstance(value, (str, bytes, bytearray)):
        return []
    try:
        items = list(value)
    except TypeError:
        return []
    return [e for e in items if isinstance(e, dict)]
def enhancement_dedup_key(entry: dict) -> tuple[str, str]:
    return (clean_enhancement_text(entry.get("target")).strip(),
            clean_enhancement_text(entry.get("description")).strip())
def clean_enhancement_text(value) -> str:
    if isinstance(value, str):
        return value
    return "" if value is None else str(value)
def clean_enhancement_confidence(
        value, default: float | None = None) -> float:
    fallback = default
    if (not isinstance(fallback, (int, float))
            or isinstance(fallback, bool)
            or (isinstance(fallback, float) and not math.isfinite(fallback))):
        fallback = DEFAULT_CONFIDENCE_FALLBACK
    fallback = float(min(1.0, max(0.0, fallback)))
    if (not isinstance(value, (int, float)) or isinstance(value, bool)
            or (isinstance(value, float) and not math.isfinite(value))):
        return fallback
    return float(min(1.0, max(0.0, value)))
def _base_enhancement_entry(*, timestamp: str, target: str,
                            description: str, suggested_value: str,
                            expected_impact: str, confidence,
                            action_type: str,
                            confidence_default: float | None = None) -> dict:
    return {
        "timestamp": timestamp,
        "target": clean_enhancement_text(target),
        "action_type": clean_enhancement_text(action_type),
        "description": clean_enhancement_text(description),
        FIELD_SUGGESTED_VALUE: clean_enhancement_text(suggested_value),
        FIELD_EXPECTED_IMPACT: clean_enhancement_text(expected_impact),
        "confidence": clean_enhancement_confidence(
            confidence, default=confidence_default),
        "status": _PENDING_ENTRY_STATUS,
    }
class EnhancementEntryFactory:
    def __init__(self, skill_dir: str, *,
                 round_start_ts: str | None = None) -> None:
        self.round_start_ts = (
            peek_round_start_ts(skill_dir) if round_start_ts is None
            else round_start_ts)
    def build(self, *, timestamp: str, target: str, description: str,
              suggested_value: str, expected_impact: str,
              confidence, action_type: str,
              provenance: dict | None) -> dict:
        return {
            **_base_enhancement_entry(
                timestamp=timestamp, target=target,
                description=description, suggested_value=suggested_value,
                expected_impact=expected_impact, confidence=confidence,
                action_type=action_type),
            **(provenance or {}),
            "round_start_ts": self.round_start_ts,
        }
def backfill_enhancement_round_anchor(entry: dict, round_ts: str) -> dict:
    if "round_start_ts" in entry:
        return entry
    return {**entry, "round_start_ts": round_ts}
def append_enhancement_entry(entries: list, entry: dict) -> None:
    if not isinstance(entries, list) or not isinstance(entry, dict):
        logger.warning(
            "[EnhLog] 追加增强条目形状非法(entries=%s, entry=%s),已跳过",
            type(entries).__name__, type(entry).__name__)
        return
    key = enhancement_dedup_key(entry)
    dup = (_is_pending_entry(entry)
           and any(_is_pending_entry(e)
                   and enhancement_dedup_key(e) == key
                   for e in entries if isinstance(e, dict)))
    if not dup:
        entries.append({**entry, "target": key[0], "description": key[1]})
def append_pending_enhancements(skill_dir: str, entries: list[dict]) -> int:
    _t0 = time.monotonic()
    if isinstance(entries, (set, frozenset)):
        entries = sorted(entries, key=lambda e: (
            enhancement_dedup_key(e) if isinstance(e, dict) else ("", "")))
    elif not isinstance(entries, (list, tuple)):
        if entries is None or isinstance(entries, (str, bytes, bytearray)):
            entries = ()
        else:
            try:
                entries = list(entries)
            except TypeError:
                logger.warning(
                    "[Retrospective] entries 非法容器(%s)，按空条目集处理",
                    type(entries).__name__)
                entries = ()
    try:
        with _required_write_lock(skill_dir):
            data = load_enhancement_log(skill_dir)
            existing = normalized_enhancement_entries(data)
            previous_count = len(existing)
            appended = _append_entries_with_dedup(
                existing, entries, _pending_dedup_keys(existing),
                peek_round_start_ts(skill_dir))
            appended_entry_ids = {id(entry) for entry in existing[previous_count:]}
            save_enhancement_log(skill_dir, data)
            appended = sum(
                1 for entry in normalized_enhancement_entries(data)
                if id(entry) in appended_entry_ids)
        trace_module_run("retrospective_ledger", "append_pending_enhancements", _t0,
                          appended=appended, entries=len(data.get("entries") or []))
        return appended
    except _READ_ERRORS as e:
        logger.warning("[Retrospective] 追加增强条目失败: %s", e)
        trace_module_run("retrospective_ledger", "append_pending_enhancements", _t0, "failed", appended=0)
        return 0
def _read_log_file(log_path: str) -> object:
    with open(log_path, encoding="utf-8-sig") as f:
        return json.load(f)
def _empty_enhancement_history() -> dict:
    return {"entries": [], "sessions": []}
def _coerce_enhancement_history(data) -> dict:
    if isinstance(data, dict):
        return data
    if isinstance(data, list):
        return {"entries": data, "sessions": []}
    raise ValueError(
        f"增强日志顶层必须是对象或数组，收到 {type(data).__name__}")
def load_enhancement_log(skill_dir: str) -> dict:
    return _coerce_enhancement_history(
        read_evolution_section(skill_dir, "enhancement_log",
                               _empty_enhancement_history()))
def _prepare_new_entry(entry, existing_keys: set,
                       round_ts: str) -> dict | None:
    if not isinstance(entry, dict):
        logger.warning("[Retrospective] 跳过非法增强条目(%s)",
                       type(entry).__name__)
        return None
    entry = dict(entry)
    status = entry.get("status")
    if status is None or (isinstance(status, str) and not status.strip()):
        entry["status"] = _PENDING_ENTRY_STATUS
    key = enhancement_dedup_key(entry)
    if _is_pending_entry(entry) and key in existing_keys:
        return None
    entry = backfill_enhancement_round_anchor(entry, round_ts)
    return {**entry, "target": key[0], "description": key[1]}
def write_enhancement_log(skill_dir: str, data: dict) -> None:
    if not write_evolution_section(skill_dir, "enhancement_log", data):
        raise OSError(
            f"增强日志 section 落盘失败（evolution_state.json）: {skill_dir}")
def save_enhancement_log(skill_dir: str, data: dict) -> None:
    staged = prune_enhancement_data(dict(data))
    write_enhancement_log(skill_dir, staged)
    data.clear()
    data.update(staged)
def get_retrospective_history(skill_dir: str) -> dict:
    data, _readable = read_enhancement_log(
        skill_dir, label="Retrospective")
    return data if data is not None else _empty_enhancement_history()
def get_pending_enhancements(skill_dir: str) -> list[dict]:
    history = get_retrospective_history(skill_dir)
    return [e for e in enhancement_dict_items(history)
            if _is_pending_entry(e)]
def _mark_pending_entry(
        log, target: str, description: str, status: str,
        review_info: dict | None,
        entry_filter: Callable[[dict], bool] | None = None) -> dict | None:
    marked_entry: dict | None = None
    identity = (target, description)
    for entry in enhancement_dict_items(log):
        if not _is_pending_entry(entry):
            continue
        if enhancement_dedup_key(entry) != identity:
            continue
        if entry_filter is not None and not entry_filter(entry):
            continue
        entry["target"], entry["description"] = identity
        entry["status"] = status
        entry[f"{status}_at"] = time.strftime(FMT_DATETIME)
        _apply_review_info(entry, review_info)
        marked_entry = entry
    return marked_entry
def _apply_review_info(entry: dict, review_info: dict | None) -> None:
    if not isinstance(review_info, dict):
        return
    specs = (
        ("ai_review_verdict", str, 0),
        ("ai_review_rationale", str, 800),
        ("ai_review_assessment", dict, 0),
    )
    for key, expected_type, limit in specs:
        value = review_info.get(key)
        if not isinstance(value, expected_type) or not value:
            continue
        entry[key] = value[:limit] if limit else value
_MEMORY_PROJECT_SEGMENT_UNSAFE_RE = re.compile(r'[\\/:*?"<>|\r\n\t]+')
def _memory_project_segment(skill_dir: str) -> str:
    try:
        normalized = os.path.normpath(os.fsdecode(os.fspath(skill_dir)))
        raw_name = os.path.basename(normalized)
        identity = os.path.normcase(
            os.path.realpath(os.path.abspath(normalized)))
    except (TypeError, ValueError, OSError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_memory_project_segment:{type(_swallowed_exc).__name__}')
        raw_name = ""
        identity = str(skill_dir)
    cleaned = (_MEMORY_PROJECT_SEGMENT_UNSAFE_RE.sub("_", raw_name).strip(" .")
               or "project")
    digest = hashlib.sha256(
        identity.encode("utf-8", "replace")).hexdigest()[:8]
    return f"{cleaned}-{digest}"
def _applied_memory_op_with_provenance(marked_entry: dict, target: str,
                                       description: str,
                                       skill_dir: str) -> dict:
    project = _memory_project_segment(skill_dir)
    memory_op = {
        "action": "patch",
        "path": f"wiki/projects/{project}-enhancements",
        "content": (f"## 增强已应用\n- target: {target}\n"
                    f"- description: {description}\n"
                    f"- applied_at: {time.strftime(FMT_DATETIME)}\n"
                    f"- source: enhancement_log"),
    }
    mem_prov = {k: marked_entry[k] for k in (
        "phase", "source", "rule_id", "diagnosis_context",
        "treatment_context", "retrospective_context")
        if marked_entry.get(k) not in (None, "", [], {})}
    if mem_prov:
        memory_op["provenance"] = mem_prov
        mc = memory_op["content"]
        rid = str(marked_entry.get("rule_id", "") or "")
        ph = str(marked_entry.get("phase", "") or "")
        if rid:
            mc += f"\n- rule_id: {rid}"
        if ph:
            mc += f"\n- phase: {ph}"
        memory_op["content"] = mc
    return memory_op
def _emit_mark_trace(skill_dir: str, target: str, description: str,
                     status: str, result: dict) -> dict:
    emit_step_trace("enhancement_apply", skill_dir, result,
                    extra={"target": target, "description": description,
                           "mark_status": status},
                    context="enhancement 销项 HTML 留痕失败")
    return result
def mark_enhancement_applied(
        skill_dir: str, target: str, description: str,
        status: str = "applied", review_info: dict | None = None, *,
        entry_filter: Callable[[dict], bool] | None = None) -> dict:
    _t0 = time.monotonic()
    status = (status.strip().lower() if isinstance(status, str) else "")
    status = status or "applied"
    target = clean_enhancement_text(target).strip()
    description = clean_enhancement_text(description).strip()
    log, _readable = read_enhancement_log(skill_dir, label="Retrospective")
    if log is None:
        trace_module_run(
            "retrospective_ledger", "mark_enhancement_applied", _t0,
            "log_unreadable", file_marked=False, status=status)
        return _emit_mark_trace(
            skill_dir, target, description, status,
            {"file_marked": False, "memory_operation": None,
             "error": _ENH_LOG_UNREADABLE_ERROR})
    try:
        with _required_write_lock(skill_dir):
            log, _readable = read_enhancement_log(
                skill_dir, label="Retrospective")
            if log is None:
                trace_module_run(
                    "retrospective_ledger", "mark_enhancement_applied", _t0,
                    "log_unreadable", file_marked=False, status=status)
                result = {
                    "file_marked": False, "memory_operation": None,
                    "error": _ENH_LOG_UNREADABLE_ERROR,
                }
            else:
                marked_entry = _mark_pending_entry(
                    log, target, description, status, review_info,
                    entry_filter=entry_filter)
                marked = marked_entry is not None
                if marked:
                    entries = log.get("entries")
                    if isinstance(entries, list):
                        marked_index = next(
                            (index for index, entry in enumerate(entries)
                             if entry is marked_entry), None)
                        if marked_index is not None:
                            entries.append(entries.pop(marked_index))
                    prune_enhancement_data(log)
                    write_enhancement_log(skill_dir, log)
                memory_op = None
                if marked and status == "applied":
                    memory_op = _applied_memory_op_with_provenance(
                        marked_entry, target, description, skill_dir)
                trace_module_run(
                    "retrospective_ledger", "mark_enhancement_applied", _t0,
                    file_marked=marked, status=status)
                result = {
                    "file_marked": marked, "memory_operation": memory_op,
                    "error": "",
                }
    except _READ_ERRORS as e:
        logger.warning("[Retrospective] 标记增强失败: %s", e)
        trace_module_run("retrospective_ledger", "mark_enhancement_applied", _t0, "failed",
                          file_marked=False, status=status)
        result = {
            "file_marked": False, "memory_operation": None, "error": str(e),
        }
    return _emit_mark_trace(skill_dir, target, description, status, result)
def _tx_status_key(item: dict) -> str:
    status = item.get("status")
    return status.strip().lower() if isinstance(status, str) else ""
def _treatment_counts(details: list) -> tuple:
    fixed = 0
    total_attempted = 0
    latest_by_index: dict[int, dict] = {}
    records: list[dict] = []
    for item in details:
        if not isinstance(item, dict):
            continue
        idx = plan_index(item.get("index"))
        if idx is None or idx < 0:
            records.append(item)
        else:
            latest_by_index[idx] = item
    records.extend(latest_by_index.values())
    for item in records:
        status = _tx_status_key(item)
        if status in _TX_FIXED_STATUS_KEYS:
            fixed += 1
        if status in _ATTEMPTED_STATUSES:
            total_attempted += 1
    return fixed, total_attempted
_TREATMENT_RECORD_CARRIERS = (
    "items", "treatment_items", "details", "fix_details",
)
def _treatment_outcome_records(treatment_outcome: dict) -> list:
    fallback = None
    for key in _TREATMENT_RECORD_CARRIERS:
        records = treatment_outcome.get(key)
        if not isinstance(records, list):
            continue
        if not any(isinstance(record, dict)
                   and isinstance(record.get("status"), str)
                   and record["status"].strip() for record in records):
            continue
        if fallback is None:
            fallback = records
        if any(isinstance(record, dict)
               and _tx_status_key(record) in _ATTEMPTED_STATUSES
               for record in records):
            return records
    return fallback if fallback is not None else []
def apply_treatment_fix_rate(metrics: dict,
                              treatment_outcome: dict | None) -> None:
    if not (isinstance(treatment_outcome, dict) and treatment_outcome):
        return
    records = _treatment_outcome_records(treatment_outcome)
    if not records:
        return
    fixed, total_attempted = _treatment_counts(records)
    if total_attempted > 0:
        metrics["fix_rate"] = round(fixed / total_attempted, 4)
_MAX_COMPLETED_SNAPSHOTS = 50
_ROI_EVALUATED_VERDICTS = ("improved", "degraded", "neutral")
_BASELINE_MEASURED_DEFAULT = True
_BASELINE_MEASURED_TRUE_TEXT = frozenset({
    "1", "true", "yes", "measured", "pass", "passed", "completed"})
_DELTA_PRECISION_EPS = 0.01
_DELTA_RECALL_EPS = 0.05
_DELTA_FN_EPS = 2
_IMPROVE_RECALL_TOLERANCE = -0.02
_IMPROVE_PRECISION_TOLERANCE = -0.01
_LARGE_DEGRADATION_DELTA_PRECISION = -0.05
_SNAPSHOT_METRIC_DELTAS = (
    ("precision", "before_precision", "delta_precision", 0.0, 4, 1),
    ("recall", "before_recall", "delta_recall", 0.0, 4, 1),
    ("fp_count", "before_fp_count", "delta_fp", 0, None, -1),
    ("fn_count", "before_fn_count", "delta_fn", 0, None, -1),
    ("fix_rate", "before_fix_rate", "delta_fix_rate", 0.0, 4, 1),
)
def _normalize_adjustment_id(adjustment_id) -> str:
    return adjustment_id if isinstance(adjustment_id, str) else str(adjustment_id)
def _finite_baseline(snap: dict, key: str, default):
    v = snap.get(key, default)
    if isinstance(v, bool) or not isinstance(v, (int, float)):
        return default
    try:
        num = float(v)
    except (OverflowError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_finite_baseline:{type(_e).__name__}')
        return default
    if not math.isfinite(num) or num < 0:
        return default
    return num
def _evaluate_delta_verdict(delta_precision: float, delta_recall: float,
                            delta_fn) -> str:
    degraded = any((
        delta_precision < -_DELTA_PRECISION_EPS,
        delta_fn < -_DELTA_FN_EPS,
        delta_recall < -_DELTA_RECALL_EPS,
    ))
    if degraded:
        return "degraded"
    precision_improved = (
        delta_precision > _DELTA_PRECISION_EPS
        and delta_recall >= _IMPROVE_RECALL_TOLERANCE)
    recall_improved = (
        delta_recall > _DELTA_RECALL_EPS
        and delta_precision >= _IMPROVE_PRECISION_TOLERANCE)
    if precision_improved or recall_improved:
        return "improved"
    return "neutral"
def _consecutive_degraded(completed: list, snapshot: dict,
                          verdict: str) -> int:
    consecutive = 0
    for prev in reversed(completed):
        if not isinstance(prev, dict):
            continue
        if prev.get("target") != snapshot.get("target"):
            continue
        _prev_verdict = prev.get("verdict")
        if _prev_verdict not in _ROI_EVALUATED_VERDICTS:
            continue
        if _prev_verdict == "degraded":
            consecutive = max(1, int(_finite_baseline(
                prev, "consecutive_degraded", 1)))
        break
    return consecutive + 1 if verdict == "degraded" else 0
def _baseline_measurement_flag(snapshot: dict) -> bool:
    raw = snapshot.get("baseline_measured", _BASELINE_MEASURED_DEFAULT)
    if isinstance(raw, bool):
        return raw
    if isinstance(raw, str):
        return raw.strip().lower() in _BASELINE_MEASURED_TRUE_TEXT
    if is_finite_num(raw):
        return bool(raw)
    return False
def _score_snapshot(snapshot: dict, metrics: dict, *,
                    baseline_measured: bool = _BASELINE_MEASURED_DEFAULT) -> tuple:
    for (metrics_key, before_key, delta_key, default,
         ndigits, direction) in _SNAPSHOT_METRIC_DELTAS:
        after = metrics[metrics_key]
        snapshot[f"after_{metrics_key}"] = after
        delta = direction * (after - _finite_baseline(snapshot, before_key, default))
        snapshot[delta_key] = round(delta, ndigits)
    if baseline_measured:
        snapshot["verdict"] = _evaluate_delta_verdict(
            snapshot["delta_precision"], snapshot["delta_recall"],
            snapshot["delta_fn"])
    else:
        snapshot["verdict"] = "unevaluated"
        snapshot["unevaluated_reason"] = "baseline_unmeasured"
    return snapshot["delta_precision"], snapshot["delta_fn"]
def _snapshot_id_matches(stored, adjustment_id: str) -> bool:
    if stored == adjustment_id:
        return True
    return (isinstance(stored, (int, float)) and not isinstance(stored, bool)
            and str(stored) == adjustment_id)
def _pending_snapshot_stale(snapshot: dict, now: datetime.datetime,
                            max_age_days: int) -> bool:
    ts_str = snapshot.get("timestamp", "")
    if not isinstance(ts_str, str) or not ts_str:
        return True
    try:
        ts = datetime.datetime.strptime(ts_str, FMT_DATETIME)
    except ValueError as e:
        logger.warning("[EnhancementTracker] 快照时间戳格式异常，按过期清理: %s", e)
        return True
    age = now - ts
    return age < datetime.timedelta(0) or age > datetime.timedelta(days=max_age_days)
def _normalize_snapshot_frame(data: dict) -> dict:
    pending = data.get("pending", {})
    completed = data.get("completed", [])
    if not isinstance(pending, dict):
        raise TypeError(
            f"快照 pending 容器必须为空缺或对象，收到 {type(pending).__name__}")
    if not isinstance(completed, list):
        raise TypeError(
            f"快照 completed 容器必须为空缺或数组，收到 {type(completed).__name__}")
    invalid_pending = sum(
        not isinstance(value, dict) for value in pending.values())
    invalid_completed = sum(
        not isinstance(entry, dict) for entry in completed)
    if invalid_pending or invalid_completed:
        raise TypeError(
            "快照含非对象条目，保留原始证据并暂停写入: "
            f"pending={invalid_pending}, completed={invalid_completed}")
    data["pending"] = pending
    data["completed"] = completed
    return data
def _extract_metrics(cv_report: dict | None = None,
                     treatment_outcome: dict | None = None) -> dict:
    metrics = {
        "precision": 0.0,
        "recall": 0.0,
        "fp_count": 0,
        "fn_count": 0,
        "fix_rate": 0.0,
    }
    _metrics_from_findings(_findings_index_of(cv_report), metrics)
    apply_treatment_fix_rate(metrics, treatment_outcome)
    return metrics
def _findings_index_of(cv_report: dict | None) -> list:
    if not (isinstance(cv_report, dict) and cv_report):
        return []
    cv = cv_report.get(CAT_CROSS_VALIDATION)
    cv = cv if isinstance(cv, dict) else {}
    top_index = cv_report.get("findings_index")
    if has_finding_entries(top_index):
        return top_index
    cv_index = cv.get("findings_index")
    if has_finding_entries(cv_index):
        return cv_index
    if isinstance(top_index, list):
        return top_index
    return cv_index if isinstance(cv_index, list) else []
_MEASURED_CONCLUSIONS: frozenset[str] = frozenset({
    "confirmed", "suppressed", "likely", "uncertain", "investigated"})
_FN_CONCLUSIONS: frozenset[str] = frozenset({
    "likely", "uncertain", "investigated"})
def _effective_conclusion(finding: dict) -> str:
    conclusion_v2 = finding.get("conclusion_v2")
    if isinstance(conclusion_v2, str):
        candidate = conclusion_v2.strip().lower()
        mapped = CONCLUSION_V2_MAP.get(candidate)
        if mapped is not None:
            return mapped
    conclusion = finding.get("conclusion")
    if not isinstance(conclusion, str):
        return ""
    candidate = conclusion.strip().lower()
    return CONCLUSION_V2_MAP.get(candidate, candidate)
def _has_cv_measurement(cv_report: dict | None) -> bool:
    return any(
        isinstance(f, dict) and _effective_conclusion(f) in _MEASURED_CONCLUSIONS
        for f in _findings_index_of(cv_report))
def _count_conclusion(findings_index: list, conclusion: str) -> int:
    return sum(1 for f in findings_index
               if isinstance(f, dict) and _effective_conclusion(f) == conclusion)
def _fn_count_of(findings_index: list) -> int:
    return sum(
        1 for f in findings_index
        if isinstance(f, dict) and _effective_conclusion(f) in _FN_CONCLUSIONS)
def _metrics_from_findings(findings_index: list, metrics: dict) -> None:
    total = len(findings_index)
    if not total:
        return
    confirmed = _count_conclusion(findings_index, "confirmed")
    suppressed = _count_conclusion(findings_index, "suppressed")
    fn_count = _fn_count_of(findings_index)
    metrics["precision"] = round(
        confirmed / max(confirmed + suppressed, 1), 4)
    metrics["recall"] = round(
        confirmed / max(confirmed + fn_count, 1), 4)
    metrics["fp_count"] = suppressed
    metrics["fn_count"] = fn_count
class EnhancementTracker:
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
        self._snapshot_path = f"evolution_state.json#enhancement_snapshots[{skill_dir}]"
        self._snapshot_source_readable = True
        self._snapshots: dict[str, dict] = self._load_snapshots()
        if self._snapshots.get("pending"):
            try:
                with _required_write_lock(self.skill_dir):
                    self._snapshots = self._load_snapshots()
                    self._cleanup_stale_snapshots()
            except _READ_ERRORS as exc:
                logger.warning(
                    "[EnhancementTracker] 过期快照清理跳过，保留原状态: %s", exc)
    def _cleanup_stale_snapshots(self, max_age_days: int = 7, *,
                                 persist: bool = True) -> int:
        pending = self._snapshots.get("pending", {})
        if not pending:
            return 0
        previous = copy.deepcopy(self._snapshots) if persist else None
        now = datetime.datetime.now()
        completed = self._snapshots.setdefault("completed", [])
        stale_ids = [adj_id for adj_id, snapshot in pending.items()
                     if _pending_snapshot_stale(snapshot, now, max_age_days)]
        for adj_id in stale_ids:
            snapshot = pending.pop(adj_id)
            snapshot["verdict"] = "stale"
            snapshot["stale_reason"] = f"pending 超过 {max_age_days} 天未被 capture_after 闭合"
            completed.append(snapshot)
        if not stale_ids:
            return 0
        if persist:
            if not self._save_snapshots():
                self._snapshots = previous
                logger.warning(
                    "[EnhancementTracker] 过期快照持久化失败，已恢复 %d 个 pending",
                    len(stale_ids))
                return 0
            logger.info("[EnhancementTracker] 共清理 %d 个过期 pending 快照", len(stale_ids))
        return len(stale_ids)
    def _load_snapshots(self) -> dict[str, dict]:
        snapshot = read_evolution_section(
            self.skill_dir, "enhancement_snapshots")
        if snapshot is not None:
            try:
                data = snapshot
                if not isinstance(data, dict):
                    self._snapshot_source_readable = False
                    logger.warning(
                        "[EnhancementTracker] 快照顶层非对象(%s)，保留原文件并暂停写入",
                        type(data).__name__)
                    return {"pending": {}, "completed": []}
                return _normalize_snapshot_frame(data)
            except (OSError, ValueError, TypeError, RecursionError):
                self._snapshot_source_readable = False
                logger.warning(
                    "[EnhancementTracker] 快照文件损坏，保留原文件并暂停写入",
                    exc_info=True)
        return {"pending": {}, "completed": []}
    def _save_snapshots(self) -> bool:
        if not self._snapshot_source_readable:
            logger.warning(
                "[EnhancementTracker] 快照源文件不可读，保留原文件并拒绝覆盖: %s",
                self._snapshot_path)
            return False
        try:
            completed = self._snapshots.get("completed", [])
            if len(completed) > _MAX_COMPLETED_SNAPSHOTS:
                self._snapshots["completed"] = completed[-_MAX_COMPLETED_SNAPSHOTS:]
            if not write_evolution_section(
                    self.skill_dir, "enhancement_snapshots", self._snapshots):
                logger.warning(
                    "[EnhancementTracker] 快照 section 落盘失败: %s",
                    self.skill_dir)
                return False
        except _READ_ERRORS as e:
            logger.warning("[EnhancementTracker] 快照持久化失败: %s", e)
            return False
        return True
    def capture_before(self, adjustment_id: str, level: str,
                       target: str, action_type: str,
                       cv_report: dict | None = None,
                       treatment_outcome: dict | None = None) -> bool:
        _t0 = time.monotonic()
        try:
            with _required_write_lock(self.skill_dir):
                self._snapshots = self._load_snapshots()
                return self._capture_before_current(
                    adjustment_id, level, target, action_type,
                    cv_report=cv_report, treatment_outcome=treatment_outcome)
        except _READ_ERRORS as exc:
            logger.warning(
                "[EnhancementTracker] 基线快照事务失败: %s", exc)
            trace_module_run(
                "retrospective_ledger", "capture_before", _t0, "save_failed",
                adjustment_id=_normalize_adjustment_id(adjustment_id))
            return False
    def _capture_before_current(self, adjustment_id: str, level: str,
                                target: str, action_type: str,
                                cv_report: dict | None = None,
                                treatment_outcome: dict | None = None) -> bool:
        _t0 = time.monotonic()
        adjustment_id = _normalize_adjustment_id(adjustment_id)
        metrics = _extract_metrics(cv_report, treatment_outcome)
        snapshot = {
            "adjustment_id": adjustment_id,
            "timestamp": time.strftime(FMT_DATETIME),
            "level": clean_enhancement_text(level),
            "target": clean_enhancement_text(target),
            "action_type": clean_enhancement_text(action_type),
            "baseline_measured": _has_cv_measurement(cv_report),
            "before_precision": metrics["precision"],
            "before_recall": metrics["recall"],
            "before_fp_count": metrics["fp_count"],
            "before_fn_count": metrics["fn_count"],
            "before_fix_rate": metrics["fix_rate"],
            "verdict": "pending",
        }
        previous = copy.deepcopy(self._snapshots)
        self._snapshots.setdefault("pending", {})[adjustment_id] = snapshot
        stale_cleaned = self._cleanup_stale_snapshots(persist=False)
        if not self._save_snapshots():
            self._snapshots = previous
            logger.warning(
                "[EnhancementTracker] 基线快照持久化失败，已恢复写前状态: %s",
                adjustment_id)
            trace_module_run("retrospective_ledger", "capture_before", _t0,
                              "save_failed", adjustment_id=adjustment_id)
            return False
        if stale_cleaned:
            logger.info("[EnhancementTracker] 共清理 %d 个过期 pending 快照",
                        stale_cleaned)
        logger.info("[EnhancementTracker] 捕获基线: %s (target=%s, precision=%.2f)",
                    adjustment_id, target, metrics["precision"])
        trace_module_run("retrospective_ledger", "capture_before", _t0, adjustment_id=adjustment_id, target=target, precision=metrics["precision"])
        return True
    def capture_after(self, adjustment_id: str,
                      cv_report: dict | None = None,
                      treatment_outcome: dict | None = None) -> dict:
        _t0 = time.monotonic()
        try:
            with _required_write_lock(self.skill_dir):
                self._snapshots = self._load_snapshots()
                return self._capture_after_current(
                    adjustment_id, cv_report=cv_report,
                    treatment_outcome=treatment_outcome)
        except _READ_ERRORS as exc:
            logger.warning(
                "[EnhancementTracker] 效果快照事务失败: %s", exc)
            trace_module_run(
                "retrospective_ledger", "capture_after", _t0, "save_failed",
                adjustment_id=_normalize_adjustment_id(adjustment_id))
            return {}
    def _capture_after_current(self, adjustment_id: str,
                               cv_report: dict | None = None,
                               treatment_outcome: dict | None = None) -> dict:
        _t0 = time.monotonic()
        adjustment_id = _normalize_adjustment_id(adjustment_id)
        pending = self._snapshots.get("pending", {})
        if adjustment_id not in pending:
            logger.warning("[EnhancementTracker] 未找到 pending 快照: %s", adjustment_id)
            trace_module_run("retrospective_ledger", "capture_after", _t0, "no_pending", adjustment_id=adjustment_id)
            return {}
        if not _has_cv_measurement(cv_report):
            logger.warning(
                "[EnhancementTracker] 本轮无 CV 结论样本，快照保持 pending "
                "待下轮评估（无数据不参与效果判定）: %s", adjustment_id)
            trace_module_run("retrospective_ledger", "capture_after",
                              _t0, "no_measurement", adjustment_id=adjustment_id)
            return {}
        previous = copy.deepcopy(self._snapshots)
        snapshot = pending.pop(adjustment_id)
        try:
            metrics = _extract_metrics(cv_report, treatment_outcome)
            baseline_measured = _baseline_measurement_flag(snapshot)
            delta_precision, delta_fn = _score_snapshot(
                snapshot, metrics, baseline_measured=baseline_measured)
            verdict = snapshot["verdict"]
            completed = self._snapshots.setdefault("completed", [])
            consecutive = _consecutive_degraded(completed, snapshot, verdict)
            snapshot["consecutive_degraded"] = consecutive
            large_degradation = (
                verdict == "degraded"
                and delta_precision < _LARGE_DEGRADATION_DELTA_PRECISION)
            snapshot[FIELD_ROLLBACK_RECOMMENDED] = (
                consecutive >= 2 or large_degradation)
            if large_degradation and consecutive < 2:
                snapshot["rollback_reason"] = "single_large_degradation"
                logger.warning(
                    "[EnhancementTracker] 单次大幅退化 (delta_precision=%+.4f), "
                    "建议立即回滚: %s", delta_precision, adjustment_id)
            completed.append(snapshot)
        except Exception as _score_err:
            self._snapshots = previous
            logger.warning(
                "[EnhancementTracker] 效果评估异常，保留 pending 待重试: %s (%s)",
                adjustment_id, _score_err, exc_info=True)
            trace_module_run("retrospective_ledger", "capture_after", _t0,
                             "score_failed", adjustment_id=adjustment_id)
            return {}
        if not self._save_snapshots():
            self._snapshots = previous
            logger.warning(
                "[EnhancementTracker] 效果快照持久化失败，保留 pending 待重试: %s",
                adjustment_id)
            trace_module_run("retrospective_ledger", "capture_after", _t0,
                              "save_failed", adjustment_id=adjustment_id)
            return {}
        logger.info("[EnhancementTracker] 效果评估: %s verdict=%s "
                    "(delta_precision=%+.4f, delta_fn=%d, rollback=%s)",
                     adjustment_id, verdict, delta_precision, delta_fn,
                     snapshot[FIELD_ROLLBACK_RECOMMENDED])
        trace_module_run("retrospective_ledger", "capture_after", _t0, verdict, adjustment_id=adjustment_id,
                          delta_precision=delta_precision, delta_fn=delta_fn, rollback=bool(snapshot[FIELD_ROLLBACK_RECOMMENDED]))
        return snapshot
    def capture_after_pending(self, cv_report: dict | None = None,
                              treatment_outcome: dict | None = None) -> int:
        closed = 0
        for adj_id in list(self._snapshots.get("pending", {}).keys()):
            if self.capture_after(adj_id, cv_report=cv_report,
                                  treatment_outcome=treatment_outcome):
                closed += 1
        return closed
    def get_rollback_targets(self) -> list[dict]:
        latest: dict[str, dict] = {}
        for snap in self._snapshots.get("completed", []):
            _sid = snap.get("adjustment_id")
            if _sid is None:
                continue
            latest[_normalize_adjustment_id(_sid)] = snap
        return [snap for snap in latest.values()
                if snap.get(FIELD_ROLLBACK_RECOMMENDED) is True]
    def should_rollback(self, adjustment_id: str) -> bool:
        adjustment_id = _normalize_adjustment_id(adjustment_id)
        for snap in reversed(self._snapshots.get("completed", [])):
            snap_id = snap.get("adjustment_id")
            if snap_id is not None and _snapshot_id_matches(snap_id, adjustment_id):
                return snap.get(FIELD_ROLLBACK_RECOMMENDED, False) is True
        return False
    def get_roi_report(self) -> dict:
        completed = self._snapshots.get("completed", [])
        counts = dict.fromkeys(
            (*_ROI_EVALUATED_VERDICTS, "stale", "unevaluated"), 0)
        for snapshot in completed:
            verdict = snapshot.get("verdict")
            bucket = (verdict if isinstance(verdict, str) and verdict in counts
                      else "stale")
            counts[bucket] += 1
        evaluated = (len(completed) - counts["stale"]
                     - counts["unevaluated"])
        return {
            "total_adjustments": evaluated,
            "stale": counts["stale"],
            "unevaluated": counts["unevaluated"],
            "improved": counts["improved"],
            "degraded": counts["degraded"],
            "neutral": counts["neutral"],
            "improvement_rate": round(counts["improved"] / evaluated, 4) if evaluated else 0.0,
            "degradation_rate": round(counts["degraded"] / evaluated, 4) if evaluated else 0.0,
            FIELD_ROLLBACK_RECOMMENDED: len(self.get_rollback_targets()),
        }

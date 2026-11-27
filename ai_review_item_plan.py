from __future__ import annotations

import functools
import itertools
import logging
import math
import os
import time
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass, replace
from typing import Any

from jwsgj.build_safe_rollback import regression_undecided
from jwsgj.diag_guard_state import (
    ensure_plan_dir,
    max_review_seq,
    read_queue_json,
    write_json_artifact,
    write_queue_json,
)
from jwsgj.diag_types_normalize import (
    as_dict,
    as_item_list,
    as_list,
    as_pure_count,
    as_str,
    cv_int,
    dict_or_empty,
    is_finite_num,
    method_status_bucket,
    normalize_file_ref,
    normalize_line_no,
    safe_float,
    signal_bool,
    str_or,
    timestamp_human,
)
from jwsgj.diag_types_vocab import (
    FIELD_CODE_LEVEL_FEEDBACK,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    FIELD_FINDINGS_SUPPRESSED,
    FIELD_INTERMEDIATE_REPORTS,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_SUGGESTED_VALUE,
    FIELD_TOTAL_INPUT_FINDINGS,
    FMT_DATETIME,
    FMT_DATETIME_ISO,
)
from jwsgj.feedback_coordinator import (
    CodeLevelFeedbackRouter,
    FeedbackCoordinator,
    FeedbackRouteContext,
    Verdict,
    entry_confidence,
    level_target_key,
    load_pending_entries,
    resolve_target_file,
    route_entry,
)
from jwsgj.log_config import locked_artifact
from jwsgj.retrospective_ledger import mark_enhancement_applied
from jwsgj.runtime_paths import (
    adjustment_plan_path,
    feedback_enhancement_log_context,
    json_artifact_path,
    read_evolution_state,
)
from jwsgj.runtime_scope import normalize_skill_dir, normalize_text

__all__ = [
    'DEFAULT_MAX_ITEMS',
    'DEFAULT_MIN_CONFIDENCE',
    'FIELD_SUGGESTED_VALUE',
    'MAX_ADJUSTMENT_PLANS',
    'MAX_FIX_PLANS',
    'MAX_SECURITY_PLANS',
    'apply_code_level_feedback_step',
    'apply_enhancement_verdict',
    'apply_feedback_verdict',
    'build_auto_enhancement_report',
    'cleanup_operation',
    'code_feedback_phase_payload',
    'code_feedback_report',
    'coordinator_deferred_gate',
    'enqueue_adjustment_proposals',
    'enqueue_plan_items',
    'feedback_plan_path',
    'find_pending_entry',
    'identity_pair',
    'is_pending_plan',
    'load_pending_security_plan',
    'mark_plan_resolved',
    'needs_fixed_source',
    'pending_review_count',
    'preview_pending_feedback',
    'provided_source',
    'prune_consumed_items',
    'resolve_security_plan',
    'run_code_level_feedback',
    'run_stage6d_auto_enhancements',
    'security_plan_path',
    'stage_code_feedback',
    'sync_adjustment_proposals',
    'verdict_text',
]
logger = logging.getLogger(__name__)
logger.info("ai_review_item_plan 已加载: %d 项导出", len(__all__))
_CTX = FeedbackRouteContext()
DEFAULT_MAX_ITEMS = 10
DEFAULT_MIN_CONFIDENCE = 0.6
_PLAN_COLLECT_MAX_ITEMS = 50
_DEFAULT_PROPOSAL_CONFIDENCE = DEFAULT_MIN_CONFIDENCE
_DEFAULT_PROPOSAL_REASON = "由治疗反馈闭环产出，待 AI 审核并执行"
_PROPOSAL_REASONS: dict[str, str] = {
    "fixer_safety_override": "修复器安全标签调整（依据见 suggested_value.reason）",
}
def run_code_level_feedback(
        skill_dir: str, max_items: int = DEFAULT_MAX_ITEMS,
        min_confidence: float = DEFAULT_MIN_CONFIDENCE, *,
        context=_CTX) -> dict:
    started = time.monotonic()
    try:
        skill_dir, log_path = feedback_enhancement_log_context(skill_dir)
        return _export_plan(
            skill_dir, log_path, max_items, min_confidence, context=context)
    finally:
        logger.debug("[AIReview] 反哺只读规划耗时: %.3fs",
                     time.monotonic() - started)
def _preview_row(entry: dict) -> dict:
    route = route_entry(entry)
    return {
        "target": str_or(entry.get("target")),
        "description": str_or(entry.get("description")),
        FIELD_SUGGESTED_VALUE: str_or(entry.get(FIELD_SUGGESTED_VALUE)),
        "confidence": entry_confidence(entry, 0),
        "routed_target": route.get("target_key") or "auto",
        "routed_level": route.get("level") or "unknown",
    }
def preview_pending_feedback(skill_dir: str) -> list[dict]:
    skill_dir, log_path = feedback_enhancement_log_context(skill_dir)
    return [_preview_row(entry) for entry in load_pending_entries(log_path)]
def _coerce_number(value: Any, cast, default, field: str):
    if isinstance(value, bool):
        return default
    try:
        return cast(value)
    except (TypeError, ValueError, OverflowError) as exc:
        logger.debug(
                      "[AIReview] 数值归一降级 %s: %s", field, exc,
                      exc_info=True)
        return default
def _normalized_limits(max_items: Any, min_confidence: Any) -> tuple[int, float]:
    limit = max(0, _coerce_number(max_items, int, 0, "max_items"))
    floor = _coerce_number(
        min_confidence, float, DEFAULT_MIN_CONFIDENCE, "min_confidence")
    if not math.isfinite(floor):
        floor = DEFAULT_MIN_CONFIDENCE
    return limit, floor
def _is_l4_entry(entry: dict) -> bool:
    return (entry.get("action_type") == "fp_suppression"
            or str_or(entry.get("target")).startswith("fp_suppression/"))
def _select_pending_entries(entries: list, max_items: int,
                           min_confidence: float) -> list:
    max_items, min_confidence = _normalized_limits(max_items, min_confidence)
    candidates = entries if isinstance(entries, list) else []
    l4_entries: list = []
    non_l4_entries: list = []
    for entry in candidates:
        if not isinstance(entry, dict):
            continue
        if entry_confidence(entry, 0) < min_confidence:
            continue
        (l4_entries if _is_l4_entry(entry) else non_l4_entries).append(entry)
    if max_items <= 0:
        l4_quota = 0
    else:
        l4_quota = min(
            len(l4_entries),
            max(max_items // 2, 1, max_items - len(non_l4_entries)))
    l4_to_process = l4_entries[:l4_quota]
    non_l4_to_process = non_l4_entries[:max(0, max_items - len(l4_to_process))]
    return l4_to_process + non_l4_to_process
def _plan_item(entry: dict, route: dict, plan_id: str, *,
                context=_CTX) -> dict:
    level = route["level"]
    target_key = level_target_key(entry, route, **context.registries)
    tfile = resolve_target_file(
        entry, route, injection_aliases=context.injection_aliases,
        **context.registries) or route.get("file", "")
    action = str_or(entry.get("action_type"))
    if action == "source_fix":
        summary = "源头修改 " + (tfile or str_or(entry.get("target")))
    elif action == "fp_suppression":
        summary = "FP 抑制规则（L4，写 JSON 非改源码）"
    else:
        summary = f"{level} {action}" + (" @ " + tfile if tfile else "")
    return {
        "plan_id": plan_id,
        "target": str_or(entry.get("target")),
        "action_type": action,
        "level": level,
        "target_key": target_key,
        "file": tfile,
        "confidence": entry_confidence(entry, 0),
        "description": str_or(entry.get("description")),
        "suggested_value": ("" if entry.get(FIELD_SUGGESTED_VALUE) is None
                            else entry[FIELD_SUGGESTED_VALUE]),
        "summary": summary,
        "status": _PENDING_PLAN_STATUS,
        "entry": entry,
        "route": route,
    }
def _stable_plan_ids(entries: list, previous: list) -> list[str]:
    _prev: dict[tuple[str, str, str], str] = {}
    for previous_plan in as_list(previous):
        if not isinstance(previous_plan, dict):
            continue
        if max_review_seq([previous_plan], "PLAN", id_key="plan_id") <= 0:
            continue
        _identity = (*identity_pair(
            previous_plan.get("entry") or previous_plan),
            _review_plan_level(previous_plan))
        _prev[_identity] = previous_plan["plan_id"]
    _nxt = max_review_seq(previous, "PLAN", id_key="plan_id")
    _ids: list[str] = []
    for entry in entries:
        _pid = _prev.get(
            (*identity_pair(entry), _review_entry_level(entry)))
        if not isinstance(_pid, str) or not _pid or _pid in _ids:
            _nxt += 1
            _pid = f"PLAN-{_nxt:03d}"
        _ids.append(_pid)
    return _ids
def _unselected_pending_plans(
        current: list, previous: list, source_entries: list) -> list:
    current_ids = {
        as_str(plan.get("plan_id")) for plan in current
        if isinstance(plan, dict) and as_str(plan.get("plan_id"))
    }
    current_keys = {
        (*identity_pair(plan.get("entry") or plan), _review_plan_level(plan))
        for plan in current if isinstance(plan, dict)
    }
    source_keys = {
        (*identity_pair(entry), _review_entry_level(entry))
        for entry in source_entries
    }
    retained = []
    for plan in previous:
        if not is_pending_plan(plan):
            continue
        key = (*identity_pair(plan.get("entry") or plan),
               _review_plan_level(plan))
        if (key not in source_keys or key in current_keys
                or as_str(plan.get("plan_id")) in current_ids):
            continue
        retained.append(plan)
    return retained
def _export_plan(skill_dir: str, log_path: str, max_items: int,
                min_confidence: float, *,
                context=_CTX) -> dict:
    plan_file = feedback_plan_path(skill_dir)
    try:
        source_entries = _load_pending_entries_strict(skill_dir)
        eligible = _select_pending_entries(
            source_entries, max_items, min_confidence)
        ensure_plan_dir(plan_file)
        with _required_plan_lock(plan_file):
            _, previous = _load_plan_queue(plan_file, "plans")
            _ids = _stable_plan_ids(eligible, previous)
            plans = [_plan_item(entry, route_entry(entry), _pid, context=context)
                     for entry, _pid in zip(eligible, _ids, strict=True)]
            retained = _unselected_pending_plans(plans, previous, source_entries)
            consumed = [p for p in previous
                        if isinstance(p, dict) and not is_pending_plan(p)]
            try:
                write_json_artifact(plan_file, {
                    "_meta": {"total": len(plans),
                              "generated": time.strftime(FMT_DATETIME)},
                    "plans": prune_consumed_items(plans + retained + consumed,
                                                  MAX_FIX_PLANS)}, indent=2)
            except (OSError, ValueError, TypeError) as e:
                logger.exception("[Router] 方案清单写盘失败: %s", plan_file)
                return {"total": 0, "plans": [], "plan_file": plan_file,
                        "status": "error",
                        "message": f"方案清单写盘失败: {e}"}
    except _PLAN_STORE_ERRORS as _read_err:
        logger.exception(
            "[Router] 反哺输入或方案清单读取失败，保留原队列: %s "
            "(input=%s)", plan_file, log_path)
        return {"total": 0, "plans": [], "plan_file": plan_file,
                "status": "error",
                "message": f"反哺输入或方案清单读取失败: {_read_err}"}
    logger.info("[Router] 反哺方案清单导出: %d 条待 AI 审批 -> %s",
                len(plans), plan_file)
    return {"total": len(plans), "plans": plans, "plan_file": plan_file,
            "status": "ok",
            "message": "已导出修改方案清单，未执行任何修改；请 AI 逐项审批后调用 apply_approved_fix"}
MAX_ADJUSTMENT_PLANS = 200
_ENQUEUE_META_KEYS: frozenset[str] = frozenset({"last_updated"})
_PENDING_PLAN_STATUS = "pending_review"
_PLAN_STORE_ERRORS = (OSError, RuntimeError, ValueError, TypeError)
def provided_source(value: Any) -> str:
    return value if isinstance(value, str) and value.strip() else ""
def verdict_text(assessment: dict) -> str:
    return as_str(assessment.get("verdict"))
def needs_fixed_source(channel: str) -> dict:
    return {"status": "needs_fixed_source",
            "reason": f"{channel}修复需要 AI 提供 fixed_source（修复后源码全文）"}
def cleanup_operation(review: dict, plan: dict) -> str:
    return (provided_source(plan.get("operation"))
            or provided_source(review.get("strategy"))
            or provided_source(review.get("rule_id")))
def identity_pair(container: dict) -> tuple[str, str]:
    _c = as_dict(container)
    return (normalize_text(_c.get("target")),
            normalize_text(_c.get("description")))
def _review_entry_level(entry: dict) -> str:
    level = as_str(entry.get("level")).strip()
    return level or as_str(route_entry(entry).get("level")).strip()
def _review_plan_level(plan: dict) -> str:
    explicit = (as_str(plan.get("level")).strip()
                or as_str(as_dict(plan.get("route")).get("level")).strip())
    entry = as_dict(plan.get("entry"))
    return explicit or _review_entry_level(entry or plan)
def find_pending_entry(items: list, key: str, value):
    if value is None:
        return None
    return next((p for p in as_list(items)
                 if is_pending_plan(p) and p.get(key) == value), None)
def is_pending_plan(p) -> bool:
    return isinstance(p, dict) and p.get("status") == _PENDING_PLAN_STATUS
def _prune_preserve_order(items: list, max_keep: int) -> list:
    max_keep = normalize_line_no(max_keep)
    keep_idx: set = set()
    budget = max_keep
    for idx in range(len(items) - 1, -1, -1):
        p = items[idx]
        if not isinstance(p, dict):
            continue
        if is_pending_plan(p):
            keep_idx.add(idx)
        elif budget > 0:
            keep_idx.add(idx)
            budget -= 1
    return [p for i, p in enumerate(items) if i in keep_idx]
def _prune_regroup(items: list, max_keep: int) -> list:
    pending = [p for p in items if is_pending_plan(p)]
    consumed = [
        p for p in items if isinstance(p, dict) and not is_pending_plan(p)
    ]
    max_keep = normalize_line_no(max_keep)
    if max_keep <= 0:
        return pending
    return pending + consumed[-max_keep:]
def prune_consumed_items(items: list, max_keep: int,
                          *, preserve_order: bool = False) -> list:
    items = as_list(items)
    if preserve_order:
        return _prune_preserve_order(items, max_keep)
    return _prune_regroup(items, max_keep)
def pending_review_count(items: list) -> int:
    return sum(1 for p in as_list(items) if is_pending_plan(p))
def _queue_skill_dir(skill_dir: str) -> str:
    if not skill_dir:
        return skill_dir
    return normalize_skill_dir(os.fspath(skill_dir))
def _load_plan_queue(plan_path: str,
                     key: str = "proposals") -> tuple[dict, list]:
    data = read_queue_json(plan_path, {}, for_update=True)
    items = data.setdefault(key, [])
    if not isinstance(items, list):
        raise TypeError(
            f"队列字段 {key} 类型非法({type(items).__name__})，"
            f"拒绝按空清单覆盖: {plan_path}")
    return data, items
@contextmanager
def _required_plan_lock(plan_path: str):
    with locked_artifact(plan_path) as locked:
        if not locked:
            raise RuntimeError(f"计划队列锁不可用，拒绝无锁读改写: {plan_path}")
        yield

def _identity_text(value) -> str:
    return value.strip() if isinstance(value, str) else ""
def _proposal_index_key(proposal):
    if not isinstance(proposal, dict):
        return None
    kind = _identity_text(proposal.get("kind"))
    target = _identity_text(proposal.get("target"))
    return (kind, target) if kind and target else None
_NUMERIC_ADJUSTMENT_KINDS = frozenset((
    "method_confidence_multiplier", "cv_confidence_threshold"))
def _canonical_adjustment_value(kind, val):
    if kind in _NUMERIC_ADJUSTMENT_KINDS:
        return safe_float(val, None)
    return val
def _queued_values_index(proposals) -> dict:
    consumed: dict = {}
    pending: dict = {}
    for proposal in proposals:
        key = _proposal_index_key(proposal)
        if key is None:
            continue
        target = pending if is_pending_plan(proposal) else consumed
        target[key] = _canonical_adjustment_value(
            key[0], proposal.get(FIELD_SUGGESTED_VALUE))
    return {**consumed, **pending}
def _suggest_value_gate_passes(kind, key, val) -> bool:
    if kind in _NUMERIC_ADJUSTMENT_KINDS:
        if val is None:
            logger.warning("[FeedbackApplier] %s/%s 建议值非数值(%s)，不入队",
                           kind, key, type(val).__name__)
            return False
    elif kind == "fixer_safety_override" and not isinstance(val, dict):
        logger.warning("[FeedbackApplier] %s/%s 建议值非dict(%s)，不入队",
                       kind, key, type(val).__name__)
        return False
    return True
def _proposal_core(kind, key, val, review_id, reason,
                   confidence: float = _DEFAULT_PROPOSAL_CONFIDENCE) -> dict:
    return {
        "review_id": review_id,
        "kind": kind,
        "target": key,
        FIELD_SUGGESTED_VALUE: val,
        "reason": reason,
        "confidence": round(float(confidence), 3),
        "status": _PENDING_PLAN_STATUS,
    }
def _proposal_evidence(evidence, kind, key) -> dict:
    ev = evidence.get((kind, key)) if isinstance(evidence, dict) else None
    return ev if isinstance(ev, dict) else {}
def _build_proposal_entry(kind, key, val, review_id,
                          tctx, rctx, evidence) -> dict:
    ev = _proposal_evidence(evidence, kind, key)
    ev_conf = ev.get("confidence")
    conf = ev_conf if is_finite_num(ev_conf) else _DEFAULT_PROPOSAL_CONFIDENCE
    reason = ev.get("reason") or _PROPOSAL_REASONS.get(
        kind, _DEFAULT_PROPOSAL_REASON)
    entry = {
        **_proposal_core(kind, key, val, review_id, reason, conf),
        "phase": "treatment_feedback",
        "source": "feedback_applier",
        "diagnosis_context": {
            "target_id": key,
            "feedback_type": ev.get("feedback_type", ""),
            "description": reason,
        },
        "treatment_context": dict(tctx),
        **({"retrospective_context": rctx} if rctx else {}),
    }
    if ev:
        entry["evidence"] = {
            ek: ev[ek] for ek in
            ("feedback_type", "trigger_count", "previous_value")
            if ev.get(ek) not in (None, "")
        }
    return entry
def _pending_proposal_position(proposals: list, kind: str, key: str):
    for idx in range(len(proposals) - 1, -1, -1):
        proposal = proposals[idx]
        if (is_pending_plan(proposal)
                and normalize_file_ref(proposal.get("kind")).strip() == kind
                and normalize_file_ref(proposal.get("target")).strip() == key):
            return idx
    return None
def _enqueue_into(proposals: list, kind: str, key: str, val,
                  make_entry) -> bool:
    key = _identity_text(key)
    if not key:
        return False
    val = _canonical_adjustment_value(kind, val)
    if not _suggest_value_gate_passes(kind, key, val):
        return False
    pos = _pending_proposal_position(proposals, kind, key)
    current = proposals[pos] if pos is not None else None
    review_id = (_identity_text(current.get("review_id"))
                 if isinstance(current, dict) else "")
    current_reviewable = current is None or bool(review_id)
    if (current_reviewable
            and _queued_values_index(proposals).get((kind, key)) == val):
        return False
    entry = make_entry(review_id or None, val)
    if current is None:
        proposals.append(entry)
        return True
    merged = {**current, **entry}
    merged["revision"] = max(1, cv_int(current.get("revision", 1))) + 1
    proposals[pos] = merged
    return True
def _append_treatment_proposal(sink: _ProposalSink, treatment_context: dict,
                              retrospective_context: dict, evidence: dict,
                              kind: str, key: str, val) -> bool:
    return _enqueue_into(
        sink.proposals, kind, key, val,
        lambda review_id, normalized_val: _build_proposal_entry(
            kind, key, normalized_val,
            review_id or f"ADJ-{next(sink.seq_iter):03d}",
            treatment_context, retrospective_context, evidence))
def _persist_adjustment_plan(plan_path: str, data: dict,
                             stamp_key: str) -> int:
    proposals = prune_consumed_items(
        data.get("proposals"), MAX_ADJUSTMENT_PLANS)
    data["proposals"] = proposals
    meta = data.get("_meta")
    if not isinstance(meta, dict):
        meta = {}
    meta[stamp_key] = time.strftime(FMT_DATETIME_ISO)
    data["_meta"] = meta
    write_queue_json(plan_path, data)
    return pending_review_count(proposals)
def sync_adjustment_proposals(
        skill_dir: str, muls: dict, cvs: dict, fixs: dict,
        treatment_context: dict, retrospective_context: dict,
        evidence: dict) -> None:
    treatment_context = dict_or_empty(treatment_context)
    retrospective_context = dict_or_empty(retrospective_context)
    evidence = dict_or_empty(evidence)
    plan_path = adjustment_plan_path(normalize_skill_dir(skill_dir))
    ensure_plan_dir(plan_path)
    with _required_plan_lock(plan_path):
        data, sink = _load_adjustment_plan(plan_path)
        _add = functools.partial(
            _append_treatment_proposal, sink,
            treatment_context, retrospective_context, evidence)
        enqueued = sum(
            _enqueue_channel_entries(kind, mapping, _add, builder)
            for kind, mapping, builder in _adjustment_channel_specs(
                muls, cvs, fixs))
        pending_n = _persist_adjustment_plan(plan_path, data, "generated")
    logger.info(
        "[FeedbackApplier] 调整建议已落盘待审核队列: %s (新增 %d / pending=%d)",
        plan_path, enqueued, pending_n)
@dataclass(frozen=True)
class _ProposalSink:
    proposals: list
    seq_iter: Any
    reason: str = ""
    provenance: dict | None = None
def _pipeline_proposal_entry(sink: _ProposalSink, kind: str, key: str,
                             val, review_id: str | None) -> dict:
    entry = _proposal_core(
        kind, key, val,
        review_id or f"ADJ-{next(sink.seq_iter):03d}",
        sink.reason or _DEFAULT_PROPOSAL_REASON)
    if isinstance(sink.provenance, dict):
        for _pk, _pv in sink.provenance.items():
            if _pv not in (None, "", [], {}) and _pk not in entry:
                entry[_pk] = _pv
    return entry
def _append_proposal(sink: _ProposalSink, kind: str, key: str, val) -> bool:
    return _enqueue_into(
        sink.proposals, kind, key, val,
        lambda review_id, normalized_val: _pipeline_proposal_entry(
            sink, kind, key, normalized_val, review_id))
def _iter_channel_entries(mapping: dict, sub_key_builder):
    for key, val in mapping.items():
        if key in _ENQUEUE_META_KEYS:
            continue
        if isinstance(val, dict) and sub_key_builder is not None:
            for sub_key, sub_val in val.items():
                yield sub_key_builder(key, sub_key), sub_val
        else:
            yield str(key), val
def _enqueue_channel_entries(kind: str, mapping: dict, add, sub_key_builder) -> int:
    enqueued = 0
    for key, val in _iter_channel_entries(mapping, sub_key_builder):
        if add(kind, key, val):
            enqueued += 1
    return enqueued
def _load_adjustment_plan(plan_file: str) -> tuple[dict, _ProposalSink]:
    data, proposals = _load_plan_queue(plan_file)
    seq_iter = itertools.count(max_review_seq(proposals, "ADJ") + 1)
    return data, _ProposalSink(proposals, seq_iter)
def _multiplier_key(key: str, sub_key) -> str:
    return f"{key}:{sub_key}"
def _cv_confidence_key(key: str, sub_key) -> str:
    if key != FIELD_CV_CONFIDENCE_THRESHOLDS:
        return f"{key}.{sub_key}"
    return normalize_file_ref(sub_key)
def _adjustment_channel_specs(muls, cvs, fixs) -> tuple:
    return (
        ("method_confidence_multiplier", dict_or_empty(muls), _multiplier_key),
        ("cv_confidence_threshold", dict_or_empty(cvs), _cv_confidence_key),
        ("fixer_safety_override", dict_or_empty(fixs), None),
    )
def enqueue_adjustment_proposals(
    skill_dir: str,
    muls: dict | None = None,
    cvs: dict | None = None,
    fixs: dict | None = None,
    reason: str = "",
    provenance: dict | None = None,
) -> dict:
    sd = normalize_skill_dir(skill_dir)
    plan_file = adjustment_plan_path(sd)
    ensure_plan_dir(plan_file)
    muls, cvs, fixs = (
        dict_or_empty(muls),
        dict_or_empty(cvs),
        dict_or_empty(fixs),
    )
    with _required_plan_lock(plan_file):
        data, base_sink = _load_adjustment_plan(plan_file)
        sink = replace(base_sink, reason=reason, provenance=provenance)
        _add = functools.partial(_append_proposal, sink)
        enqueued = sum(
            _enqueue_channel_entries(kind, mapping, _add, builder)
            for kind, mapping, builder in _adjustment_channel_specs(muls, cvs, fixs)
        )
        if enqueued:
            _persist_adjustment_plan(plan_file, data, "updated")
            logger.info(
                "[AIReview] 调整建议已入队待审核执行: %d 条 -> %s",
                enqueued, plan_file)
        pending = pending_review_count(sink.proposals)
    return {
        "status": "enqueued" if enqueued else "no_new",
        "enqueued": enqueued,
        "pending": pending,
        "plan_file": plan_file,
        "next_action": "run_next_ai_review" if pending else "none",
    }
MAX_FIX_PLANS = 100
MAX_SECURITY_PLANS = MAX_FIX_PLANS
def feedback_plan_path(skill_dir: str) -> str:
    return json_artifact_path(_queue_skill_dir(skill_dir),
                              "_ai_fix_plan.json")
def security_plan_path(skill_dir: str) -> str:
    return json_artifact_path(_queue_skill_dir(skill_dir),
                              "_security_fix_plan.json")
def load_pending_security_plan(skill_dir: str, plan_id) -> dict | None:
    _, plans = _load_plan_queue(security_plan_path(skill_dir), "plans")
    return find_pending_entry(plans, "plan_id", plan_id)
def resolve_security_plan(skill_dir: str, plan_id, status: str) -> bool:
    plan_file = security_plan_path(skill_dir)
    with _required_plan_lock(plan_file):
        data, plans = _load_plan_queue(plan_file, "plans")
        plan = find_pending_entry(plans, "plan_id", plan_id)
        if plan is None:
            return False
        plan["status"] = status
        data["plans"] = prune_consumed_items(plans, MAX_SECURITY_PLANS)
        write_queue_json(plan_file, data)
        return True
def _plan_entry_matches(p: dict, plan_id, by_entry, level: str = "") -> bool:
    if plan_id:
        return p.get("plan_id") == plan_id
    if not by_entry or not any(by_entry):
        return False
    _e = p.get("entry") if isinstance(p.get("entry"), dict) else {}
    if identity_pair(p) != by_entry and identity_pair(_e) != by_entry:
        return False
    return not level or _review_plan_level(p) == level
def _mark_matching_plans(
    plans: list, plan_id, by_entry, status: str, level: str = ""
) -> int:
    changed = 0
    for plan in plans:
        if (is_pending_plan(plan)
                and _plan_entry_matches(plan, plan_id, by_entry, level)):
            plan["status"] = status
            changed += 1
    return changed
def mark_plan_resolved(
    sd: str, plan_id, status: str, by_entry: tuple[str, str] | None = None,
    *, level: str = ""
) -> int:
    level = as_str(level).strip()
    if by_entry is not None:
        _pair = tuple(by_entry)
        by_entry = ((normalize_text(_pair[0]), normalize_text(_pair[1]))
                    if len(_pair) >= 2 else None)
        if by_entry is not None and not any(by_entry):
            by_entry = None
    if not plan_id and by_entry is None:
        return 0
    plan_file = feedback_plan_path(sd)
    with _required_plan_lock(plan_file):
        data, plans = _load_plan_queue(plan_file, "plans")
        changed = _mark_matching_plans(plans, plan_id, by_entry, status, level)
        if changed:
            data["plans"] = prune_consumed_items(plans, MAX_FIX_PLANS)
            write_queue_json(plan_file, data)
            if by_entry:
                logger.info("[AIReview] 销项联动 plan %d 条 -> %s",
                            changed, status)
        return changed
def _build_review_info(verdict: str, assessment: dict | None) -> dict | None:
    if not (isinstance(assessment, dict) and assessment):
        return None
    return {
        "ai_review_verdict": verdict,
        "ai_review_rationale": as_str(
            assessment.get("verdict_rationale")
            or assessment.get("fp_evidence")),
        "ai_review_assessment": assessment,
    }
def _link_keys(plan: dict) -> tuple[str, str]:
    entry = as_dict(plan.get("entry"))
    target = entry.get("target") or plan.get("target")
    description = entry.get("description") or plan.get("description")
    return as_str(target), as_str(description)
def _review_level_filter(level: str):
    if not level:
        return None
    return lambda entry: _review_entry_level(entry) == level
def _link_resolve_entry(
    sd: str, plan: dict, status: str, review_info: dict | None = None
) -> tuple[int, Exception | None]:
    _et, _ed = _link_keys(plan)
    if not (_et or _ed):
        return 0, None
    _level = _review_plan_level(plan)
    _entry_filter = _review_level_filter(_level)
    try:
        _res = mark_enhancement_applied(
            sd, _et, _ed, status=status, review_info=review_info,
            entry_filter=_entry_filter)
    except _PLAN_STORE_ERRORS as exc:
        return 0, exc
    if not isinstance(_res, dict):
        return 0, TypeError("mark_enhancement_applied 返回值不是 dict")
    _error = as_str(_res.get("error"))
    if _error:
        return 0, RuntimeError(_error)
    return (1 if _res.get("file_marked") else 0), None
def apply_feedback_verdict(sd: str, review: dict, fixed_source: str,
                    assessment: dict | None = None, approved: bool = True) -> dict:
    plan = as_dict(review.get("plan"))
    assessment = as_dict(assessment)
    verdict = verdict_text(assessment)
    _review_info = _build_review_info(verdict, assessment)
    _by_entry = _feedback_by_entry(plan)
    if verdict == "defer":
        return _feedback_closed(sd, plan, "deferred",
                                "AI 审核后暂缓处理", "defer",
                                _by_entry, _review_info)
    if verdict in ("reject_as_fp", "reject") or not approved:
        return _feedback_closed(
            sd, plan, "rejected",
            as_str(assessment.get("verdict_rationale")
                   or assessment.get("fp_evidence")
                   or "AI 审核判定不采纳"),
            verdict or "reject", _by_entry, _review_info)
    if (review.get("requires_fixed_source")
            and not provided_source(fixed_source)):
        return needs_fixed_source("反哺源头")
    return _feedback_apply_fix(sd, plan, review, fixed_source,
                               _by_entry, _review_info)
def _feedback_by_entry(plan: dict) -> tuple[str, str] | None:
    if as_str(plan.get("plan_id")).strip():
        return None
    _bt = as_str(plan.get("target"))
    _bd = as_str(plan.get("description"))
    return (_bt, _bd) if (_bt or _bd) else None
def _plan_resolution_error(operation_status: str, plan_id,
                           exc: Exception) -> dict:
    logger.warning(
        "[AIReview] 计划 %s 终态落盘失败(%s)，保留审核可重试: %s",
        plan_id or "<by_entry>", operation_status, exc, exc_info=exc)
    return {
        "status": "error",
        "operation_status": operation_status,
        "reason": f"计划终态落盘失败（原操作: {operation_status}）: {exc}",
        "review_retained": True,
        "next_action": "retry_plan_resolution",
    }
def _feedback_link_error(operation_status: str, plan_id,
                         exc: Exception) -> dict:
    logger.warning(
        "[AIReview] 计划 %s enhancement_log 联动失败(%s)，保留审核可重试: %s",
        plan_id or "<by_entry>", operation_status, exc, exc_info=exc)
    return {
        "status": "error",
        "operation_status": operation_status,
        "reason": f"enhancement_log 联动失败（原操作: {operation_status}）: {exc}",
        "review_retained": True,
        "next_action": "retry_plan_resolution",
        "linked_entries_resolved": 0,
    }
def _feedback_closed(sd: str, plan: dict, resolve_status: str,
                     reason: str, verdict: str,
                     by_entry: tuple[str, str] | None,
                     review_info: dict | None) -> dict:
    _linked, _link_error = _link_resolve_entry(
        sd, plan, resolve_status, review_info=review_info)
    if _link_error is not None:
        result = _feedback_link_error(
            resolve_status, plan.get("plan_id"), _link_error)
        result["verdict"] = verdict
        return result
    try:
        mark_plan_resolved(sd, plan.get("plan_id"),
                           resolve_status, by_entry=by_entry,
                           level=_review_plan_level(plan))
    except _PLAN_STORE_ERRORS as exc:
        result = _plan_resolution_error(
            resolve_status, plan.get("plan_id"), exc)
        result.update({"verdict": verdict,
                       "linked_entries_resolved": _linked})
        return result
    return {"status": resolve_status, "reason": reason,
            "verdict": verdict,
            "linked_entries_resolved": _linked}
def _inject_feedback_source(plan: dict, review: dict, fixed_source: str) -> None:
    if not (review.get("requires_fixed_source") and fixed_source):
        return
    entry = plan.get("entry")
    if not isinstance(entry, dict):
        entry = {}
        plan["entry"] = entry
    entry["fixed_source"] = fixed_source
def _feedback_regression_status(applied: bool, mod: Any) -> str:
    if regression_undecided(mod):
        return "error"
    regression_passed = getattr(mod, "regression_passed", None)
    if regression_passed is False:
        return "failed"
    if regression_passed is None:
        return "not_run"
    return "passed" if applied else "not_run"
def _feedback_apply_fix(sd: str, plan: dict, review: dict, fixed_source: str,
                        by_entry: tuple[str, str] | None,
                        review_info: dict | None) -> dict:
    router = CodeLevelFeedbackRouter(sd)
    _inject_feedback_source(plan, review, fixed_source)
    if review_info and isinstance(plan.get("entry"), dict):
        plan["entry"].update(review_info)
    mod = router.apply_approved_fix(plan)
    applied = bool(getattr(mod, "applied", False))
    regression_status = _feedback_regression_status(applied, mod)
    _err_msg = as_str(getattr(mod, "error_message", ""))
    result = {
        "status": "approved_fixed",
        "linked_entries_resolved": 0,
        "reason": _err_msg or str(getattr(mod, "action_type", "") or ""),
        "targeted_regression": {
            "status": regression_status,
            "summary": _err_msg[:160],
        },
        "fix_evidence": (mod.to_dict() if hasattr(mod, "to_dict") else {}),
    }
    if not applied:
        logger.warning(
            "[AIReview] feedback 修复执行未生效，保留计划与关联条目: %s (%s)",
            plan.get("plan_id"), _err_msg or "applied=False")
        result.update({
            "status": "failed",
            "review_retained": True,
            "next_action": ("resubmit_fixed_source"
                            if review.get("requires_fixed_source")
                            else "retry_review"),
        })
        return result
    if regression_status in ("failed", "error"):
        logger.warning(
            "[AIReview] feedback 修复定向回归%s，保留计划与关联条目: %s",
            "失败" if regression_status == "failed" else "未定论",
            plan.get("plan_id"))
        result.update({
            "status": regression_status,
            "review_retained": True,
            "next_action": ("resubmit_fixed_source"
                            if review.get("requires_fixed_source")
                            else "retry_review"),
        })
        return result
    resolve_status = "applied"
    _linked, _link_error = _link_resolve_entry(
        sd, plan, resolve_status, review_info=review_info)
    if _link_error is not None:
        result.update(_feedback_link_error(
            resolve_status, plan.get("plan_id"), _link_error))
        return result
    try:
        mark_plan_resolved(
            sd, plan.get("plan_id"), resolve_status, by_entry=by_entry,
            level=_review_plan_level(plan))
    except _PLAN_STORE_ERRORS as exc:
        result.update(_plan_resolution_error(
            resolve_status, plan.get("plan_id"), exc))
        result["linked_entries_resolved"] = _linked
        return result
    result["linked_entries_resolved"] = _linked
    return result
def _enhancement_status(verdict: str, approved: bool) -> str:
    if verdict in ("reject", "reject_as_fp"):
        return "rejected"
    if verdict == "defer":
        return "deferred"
    return "applied" if approved else "rejected"
def _enhancement_effective_status(status: str, res: dict,
                                  target: str, description: str) -> str:
    error = as_str(res.get("error"))
    if error:
        logger.warning(
            "[AIReview] enhancement_log 读写失败，保留审核与关联计划: "
            "target=%r description=%r error=%s", target, description, error)
        return "failed"
    if res.get("file_marked"):
        return status
    logger.warning(
        "[AIReview] enhancement 条目未找到（已消费或匹配键不一致），"
        "不虚报终态 %s: target=%r description=%r",
        status, target, description)
    return "already_absent"
def apply_enhancement_verdict(sd: str, review: dict, fixed_source: str, approved: bool,
                       assessment: dict | None = None) -> dict:
    if provided_source(fixed_source):
        logger.warning(
            "[AIReview] enhancement 通道不写源码，已忽略 fixed_source(%d 字符): "
            "target=%r", len(fixed_source), review.get("target"))
    assessment = as_dict(assessment)
    _verdict = verdict_text(assessment)
    resolve_status = _enhancement_status(_verdict, approved)
    _bt = as_str(review.get("target"))
    _bd = as_str(review.get("description"))
    _review_info = _build_review_info(_verdict, assessment)
    _source_entry = as_dict(review.get("entry"))
    _entry_filter = (_review_level_filter(_review_entry_level(_source_entry))
                     if _source_entry else None)
    res = mark_enhancement_applied(
        sd, _bt, _bd, status=resolve_status, review_info=_review_info,
        entry_filter=_entry_filter)
    status = _enhancement_effective_status(resolve_status, res, _bt, _bd)
    _linked = 0
    result_verdict = _verdict or ("approve" if approved else "reject")
    if status != "failed" and (_bt or _bd):
        try:
            _linked = mark_plan_resolved(
                sd, None, resolve_status, by_entry=(_bt, _bd),
                level=(_review_entry_level(_source_entry)
                       if _source_entry else ""))
        except _PLAN_STORE_ERRORS as exc:
            result = _enhancement_result(status, res, result_verdict, 0)
            result.update(_plan_resolution_error(status, None, exc))
            return result
    return _enhancement_result(status, res, result_verdict, _linked)
def _enhancement_result(status: str, res: dict, verdict: str,
                        linked: int) -> dict:
    _result = {"status": status,
               "file_marked": res.get("file_marked", False),
               "verdict": verdict,
               "linked_plans_resolved": linked}
    if status == "failed":
        _result.update({
            "reason": as_str(res.get("error")) or "enhancement_log 读写失败",
            "review_retained": True,
            "next_action": "retry_review",
        })
    elif status == "rejected":
        _result["reason"] = "AI 判定不采纳"
    elif status == "deferred":
        _result["reason"] = "AI 审核后暂缓处理"
    elif status == "already_absent":
        _result["reason"] = ("enhancement_log 中未找到该条目（已消费或匹配键不一致）："
                             "未标记、不产出记忆操作")
    else:
        _result["memory_operation"] = res.get("memory_operation")
    return _result
def _plan_item_idem_fields(item: dict) -> tuple[str, str, int]:
    return (
        _identity_text(item.get("rule_id")),
        _identity_text(item.get("file")),
        normalize_line_no(item.get("line", 0)),
    )
def _build_plan_entry(
    item: dict, prefix: str, seq: int, key: tuple[str, str, int]
) -> dict:
    rule_id, file_path, line = key
    return {
        "plan_id": f"{prefix}-{seq:03d}",
        "status": _PENDING_PLAN_STATUS,
        "rule_id": rule_id,
        "severity": normalize_text(item.get("severity")),
        "file": file_path,
        "line": line,
        "message": normalize_text(item.get("message")),
        "suggestion": normalize_text(item.get("suggestion")),
        "created_at": time.strftime(FMT_DATETIME_ISO),
    }
def _append_new_plan_items(
    plans: list, items: list, existing: set, prefix: str
) -> int:
    added = 0
    seq = max_review_seq(plans, prefix, id_key="plan_id")
    for item in items:
        if not isinstance(item, dict):
            continue
        key = _plan_item_idem_fields(item)
        if key in existing:
            continue
        existing.add(key)
        seq += 1
        plans.append(_build_plan_entry(item, prefix, seq, key))
        added += 1
    return added
def enqueue_plan_items(
    skill_dir: str, plan_name: str, prefix: str, items: list[dict]
) -> dict:
    if (not isinstance(plan_name, str) or not plan_name.strip()
            or plan_name in (".", "..") or "\0" in plan_name
            or "/" in plan_name or "\\" in plan_name
            or os.path.isabs(plan_name) or os.path.splitdrive(plan_name)[0]):
        raise ValueError("plan_name 必须是临时产物根内的简单文件名")
    items = as_item_list(items, log_tag="[AIReview]")
    plan_file = json_artifact_path(_queue_skill_dir(skill_dir), plan_name)
    ensure_plan_dir(plan_file)
    with _required_plan_lock(plan_file):
        data, plans = _load_plan_queue(plan_file, "plans")
        existing = {
            _plan_item_idem_fields(p)
            for p in plans
            if (is_pending_plan(p)
                and isinstance(p.get("plan_id"), str)
                and p["plan_id"].strip())
        }
        added = _append_new_plan_items(plans, items, existing, prefix)
        if added:
            write_queue_json(plan_file, data)
            logger.info("[AIReview] %s 入队 %d 项待审建议", plan_name, added)
        return {"status": "ok", "enqueued": added, "total": len(plans)}
_ENHANCEMENT_ACTION_TYPE_KEYS = ("action_type", "type")
def _enhancement_action_type(enh: dict) -> str:
    for key in _ENHANCEMENT_ACTION_TYPE_KEYS:
        value = enh.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip().lower()
    return ""
def build_auto_enhancement_report(
    *,
    applied: int = 0,
    proposed: int = 0,
    skipped: int = 0,
    deferred: int = 0,
    adjustments: dict | None = None,
    enqueue: dict | None = None,
    fanout: dict | None = None,
) -> dict:
    return {
        "applied": applied,
        "proposed": proposed,
        "skipped": skipped,
        "deferred": deferred,
        "adjustments": adjustments or {},
        "ai_review_enqueue": enqueue or {"status": "no_new", "enqueued": 0},
        "fanout_governance": fanout or {},
    }
def _register_method_multiplier(frag: dict, report: dict) -> tuple[int, int]:
    _status = report.get("status")
    # 历史记录里的 fail 是「诊断结论未通过（P0）」，方法已完整产出，
    # 不对其 findings 施加置信度乘子。
    if isinstance(_status, str) and _status.strip().lower() in (
            "fail", "failed"):
        _status = "warn"
    bucket = method_status_bucket(_status)
    if bucket == "failed":
        mid = _identity_text(report.get("method_id"))
        if mid:
            multipliers = frag.setdefault(FIELD_METHOD_CONFIDENCE_MULTIPLIERS, {})
            if mid not in multipliers:
                multipliers[mid] = 0.8
                return 1, 0
        return 0, 0
    if bucket == "skipped":
        return 0, 1
    return 0, 0
def _ae_method_multiplier_channel(stages: dict) -> tuple[dict, int, int]:
    applied = 0
    skipped = 0
    frag: dict = {}
    stage1 = dict_or_empty(stages.get("stage1", {}))
    reports = as_list(stage1.get(FIELD_INTERMEDIATE_REPORTS))
    for report in reports:
        if not isinstance(report, dict):
            continue
        added, skip = _register_method_multiplier(frag, report)
        applied += added
        skipped += skip
    return frag, applied, skipped
def _ae_cv_threshold_channel(cv_report: dict) -> tuple[dict, int, int]:
    cv_report = dict_or_empty(cv_report)
    cv_suppressed = as_pure_count(cv_report.get(FIELD_FINDINGS_SUPPRESSED, 0))
    cv_total = as_pure_count(cv_report.get(FIELD_TOTAL_INPUT_FINDINGS, 0))
    if cv_total > 0:
        suppression_rate = cv_suppressed / cv_total
        if suppression_rate > 0.5:
            return {FIELD_CV_CONFIDENCE_THRESHOLDS: {"global_confirm": 0.80}}, 1, 0
        if suppression_rate < 0.05 and cv_total > 20:
            return {FIELD_CV_CONFIDENCE_THRESHOLDS: {"global_confirm": 0.65}}, 1, 0
        return {}, 0, 1
    return {}, 0, 1
def _override_target_key(entry: dict) -> str:
    for _key in ("rule_id", "fixer_type"):
        _v = _identity_text(entry.get(_key))
        if _v:
            return _v
    return ""
def _ae_rolled_back_targets(stage4: dict) -> list[str]:
    targets: list[str] = []
    for entry in as_list(stage4.get("items")):
        if not isinstance(entry, dict) or entry.get("status") != "rolled_back":
            continue
        _k = _override_target_key(entry)
        if _k and _k not in targets:
            targets.append(_k)
    for detail_key in ("item_details", "details"):
        for entry in as_list(stage4.get(detail_key)):
            if not isinstance(entry, dict) or entry.get("status") != "rolled_back":
                continue
            _detail = entry.get("detail")
            _k = _override_target_key(
                _detail if isinstance(_detail, dict) else entry)
            if _k and _k not in targets:
                targets.append(_k)
    return targets
def _ae_fixer_safety_channel(stages: dict) -> tuple[dict, int, int]:
    stage4 = dict_or_empty(stages.get("stage4", {}))
    rollback_count = as_pure_count(stage4.get("rolled_back", 0))
    executed_count = as_pure_count(stage4.get("executed", 0))
    if executed_count <= 0:
        return {}, 0, 0
    if rollback_count <= 0:
        return {}, 0, 1
    rollback_rate = rollback_count / executed_count
    if rollback_rate <= 0.2:
        return {}, 0, 1
    targets = _ae_rolled_back_targets(stage4)
    if not targets:
        logger.warning(
            "[Stage6d] 回滚率 %.0f%%(%d/%d) 超阈值，但 stage4 回滚项缺 rule_id"
            "，不产出无消费端的全局键",
            rollback_rate * 100, rollback_count, executed_count)
        return {}, 0, 1
    overrides = {
        _t: {"auto_safe": False,
             "reason": (f"历史回滚：回滚率 {rollback_count}/{executed_count}"
                        f"（{rollback_rate:.0%}）超 20% 稳态线，"
                        "该项禁止 auto_safe 直修，需 AI 审核")}
        for _t in targets
    }
    return {"fixer_safety_overrides": overrides}, 1, 0
_DEFERRED_ENHANCEMENT_TYPES = frozenset(("manual", "structural"))
def _is_deferred_enhancement(enh: Any) -> bool:
    return (isinstance(enh, dict)
            and _enhancement_action_type(enh) in _DEFERRED_ENHANCEMENT_TYPES
            and not signal_bool(enh.get("applied")))
def _ae_deferred_channel(review_result: dict) -> int:
    review_result = dict_or_empty(review_result)
    if not review_result:
        return 0
    enhancements = as_list(review_result.get("enhancement_actions"))
    return sum(1 for enh in enhancements if _is_deferred_enhancement(enh))
def _ae_enqueue_channel(skill_dir: str, adjustments: dict) -> dict:
    if not adjustments:
        return {"status": "no_new", "enqueued": 0}
    try:
        enq = enqueue_adjustment_proposals(
            skill_dir,
            muls=adjustments.get(FIELD_METHOD_CONFIDENCE_MULTIPLIERS),
            cvs=adjustments.get(FIELD_CV_CONFIDENCE_THRESHOLDS),
            fixs=adjustments.get("fixer_safety_overrides"),
            reason="Stage6 自适应增强产出，待 AI 审核执行",
        )
        logger.info(
            "[Stage6] [AI审核] 调整建议已入队 %d 条 —— 待 AI 审核并执行生效 (next_action=%s)",
            enq.get("enqueued", 0), enq.get("next_action"))
        return enq
    except Exception as _eq_err:
        logger.warning("[Stage6] 调整建议入队失败: %s", _eq_err)
        return {"status": "error", "enqueued": 0,
                "error": str(_eq_err)[:500]}
def run_stage6d_auto_enhancements(skill_dir: str, stages: dict,
                                  review_result: dict, cv_report: dict,
                                  fanout_signal: dict | None = None) -> dict:
    stages = dict_or_empty(stages)
    mul_adj, mul_proposed, mul_skipped = _ae_method_multiplier_channel(stages)
    cv_adj, cv_proposed, cv_skipped = _ae_cv_threshold_channel(cv_report)
    fix_adj, fix_proposed, fix_skipped = _ae_fixer_safety_channel(stages)
    deferred = _ae_deferred_channel(review_result)
    adjustments = {**mul_adj, **cv_adj, **fix_adj}
    enq = _ae_enqueue_channel(skill_dir, adjustments)
    return build_auto_enhancement_report(
        applied=0,
        proposed=mul_proposed + cv_proposed + fix_proposed,
        skipped=mul_skipped + cv_skipped + fix_skipped,
        deferred=deferred,
        adjustments=adjustments,
        enqueue=enq,
        fanout=dict_or_empty(fanout_signal),
    )
_PENDING_ENTRY_STATUSES = frozenset(("pending",))
_COORDINATOR_DEFERRED_ENTRY_STATUSES = frozenset(("coordinator_deferred",))
def _load_pending_entries_strict(
    skill_dir: str, *, statuses=_PENDING_ENTRY_STATUSES
) -> list[dict]:
    try:
        data = read_evolution_state(
            skill_dir, for_update=True).get("enhancement_log")
    except (OSError, ValueError, TypeError) as exc:
        raise RuntimeError(f"deferred 门禁读取失败: {exc}") from exc
    if data is None:
        return []
    if isinstance(data, list):
        entries = data
    elif isinstance(data, dict):
        entries = data.get("entries", [])
        if not isinstance(entries, list):
            raise RuntimeError(
                "deferred 门禁读取失败(invalid_entries): "
                f"entries 须为 list，实际为 {type(entries).__name__}")
    else:
        raise RuntimeError(
            "deferred 门禁读取失败(invalid_root): "
            f"顶层须为 dict/list，实际为 {type(data).__name__}")
    return [entry for entry in entries
            if isinstance(entry, dict) and entry.get("status") in statuses]
def _restore_entry_key(entry: dict) -> tuple[str, str, str]:
    return (
        str_or(entry.get("target")),
        str_or(entry.get("description")),
        str_or(route_entry(entry).get("level")),
    )
def _restore_deferred_entries(router, deferred: list) -> None:
    if not deferred:
        return
    for entry in deferred:
        try:
            router.update_entry_status(
                entry, "pending", from_status="coordinator_deferred")
        except Exception as restore_err:
            logger.warning("[Stage6c] deferred条目恢复失败: %s", restore_err,
                           exc_info=True)
    expected = Counter(_restore_entry_key(entry) for entry in deferred)
    pending_keys = Counter(
        _restore_entry_key(entry)
        for entry in _load_pending_entries_strict(router.skill_dir))
    remaining_keys = Counter(
        _restore_entry_key(entry)
        for entry in _load_pending_entries_strict(
            router.skill_dir,
            statuses=_COORDINATOR_DEFERRED_ENTRY_STATUSES))
    missing = expected - pending_keys
    still_deferred = expected & remaining_keys
    if missing or still_deferred:
        raise RuntimeError(
            f"deferred 条目恢复未持久化（缺 pending {sum(missing.values())} 条，"
            f"仍隔离 {sum(still_deferred.values())} 条），下一轮将重试恢复")
@contextmanager
def coordinator_deferred_gate(router, coordinator):
    deferred = []
    stale = _load_pending_entries_strict(
        router.skill_dir,
        statuses=_COORDINATOR_DEFERRED_ENTRY_STATUSES)
    if stale:
        _restore_deferred_entries(router, stale)
    try:
        for entry in _load_pending_entries_strict(
                router.skill_dir):
            verdict, _reason = coordinator.evaluate(entry)
            if verdict != Verdict.ALLOW:
                deferred.append(entry)
                router.update_entry_status(entry, "coordinator_deferred")
        if deferred:
            pending_after = _load_pending_entries_strict(
                router.skill_dir)
            not_deferred = [entry for entry in deferred if entry in pending_after]
            if not_deferred:
                raise RuntimeError(
                    f"{len(not_deferred)} 条 deferred 条目隔离未持久化，"
                    "中止代码级反哺规划")
        yield deferred
    finally:
        _restore_deferred_entries(router, deferred)
def code_feedback_report(code_fb_result: dict) -> dict:
    if not isinstance(code_fb_result, dict):
        code_fb_result = {
            "status": "error",
            "message": ("code_feedback_result 须为 dict，实际: "
                        f"{type(code_fb_result).__name__}"),
        }
    elif (not isinstance(code_fb_result.get("status"), str)
          or not code_fb_result["status"].strip()):
        code_fb_result = {
            **code_fb_result,
            "status": "error",
            "message": (code_fb_result.get("message")
                        or "code_feedback_result 缺 status 或状态值为空白"),
        }
    status = code_fb_result["status"]
    message = code_fb_result.get("message", "")
    return {
        "total_processed": code_fb_result.get("total", 0),
        "plans": code_fb_result.get("plans", []),
        "plan_file": code_fb_result.get("plan_file", ""),
        "status": status,
        "message": message,
        "l1_applied": 0, "l2_applied": 0, "l3_applied": 0,
        "l4_applied": 0, "skipped": 0,
        "errors": [message] if status == "error" and message else [],
    }
def stage_code_feedback(result: dict) -> dict:
    if not isinstance(result, dict):
        return {}
    view = result.get(FIELD_CODE_LEVEL_FEEDBACK)
    return view if isinstance(view, dict) else {}
def apply_code_level_feedback_step(skill_dir: str, result: dict) -> None:
    try:
        coordinator = FeedbackCoordinator(skill_dir)
        coordinator.reload_runtime_adjustments()
        router = CodeLevelFeedbackRouter(skill_dir)
        with coordinator_deferred_gate(router, coordinator) as deferred:
            coordinator.save_state()
            coord_report = coordinator.get_report()
            result["coordinator_report"] = {
                "total_evaluated": coord_report.total_evaluated,
                "allowed": coord_report.allowed,
                "deferred": coord_report.deferred,
                "frozen": coord_report.frozen,
                "conflicts": coord_report.conflicts,
                "new_conflicts": coord_report.new_conflicts,
                "blocked_by_verdict": len(deferred),
            }
            code_fb_result = run_code_level_feedback(
                skill_dir=skill_dir, max_items=_PLAN_COLLECT_MAX_ITEMS)
            result[FIELD_CODE_LEVEL_FEEDBACK] = code_feedback_report(
                code_fb_result)
    except Exception as e:
        logger.warning("[Stage6c] 代码级反哺跳过: %s", e, exc_info=True)
        result[FIELD_CODE_LEVEL_FEEDBACK] = {
            "error": str(e)[:200], "status": "skipped"}
def code_feedback_phase_payload(result: dict) -> dict:
    _fb = stage_code_feedback(result)
    return {
        "completed_at": timestamp_human(),
        "code_feedback_l1": _fb.get("l1_applied", 0),
        "code_feedback_l2": _fb.get("l2_applied", 0),
        "code_feedback_l3": _fb.get("l3_applied", 0),
    }

from __future__ import annotations

import hashlib
import logging
import math
import os
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_guard_state import (
    max_review_seq,
    read_queue_json,
    write_queue_json,
)
from jwsgj.diag_types_normalize import (
    as_item_list,
    elapsed_seconds,
    normalize_severity_rank,
    now_iso,
    parse_locator_file,
    plan_index,
)
from jwsgj.fix_guide_rule_identity import (
    SECURITY_FAMILY_UNION,
    is_family_member,
    make_locator,
    make_locator_from_finding,
    normalize_rule,
)
from jwsgj.fp_rules_judge import (
    DEFAULT_SEVERITY,
    finding_line_no,
    is_known_fp,
    norm_rule_key,
)
from jwsgj.log_config import locked_artifact, log_swallowed
from jwsgj.runtime_paths import (
    cv_uncertain_path,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.treatment_state import (
    TREATMENT_TERMINAL_STATUSES,
    canonical_locator_key,
    confirmed_real_locators,
    item_index,
    item_status,
    load_treatment_state,
    mark_item_fp_confirmed,
    open_confirm_store,
    save_treatment_state,
)

__all__ = [
    'FP_PREFILTER_MISS',
    'REVIEW_ID_PREFIX',
    'FpPrefilterOutcome',
    'FpPrefilterPartition',
    'append_report_error',
    'apply_fp_prefilter',
    'apply_step_fp_prefilter',
    'build_uncertain_entry',
    'enqueue_cv_uncertain',
    'enqueue_fp_prefilter_review',
    'partition_fp_prefiltered',
    'reconcile_cv_uncertain_after_llm',
    'review_entry_key',
    'run_uncertain_enqueue_channel',
]
logger = logging.getLogger(__name__)
def _text(value) -> str:
    if isinstance(value, str):
        return value
    try:
        raw = os.fspath(value)
    except TypeError:
        return ""
    if isinstance(raw, bytes):
        try:
            raw = os.fsdecode(raw)
        except (UnicodeDecodeError, TypeError) as _decode_exc:
            log_swallowed(__name__, _decode_exc, context='_text:fsdecode')
            return ""
    return raw if isinstance(raw, str) else ""
logger.info("ai_review_queue 已加载: %d 项导出", len(__all__))
REVIEW_ID_PREFIX = "CVU"
_FP_REVIEW_PREFIX = "CVU-FP"
def _read_review_queue_for_update(path: str) -> list:
    data = read_queue_json(path, {"entries": []}, for_update=True)
    entries = data.get("entries", [])
    if not isinstance(entries, list):
        raise TypeError(
            "cv_uncertain 队列 entries 字段类型不符"
            f"({type(entries).__name__}，期望 list)，拒绝覆盖: {path}")
    return entries
def build_uncertain_entry(xvr: dict) -> dict | None:
    if not isinstance(xvr, dict):
        return None
    sig = _extract_review_signals(xvr)
    if sig["human_verdict"] in ("confirmed", "false_positive"):
        return None
    flags = _resolve_review_flags(xvr, sig)
    if not _needs_review_entry(sig, flags):
        return None
    return _build_review_entry_payload(xvr, sig, flags)
def _normalize_conclusion_text(value: object) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _effective_conclusion_text(xvr: dict) -> str:
    conclusion = _normalize_conclusion_text(xvr.get("conclusion_v2"))
    return conclusion or _normalize_conclusion_text(xvr.get("conclusion"))
def _infra_degraded_flag(xvr: dict) -> bool:
    return bool(
        xvr.get("_cv_skipped_placeholder") or xvr.get("_oscillating")
        or xvr.get("_cross_locator_contradiction")
        or xvr.get("_evidence_chain_broken"))
def _independent_single_source(xvr: dict, sources: list) -> bool:
    count = xvr.get("_independent_source_count")
    if isinstance(count, int) and not isinstance(count, bool):
        return count <= 1
    return len(sources) <= 1
def _extract_review_signals(xvr: dict) -> dict:
    sources_raw = xvr.get("sources")
    sources = sources_raw if isinstance(sources_raw, list) else []
    sev = _text(xvr.get("severity")).upper()
    return {
        "concl": _effective_conclusion_text(xvr),
        "infra_flag": _infra_degraded_flag(xvr),
        "sev": sev,
        "fam": _text(xvr.get("rule_family")) or _text(xvr.get("rule_id")),
        "sources": sources,
        "is_single_source": _independent_single_source(xvr, sources),
        "sev_high": normalize_severity_rank(sev) <= 1,
        "human_verdict": xvr.get("_human_verdict"),
    }
def _resolve_review_flags(xvr: dict, sig: dict) -> dict:
    legacy_concl = _normalize_conclusion_text(xvr.get("conclusion"))
    single_confirmed = (
        sig["concl"] == "confirmed" and sig["sev_high"] and sig["is_single_source"]
    )
    sec_forced = sig["sev_high"] and (
        is_family_member(sig["fam"], SECURITY_FAMILY_UNION)
        or is_family_member(
            _text(xvr.get("rule_id")), SECURITY_FAMILY_UNION))
    suppressed_forced = "suppressed" in (sig["concl"], legacy_concl)
    review_flagged = bool(xvr.get("_review_required"))
    preserved_from_suppressed = bool(
        xvr.get("_preserved_from_suppressed"))
    fp_filter_suppressed = bool(xvr.get("_suppressed_by_fp_filter"))
    investigated_forced = sig["sev_high"] and "investigated" in (
        sig["concl"], legacy_concl)
    forced_review = (
        suppressed_forced or review_flagged or investigated_forced
        or preserved_from_suppressed)
    return {
        "single_confirmed": single_confirmed,
        "sec_forced": sec_forced,
        "suppressed_forced": suppressed_forced,
        "review_flagged": review_flagged,
        "preserved_from_suppressed": preserved_from_suppressed,
        "fp_filter_suppressed": fp_filter_suppressed,
        "investigated_forced": investigated_forced,
        "forced_review": forced_review,
    }
def _review_triggered(sig: dict, flags: dict) -> bool:
    return bool(sig["infra_flag"] or flags["forced_review"]
                or flags["single_confirmed"] or flags["sec_forced"])
def _needs_review_entry(sig: dict, flags: dict) -> bool:
    if _review_triggered(sig, flags):
        return True
    return (sig["concl"] in ("uncertain", "contradictory")
            and sig["sev_high"])
def _review_counter_evidence(inner: list) -> tuple[bool, list[str]]:
    _ce_hit = False
    _ce_reasons: list[str] = []
    counter_entries = filter(
        lambda fd: isinstance(fd, dict) and fd.get("_counter_evidence"), inner)
    for _fd in counter_entries:
        _ce_hit = True
        _raw_reasons = _fd.get("_counter_evidence_reasons")
        if isinstance(_raw_reasons, list):
            _ce_reasons.extend(_text(_reason)[:100] for _reason in _raw_reasons)
    return _ce_hit, _ce_reasons
def _suppression_evidence_entry(fd: dict) -> dict | None:
    ctx = fd.get("context_enrichment")
    if not isinstance(ctx, dict):
        return None
    cov_ctx = ctx.get("coverage_context")
    if not (isinstance(cov_ctx, dict) and cov_ctx):
        return None
    return {
        "source_method": _text(fd.get("_source_method"))[:60],
        "file_coverage": cov_ctx.get("file_coverage"),
        "risk": _text(cov_ctx.get("risk"))[:200],
    }
def _evidence_detail_entry(fd: dict) -> dict:
    return {
        "source_method": _text(fd.get("_source_method"))[:60],
        "confidence": fd.get("confidence", 0),
        "rule_id": _text(fd.get("rule_id"))[:40],
    }
def _review_evidence_details(inner: list) -> tuple[list[dict], list[dict]]:
    _supp_evidence: list[dict] = []
    _ev_detail: list[dict] = []
    for _fd in inner:
        if not isinstance(_fd, dict):
            continue
        _supp = _suppression_evidence_entry(_fd)
        if _supp is not None:
            _supp_evidence.append(_supp)
        _ev_detail.append(_evidence_detail_entry(_fd))
    return _supp_evidence, _ev_detail
def _inner_findings(xvr: dict) -> list:
    inner = xvr.get("findings")
    return inner if isinstance(inner, list) else []
def _suppression_rule_text(xvr: dict) -> str:
    for _key in ("_suppression_rule", "rule_applied", "rule_id"):
        _txt = _text(xvr.get(_key))
        if _txt:
            return _txt
    return ""
def _conclusion_params_dict(xvr: dict) -> dict:
    params = xvr.get("_conclusion_params")
    if not isinstance(params, dict):
        return {}
    return {str(k): v for k, v in params.items()}
def _sample_message_of(xvr: dict) -> str:
    _sample = xvr.get("sample_finding")
    if isinstance(_sample, dict):
        _msg = _sample.get("message")
        if isinstance(_msg, str) and _msg.strip():
            return _msg
    for _fd in _inner_findings(xvr):
        if isinstance(_fd, dict):
            _msg = _fd.get("message")
            if isinstance(_msg, str) and _msg.strip():
                return _msg
    return ""
def _entry_message(xvr: dict) -> str:
    for _key in ("message", "summary"):
        _txt = _text(xvr.get(_key))
        if _txt.strip():
            return _txt
    return _sample_message_of(xvr)
def _entry_confidence(xvr: dict):
    for _key in ("confidence", "adjusted_confidence", "base_confidence"):
        if _key in xvr and xvr[_key] is not None:
            return xvr[_key]
    return 0
def _inner_rows_of(finding: dict) -> list:
    _rows = finding.get("findings")
    if isinstance(_rows, list) and _rows:
        return _rows
    return [finding]
def _record_coords(record: dict) -> tuple[str, int]:
    file_path = _text(record.get("file_path")) or _text(record.get("file"))
    if not file_path:
        file_path = _text(parse_locator_file(record.get("locator")))
    return file_path, finding_line_no(record)
def _record_family(record: dict) -> str:
    return _text(record.get("rule_family")) or _text(record.get("rule_id"))
def _build_review_entry_payload(xvr: dict, sig: dict, flags: dict) -> dict:
    _inner = _inner_findings(xvr)
    _ce_hit, _ce_reasons = _review_counter_evidence(_inner)
    _supp_evidence, _ev_detail = _review_evidence_details(_inner)
    _file_path, _line = _record_coords(xvr)
    _suppressed_details = xvr.get("_suppressed_details")
    _locator = _text(xvr.get("locator")) or make_locator(
        _file_path, _line, _record_family(xvr))
    return {
        "review_id": "",
        "channel": "cv_uncertain",
        "locator": _locator,
        "file_path": _file_path,
        "line": _line,
        "rule_id": _text(xvr.get("rule_id")),
        "rule_family": _text(xvr.get("rule_family")),
        "severity": sig["sev"],
        "conclusion": sig["concl"],
        "confidence": _entry_confidence(xvr),
        "single_source_confirmed": flags["single_confirmed"],
        "forced_security": flags["sec_forced"],
        "suppressed_review": flags["suppressed_forced"],
        "suppression_rule": _suppression_rule_text(xvr),
        "preserved_from_suppressed": flags["preserved_from_suppressed"],
        "fp_filter_suppressed": flags["fp_filter_suppressed"],
        "review_flagged": flags["review_flagged"],
        "aggregate_review": bool(xvr.get("_aggregate_review")),
        "suppressed_count": max(
            0, plan_index(xvr.get("_suppressed_count")) or 0),
        "suppressed_details": (list(_suppressed_details)
                               if isinstance(_suppressed_details, list) else []),
        "investigated_review": flags["investigated_forced"],
        "suppression_evidence": _supp_evidence[:5],
        "evidence_detail": _ev_detail[:10],
        "conclusion_params": _conclusion_params_dict(xvr),
        "message": _entry_message(xvr)[:400],
        "code_context": _text(xvr.get("code_context"))[:800],
        "sources": [str(s)[:60] for s in sig["sources"]][:8],
        "evidence_strength": xvr.get("evidence_strength", 0.0),
        "adjusted_confidence": xvr.get("adjusted_confidence", 0.0),
        "notes": _text(xvr.get("notes"))[:300],
        "counter_evidence": _ce_hit,
        "counter_evidence_reasons": _ce_reasons[:5],
        "status": "pending_review",
    }
def _canonical_queue_locator(locator: object) -> str:
    _key = canonical_locator_key(locator)
    if not _key:
        return _key
    _parts = _key.rsplit(":", 2)
    if len(_parts) != 3:
        return _key
    _head, _line_slot, _family = _parts
    if not _family.strip():
        return _key
    _normalized = normalize_rule(_family)
    if not _normalized or _normalized == _family:
        return _key
    return f"{_head}:{_line_slot}:{_normalized}"
def review_entry_key(e: dict) -> tuple:
    _locator = _canonical_queue_locator(e.get("locator"))
    if not _locator:
        _locator = _canonical_queue_locator(make_locator_from_finding(e))
    return (_locator, str(e.get("rule_id") or "").strip())
def _is_rejected_history(entry: object) -> bool:
    return (isinstance(entry, dict)
            and entry.get("status") == "resolved"
            and entry.get("ai_verdict") == "rejected")
def _rejected_history_keys(old_entries: list) -> set:
    return {review_entry_key(e) for e in old_entries
            if _is_rejected_history(e)}
def _aggregate_series_key(entry: object) -> tuple[str, str] | None:
    if (not isinstance(entry, dict) or not entry.get("aggregate_review")):
        return None
    _locator = _text(entry.get("locator"))
    _rule_id = _text(entry.get("rule_id"))
    _prefix = f"{_AGGREGATE_LOCATOR_PREFIX}:{_rule_id}:"
    if not _locator.startswith(_prefix):
        return None
    _category, _sep, _fingerprint = _locator[len(_prefix):].partition(":")
    if not _sep or not _category:
        return None
    return _rule_id, _category
def _is_fp_snapshot_entry(entry: object) -> bool:
    return (isinstance(entry, dict)
            and _effective_conclusion_text(entry) != "fp_prefilter"
            and (_aggregate_series_key(entry) is not None
                 or bool(entry.get("fp_filter_suppressed"))))
def _supersede_stale_fp_snapshots(
        old_entries: list, candidates: list,
        complete_snapshot: bool) -> None:
    _candidate_keys = {
        review_entry_key(e) for e in candidates if isinstance(e, dict)}
    _series = {
        _key for e in candidates
        if (_key := _aggregate_series_key(e)) is not None}
    if not _series and not complete_snapshot:
        return
    for _old in old_entries:
        if (not isinstance(_old, dict)
                or _old.get("status") != "pending_review"):
            continue
        _old_series = _aggregate_series_key(_old)
        _in_snapshot = (_is_fp_snapshot_entry(_old) if complete_snapshot
                        else _old_series is not None and _old_series in _series)
        if not _in_snapshot or review_entry_key(_old) in _candidate_keys:
            continue
        _old["status"] = "superseded"
        _old["resolved_at"] = now_iso()
        _old["superseded_reason"] = (
            "FP抑制残留成员、分页或存在性已变化，以最新快照为准")
def _queue_dedupe_keys(old_entries: list) -> tuple[set, set]:
    _pending_keys: set = set()
    for e in old_entries:
        if isinstance(e, dict) and e.get("status") == "pending_review":
            _pending_keys.add(review_entry_key(e))
    return _pending_keys, _rejected_history_keys(old_entries)
def _keep_mergeable_old_entry(entry: object, new_keys: set) -> bool:
    if not isinstance(entry, dict):
        return False
    if entry.get("status") != "pending_review":
        return True
    return review_entry_key(entry) not in new_keys
def _merge_pending_snapshot(old_entries: list, entries: list,
                            skipped: dict | None,
                            review_prefix: str,
                            complete_aggregate_snapshot: bool,
                            ) -> tuple[int, int]:
    _supersede_stale_fp_snapshots(
        old_entries, entries, complete_snapshot=complete_aggregate_snapshot)
    seq_floor = max_review_seq(old_entries, review_prefix)
    pending_keys, rejected_keys = _queue_dedupe_keys(old_entries)
    new_keys = set()
    unique_entries = []
    for entry in entries:
        if not isinstance(entry, dict):
            logger.debug("跳过非 dict 复核候选: %s", type(entry).__name__)
            continue
        key = review_entry_key(entry)
        if key in rejected_keys:
            if skipped is not None:
                skipped["skipped_history_rejected"] = (
                    skipped.get("skipped_history_rejected", 0) + 1)
            continue
        if key in new_keys or key in pending_keys:
            continue
        new_keys.add(key)
        unique_entries.append(entry)
    added = len(unique_entries)
    entries[:] = unique_entries
    kept = [e for e in old_entries if _keep_mergeable_old_entry(e, new_keys)]
    if kept:
        entries[:0] = kept
        logger.info(
            "[ChannelLoop2] cv_uncertain 队列合并: 保留上一轮未复核条目与"
            " AI 否决历史 %d 条（否决历史供跨轮去重，封顶 %d）",
            len(kept), MAX_CV_UNCERTAIN_HISTORY,
        )
    return seq_floor, added
def _assign_review_ids(entries: list, seq_floor: int,
                       review_prefix: str) -> None:
    max_seq = max(seq_floor, max_review_seq(entries, review_prefix))
    for e in entries:
        if not isinstance(e, dict):
            continue
        _rid = e.get("review_id")
        if isinstance(_rid, str) and _rid.strip():
            continue
        max_seq += 1
        e["review_id"] = f"{review_prefix}-{max_seq:03d}"
def _needs_review_id_assignment(entries: list) -> bool:
    return any(
        isinstance(entry, dict)
        and not (isinstance(entry.get("review_id"), str)
                 and entry["review_id"].strip())
        for entry in entries)
MAX_CV_UNCERTAIN_HISTORY = 200
def _prune_cv_uncertain_history(
        entries: list,
        keep_history: int = MAX_CV_UNCERTAIN_HISTORY) -> list:
    if not isinstance(entries, list):
        return []
    history_idx = [
        i for i, e in enumerate(entries)
        if isinstance(e, dict) and e.get("status") != "pending_review"
    ]
    if len(history_idx) <= keep_history:
        return entries
    ordered = sorted(
        history_idx,
        key=lambda i: (str(entries[i].get("resolved_at") or ""), i),
    )
    drop = set(ordered[:len(ordered) - keep_history])
    return [e for i, e in enumerate(entries) if i not in drop]
def _write_review_queue(path: str, entries: list, seq_floor: int,
                        review_prefix: str) -> list:
    _assign_review_ids(entries, seq_floor, review_prefix)
    pruned = _prune_cv_uncertain_history(entries)
    write_queue_json(path, {"entries": pruned})
    return pruned
def _persist_merged_entries(skill_dir: str, entries: list,
                            skipped: dict | None = None,
                            review_prefix: str = REVIEW_ID_PREFIX,
                            complete_aggregate_snapshot: bool = False) -> int:
    path = cv_uncertain_path(skill_dir)
    if not isinstance(skipped, dict):
        skipped = {}
    entries = list(entries) if isinstance(entries, list) else []
    if not entries and not complete_aggregate_snapshot:
        return 0
    with locked_artifact(path) as locked:
        if not locked:
            raise RuntimeError(
                f"cv_uncertain 队列锁不可用，拒绝无锁读改写: {path}")
        old_entries = _read_review_queue_for_update(path)
        _pending_fp_snapshot_ids = {
            id(e) for e in old_entries
            if _is_fp_snapshot_entry(e) and e.get("status") == "pending_review"}
        seq_floor, added = _merge_pending_snapshot(
            old_entries, entries, skipped, review_prefix,
            complete_aggregate_snapshot=complete_aggregate_snapshot)
        _stale_fp_snapshot_superseded = any(
            isinstance(e, dict) and id(e) in _pending_fp_snapshot_ids
            and e.get("status") == "superseded" for e in old_entries)
        if (not added and not _stale_fp_snapshot_superseded
                and not _needs_review_id_assignment(entries)):
            return 0
        _write_review_queue(path, entries, seq_floor, review_prefix)
        return added
def enqueue_cv_uncertain(skill_dir: str, xv_findings: list | None) -> int:
    entries = []
    for xvr in xv_findings or []:
        if not isinstance(xvr, dict):
            continue
        entry = build_uncertain_entry(xvr)
        if entry is not None:
            entries.append(entry)
    return _persist_merged_entries(skill_dir, entries)
_AGGREGATE_LOCATOR_PREFIX = "fp-suppressed-aggregate"
_AGGREGATE_DETAIL_CAP = 20
# 全严重度强制口径：P0–P3 一律逐项入审，不再按严重度把 P3/P4 抑制残留
# 聚合成单条「株连式」审核项。聚合项只能给出一条模糊裁决，同组其余真实
# 问题会跟着一起被掩盖；保留该常量仅供显式策略回退。
_AGGREGATE_SEVERITIES: frozenset[str] = frozenset()
_FP_D2_SKIP_REPORT_KEYS: dict[str, str] = {
    "skipped_human_rejected": "fp_suppressed_skipped_human_rejected",
    "skipped_history_rejected": "fp_suppressed_skipped_history_rejected",
}
def _residual_location(rec: dict) -> tuple[str, int, str]:
    return (*_record_coords(rec), _record_family(rec))
def _severity_text(rec: dict) -> str:
    return _text(rec.get("severity")).strip().upper() or DEFAULT_SEVERITY
def _suppressed_xvr_like(rec: dict, severity: str) -> dict:
    _file, _line, _family = _residual_location(rec)
    return {
        "file": _file,
        "line": _line,
        "rule_id": _text(rec.get("rule_id")),
        "rule_family": _family,
        "severity": severity,
        "confidence": rec.get("confidence", 0),
        "message": _text(rec.get("message")),
        "locator": make_locator(_file, _line, _family),
    }
def _suppressed_review_entry(rec: dict) -> dict | None:
    _xvr = _suppressed_xvr_like(rec, _severity_text(rec))
    _xvr.update({
        "conclusion": "suppressed",
        "conclusion_v2": "suppressed",
        "_suppression_rule": _text(rec.get("_fp_deferred_reason")),
        "_suppressed_by_fp_filter": True,
    })
    return build_uncertain_entry(_xvr)
def _suppression_category(rec: object) -> str:
    if not isinstance(rec, dict):
        return "unknown"
    _txt = _text(rec.get("_fp_deferred_reason")).strip()
    if not _txt:
        return "unknown"
    return _txt.split(":", 1)[0].strip() or "unknown"
def _aggregate_member_detail(rec: dict) -> dict:
    _file, _line, _family = _residual_location(rec)
    return {
        "file": _file,
        "line": _line,
        "rule_id": _text(rec.get("rule_id")),
        "rule_family": _family,
        "severity": _severity_text(rec),
        "message": _text(rec.get("message"))[:200],
        "locator": make_locator(_file, _line, _family),
        "confidence": rec.get("confidence", 0),
        "source_method": _text(rec.get("_source_method")),
        "counter_evidence": bool(rec.get("_counter_evidence")),
        "fp_deferred_reason": _text(rec.get("_fp_deferred_reason")),
    }
def _member_signature(rec: dict) -> str:
    _file, _line, _family = _residual_location(rec)
    return "\x1e".join((
        _file, str(_line), _text(rec.get("rule_id")), _family,
        _severity_text(rec), _text(rec.get("message")),
        _text(rec.get("_source_method")),
    ))
def _aggregate_members_fingerprint(members: list) -> str:
    _sigs = sorted(
        _member_signature(_rec) for _rec in (members or [])
        if isinstance(_rec, dict)
    )
    if not _sigs:
        return "empty"
    return hashlib.sha1("\x1f".join(_sigs).encode("utf-8"),
                        usedforsecurity=False).hexdigest()[:8]
def _top_severity(details: list) -> str:
    _sevs = [str(_d.get("severity") or "") for _d in details]
    _sevs = [_s for _s in _sevs if _s]
    if not _sevs:
        return DEFAULT_SEVERITY
    return min(_sevs, key=normalize_severity_rank)
def _aggregate_suppressed_xvr(rule_id: str, category: str,
                              members: list) -> dict:
    _details = [_aggregate_member_detail(_rec) for _rec in (members or [])
                if isinstance(_rec, dict)]
    _details.sort(key=lambda _d: normalize_severity_rank(_d.get("severity")))
    _reasons = [_text(_rec.get("_fp_deferred_reason"))
                for _rec in (members or []) if isinstance(_rec, dict)]
    _rule_id = _text(rule_id)
    _category = _text(category) or "unknown"
    return {
        "locator": (f"{_AGGREGATE_LOCATOR_PREFIX}:{_rule_id}:{_category}:"
                    f"{_aggregate_members_fingerprint(members)}"),
        "rule_id": _rule_id,
        "rule_family": _details[0]["rule_family"] if _details else "",
        "severity": _top_severity(_details),
        "confidence": 0,
        "message": (f"FP 抑制残留聚合：{len(members or [])} 条"
                    f"（{_category}）"),
        "conclusion": "suppressed",
        "conclusion_v2": "suppressed",
        "_suppression_rule": next((_r for _r in _reasons if _r), _category),
        "_suppressed_by_fp_filter": True,
        "_aggregate_review": True,
        "_suppressed_count": len(members or []),
        "_suppressed_details": _details[:_AGGREGATE_DETAIL_CAP],
    }
def _paginate_members(members: list) -> list[list[dict]]:
    _sorted = sorted(
        (_rec for _rec in (members or []) if isinstance(_rec, dict)),
        key=_member_signature,
    )
    if not _sorted:
        return []
    return [_sorted[_i:_i + _AGGREGATE_DETAIL_CAP]
            for _i in range(0, len(_sorted), _AGGREGATE_DETAIL_CAP)]
def _aggregate_queue_entries(groups: dict) -> list[dict]:
    _entries: list[dict] = []
    for (_rule_id, _category), _members in (groups or {}).items():
        _valid = [_rec for _rec in (_members or []) if isinstance(_rec, dict)]
        if not _valid:
            continue
        _pages = _paginate_members(_valid)
        if len(_pages) > 1:
            _total = len(_pages)
            for _idx, _page in enumerate(_pages, 1):
                _page_xvr = _aggregate_suppressed_xvr(
                    _rule_id, _category, _page)
                _page_xvr["locator"] = (
                    f"{_page_xvr['locator']}:p{_idx}of{_total}")
                _queued = build_uncertain_entry(_page_xvr)
                if _queued is not None:
                    _entries.append(_queued)
            continue
        _queued = build_uncertain_entry(
            _aggregate_suppressed_xvr(_rule_id, _category, _valid))
        if _queued is not None:
            _entries.append(_queued)
    return _entries
def _human_rejected(lookup, locator: str) -> bool:
    if lookup is None or not locator:
        return False
    try:
        _rec = lookup(locator)
    except Exception as _e:
        log_swallowed(__name__, _e, context='_human_rejected:lookup')
        return False
    if _rec is None:
        return False
    _verdict = getattr(_rec, "verdict", None)
    if _verdict is None and isinstance(_rec, dict):
        _verdict = _rec.get("verdict")
    return str(_verdict or "").strip() == "false_positive"
def _as_skip_count(value, default: int) -> int:
    if isinstance(value, bool) or value is None:
        return default
    if isinstance(value, int):
        return value if value >= 0 else default
    if isinstance(value, float):
        return (int(value) if math.isfinite(value) and value >= 0
                and value.is_integer() else default)
    if isinstance(value, str):
        try:
            _count = int(value.strip())
        except (TypeError, ValueError) as _e:
            log_swallowed(__name__, _e, context='_as_skip_count:ValueError')
            return default
        return _count if _count >= 0 else default
    return default
def _attach_d2_skip_counts(report: dict, cv) -> None:
    try:
        _raw = getattr(cv, "_fp_d2_skip_report", None)
    except Exception as _e:
        log_swallowed(__name__, _e, context='_attach_d2_skip_counts:attr')
        return
    if not isinstance(_raw, dict):
        return
    for _src, _dst in _FP_D2_SKIP_REPORT_KEYS.items():
        report[_dst] = _as_skip_count(_raw.get(_src), report.get(_dst, 0))
def _partition_suppressed_residual(
        residual: list[dict], lookup,
        skipped: dict[str, int]) -> tuple[list[dict], dict[tuple[str, str], list[dict]]]:
    single: list[dict] = []
    groups: dict[tuple[str, str], list[dict]] = {}
    for rec in residual:
        _file, _line, _family = _residual_location(rec)
        if _human_rejected(lookup, make_locator(_file, _line, _family)):
            skipped["skipped_human_rejected"] += 1
            continue
        if _severity_text(rec) in _AGGREGATE_SEVERITIES:
            groups.setdefault(
                (_text(rec.get("rule_id")), _suppression_category(rec)),
                []).append(rec)
            continue
        single.append(rec)
    return single, groups
def _enqueue_unrescued_fp_suppressed(skill_dir: str, cv) -> int:
    _skipped: dict[str, int] = {_k: 0 for _k in _FP_D2_SKIP_REPORT_KEYS}
    cv._fp_d2_skip_report = _skipped
    _raw = getattr(cv, "_fp_unrescued_deferred", None)
    _residual = ([_rec for _rec in _raw if isinstance(_rec, dict)]
                 if isinstance(_raw, list) else [])
    if not _residual:
        return _persist_merged_entries(
            skill_dir, [], _skipped, complete_aggregate_snapshot=True)
    _store = open_confirm_store(skill_dir)
    _single, _groups = _partition_suppressed_residual(
        _residual, _store.lookup if _store is not None else None, _skipped)
    _candidates = [_entry for _entry in
                   (_suppressed_review_entry(_rec) for _rec in _single)
                   if _entry is not None]
    _candidates.extend(_aggregate_queue_entries(_groups))
    return _persist_merged_entries(
        skill_dir, _candidates, _skipped, complete_aggregate_snapshot=True)
def run_uncertain_enqueue_channel(cv, skill_dir: str,
                                  xv_findings: list) -> dict:
    report: dict[str, Any] = {
        "attempted": True,
        "enqueued": 0,
        "failed": False,
        "error": "",
        "fp_suppressed_forced": 0,
        "fp_suppressed_skipped_human_rejected": 0,
        "fp_suppressed_skipped_history_rejected": 0,
    }
    try:
        report["fp_suppressed_forced"] = _enqueue_unrescued_fp_suppressed(
            skill_dir, cv)
    except Exception as _e:
        log_swallowed(__name__, _e, context="enqueue_uncertain:fp_suppressed")
        append_report_error(report, _e, "fp_suppressed")
    _attach_d2_skip_counts(report, cv)
    try:
        report["enqueued"] = enqueue_cv_uncertain(skill_dir, xv_findings)
    except Exception as _e:
        log_swallowed(__name__, _e, context="enqueue_uncertain:enqueue")
        append_report_error(report, _e, "enqueue")
    return report
def reconcile_cv_uncertain_after_llm(skill_dir: str,
                                     before_findings: list | None,
                                     after_findings: list | None) -> dict:
    report = {"attempted": True, "pending_new": 0,
              "suppressed_new": 0, "confirmed_new": 0,
              "superseded": 0, "failed": False, "error": ""}
    _sd = _normalize_or_report(skill_dir, report)
    if not _sd:
        return report
    try:
        before_by_key = _index_by_review_key(before_findings)
        new_entries, after_by_key = _collect_llm_reconcile_entries(
            before_by_key, after_findings)
        path = cv_uncertain_path(_sd)
        if not _persist_reconciled_entries(
                path, new_entries, after_by_key, report):
            return report
        logger.info("[LLM-Reconcile] 队列对账: 新待审 %d（抑制 %d, 升级 %d）, "
                    "陈旧销项 %d",
                    report["pending_new"], report["suppressed_new"],
                    report["confirmed_new"], report["superseded"])
        return report
    except Exception as e:
        report.update({"failed": True,
                       "error": f"{type(e).__name__}: {e}"[:300]})
        logger.warning("[LLM-Reconcile] 队列对账异常（复核闭环可能未闭合）: %s",
                       e, exc_info=True)
        return report
def append_report_error(report: dict, err: BaseException, label: str = "") -> None:
    segment = f"{type(err).__name__}: {err}"
    if label:
        segment = f"{label}:{segment}"
    report["failed"] = True
    _prev = report.get("error")
    _prev = _prev if isinstance(_prev, str) else ""
    report["error"] = (f"{_prev} | {segment}" if _prev else segment)[:300]
def _normalize_or_report(skill_dir: str, report: dict) -> str:
    try:
        sd = normalize_skill_dir(_text(skill_dir)) if skill_dir else ""
    except Exception as e:
        report.update({"failed": True,
                       "error": f"skill_dir 归一失败: {type(e).__name__}"[:300]})
        logger.warning("[LLM-Reconcile] skill_dir 归一失败，复核闭环不闭合: %s", e)
        return ""
    if not sd:
        report.update({"failed": True, "error": "skill_dir 空"})
    return sd
def _index_by_review_key(findings: list | None) -> dict:
    return {
        review_entry_key(f): f
        for f in (findings or []) if isinstance(f, dict)
    }
def _persist_reconciled_entries(path: str, new_entries: list,
                                after_by_key: dict, report: dict) -> bool:
    with locked_artifact(path) as locked:
        if not locked:
            raise RuntimeError(
                f"cv_uncertain 队列锁不可用，拒绝无锁读改写: {path}")
        old_entries = _read_review_queue_for_update(path)
        superseded = _supersede_pending_entries(old_entries, after_by_key)
        candidate_ids = {id(entry) for entry in new_entries}
        entries = list(new_entries)
        seq_floor, _added = _merge_pending_snapshot(
            old_entries, entries, None, REVIEW_ID_PREFIX,
            complete_aggregate_snapshot=False)
        added_entries = [
            entry for entry in entries
            if isinstance(entry, dict) and id(entry) in candidate_ids
        ]
        if (not superseded and not added_entries
                and not _needs_review_id_assignment(entries)):
            report["pending_new"] = 0
            report["suppressed_new"] = 0
            report["confirmed_new"] = 0
            return True
        try:
            _write_review_queue(path, entries, seq_floor, REVIEW_ID_PREFIX)
        except (OSError, ValueError, TypeError) as e:
            report["pending_new"] = 0
            report["suppressed_new"] = 0
            report["confirmed_new"] = 0
            append_report_error(report, e, "queue_write")
            logger.warning("[LLM-Reconcile] 队列写回失败: %s", e)
            return False
        report["pending_new"] = len(added_entries)
        report["suppressed_new"] = sum(
            entry.get("conclusion") == "suppressed" for entry in added_entries)
        report["confirmed_new"] = sum(
            entry.get("conclusion") == "confirmed" for entry in added_entries)
        report["superseded"] = superseded
        return True
def _collect_llm_reconcile_entry(_f: dict, before_by_key: dict,
                                 new_entries: list) -> None:
    _key = review_entry_key(_f)
    _before = before_by_key.get(_key) or {}
    _before_concl = _effective_conclusion_text(_before)
    _after_concl = _effective_conclusion_text(_f)
    if not _after_concl or _after_concl == _before_concl:
        return
    if (_after_concl == "confirmed"
            and not _llm_upgrade_needs_review(_f)):
        return
    _suppression_rule = (
        "LLM语义复核(多数决抑制)" if _after_concl == "suppressed"
        else str(_f.get("rule_applied") or _f.get("rule_id") or ""))
    _xvr = _llm_review_xvr(_f, _suppression_rule)
    if _after_concl == "confirmed":
        _xvr["_review_required"] = True
    _entry = build_uncertain_entry(_xvr)
    if _entry is not None:
        new_entries.append(_entry)
def _collect_llm_reconcile_entries(before_by_key: dict,
                                   after_findings: list | None) -> tuple[list, dict]:
    new_entries: list = []
    verified_findings = [
        finding for finding in (after_findings or [])
        if isinstance(finding, dict) and finding.get("_llm_verified")
    ]
    after_by_key = _index_by_review_key(verified_findings)
    for _f in after_by_key.values():
        _collect_llm_reconcile_entry(_f, before_by_key, new_entries)
    return new_entries, after_by_key
def _llm_review_xvr(finding: dict, suppression_rule: str) -> dict:
    return {
        "conclusion": _effective_conclusion_text(finding),
        "severity": str(finding.get("severity") or ""),
        "rule_family": finding.get("rule_family") or finding.get("rule_id") or "",
        "sources": finding.get("sources") or [],
        "_independent_source_count": finding.get("_independent_source_count"),
        "locator": (_text(finding.get("locator"))
                    or make_locator_from_finding(finding)),
        "file_path": finding.get("file_path") or finding.get("file", ""),
        "file": finding.get("file", ""),
        "line": finding.get("line", 0),
        "rule_id": finding.get("rule_id", ""),
        "rule_applied": finding.get("rule_applied", ""),
        "confidence": _entry_confidence(finding),
        "adjusted_confidence": finding.get("adjusted_confidence", 0.0),
        "base_confidence": finding.get("base_confidence", 0.0),
        "evidence_strength": finding.get("evidence_strength", 0.0),
        "sample_finding": finding.get("sample_finding", {}),
        "message": finding.get("message", ""),
        "code_context": finding.get("code_context", ""),
        "findings": _inner_rows_of(finding),
        "_suppression_rule": suppression_rule,
        "_conclusion_params": {
            "decision_channel": "llm_semantic_review",
            "llm_vote_confidence": finding.get("_llm_vote_confidence", ""),
            "llm_reasoning": str(finding.get("_llm_reasoning", ""))[:400],
        },
    }
def _llm_upgrade_needs_review(finding: dict) -> bool:
    try:
        _sig = _extract_review_signals(finding)
        _flags = _resolve_review_flags(finding, _sig)
        return _review_triggered(_sig, _flags)
    except Exception as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_llm_upgrade_needs_review:Exc')
        return True
def _supersede_entry(e: dict, after_by_key: dict) -> bool:
    if not isinstance(e, dict) or e.get("status") != "pending_review":
        return False
    _after = after_by_key.get(review_entry_key(e))
    if not isinstance(_after, dict):
        return False
    _new_concl = _effective_conclusion_text(_after)
    _old_concl = _effective_conclusion_text(e)
    if not _new_concl or _new_concl == _old_concl:
        return False
    e["status"] = "superseded"
    e["resolved_at"] = now_iso()
    e["superseded_reason"] = (
        f"LLM复核改写结论 {_old_concl}→{_new_concl}，原复核对象已变化")
    return True
def _supersede_pending_entries(old_entries: list, after_by_key: dict) -> int:
    return sum(1 for e in old_entries if _supersede_entry(e, after_by_key))
def _fp_review_location(item: dict) -> tuple[str, int, str]:
    file_path, line = _record_coords(item)
    locator = (_text(item.get("locator"))
               or make_locator(file_path, line, _record_family(item)))
    return file_path, line, locator
_CONFIRMED_LOCATOR_CANON_CACHE: dict[frozenset[str], frozenset[str]] = {}
_CONFIRMED_LOCATOR_CANON_CACHE_MAX = 32
def _canonical_confirmed_locators(skill_dir: str) -> frozenset[str]:
    confirmed = confirmed_real_locators(skill_dir)
    if not confirmed:
        return frozenset()
    _cached = _CONFIRMED_LOCATOR_CANON_CACHE.get(confirmed)
    if _cached is not None:
        return _cached
    _normalized = frozenset(
        _canonical_queue_locator(_locator) for _locator in confirmed)
    if len(_CONFIRMED_LOCATOR_CANON_CACHE) >= _CONFIRMED_LOCATOR_CANON_CACHE_MAX:
        _CONFIRMED_LOCATOR_CANON_CACHE.clear()
    _CONFIRMED_LOCATOR_CANON_CACHE[confirmed] = _normalized
    return _normalized
def _suppression_revoked(skill_dir: str, item: dict) -> bool:
    _locator = _canonical_queue_locator(_fp_review_location(item)[2])
    if not _locator:
        return False
    return _locator in _canonical_confirmed_locators(skill_dir)
def _build_fp_review_entry(item: dict, fp_reason: str) -> dict:
    file_path, line, locator = _fp_review_location(item)
    return {
        "review_id": "",
        "channel": "cv_uncertain",
        "locator": locator,
        "file_path": file_path,
        "line": line,
        "rule_id": norm_rule_key(item.get("rule_id")),
        "rule_family": _text(item.get("rule_family")),
        "severity": _text(item.get("severity")) or DEFAULT_SEVERITY,
        "conclusion": "fp_prefilter",
        "fp_filter_suppressed": True,
        "confidence": 0.5,
        "message": f"[FP预过滤] {_text(item.get('sample_message')) or fp_reason}",
        "code_context": _text(item.get("code_snippet"))[:800],
        "status": "pending_review",
    }
def enqueue_fp_prefilter_review(skill_dir: str, item: dict, fp_reason: str) -> bool:
    try:
        entry = _build_fp_review_entry(item, fp_reason)
        added = _persist_merged_entries(
            skill_dir, [entry], {}, review_prefix=_FP_REVIEW_PREFIX)
        if not added:
            return False
        logger.info("[FpJudge] FP 疑似误报已入队 AI 语义复核: %s",
                    entry["locator"])
        return True
    except Exception as _eq_err:
        logger.warning("[FpJudge] FP 疑似误报入队失败(不阻断): %s", _eq_err)
        return False
@dataclass(frozen=True)
class FpPrefilterOutcome:
    hit: bool
    enqueued: bool
FP_PREFILTER_MISS = FpPrefilterOutcome(hit=False, enqueued=False)
def _fp_prefilter_reason(skill_dir: str, item: dict,
                         log_tag: str) -> tuple[bool, str]:
    try:
        is_fp, fp_reason = is_known_fp(item, skill_dir)
    except Exception as _fp_err:
        logger.warning("[%s] FP 预过滤检测失败，按未命中继续: %s",
                       log_tag, _fp_err)
        return False, ""
    if not is_fp:
        return False, ""
    if _suppression_revoked(skill_dir, item):
        logger.info(
            "[%s] 定位已确认真实，撤销误报抑制不再销项: %s",
            log_tag, item.get("rule_id"))
        return False, ""
    return True, fp_reason
def apply_fp_prefilter(skill_dir: str, state: dict, item: dict,
                       index: int) -> FpPrefilterOutcome:
    if not isinstance(item, dict):
        return FP_PREFILTER_MISS
    is_fp, fp_reason = _fp_prefilter_reason(skill_dir, item, "AIManualFix")
    if not is_fp:
        return FP_PREFILTER_MISS
    _resolved = plan_index(index)
    if _resolved is None or _resolved < 0:
        logger.warning("[AIManualFix] FP 预过滤跳过：条目索引不可定位(%s)",
                       item.get("rule_id"))
        return FP_PREFILTER_MISS
    if not mark_item_fp_confirmed(
            state, item, fp_reason, position=_resolved):
        logger.warning(
            "[AIManualFix] FP 预过滤标记未落到目标条目（索引身份冲突），"
            "降级为未命中交由候选装配暴露: %s", item.get("rule_id"))
        return FP_PREFILTER_MISS
    enqueued = False
    try:
        enqueued = bool(enqueue_fp_prefilter_review(skill_dir, item, fp_reason))
    except Exception as _enq_err:
        logger.warning("[AIManualFix] FP 预过滤入队异常(不阻断): %s", _enq_err)
    return FpPrefilterOutcome(hit=True, enqueued=enqueued)
@dataclass(frozen=True)
class FpPrefilterPartition:
    kept: tuple[tuple[int, dict, str], ...] = ()
    filtered: int = 0
    enqueued: int = 0
def partition_fp_prefiltered(skill_dir: str, state: dict,
                             items: list) -> FpPrefilterPartition:
    kept: list[tuple[int, dict, str]] = []
    filtered = 0
    enqueued = 0
    _items = as_item_list(items, log_tag="partition_fp_prefiltered")
    for position, item in enumerate(_items):
        if not isinstance(item, dict):
            continue
        status = item_status(item)
        if status in TREATMENT_TERMINAL_STATUSES:
            continue
        outcome = apply_fp_prefilter(
            skill_dir, state, item, item_index(item, position))
        if outcome.hit:
            enqueued += int(outcome.enqueued)
            filtered += 1
            continue
        kept.append((position, item, status))
    return FpPrefilterPartition(tuple(kept), filtered, enqueued)
def apply_step_fp_prefilter(sd: str, item: dict, fallback_index: int,
                            stage_start: float,
                            state: dict | None = None) -> dict | None:
    if not isinstance(item, dict):
        logger.warning("[TreatmentStep] FP 预过滤跳过：治疗项非映射(%s)",
                       type(item).__name__)
        return None
    _is_fp, _fp_reason = _fp_prefilter_reason(sd, item, "TreatmentStep")
    if not _is_fp:
        return None
    _state_index = item_index(item, fallback_index)
    if _state_index < 0:
        logger.warning("[TreatmentStep] FP 预过滤跳过：条目索引不可定位(%s)",
                       item.get("rule_id"))
        return None
    _state = state if state is not None else load_treatment_state(sd)
    if not mark_item_fp_confirmed(
            _state, item, _fp_reason, position=_state_index):
        logger.warning(
            "[TreatmentStep] FP 预过滤标记未落到目标条目（索引身份冲突），"
            "降级为未命中: %s", item.get("rule_id"))
        return None
    save_treatment_state(sd, _state)
    try:
        _eq = enqueue_fp_prefilter_review(sd, item, _fp_reason)
    except Exception as _enq_err:
        logger.warning("[TreatmentStep] FP复核入队异常(不阻断): %s", _enq_err)
        _eq = False
    return {"status": "fp_confirmed", "index": _state_index,
            "reason": _fp_reason,
            "ai_review_enqueued": bool(_eq),
            "next_action": ("run_next_ai_review" if _eq else "none"),
            "elapsed_s": elapsed_seconds(stage_start)}

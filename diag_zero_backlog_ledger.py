from __future__ import annotations

import hashlib
import json
import logging
import os
import time
from dataclasses import dataclass, field
from typing import Any, NamedTuple

from jwsgj.diag_guard_io import (
    guarded_open,
)
from jwsgj.diag_types_normalize import (
    as_dict,
    compact_ts_to_ms,
    dict_items,
    extract_finding_line,
    finding_file_key,
    int_or,
    normalize_confidence,
    normalize_line_no,
    normalize_list_field,
    parse_locator_file,
    str_or,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    FINDING_KEY_ALIASES,
    FMT_DATETIME,
    FMT_DATETIME_ISO,
    SEVERITY_RANK,
)
from jwsgj.log_config import (
    append_jsonl_locked,
    locked_artifact,
    log_swallowed,
    prune_jsonl_file,
)
from jwsgj.runtime_paths import (
    ai_review_verdicts_path,
    fp_rules_path,
    path_scoped_namespace,
    zero_backlog_ledger_path,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
    normalize_text,
)
from jwsgj.treatment_state import (
    TREATMENT_TERMINAL_STATUSES,
    load_treatment_state,
)
from jwsgj.xv_intermediate_store import (
    peek_pipeline_phase,
    peek_round_start_ts,
    round_anchor_equiv_form,
)

logger = logging.getLogger(__name__)
__all__ = [
    'APPROVED_EXECUTION_OK_STATUSES',
    'FIXED_RESOLUTIONS',
    'FUZZY_VERDICT_CHANNELS',
    'P0_SEVERITIES',
    'PRECISE_VERDICT_CHANNELS',
    'VERDICT_TRACE_KEY_SPEC',
    '_BACKLOG_ITEMS_PREVIEW',
    '_DEFAULT_ROUND_START_TS',
    '_LEDGER_MISSING_ACTION',
    '_STATE_EVENT_TYPES',
    'RoundScope',
    'TerminalVerdictContext',
    '_audit_fp_mask_from_snapshot',
    '_build_empty_backlog_report',
    '_finding_keys',
    '_fix_proof',
    '_last_state_by_fid',
    '_latest_events_by_idx',
    '_latest_finding_seen',
    '_load_fp_rules_snapshot',
    '_load_ledger_snapshot',
    '_pipeline_round_ledger_missing',
    '_report_skeleton',
    '_round_anchor',
    '_severity_rank_of',
    '_treatment_fix_proof',
    '_verdict_hit',
    '_verdict_hit_for_context',
    'audit_fp_mask',
    'build_review_target_digest',
    'build_round_scope',
    'build_terminal_context',
    'carried_findings',
    'classify_terminal',
    'current_round_ts',
    'describe_verdict_trace_keys',
    'finding_identity',
    'fixed_source_sha256',
    'fp_mask_actions',
    'get_ai_review_verdicts',
    'ledger_resolution',
    'load_ai_review_summary',
    'load_ledger_events',
    'p0_has_fixed_proof',
    'project_round_events',
    'register_cv_findings_snapshot',
    'resolve_backlog_item',
    'resolved_map',
    'round_events',
    'terminal_verb',
    'write_verdict_trace',
]
APPROVED_EXECUTION_OK_STATUSES = frozenset({
    "ai_fixed", "approved_fixed", "applied", "approved",
    "approved_removed", "invalid_plan_consumed", "already_absent",
    "completed", "ok", "success", "applied_with_review", "executed",
})
_APPROVE_AND_FIX_EXECUTION_OK_STATUSES = (
    APPROVED_EXECUTION_OK_STATUSES - {"approved"}
)
LEDGER_FILENAME = "zero_backlog_ledger.jsonl"
TERMINAL_RESOLUTIONS = frozenset({
    "fixed", "ai_fixed", "succeeded",
    "fp_confirmed", "rejected", "deferred", "suggestion",
    "suppressed_reviewed", "sampled_reviewed",
})
FP_RULE_SAMPLE_RESOLUTION = "sampled_reviewed"
CARRY_FORWARD_EVENT = "carry_forward"
# 结转快照事件：把「逐 finding 一条 carry_forward」收敛为「每轮一条」。
# 3 轮滚动窗口只约束 round_open/finding_seen，对 carry_forward 完全无效
# （实测 183 个 finding_id 中 0 条终态、182 条结转），是看似有界实则无界。
CARRY_SNAPSHOT_EVENT = "carry_snapshot"
# 快照载荷上限：超过即记 overflow_count，由门禁显式阻断（不静默漏报）。
_MAX_CARRIED_FINDINGS = 500
_LEDGER_KEEP_ROUNDS = 3
FIXED_RESOLUTIONS = frozenset({"fixed", "ai_fixed", "succeeded"})
P0_SEVERITIES = frozenset(
    sev for sev, rank in SEVERITY_RANK.items() if rank == 0)
_TERMINAL_VERDICTS = frozenset({
    "approve_and_fix", "approve", "reject_as_fp", "reject", "defer",
})
_EXECUTION_REQUIRED_VERDICTS = frozenset({"approve_and_fix", "approve"})
_FIX_VETO_VERDICTS = frozenset({"reject_as_fp", "reject", "defer"})
_EXECUTION_FAILED_STATUSES = frozenset({"failed", "error"})
FP_RULE_AUDIT_SAMPLE_RATIO = 0.1
FP_RULE_AUDIT_SAMPLE_MIN = 2
_DEFAULT_ACTOR = "ai"
_VERDICT_NOT_BEFORE = 0.0
_DEFAULT_ROUND_START_TS = ""
def _round_anchor(value: Any) -> str:
    return str_or(value).strip()
def append_ledger_event(skill_dir: str, event: dict) -> bool:
    if not isinstance(event, dict):
        logger.warning("[ZeroBacklog] 台账事件必须是 JSON object（拒绝 %s，"
                       "不阻断）", type(event).__name__)
        return False
    try:
        path = zero_backlog_ledger_path(skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[ZeroBacklog] 台账路径解析失败（不阻断）: %s", exc)
        return False
    try:
        line = json.dumps(event, ensure_ascii=False, default=str)
    except (TypeError, ValueError, RecursionError) as exc:
        logger.warning("[ZeroBacklog] 台账事件序列化失败（不阻断）: %s", exc)
        return False
    with locked_artifact(path) as locked:
        if not locked:
            logger.warning("[ZeroBacklog] 台账写锁不可用，拒绝无锁追加: %s",
                           path)
            return False
        if not append_jsonl_locked(path, line):
            logger.warning("[ZeroBacklog] 台账事件写入失败（不阻断）: %s", path)
            return False
    return True
def _parse_ledger_line_result(line: str,
                               line_no: int) -> tuple[dict | None, str]:
    text = line.strip()
    if not text:
        return None, ""
    try:
        event = json.loads(text)
    except (ValueError, RecursionError) as _e:
        log_swallowed(__name__, _e, context="load_ledger_events:ValueError")
        return None, f"line {line_no}: {type(_e).__name__}: {_e}"
    if not isinstance(event, dict):
        return None, f"line {line_no}: 台账事件必须是 JSON object"
    return event, ""
def _load_ledger_snapshot(skill_dir: str) -> tuple[list, list[str]]:
    try:
        path = zero_backlog_ledger_path(skill_dir)
    except (OSError, RuntimeError, ValueError) as _e:
        log_swallowed(__name__, _e, context="load_ledger_events:path")
        return [], [f"{skill_dir}: {type(_e).__name__}: {_e}"]
    if not os.path.isfile(path):
        return [], []
    events = []
    errors = []
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as f:
            events.extend(_iter_ledger_events(f, errors))
    except OSError as _e:
        log_swallowed(__name__, _e, context="load_ledger_events:OSError")
        errors.append(f"{path}: {type(_e).__name__}: {_e}")
    return events, errors
def load_ledger_events(skill_dir: str) -> list:
    events, _errors = _load_ledger_snapshot(skill_dir)
    return events
def _iter_ledger_events(f, errors: list | None = None):
    for line_no, ln in enumerate(f, start=1):
        event, error = _parse_ledger_line_result(ln, line_no)
        if error and errors is not None:
            errors.append(error)
        if event is not None:
            yield event
def current_round_ts(events: list, project: str = "") -> str:
    """返回最近一轮的轮次锚；给定 ``project`` 时只认该项目的轮次。

    台账跨项目共享，若只取「全局最新 round_open」，A 项目会读到 B 项目的
    轮次锚，进而把 B 项目的 finding 整批记成自己的积压（反向也会让 B 项目的
    finding_resolved 把 A 项目的发现静默当成已了结）。
    """
    wanted = str_or(project).strip()
    for ev in reversed(dict_items(events)):
        if ev.get("event") != "round_open":
            continue
        if wanted and str_or(ev.get("project")).strip() != wanted:
            continue
        anchor = _round_anchor(ev.get("round_start_ts"))
        if anchor:
            return anchor
    return ""
def _project_round_anchors(events: list, project: str) -> set[str]:
    wanted = str_or(project).strip()
    if not wanted:
        return set()
    return {
        anchor
        for ev in dict_items(events)
        if ev.get("event") == "round_open"
        and str_or(ev.get("project")).strip() == wanted
        if (anchor := _round_anchor(ev.get("round_start_ts")))
    }
def project_round_events(events: list, round_ts: str, project: str) -> list:
    """项目作用域内的轮次事件；该项目无轮次时返回空列表。

    ``round_events`` 在轮次锚为空时会回落到「全部事件」，跨项目共享台账下
    这等于把其他项目的 finding 全盘计入本项目，因此这里显式短路。
    """
    wanted = str_or(project).strip()
    if not wanted:
        return round_events(events, round_ts)
    anchor = _round_anchor(round_ts)
    if not anchor or anchor not in _project_round_anchors(events, wanted):
        return []
    return round_events(events, anchor)
def round_events(events: list, round_ts: str) -> list:
    events = dict_items(events)
    anchor = _round_anchor(round_ts)
    if not anchor:
        return list(events)
    cut: int | None = None
    for i in range(len(events) - 1, -1, -1):
        ev = events[i]
        if ev.get("event") != "round_open":
            continue
        event_round = _round_anchor(ev.get("round_start_ts"))
        if event_round == anchor:
            cut = i + 1
        elif event_round and cut is not None:
            break
    if cut is not None:
        selected = []
        for ev in events[cut:]:
            event_round = _round_anchor(ev.get("round_start_ts"))
            if (ev.get("event") == "round_open" and event_round
                    and event_round != anchor):
                break
            if event_round and event_round != anchor:
                continue
            selected.append(ev)
        return selected
    return [ev for ev in events
            if _round_anchor(ev.get("round_start_ts")) == anchor]
def _events_through_round(events: list, round_ts: str) -> list:
    events = dict_items(events)
    anchor = _round_anchor(round_ts)
    if not anchor:
        return events
    selected_open: int | None = None
    for i in range(len(events) - 1, -1, -1):
        ev = events[i]
        if ev.get("event") != "round_open":
            continue
        event_round = _round_anchor(ev.get("round_start_ts"))
        if event_round == anchor:
            selected_open = i
        elif event_round and selected_open is not None:
            break
    if selected_open is None:
        return [ev for ev in events
                if _round_anchor(ev.get("round_start_ts")) == anchor]
    end = len(events)
    for i in range(selected_open + 1, len(events)):
        ev = events[i]
        if ev.get("event") != "round_open":
            continue
        event_round = _round_anchor(ev.get("round_start_ts"))
        if event_round and event_round != anchor:
            end = i
            break
    history = events[:selected_open + 1]
    for ev in events[selected_open + 1:end]:
        event_round = _round_anchor(ev.get("round_start_ts"))
        if event_round and event_round != anchor:
            continue
        history.append(ev)
    return history
def _latest_events_by_idx(events: list,
                          types: tuple) -> list[tuple[int, dict]]:
    latest: dict[str, tuple[int, dict]] = {}
    unkeyed: list[tuple[int, dict]] = []
    for idx, ev in enumerate(dict_items(events)):
        if ev.get("event") not in types:
            continue
        fid = str_or(ev.get("finding_id"))
        if fid:
            latest[fid] = (idx, ev)
        else:
            unkeyed.append((idx, ev))
    return sorted(list(latest.values()) + unkeyed, key=lambda pair: pair[0])
def _latest_finding_seen(events: list) -> list:
    return [ev for _idx, ev in _latest_events_by_idx(
        events, ("finding_seen",))]
def _should_carry(fid: str, resolved_ids: set, kept_seen_ids: set,
                  kept_carry_ids: set, carry_seen: set) -> bool:
    return bool(fid) and not (fid in resolved_ids or fid in kept_seen_ids
                              or fid in kept_carry_ids or fid in carry_seen)
def _iter_carry_candidates(dropped: list, resolved_ids: set,
                           kept_seen_ids: set, kept_carry_ids: set):
    """未终结 finding 的结转事件：只保留门禁分类必需字段。

    ``finding_seen`` 原事件含 6 个时间字段（``ts``/``at``/``timestamp``/
    ``round_start_ts``/``carried_at`` 与原 ``event`` 值），单条占约 20% 体积
    却与跨轮追踪无关。只保留 ``_FINDING_STATE_KEYS`` + ``origin_round``：
    实测单条 580B -> 381B（1.52x），门禁 ``_classify_bucketed`` 所需字段
    全部保留，``origin_round`` 供 ``carried_findings`` 追溯来源轮次。
    """
    carry_seen = set()
    for ev in reversed(dropped):
        if ev.get("event") not in ("finding_seen", CARRY_FORWARD_EVENT):
            continue
        fid = str_or(ev.get("finding_id"))
        if not _should_carry(fid, resolved_ids, kept_seen_ids,
                             kept_carry_ids, carry_seen):
            continue
        carry_seen.add(fid)
        # ``finding_id`` 是身份键（``carried_findings`` 用它去重与匹配），
        # 但不在 ``_FINDING_STATE_KEYS``（那是状态比较字段集）里，必须显式带上。
        carry_ev: dict = {
            key: ev[key]
            for key in (*_FINDING_STATE_KEYS, "finding_id") if key in ev}
        carry_ev["event"] = CARRY_FORWARD_EVENT
        carry_ev["origin_round"] = (_round_anchor(ev.get("origin_round"))
                                    or _round_anchor(ev.get("round_start_ts")))
        yield carry_ev
def _round_open_indexes(events: list) -> list[int]:
    opens: list[int] = []
    seen: set[str] = set()
    for i, ev in enumerate(events):
        if ev.get("event") != "round_open":
            continue
        round_ts = _round_anchor(ev.get("round_start_ts"))
        if not round_ts or round_ts in seen:
            continue
        seen.add(round_ts)
        opens.append(i)
    return opens
def prune_ledger(skill_dir: str, events: list) -> None:
    if len(_round_open_indexes(events)) <= _LEDGER_KEEP_ROUNDS:
        return
    try:
        path = zero_backlog_ledger_path(skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[ZeroBacklog] 台账修剪跳过（路径解析失败）: %s", exc)
        return
    with locked_artifact(path) as locked:
        if not locked:
            logger.warning("[ZeroBacklog] 台账修剪跳过（写锁不可用）: %s", path)
            return
        if os.path.isfile(path):
            current, ledger_errors = _load_ledger_snapshot(skill_dir)
            if ledger_errors:
                logger.warning(
                    "[ZeroBacklog] 台账修剪跳过（保留损坏证据）: %s",
                    "；".join(ledger_errors[:3]))
                return
        else:
            current = events
        opens = _round_open_indexes(current)
        if len(opens) <= _LEDGER_KEEP_ROUNDS:
            return
        keep_from = opens[-_LEDGER_KEEP_ROUNDS]
        dropped = current[:keep_from]
        kept = current[keep_from:]
        carried_events = _carry_forward_events(dropped, current, kept)
        snapshot = _build_carry_snapshot(carried_events, current, skill_dir)
        if snapshot is not None:
            kept = [snapshot, *kept]
            logger.info(
                "[ZeroBacklog] 修剪结转: %d 条历史未终态 finding 收敛为 1 条 "
                "carry_snapshot（跨轮追踪至终态，溢出 %d 条）",
                snapshot["carried_count"], snapshot["overflow_count"])
        _rewrite_ledger(path, kept, len(current))
_STATE_EVENT_TYPES = ("finding_seen", CARRY_FORWARD_EVENT,
                      "finding_resolved")
def _last_state_by_fid(events: list) -> dict[str, dict]:
    return {str_or(ev.get("finding_id")): ev
            for _idx, ev in _latest_events_by_idx(events, _STATE_EVENT_TYPES)
            if str_or(ev.get("finding_id"))}
def _carry_forward_events(dropped: list, events: list, kept: list) -> list:
    resolved_ids = set(resolved_map(events))
    kept_seen_ids = {str_or(ev.get("finding_id"))
                     for ev in kept if ev.get("event") == "finding_seen"}
    kept_carry_ids = {str_or(ev.get("finding_id"))
                      for ev in kept if ev.get("event") == CARRY_FORWARD_EVENT}
    candidates = []
    for ev in dropped:
        if ev.get("event") != CARRY_SNAPSHOT_EVENT:
            candidates.append(ev)
            continue
        payloads = ev.get("findings")
        for item in payloads if isinstance(payloads, list) else []:
            if not isinstance(item, dict):
                continue
            candidates.append({
                **item,
                "event": CARRY_FORWARD_EVENT,
                "origin_round": (_round_anchor(item.get("origin_round"))
                                 or _round_anchor(ev.get("round_start_ts"))),
            })
    return list(_iter_carry_candidates(
        candidates, resolved_ids, kept_seen_ids, kept_carry_ids))[::-1]
def _rewrite_ledger(path: str, kept: list, total_events: int) -> None:
    try:
        with guarded_open(path, "w", encoding="utf-8") as f:
            for ev in kept:
                f.write(json.dumps(ev, ensure_ascii=False, default=str) + "\n")
        logger.info("[ZeroBacklog] 台账滚动修剪: %d -> %d 事件（保留最近 %d 轮）",
                    total_events, len(kept), _LEDGER_KEEP_ROUNDS)
    except (OSError, TypeError, ValueError, RecursionError) as exc:
        logger.warning("[ZeroBacklog] 台账修剪失败（不阻断）: %s", exc)
def resolved_map(cur_events: list) -> dict:
    resolved: dict = {}
    for fid, ev in _last_state_by_fid(cur_events).items():
        if ev.get("event") != "finding_resolved":
            continue
        if (str_or(ev.get("resolution")).strip().lower()
                not in TERMINAL_RESOLUTIONS):
            continue
        resolved[fid] = ev
    return resolved
def _treatment_alias_line(item: dict) -> int:
    for key in FINDING_KEY_ALIASES["line"]:
        line = normalize_line_no(item.get(key))
        if line > 0:
            return line
    return 0
def _treatment_file_line(item: dict) -> tuple[str, int]:
    file_path, line = _finding_file_line(item)
    return file_path, line if line > 0 else _treatment_alias_line(item)
def _treatment_terminal_keys(item: Any) -> tuple[str, tuple | None, str, str]:
    if not isinstance(item, dict):
        return "", None, "", ""
    status = str_or(item.get("status")).strip().lower()
    if status not in TREATMENT_TERMINAL_STATUSES:
        return "", None, "", ""
    locator = str_or(item.get("locator"))
    file_path, line = _treatment_file_line(item)
    triple = None
    if file_path:
        triple = (os.path.basename(file_path), line,
                  str_or(item.get("rule_id")))
    return locator, triple, file_path, status
def _prefer_fixed_status(previous: str, current: str) -> str:
    return previous if previous in FIXED_RESOLUTIONS else current
_TIME_PARSE_FORMATS = (FMT_DATETIME_ISO, FMT_DATETIME)
def _positive_epoch(value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 0.0
    try:
        value = float(value)
    except (OverflowError, TypeError, ValueError):  # jwsgj:silent-ok
        return 0.0
    return value if 0 < value < float("inf") else 0.0
def _record_epoch(record: dict) -> float:
    if not isinstance(record, dict):
        return 0.0
    ts = _positive_epoch(record.get("ts"))
    if ts:
        return ts
    for key in ("timestamp", "at"):
        raw = str_or(record.get(key)).strip()
        for fmt in _TIME_PARSE_FORMATS:
            try:
                parsed = _positive_epoch(
                    time.mktime(time.strptime(raw, fmt)))
            except (ValueError, OverflowError, OSError):
                continue
            if parsed:
                return parsed
    compact = compact_ts_to_ms(str_or(record.get("at_ts")).strip())
    return compact / 1000.0 if compact else 0.0
def _verdict_clock(value: Any) -> dict:
    if isinstance(value, dict):
        return {str_or(key).strip().lower(): _positive_epoch(at)
                for key, at in value.items() if str_or(key).strip()}
    if isinstance(value, (set, frozenset, list, tuple)):
        return {str_or(verdict).strip().lower(): 0.0 for verdict in value
                if str_or(verdict).strip()}
    return {}
def _fresh_verdicts(
        value: Any, not_before: float = _VERDICT_NOT_BEFORE) -> frozenset:
    entries = _verdict_clock(value)
    if not_before <= 0:
        return frozenset(entries)
    return frozenset(verdict for verdict, at in entries.items()
                     if at <= 0 or at >= not_before)
def _union_verdicts(previous: Any, current: Any) -> dict:
    merged = _verdict_clock(previous)
    for verdict, at in _verdict_clock(current).items():
        merged[verdict] = max(merged.get(verdict, 0.0), at)
    return merged
def _latest_verdict_clock(previous: Any, current: Any) -> dict:
    previous_clock = _verdict_clock(previous)
    current_clock = _verdict_clock(current)
    if not previous_clock:
        return current_clock
    if not current_clock:
        return previous_clock
    current_at = max(current_clock.values())
    previous_at = max(previous_clock.values())
    if current_at <= 0 or current_at >= previous_at:
        return current_clock
    return previous_clock
def _same_file_path(first: str, second: str) -> bool:
    left = finding_file_key(first)
    right = finding_file_key(second)
    if not left or not right:
        return False
    return (left == right or left.endswith("/" + right)
            or right.endswith("/" + left))
class _TerminalIndex:
    __slots__ = ("_exact_merge", "_merge", "basenames", "finding_ids",
                 "locators", "paths", "rules", "triples")
    def __init__(self, *, merge=None, finding_ids=None, locators=None,
                 triples=None, rules=None, basenames=None, paths=None,
                 exact_merge=None):
        self.finding_ids: dict = dict(finding_ids or {})
        self.locators: dict = dict(locators or {})
        self.triples: dict = dict(triples or {})
        self.rules: dict = dict(rules or {})
        self.basenames: dict = dict(basenames or {})
        self.paths: dict = {key: dict(group)
                            for key, group in (paths or {}).items()}
        self._merge = merge or (lambda _previous, current: current)
        self._exact_merge = exact_merge or self._merge
    def _put(self, table: dict, key, value, *, exact: bool = False) -> None:
        if not key:
            return
        if key in table:
            merge = self._exact_merge if exact else self._merge
            table[key] = merge(table[key], value)
        else:
            table[key] = value
    def add_finding_id(self, finding_id: str, value) -> None:
        self._put(self.finding_ids, finding_id, value, exact=True)
    def add_locator(self, locator: str, value) -> None:
        self._put(self.locators, locator, value, exact=True)
    def add_triple(self, triple: tuple | None, value) -> None:
        if triple is not None:
            self._put(self.triples, triple, value, exact=True)
    def add_path(self, file_path: str, line: int, rule_id: str, value) -> None:
        key = finding_file_key(file_path)
        if key:
            self._put(self.paths.setdefault((line, rule_id), {}), key, value,
                      exact=True)
    def add_rule(self, rule_id: str, value) -> None:
        self._put(self.rules, rule_id, value)
    def add_basename(self, file_name: str, value) -> None:
        self._put(self.basenames, file_name, value)
    def _path_match_state(self, keys: _FindingKeys) -> tuple[dict, list]:
        group = self.paths.get((keys.line, keys.rule_id))
        matches = [] if not group else [
            path for path in group if _same_file_path(keys.file, path)]
        return group, matches
    def path_candidate(self, keys: _FindingKeys) -> tuple[bool, str]:
        group, matches = self._path_match_state(keys)
        if not group:
            return False, ""
        if len(matches) != 1:
            return True, ""
        return True, matches[0]
    def has_evidence(self, keys: _FindingKeys) -> bool:
        if keys.finding_id and keys.finding_id in self.finding_ids:
            return True
        if keys.locator and keys.locator in self.locators:
            return True
        group, matches = self._path_match_state(keys)
        if group:
            return len(matches) == 1
        return bool(keys.file
                    and (os.path.basename(keys.file), keys.line, keys.rule_id)
                    in self.triples)
    def iter_evidence(self, keys: _FindingKeys,
                      require_complete: bool = False):
        if keys.finding_id and keys.finding_id in self.finding_ids:
            yield self.finding_ids[keys.finding_id]
        if keys.locator and keys.locator in self.locators:
            yield self.locators[keys.locator]
        if require_complete and not (keys.rule_id and keys.line > 0):
            return
        if not keys.file:
            return
        group, matches = self._path_match_state(keys)
        if len(matches) == 1:
            yield group[matches[0]]
            return
        if group:
            return
        triple = (os.path.basename(keys.file), keys.line, keys.rule_id)
        if triple in self.triples:
            yield self.triples[triple]
    def first(self, channel: str, keys: _FindingKeys):
        if channel == "finding_id":
            return self.finding_ids.get(keys.finding_id) if keys.finding_id else None
        if channel == "locator":
            return self.locators.get(keys.locator) if keys.locator else None
        if channel == "path":
            has_candidates, path = self.path_candidate(keys)
            return (self.paths[(keys.line, keys.rule_id)][path]
                    if has_candidates and path else None)
        if channel == "rule":
            return self.rules.get(keys.rule_id) if keys.rule_id else None
        if channel == "basename":
            return (self.basenames.get(os.path.basename(keys.file))
                    if keys.file else None)
        return None
def _index_treatment_items(items: list) -> _TerminalIndex:
    index = _TerminalIndex(merge=_prefer_fixed_status)
    for item in items:
        if not isinstance(item, dict):
            continue
        locator, triple, file_path, status = _treatment_terminal_keys(item)
        if not status:
            continue
        index.add_finding_id(str_or(item.get("finding_id")).strip(), status)
        index.add_locator(locator, status)
        index.add_triple(triple, status)
        if triple is not None:
            index.add_path(file_path, triple[1], triple[2], status)
    return index
def _treatment_terminal_index(skill_dir: str) -> tuple:
    empty = _TerminalIndex(merge=_prefer_fixed_status)
    try:
        state = load_treatment_state(skill_dir)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context="_treatment_terminal_index:load")
        return [], empty
    items = state.get("items") if isinstance(state, dict) else None
    if not isinstance(items, list):
        return [], empty
    return items, _index_treatment_items(items)
def _verdict_is_terminal(v: dict) -> bool:
    assessment = v.get("assessment")
    verdict = (str_or(assessment.get("verdict")).strip().lower()
               if isinstance(assessment, dict) else "")
    if verdict not in _TERMINAL_VERDICTS:
        return False
    execution_status = str_or(v.get("execution_status")).strip().lower()
    if verdict in _EXECUTION_REQUIRED_VERDICTS:
        ok_statuses = (_APPROVE_AND_FIX_EXECUTION_OK_STATUSES
                       if verdict == "approve_and_fix"
                       else APPROVED_EXECUTION_OK_STATUSES)
        return execution_status in ok_statuses
    return execution_status not in _EXECUTION_FAILED_STATUSES
def _index_one_verdict(v: dict, index: _TerminalIndex) -> None:
    verdict = str_or((v.get("assessment") or {}).get("verdict")).strip().lower()
    target = str_or(v.get("target"))
    rule_id = str_or(v.get("rule_id"))
    file_path = (str_or(v.get("file_path"))
                 or str_or(v.get("file_path_abs")))
    line = int_or(v.get("line"), 0)
    value = {verdict: _record_epoch(v)}
    index.add_finding_id(str_or(v.get("finding_id")).strip(), value)
    index.add_locator(target, value)
    index.add_rule(rule_id, value)
    if file_path:
        basename = os.path.basename(file_path)
        index.add_basename(basename, value)
        if rule_id and line > 0:
            index.add_triple((basename, line, rule_id), value)
            index.add_path(file_path, line, rule_id, value)
def _verdict_other_round(v: dict, round_start_ts: str) -> bool:
    current = _round_anchor(round_start_ts)
    anchored = _round_anchor(v.get("round_start_ts"))
    return bool(current and anchored and anchored != current)
def _verdict_terminal_indexes(
        skill_dir: str, round_start_ts: str = _DEFAULT_ROUND_START_TS,
) -> dict[str, _TerminalIndex]:
    current = _round_anchor(round_start_ts)
    try:
        verdicts = get_ai_review_verdicts(skill_dir, round_start_ts="")
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context="_verdict_terminal_indexes:load")
        return {current: _TerminalIndex(
            merge=_union_verdicts, exact_merge=_latest_verdict_clock)}
    terminal = [v for v in verdicts
                if isinstance(v, dict) and _verdict_is_terminal(v)]
    anchors = {"", current} | {
        _round_anchor(v.get("round_start_ts")) for v in terminal
        if _round_anchor(v.get("round_start_ts"))}
    indexes = {anchor: _TerminalIndex(
        merge=_union_verdicts, exact_merge=_latest_verdict_clock)
               for anchor in anchors}
    for v in terminal:
        anchored = _round_anchor(v.get("round_start_ts"))
        if anchored:
            targets = [indexes[anchored]]
            if not current:
                targets.append(indexes[current])
        else:
            targets = list(indexes.values())
        for index in targets:
            _index_one_verdict(v, index)
    return indexes
@dataclass
class TerminalVerdictContext:
    resolved: dict = field(default_factory=dict)
    t_index: _TerminalIndex = field(default_factory=_TerminalIndex)
    v_index: _TerminalIndex = field(default_factory=_TerminalIndex)
    t_items: list = field(default_factory=list)
    round_start_ts: str = ""
    v_indexes: dict[str, _TerminalIndex] = field(default_factory=dict)
def _current_round_anchor(skill_dir: str, round_start_ts: str) -> str:
    anchor = _round_anchor(round_start_ts)
    if anchor:
        return anchor
    try:
        return _round_anchor(peek_round_start_ts(skill_dir))
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context="build_terminal_context:peek_round")
        return ""
def build_terminal_context(
        skill_dir: str, resolved: dict,
        round_start_ts: str = _DEFAULT_ROUND_START_TS,
) -> TerminalVerdictContext:
    t_items, t_index = _treatment_terminal_index(skill_dir)
    anchor = _current_round_anchor(skill_dir, round_start_ts)
    v_indexes = _verdict_terminal_indexes(skill_dir, anchor)
    return TerminalVerdictContext(
        resolved=resolved, t_index=t_index,
        v_index=v_indexes[anchor], t_items=t_items,
        round_start_ts=anchor, v_indexes=v_indexes)
class _FindingKeys(NamedTuple):
    locator: str
    file: str
    line: int
    rule_id: str
    at: float = 0.0
    finding_id: str = ""
    round_start_ts: str = ""
    verdict_rounds: tuple = ()
def _finding_file_line(finding: dict) -> tuple[str, int]:
    data = finding if isinstance(finding, dict) else {}
    file_path = str_or(
        data.get("file") or data.get("file_path") or data.get("filepath"))
    if not file_path:
        file_path = parse_locator_file(data.get("locator"))
    return file_path, extract_finding_line(data)
def _finding_keys(finding: dict) -> _FindingKeys:
    if not isinstance(finding, dict):
        logger.warning("[ZeroBacklog] finding 非映射(%s)，按无键处理",
                       type(finding).__name__)
        finding = {}
    file_path, line = _finding_file_line(finding)
    verdict_rounds = finding.get("_verdict_rounds")
    if not isinstance(verdict_rounds, (list, tuple)):
        verdict_rounds = ()
    return _FindingKeys(
        locator=str_or(finding.get("locator")),
        file=file_path,
        line=line,
        rule_id=str_or(finding.get("rule_id")),
        at=_record_epoch(finding),
        finding_id=str_or(finding.get("finding_id")).strip(),
        round_start_ts=_round_anchor(finding.get("round_start_ts")),
        verdict_rounds=tuple(
            anchor for value in verdict_rounds
            if (anchor := _round_anchor(value))),
    )
_VERDICT_TERMINAL_CHANNELS = (
    ("finding_id", "ai_verdict_exact"),
    ("locator", "ai_verdict_exact"),
    ("path", "ai_verdict_exact"),
    ("rule", "ai_verdict_fuzzy"),
    ("basename", "ai_verdict_fuzzy_file"),
)
PRECISE_VERDICT_CHANNELS = frozenset(
    label for _channel, label in _VERDICT_TERMINAL_CHANNELS
    if label == "ai_verdict_exact")
FUZZY_VERDICT_CHANNELS = frozenset(
    label for _channel, label in _VERDICT_TERMINAL_CHANNELS
    if label.startswith("ai_verdict_fuzzy"))
def _verdict_hit(
        keys: _FindingKeys, index: _TerminalIndex,
        not_before: float = _VERDICT_NOT_BEFORE) -> tuple[str, frozenset]:
    for channel, label in _VERDICT_TERMINAL_CHANNELS:
        fresh = _fresh_verdicts(index.first(channel, keys), not_before)
        if fresh:
            return label, fresh
    return "", frozenset()
def _verdict_index_for_context(
        keys: _FindingKeys, ctx: TerminalVerdictContext) -> _TerminalIndex:
    if not keys.round_start_ts:
        return ctx.v_index
    return ctx.v_indexes.get(
        keys.round_start_ts, ctx.v_indexes.get("", ctx.v_index))
def _verdict_indexes_for_context(
        keys: _FindingKeys, ctx: TerminalVerdictContext,
) -> tuple[_TerminalIndex, ...]:
    primary = _verdict_index_for_context(keys, ctx)
    if keys.verdict_rounds:
        indexes = []
        candidates = [ctx.v_index]
        candidates.extend(
            ctx.v_indexes[anchor] for anchor in reversed(keys.verdict_rounds)
            if anchor in ctx.v_indexes)
        candidates.append(primary)
        for index in candidates:
            if all(index is not known for known in indexes):
                indexes.append(index)
        return tuple(indexes)
    if (keys.round_start_ts and ctx.round_start_ts
            and keys.round_start_ts != ctx.round_start_ts
            and primary is not ctx.v_index):
        return ctx.v_index, primary
    return (primary,)
def _verdict_hit_for_context(
        keys: _FindingKeys, ctx: TerminalVerdictContext,
) -> tuple[str, frozenset]:
    indexes = _verdict_indexes_for_context(keys, ctx)
    for channel, label in _VERDICT_TERMINAL_CHANNELS:
        for index in indexes:
            fresh = _fresh_verdicts(index.first(channel, keys), keys.at)
            if fresh:
                return label, fresh
    return "", frozenset()
def ledger_resolution(finding: dict, resolved: dict) -> str:
    fid = (str_or(finding.get("finding_id"))
           if isinstance(finding, dict) else "")
    if not fid or not isinstance(resolved, dict):
        return ""
    raw = resolved.get(fid, "")
    value = raw.get("resolution") if isinstance(raw, dict) else raw
    return str_or(value).strip().lower()
def classify_terminal(finding: dict,
                       ctx: TerminalVerdictContext) -> str:
    if not isinstance(finding, dict):
        logger.warning("[ZeroBacklog] 终态判定入参非映射(%s)，按未终态处理",
                       type(finding).__name__)
        return ""
    fid = str_or(finding.get("finding_id"))
    if fid and fid in ctx.resolved:
        return f"ledger:{ledger_resolution(finding, ctx.resolved)}"
    keys = _finding_keys(finding)
    if ctx.t_index.has_evidence(keys):
        return "treatment_state"
    return _verdict_hit_for_context(keys, ctx)[0]
@dataclass
class _CarryScope:
    cur_ids: set
    resolved_ids: set
    seen: set = field(default_factory=set)
    cur_round_ts: str = ""
def _carried_event_qualified(ev: dict, fid: str,
                             scope: _CarryScope) -> bool:
    if (not fid or fid in scope.cur_ids or fid in scope.resolved_ids
            or fid in scope.seen):
        return False
    etype = ev.get("event")
    if etype == CARRY_FORWARD_EVENT:
        return True
    if etype == "finding_seen":
        return (_round_anchor(ev.get("round_start_ts"))
                != _round_anchor(scope.cur_round_ts))
    return False
def _carry_payload_qualified(item: dict, scope: _CarryScope) -> bool:
    """快照载荷是否仍需结转（未被本轮重新发现、未终态、未重复）。"""
    fid = str_or(item.get("finding_id"))
    return bool(fid) and not (
        fid in scope.cur_ids or fid in scope.resolved_ids
        or fid in scope.seen)
def _build_carry_snapshot(carried: list, events: list,
                          skill_dir: str) -> dict | None:
    """把逐条结转事件收敛为单条快照事件（事件数 O(finding) -> O(1)）。

    快照的 ``findings`` 只保留 ``_FINDING_STATE_KEYS`` + ``finding_id`` +
    ``origin_round``；超过 ``_MAX_CARRIED_FINDINGS`` 时按最旧丢弃并记
    ``overflow_count``，由门禁显式阻断（不静默漏报）。
    """
    payloads = [
        {key: event[key]
         for key in (*_FINDING_STATE_KEYS, "finding_id", "origin_round")
         if key in event}
        for event in carried if isinstance(event, dict)]
    if not payloads:
        return None
    overflow = max(0, len(payloads) - _MAX_CARRIED_FINDINGS)
    if overflow:
        payloads = payloads[-_MAX_CARRIED_FINDINGS:]
        logger.warning(
            "[ZeroBacklog] 结转积压 %d 条超出追踪上限 %d，最旧 %d 条只记"
            "计数（门禁将阻断，需先 resolve_backlog_item 清理）",
            len(carried), _MAX_CARRIED_FINDINGS, overflow)
    return {
        "event": CARRY_SNAPSHOT_EVENT,
        **_event_time_fields(),
        "round_start_ts": current_round_ts(events),
        "project": path_scoped_namespace(skill_dir),
        "carried_count": len(carried),
        "overflow_count": overflow,
        "findings": payloads,
    }
def carried_findings(events: list, cur: list, cur_round_ts: str,
                     project: str = "") -> list:
    # 本项目尚无轮次时不存在「上一轮的未了结项」；若继续往下走，
    # ``_events_through_round`` 会因锚为空回落到全台账，把其他项目的
    # 历史 finding 全部当成本项目的结转项。
    wanted = str_or(project).strip()
    if wanted and not _round_anchor(cur_round_ts):
        return []
    source = dict_items(events)
    own_rounds = _project_round_anchors(source, wanted)
    if wanted and not own_rounds:
        return []
    # 其他项目仍开着的轮次：快照载荷若来自这些轮次则不得被本项目认领。
    foreign_rounds = {
        anchor for ev in source
        if ev.get("event") == "round_open"
        and str_or(ev.get("project")).strip() != wanted
        and (anchor := _round_anchor(ev.get("round_start_ts")))
    } if wanted else set()
    if wanted:
        source = [
            ev for ev in source
            if str_or(ev.get("project")).strip() == wanted
            or _round_anchor(ev.get("round_start_ts")) in own_rounds
        ]
    events = _events_through_round(source, cur_round_ts)
    cur = dict_items(cur)
    cur_ids = {str_or(ev.get("finding_id"))
               for ev in cur if ev.get("event") == "finding_seen"}
    resolved_ids = set(resolved_map(events))
    scope = _CarryScope(cur_ids=cur_ids, resolved_ids=resolved_ids,
                        cur_round_ts=cur_round_ts)
    verdict_rounds = []
    for ev in events:
        if ev.get("event") != "round_open":
            continue
        anchor = _round_anchor(ev.get("round_start_ts"))
        if anchor and anchor not in verdict_rounds:
            verdict_rounds.append(anchor)
    current_anchor = _round_anchor(cur_round_ts)
    if current_anchor and current_anchor not in verdict_rounds:
        verdict_rounds.append(current_anchor)
    out = []
    for ev in reversed(events):
        if ev.get("event") == CARRY_SNAPSHOT_EVENT:
            # 快照载荷不带 project：归属以写出快照的项目（快照事件 project
            # 字段）为准。origin_round 只作追溯，不能作归属判据——修剪会删掉
            # 来源轮的 round_open，按它判归属会把本项目未终态的结转项整批
            # 静默丢弃（门禁假通过）。
            snapshot_project = str_or(ev.get("project")).strip()
            snapshot_owned = bool(
                snapshot_project and snapshot_project == wanted)
            payloads = ev.get("findings")
            payloads = payloads if isinstance(payloads, list) else []
            for item in reversed(payloads):
                if not isinstance(item, dict):
                    continue
                fid = str_or(item.get("finding_id"))
                if not _carry_payload_qualified(item, scope):
                    continue
                carry = dict(item)
                carry["carried"] = True
                carry["origin_round"] = (
                    _round_anchor(item.get("origin_round"))
                    or _round_anchor(ev.get("round_start_ts")))
                payload_owned = (
                    (snapshot_owned
                     and carry["origin_round"] not in foreign_rounds)
                    or carry["origin_round"] in own_rounds)
                if wanted and not payload_owned:
                    continue
                carry["_verdict_rounds"] = tuple(verdict_rounds)
                out.append(carry)
                scope.seen.add(fid)
            continue
        fid = str_or(ev.get("finding_id"))
        if not _carried_event_qualified(ev, fid, scope):
            continue
        carry = dict(ev)
        carry["carried"] = True
        carry["origin_round"] = (_round_anchor(ev.get("origin_round"))
                                or _round_anchor(ev.get("round_start_ts")))
        carry["_verdict_rounds"] = tuple(verdict_rounds)
        out.append(carry)
        scope.seen.add(fid)
    out.reverse()
    return out
class RoundScope(NamedTuple):
    round_start_ts: str
    findings: list
    ctx: TerminalVerdictContext
    ledger_errors: list
def build_round_scope(
        skill_dir: str,
        round_start_ts: str = _DEFAULT_ROUND_START_TS) -> RoundScope:
    events, ledger_errors = _load_ledger_snapshot(skill_dir)
    project = path_scoped_namespace(skill_dir)
    anchor = _round_anchor(round_start_ts) or current_round_ts(events, project)
    cur = project_round_events(events, anchor, project)
    findings = (_latest_finding_seen(cur)
                + carried_findings(events, cur, anchor, project=project))
    ctx = build_terminal_context(skill_dir, resolved_map(cur), anchor)
    return RoundScope(anchor, findings, ctx, ledger_errors)
_BACKLOG_ITEMS_PREVIEW = 50
_MIN_RATIONALE_LEN = 10
_RANK_TO_P = {0: "P0", 1: "P1", 2: "P2", 3: "P3", 4: "P4"}
_DOMAINS = ("A", "B", "C", "D", "E", "F", "G")
def _entry_findings_chain(entry: dict):
    sf = entry.get("sample_finding")
    if isinstance(sf, dict):
        yield sf
    raw_subs = entry.get("findings")
    if isinstance(raw_subs, (list, tuple)):
        for ff in raw_subs:
            if isinstance(ff, dict):
                yield ff
def _severity_rank_of(carrier: dict) -> int | None:
    if not isinstance(carrier, dict):
        return None
    return SEVERITY_RANK.get(str_or(carrier.get("severity")).strip().upper())
def _entry_max_severity(entry: dict) -> str:
    ranks = [_severity_rank_of(cand) for cand in _entry_findings_chain(entry)]
    ranks.append(_severity_rank_of(entry))
    valid = [rank for rank in ranks if rank is not None]
    if not valid:
        return "unknown"
    return _RANK_TO_P.get(min(valid), "unknown")
def _normalize_sources(value: Any) -> list:
    if isinstance(value, str):
        raw = [value]
    elif isinstance(value, (list, tuple, set, frozenset)):
        raw = list(value)
    else:
        return []
    return sorted({text for text in (str_or(item).strip().upper()
                                     for item in raw) if text})
def _infer_domain(entry: dict) -> str:
    sources = tuple(_normalize_sources(entry.get("sources")))
    found = {source[0].upper() for source in sources if source}
    for domain in _DOMAINS:
        if domain in found:
            return domain
    return sources[0] if sources else "unknown"
def _entry_file_line(entry: dict) -> tuple:
    for cand in _entry_findings_chain(entry):
        file_path, line = _finding_file_line(cand)
        if file_path:
            return file_path, line
    return _finding_file_line(entry)
def _entry_rule_id(entry: dict) -> str:
    for cand in _entry_findings_chain(entry):
        rid = (str_or(cand.get("rule_id")) or str_or(cand.get("rule_family")))
        if rid:
            return rid
    return (str_or(entry.get("rule_id"))
            or str_or(entry.get("rule_family")))
def _entry_message(entry: dict) -> str:
    for cand in _entry_findings_chain(entry):
        msg = str_or(cand.get("message"))
        if msg:
            return msg
    return str_or(entry.get("message"))
def finding_identity(finding: dict, *, occurrence: int | None = None) -> str:
    data = finding if isinstance(finding, dict) else {}
    fid = str_or(data.get("finding_id"))
    if fid:
        return fid
    file_path, line = _finding_file_line(data)
    base = (f"<no-finding-id>:{str_or(data.get('rule_id'))}"
            f"@{file_path}:{line}")
    return base if occurrence is None else f"{base}#{occurrence}"
def make_finding_id(domain: str, rule_id: str, file_path: str,
                    line: int, message: str,
                    project: str = "") -> str:
    """台账 finding 身份。

    ``file_path`` 可能是项目内 basename（如 ``cad_bridge.py``），而账本已是跨
    目标共享的单一账本；若不拼项目作用域，两个项目的同名文件同行同规则会得
    到同一个 id，导致 B 项目的 finding 被 A 项目的 ``finding_resolved`` 当成
    已了结（静默漏报）。
    """
    scope = f"{str_or(project)}|" if project else ""
    raw = (f"{scope}{str_or(domain)}|{str_or(rule_id)}|{str_or(file_path)}|"
           f"{int_or(line, 0)}|{str_or(message)}")
    return "zb-" + hashlib.sha1(
        raw.encode("utf-8"), usedforsecurity=False).hexdigest()[:12]
def register_cv_findings_snapshot(
        skill_dir: str, report: dict,
        round_start_ts: str = _DEFAULT_ROUND_START_TS) -> dict:
    sd = normalize_skill_dir(skill_dir)
    if not isinstance(report, dict):
        return {"ok": False, "registered": 0, "skipped_dup": 0,
                "round_start_ts": "", "error": "report 非 dict"}
    project = path_scoped_namespace(sd)
    events = load_ledger_events(sd)
    round_ts = _snapshot_round_anchor(sd, round_start_ts, events, project)
    round_owners = {
        str_or(ev.get("project")).strip()
        for ev in events
        if round_ts and ev.get("event") == "round_open"
        and _round_anchor(ev.get("round_start_ts")) == round_ts
    }
    if project and any(owner != project for owner in round_owners):
        return {
            "ok": False, "registered": 0, "updated": 0, "skipped_dup": 0,
            "round_start_ts": round_ts, "by_conclusion": {}, "by_domain": {},
            "error": (
                f"轮次锚 {round_ts!r} 已由其他项目或无归属 round_open 使用 "
                f"（owners={sorted(round_owners)}）；请改用新的轮次锚，"
                "拒绝同锚跨项目登记造成串账与假成功"
            ),
        }
    # 取全局当前轮：追加式台账里若有其他项目更新的 round_open，向本项目旧轮
    # 追加 finding_seen 会落在 round_events 可见范围之外（假成功 + 静默丢失）。
    current_anchor = current_round_ts(events)
    known_round = any(
        ev.get("event") == "round_open"
        and _round_anchor(ev.get("round_start_ts")) == round_ts
        and (not project or str_or(ev.get("project")).strip() == project)
        for ev in events)
    if (round_ts and current_anchor and known_round
            and round_ts != current_anchor):
        return {
            "ok": False, "registered": 0, "updated": 0, "skipped_dup": 0,
            "round_start_ts": round_ts, "by_conclusion": {}, "by_domain": {},
            "error": (
                f"追加式台账拒绝重开历史轮 {round_ts!r}（当前轮 "
                f"{current_anchor!r}）；历史轮事件若跨 open 块追加会退出 "
                "round_events 可见作用域，形成假成功与 finding 静默丢失。"
                "请使用当前轮锚或新的轮次锚登记"
            ),
        }
    entries = _collect_snapshot_entries(report)
    wrote_round_open = _ensure_round_open(sd, events, round_ts, project)
    if wrote_round_open:
        events = load_ledger_events(sd)
    round_open_ok = bool(
        not round_ts or wrote_round_open
        or any(ev.get("event") == "round_open"
               and _round_anchor(ev.get("round_start_ts")) == round_ts
               and (not project or str_or(ev.get("project")).strip() == project)
               for ev in events))
    if not round_open_ok:
        return {
            "ok": False, "registered": 0, "updated": 0, "skipped_dup": 0,
            "round_start_ts": round_ts, "by_conclusion": {}, "by_domain": {},
            "error": f"round_open 登记缺失（round_start_ts={round_ts or '-'}）",
        }
    open_states = {fid: ev for fid, ev in _last_state_by_fid(events).items()
                   if ev.get("event") != "finding_resolved"}
    stats = _register_snapshot_entries(
        sd, entries, round_ts, open_states, project)
    prune_ledger(sd, load_ledger_events(sd))
    logger.info("[ZeroBacklog] 台账登记: %d 条新 finding，%d 条状态更新"
                "（重复跳过 %d，写失败 %d），结论分布=%s, 域分布=%s",
                stats["registered"], stats["updated"], stats["skipped_dup"],
                stats["write_failed"], stats["by_conclusion"], stats["by_domain"])
    write_failed = stats["write_failed"]
    ok = round_open_ok and write_failed == 0
    result = {"ok": ok, "registered": stats["registered"],
              "updated": stats["updated"], "skipped_dup": stats["skipped_dup"],
              "round_start_ts": round_ts, "by_conclusion": stats["by_conclusion"],
              "by_domain": stats["by_domain"]}
    if not ok:
        result["error"] = (
            f"台账写入失败 {write_failed} 条" if write_failed
            else f"round_open 登记缺失（round_start_ts={round_ts or '-'}）")
    return result
def _register_snapshot_entries(sd: str, entries: list, round_ts: str,
                               open_findings: dict,
                               project: str = "") -> dict:
    stats = {"registered": 0, "updated": 0, "skipped_dup": 0, "write_failed": 0,
             "by_conclusion": {}, "by_domain": {}}
    for entry in entries:
        fid, ev, conclusion, domain = _build_finding_seen_event(
            entry, round_ts, project)
        previous = open_findings.get(fid)
        if previous is not None:
            if any(previous.get(key) != ev.get(key)
                   for key in _FINDING_STATE_KEYS):
                if append_ledger_event(sd, ev):
                    stats["updated"] += 1
                    open_findings[fid] = ev
                else:
                    stats["write_failed"] += 1
            else:
                stats["skipped_dup"] += 1
            continue
        if append_ledger_event(sd, ev):
            stats["registered"] += 1
            open_findings[fid] = ev
            key = conclusion or "unknown"
            by_conclusion = stats["by_conclusion"]
            by_domain = stats["by_domain"]
            by_conclusion[key] = by_conclusion.get(key, 0) + 1
            by_domain[domain] = by_domain.get(domain, 0) + 1
        else:
            stats["write_failed"] += 1
    return stats
def _snapshot_round_anchor(sd: str, round_start_ts: str, events: list,
                           project: str = "") -> str:
    anchor = _round_anchor(round_start_ts)
    if not anchor:
        try:
            anchor = _round_anchor(peek_round_start_ts(sd))
        except Exception as _e:  # noqa: BLE001
            log_swallowed(__name__, _e,
                          context="register_cv_findings_snapshot:peek_round")
            anchor = ""
    if anchor:
        return anchor
    return _latest_own_round_anchor(events, project)
def _latest_own_round_anchor(events: list, project: str) -> str:
    """共享台账里只认领本项目开启的轮次。

    ``round_open`` 现在落 ``project``；别的项目的轮次不得被本项目认领，否则本
    轮 finding 会被登记进别人的轮次，门禁按轮次切分时跨项目误报。无归属的
    历史轮次（升级前写入）一律不认领。
    """
    if not project:
        return ""
    for ev in reversed(dict_items(events)):
        if ev.get("event") != "round_open":
            continue
        if str_or(ev.get("project")) == project:
            return _round_anchor(ev.get("round_start_ts"))
    return ""
_FINDING_STATE_KEYS = (
    "domain", "rule_id", "severity", "file", "line", "locator",
    "message", "conclusion", "confidence", "sources",
)
def _collect_snapshot_entries(report: dict) -> list:
    entries = []
    fi = report.get("findings_index")
    if isinstance(fi, list):
        entries.extend(e for e in fi if isinstance(e, dict))
    layer_2 = report.get("layer_2")
    cv_results = (layer_2.get("cv_results")
                  if isinstance(layer_2, dict) else None)
    if isinstance(cv_results, dict):
        for locator, result in cv_results.items():
            if isinstance(result, dict):
                entries.append({**result, "locator": locator})
    return entries
def _ensure_round_open(sd: str, events: list, round_ts: str,
                       project: str = "") -> bool:
    if not round_ts or any(
            ev.get("event") == "round_open"
            and _round_anchor(ev.get("round_start_ts")) == _round_anchor(round_ts)
            and (not project or str_or(ev.get("project")).strip() == project)
            for ev in events):
        return False
    return append_ledger_event(sd, {
        "event": "round_open", **_event_time_fields(),
        "round_start_ts": round_ts,
        "project": project,
    })
def _event_time_fields() -> dict:
    return {"ts": time.time(),
            "at": time.strftime(FMT_DATETIME, time.localtime()),
            "timestamp": time.strftime(FMT_DATETIME_ISO, time.localtime())}
def _build_finding_seen_event(entry: dict, round_ts: str,
                              project: str = "") -> tuple:
    sources = _normalize_sources(entry.get("sources"))
    domain = _infer_domain({"sources": sources})
    rule_id = _entry_rule_id(entry)
    file_path, line = _entry_file_line(entry)
    message = _entry_message(entry)
    fid = make_finding_id(domain, rule_id, file_path, line, message,
                          project)
    conclusion = str_or(entry.get("conclusion")).strip().lower()
    severity = _entry_max_severity(entry)
    ev = {
        "event": "finding_seen",
        **_event_time_fields(),
        "round_start_ts": round_ts,
        "finding_id": fid,
        "domain": domain,
        "rule_id": rule_id,
        "severity": severity,
        "file": file_path,
        "line": line,
        "locator": str_or(entry.get("locator")),
        "message": message[:200],
        "conclusion": conclusion,
        "confidence": normalize_confidence(
            entry.get("adjusted_confidence"), None),
        "sources": sources,
    }
    return fid, ev, conclusion, domain
def _historical_round_append_error(events: list, round_ts: str) -> str:
    """轮次可见性校验：追加事件必须落在日志尾部的当前轮内。

    取全局当前轮而不是项目当前轮：台账是追加式单日志，``round_events`` 只能
    看到「该轮 round_open 之后、下一个他轮 round_open 之前」的事件。其他项目
    已开新轮时，本项目旧轮的追加事件会落在可见范围之外，写入成功但门禁读不到
    ——用项目轮次作判据会把这种假成功放行。
    """
    anchor = _round_anchor(round_ts)
    current = current_round_ts(events)
    if anchor and current and anchor != current:
        return (
            f"追加式台账拒绝向历史轮 {anchor!r} 写入处置（全局当前轮 "
            f"{current!r}）；后续 round_open 会使追加事件退出该轮可见范围，"
            "形成 resolved 假成功。请先开启本项目新轮次再处置"
        )
    return ""
def resolve_backlog_item(skill_dir: str, finding_id: str, resolution: str,
                         rationale: str, actor: str = _DEFAULT_ACTOR) -> dict:
    sd = normalize_skill_dir(skill_dir)
    finding_id = str_or(finding_id).strip()
    resolution = str_or(resolution).strip()
    rationale = str_or(rationale).strip()
    _args_err = _validate_resolve_args(finding_id, resolution, rationale)
    if _args_err:
        return {"status": "error", "error": _args_err}
    if resolution == FP_RULE_SAMPLE_RESOLUTION:
        return _resolve_fp_rule_sample(sd, finding_id, rationale, actor)
    scope = build_round_scope(sd)
    round_ts, targets = scope.round_start_ts, scope.findings
    if finding_id not in {str_or(ev.get("finding_id"))
                          for ev in targets}:
        return {"status": "error",
                "error": f"finding_id {finding_id!r} 不在当前轮台账中"
                         "（拒绝幽灵处置）",
                "round_start_ts": round_ts}
    _applicability_err = _resolution_applicability_error(
        targets, finding_id, resolution)
    if _applicability_err:
        return {"status": "error", "error": _applicability_err,
                "round_start_ts": round_ts}
    append_err = _historical_round_append_error(
        load_ledger_events(sd), round_ts)
    if append_err:
        return {"status": "error", "error": append_err,
                "round_start_ts": round_ts}
    if resolution in FIXED_RESOLUTIONS:
        _proof_err = _verify_fixed_evidence(
            sd, targets, finding_id, resolution)
        if _proof_err:
            return {"status": "error", "error": _proof_err,
                    "round_start_ts": round_ts}
    ok = append_ledger_event(sd, {
        "event": "finding_resolved",
        **_event_time_fields(),
        "round_start_ts": round_ts,
        "finding_id": finding_id,
        **_resolution_metadata(targets, finding_id),
        "resolution": resolution,
        "rationale": rationale,
        "actor": str_or(actor) or _DEFAULT_ACTOR,
    })
    if not ok:
        return {"status": "error", "error": "台账事件写入失败"}
    logger.info("[ZeroBacklog] 处置回填: %s → %s (%s)",
                finding_id, resolution, rationale[:60])
    return {"status": "resolved", "finding_id": finding_id,
            "resolution": resolution, "round_start_ts": round_ts}
def _resolve_fp_rule_sample(sd: str, rule_id: str, rationale: str,
                            actor: str) -> dict:
    active, _fp_rule_errors = _load_fp_rules_snapshot(sd)
    if rule_id not in active:
        return {"status": "error",
                "error": f"误报规则 {rule_id!r} 不在生效规则清单中"
                         "（拒绝幽灵复核）"}
    events = load_ledger_events(sd)
    project = path_scoped_namespace(sd)
    round_ts = _snapshot_round_anchor(
        sd, _DEFAULT_ROUND_START_TS, events, project)
    if not round_ts:
        return {"status": "error", "round_start_ts": "",
                "error": "当前项目无可用轮次，拒绝写入无归属的抽样复核事件"}
    append_err = _historical_round_append_error(events, round_ts)
    if append_err:
        return {"status": "error", "error": append_err,
                "round_start_ts": round_ts}
    ok = append_ledger_event(sd, {
        "event": "finding_resolved",
        **_event_time_fields(),
        "round_start_ts": round_ts,
        "finding_id": rule_id,
        "rule_id": rule_id,
        "resolution": FP_RULE_SAMPLE_RESOLUTION,
        "rationale": rationale,
        "actor": str_or(actor) or _DEFAULT_ACTOR,
    })
    if not ok:
        return {"status": "error", "error": "台账事件写入失败"}
    logger.info("[ZeroBacklog] 误报规则抽样复核: %s (%s)",
                rule_id, rationale[:60])
    return {"status": "resolved", "rule_id": rule_id,
            "resolution": FP_RULE_SAMPLE_RESOLUTION,
            "round_start_ts": round_ts}
def _target_event(targets: list, finding_id: str) -> dict:
    for ev in targets:
        if str_or(ev.get("finding_id")) == finding_id:
            return ev
    return {}
def _resolution_metadata(targets: list, finding_id: str) -> dict:
    ev = _target_event(targets, finding_id)
    if not ev:
        return {}
    return {
        "rule_id": str_or(ev.get("rule_id")),
        "severity": str_or(ev.get("severity")),
        "domain": str_or(ev.get("domain")),
        "file": str_or(ev.get("file")),
        "line": int_or(ev.get("line"), 0),
        "locator": str_or(ev.get("locator")),
    }
def _resolution_applicability_error(targets: list, finding_id: str,
                                    resolution: str) -> str | None:
    if resolution != "suppressed_reviewed":
        return None
    conclusion = str_or(
        _target_event(targets, finding_id).get("conclusion")).strip().lower()
    if conclusion == "suppressed":
        return None
    return (
        f"resolution=suppressed_reviewed 仅适用于被抑制 finding"
        f"（conclusion=suppressed），当前 finding 结论为 "
        f"{conclusion or 'unknown'}——该处置会绕过修复/误报固化证据门；"
        "真实问题请用 fixed/ai_fixed/succeeded（须精确修复证据），"
        "误报请用 fp_confirmed（须固化误报规则）")
def _validate_resolve_args(finding_id: str, resolution: str,
                           rationale: str) -> str | None:
    if not finding_id:
        return "finding_id 必填"
    if resolution not in TERMINAL_RESOLUTIONS:
        return (f"resolution 非法: {resolution!r}（合法值域 "
                f"{sorted(TERMINAL_RESOLUTIONS)}）")
    if len(rationale) < _MIN_RATIONALE_LEN:
        return (f"rationale 太短（<{_MIN_RATIONALE_LEN} 字符），"
                "处置理由必须可审计")
    return None
def _verify_fixed_evidence(sd: str, candidate_events: list,
                           finding_id: str, resolution: str) -> str | None:
    _f_src = _target_event(candidate_events, finding_id)
    anchor = str_or(_f_src.get("round_start_ts")).strip()
    ctx = build_terminal_context(sd, {}, anchor)
    _proof = _fix_proof(_finding_keys(_f_src), ctx)
    if not _proof:
        return (f"resolution={resolution} 要求精确修复证据："
                "治疗状态 fixed/ai_fixed/succeeded 终态或该 finding 的 "
                "approve_and_fix 精确裁决（locator/三元组）均缺失——"
                "rule_id/basename 株连裁决无逐项修复事实，不作证据；"
                "请先完成修复执行，或以 fp_confirmed/rejected/deferred "
                "等语义处置")
    return None
def audit_fp_mask(
        skill_dir: str, round_start_ts: str = _DEFAULT_ROUND_START_TS) -> dict:
    sd = normalize_skill_dir(skill_dir)
    events, ledger_errors = _load_ledger_snapshot(sd)
    project = path_scoped_namespace(sd)
    round_ts = (_round_anchor(round_start_ts)
                or current_round_ts(events, project))
    return _audit_fp_mask_from_snapshot(sd, events, round_ts, ledger_errors)
def _audit_fp_mask_from_snapshot(
        sd: str, events: list, round_ts: str, ledger_errors: list,
        ctx: TerminalVerdictContext | None = None) -> dict:
    project = path_scoped_namespace(sd)
    cur = project_round_events(events, round_ts, project)
    resolved = resolved_map(cur)
    if ctx is None:
        ctx = build_terminal_context(sd, resolved, round_ts)
    suppressed = _suppressed_events(
        events, cur, round_ts, project=project)
    unreviewed, per_rule = _scan_unreviewed_suppressed(suppressed, ctx)
    fp_rules_active, fp_rule_errors = _load_fp_rules_snapshot(sd)
    fp_sampled_rules, fp_unsampled = _fp_rule_sample_unreviewed(
        events, round_ts, fp_rules_active, project=project)
    passed = (not unreviewed and not fp_unsampled
              and not ledger_errors and not fp_rule_errors)
    if not passed:
        logger.warning("[ZeroBacklog] 误报掩盖审计未通过: %d/%d 条被抑制 "
                       "finding 未经复核, %d/%d 条抽样规则未复核, "
                       "台账错误 %d 条, 规则配置错误 %d 条",
                       len(unreviewed), len(suppressed),
                       len(fp_unsampled), len(fp_sampled_rules),
                       len(ledger_errors), len(fp_rule_errors))
    return {
        "passed": passed,
        "round_start_ts": round_ts,
        "total_suppressed": len(suppressed),
        "reviewed": len(suppressed) - len(unreviewed),
        "unreviewed": len(unreviewed),
        "unreviewed_items": unreviewed[:_BACKLOG_ITEMS_PREVIEW],
        "unreviewed_truncated": max(0, len(unreviewed) - _BACKLOG_ITEMS_PREVIEW),
        "fp_rules_active": fp_rules_active,
        "per_rule_suppressed": per_rule,
        "carried_suppressed": sum(1 for f in suppressed if f.get("carried")),
        "fp_sampled_rules": fp_sampled_rules,
        "fp_sampled_count": len(fp_sampled_rules),
        "fp_sampled_reviewed": len(fp_sampled_rules) - len(fp_unsampled),
        "fp_sampled_unreviewed": fp_unsampled,
        "fp_sample_passed": not fp_unsampled,
        "ledger_errors": list(ledger_errors),
        "fp_rule_errors": fp_rule_errors,
    }
def _suppressed_events(events: list, cur: list, round_ts: str,
                       project: str = "") -> list:
    suppressed = [ev for ev in _latest_finding_seen(cur)
                  if str_or(ev.get("conclusion")).strip().lower() == "suppressed"]
    suppressed += [ev for ev in carried_findings(
        events, cur, round_ts, project=project)
                   if str_or(ev.get("conclusion")).strip().lower() == "suppressed"]
    return suppressed
def _scan_unreviewed_suppressed(suppressed: list,
                                ctx: TerminalVerdictContext
                                ) -> tuple[list, dict]:
    unreviewed = []
    per_rule: dict = {}
    for f in suppressed:
        rid0 = str_or(f.get("rule_id"))
        per_rule[rid0] = per_rule.get(rid0, 0) + 1
        fid = str_or(f.get("finding_id"))
        if fid in ctx.resolved:
            continue
        if classify_terminal(f, ctx):
            continue
        unreviewed.append({
            "finding_id": fid,
            "rule_id": rid0,
            "severity": str_or(f.get("severity")),
            "domain": str_or(f.get("domain")),
            "file": str_or(f.get("file")),
            "line": int_or(f.get("line"), 0),
            "message": str_or(f.get("message"))[:120],
            "carried": bool(f.get("carried")),
            "origin_round": str_or(f.get("origin_round")),
        })
    return unreviewed, per_rule
def _fp_rule_ids(rules_doc: Any) -> list:
    rules = (rules_doc.get("rules") if isinstance(rules_doc, dict)
             else rules_doc)
    if isinstance(rules, dict):
        rules = list(rules)
    if not isinstance(rules, list):
        return []
    return sorted(filter(None, {
        str_or(r.get("rule_id") if isinstance(r, dict) else r).strip()
        for r in rules}))
def _load_fp_rules_snapshot(sd: str) -> tuple[list, list[str]]:
    rp = ""
    try:
        rp = fp_rules_path(sd)
        if not os.path.isfile(rp):
            return [], []
        with open(rp, encoding="utf-8-sig", errors="replace") as f:
            document = json.load(f)
        if not isinstance(document, (dict, list)):
            return [], [f"{rp}: 顶层必须是 JSON object 或 array"]
        if (isinstance(document, dict) and "rules" in document
                and not isinstance(document["rules"], (dict, list))):
            return [], [f"{rp}: rules 必须是 JSON object 或 array"]
        return _fp_rule_ids(document), []
    except (OSError, ValueError, RuntimeError, RecursionError) as _e:
        log_swallowed(__name__, _e, context="audit_fp_mask:fp_rules")
        location = rp or sd
        return [], [f"{location}: {type(_e).__name__}: {_e}"]
def _fp_rule_sample_unreviewed(events: list, round_ts: str,
                               fp_rules_active: list,
                               project: str = "") -> tuple[list, list]:
    fp_sample_size = max(
        FP_RULE_AUDIT_SAMPLE_MIN,
        int(len(fp_rules_active) * FP_RULE_AUDIT_SAMPLE_RATIO))
    fp_sample_size = min(fp_sample_size, len(fp_rules_active))
    _sample_seed = str_or(round_ts) or "ledger_baseline"
    fp_sampled_rules = sorted(
        fp_rules_active,
        key=lambda r: hashlib.sha1(
            f"{_sample_seed}:{r}".encode(), usedforsecurity=False).hexdigest()
    )[:fp_sample_size]
    _sampled_reviewed = {
        str_or(ev.get("rule_id")).strip() or str_or(ev.get("finding_id")).strip()
        for ev in project_round_events(events, round_ts, project)
        if (ev.get("event") == "finding_resolved"
            and str_or(ev.get("resolution")).strip().lower()
            == FP_RULE_SAMPLE_RESOLUTION)
    }
    _sampled_reviewed.discard("")
    return fp_sampled_rules, [r for r in fp_sampled_rules
                              if r not in _sampled_reviewed]
def _report_skeleton(round_ts: str, fp_audit: dict) -> dict:
    fp_audit = as_dict(fp_audit)
    def _errors(value: Any) -> list[str]:
        return [text for text in (str_or(item).strip()
                                  for item in normalize_list_field(value))
                if text]
    return {
        "passed": False,
        "ledger_empty": False,
        "round_start_ts": round_ts,
        "total_findings": 0,
        "carried_count": 0,
        "terminal_count": 0,
        "terminal_fuzzy_count": 0,
        "backlog_count": 0,
        "backlog_by_domain": {},
        "backlog_by_severity": {},
        "backlog_by_stage": {},
        "backlog_items": [],
        "ledger_errors": _errors(fp_audit.get("ledger_errors")),
        "fp_rule_errors": _errors(fp_audit.get("fp_rule_errors")),
        "fp_mask_audit": fp_audit,
        "actions_required": [],
    }
_LEDGER_MISSING_ACTION = (
    "ledger_missing: 管线轮次存在但台账未登记——重跑诊断聚合"
    "（register_cv_findings_snapshot）修复登记链，人工排查台账"
    "写盘失败原因")
def fp_mask_actions(fp_audit: dict) -> list:
    fp_audit = as_dict(fp_audit)
    actions = []
    if fp_audit.get("gate_error"):
        actions.append(
            "fp_mask_audit_error: 误报掩盖审计执行异常——修复 audit_fp_mask "
            "异常后重新审计（unreviewed=-1 为异常哨兵，非待复核条数）")
    ledger_errors = fp_audit.get("ledger_errors") or []
    if ledger_errors:
        actions.append(
            f"ledger_read: {len(ledger_errors)} 条台账读取/解析错误"
            "——修复或恢复 zero_backlog_ledger.jsonl 后重新审计")
    fp_rule_errors = fp_audit.get("fp_rule_errors") or []
    if fp_rule_errors:
        actions.append(
            f"fp_rules_read: {len(fp_rule_errors)} 条误报规则读取/解析错误"
            "——修复或恢复 fp_rules.json 后重新审计")
    unreviewed = int_or(fp_audit.get("unreviewed"), 0)
    if unreviewed > 0:
        actions.append(f"fp_mask: {unreviewed} 条误报抑制项未复核"
                       "（audit_fp_mask）")
    sampled_unreviewed = fp_audit.get("fp_sampled_unreviewed") or []
    if isinstance(sampled_unreviewed, (list, tuple)) and sampled_unreviewed:
        sample_total = int_or(fp_audit.get("fp_sampled_count"),
                              len(sampled_unreviewed))
        rules = "、".join(str_or(r) for r in sampled_unreviewed[:5])
        actions.append(
            f"fp_rule_sample: {len(sampled_unreviewed)}/{sample_total} 条生效"
            f"误报规则抽样未复核（{rules}）——逐条复核规则抑制有效性"
            f"（resolve_backlog_item resolution={FP_RULE_SAMPLE_RESOLUTION}）")
    return actions
def _pipeline_round_ledger_missing(sd: str, events: list) -> tuple[str, bool]:
    project = path_scoped_namespace(sd)
    try:
        pipeline_round = _round_anchor(peek_round_start_ts(sd))
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context="check_zero_backlog:peek_round")
        pipeline_round = ""
    ledger_missing = bool(
        pipeline_round
        and not any(ev.get("event") == "round_open"
                    and _round_anchor(ev.get("round_start_ts")) == pipeline_round
                    and str_or(ev.get("project")).strip() == project
                    for ev in events))
    return pipeline_round, ledger_missing
def _build_empty_backlog_report(sd: str, round_ts: str, fp_audit: dict,
                                events: list) -> dict:
    pipeline_round, ledger_missing = _pipeline_round_ledger_missing(sd, events)
    if ledger_missing:
        logger.error("[ZeroBacklog] 登记缺失阻塞: 管线轮 %s 存在但台账无该轮"
                     "事件（登记软失败=静默绕过通道已封闭）", pipeline_round)
    actions = ([_LEDGER_MISSING_ACTION] if ledger_missing else [])
    actions.extend(fp_mask_actions(fp_audit))
    return {
        **_report_skeleton(round_ts, fp_audit),
        "passed": bool(fp_audit.get("passed", False)) and not ledger_missing,
        "ledger_empty": True,
        "ledger_missing": ledger_missing,
        "actions_required": actions,
    }
def treatment_status(keys: _FindingKeys,
                     ctx: TerminalVerdictContext) -> str:
    statuses = [str_or(value).strip().lower()
                for value in ctx.t_index.iter_evidence(keys)]
    for status in statuses:
        if status in FIXED_RESOLUTIONS:
            return status
    return statuses[0] if statuses else ""
def _treatment_fix_proof(keys: _FindingKeys,
                         ctx: TerminalVerdictContext) -> str:
    return ("treatment_state"
            if treatment_status(keys, ctx) in FIXED_RESOLUTIONS else "")
def _verdict_fix_proof(keys: _FindingKeys,
                       ctx: TerminalVerdictContext) -> str:
    source, decisive = _verdict_hit_for_context(keys, ctx)
    if source == "ai_verdict_exact" and decisive & _FIX_VETO_VERDICTS:
        return ""
    fixed = any(
        "approve_and_fix" in _fresh_verdicts(verdicts, keys.at)
        for index in _verdict_indexes_for_context(keys, ctx)
        for verdicts in index.iter_evidence(keys, require_complete=True))
    return "ai_verdict_exact" if fixed else ""
def _fix_proof(keys: _FindingKeys, ctx: TerminalVerdictContext) -> str:
    return (_treatment_fix_proof(keys, ctx)
            or _verdict_fix_proof(keys, ctx))
def terminal_verb(finding: dict, ctx: TerminalVerdictContext) -> str:
    verb = ledger_resolution(finding, ctx.resolved)
    if verb:
        return verb
    keys = _finding_keys(finding)
    status = treatment_status(keys, ctx)
    if status:
        return status
    _label, verdicts = _verdict_hit_for_context(keys, ctx)
    return "|".join(sorted(verdicts))
def p0_has_fixed_proof(finding: dict,
                       ctx: TerminalVerdictContext) -> bool:
    resolution = ledger_resolution(finding, ctx.resolved)
    if resolution in FIXED_RESOLUTIONS:
        return True
    return not resolution and bool(_fix_proof(_finding_keys(finding), ctx))
_CONTEXT_DIGEST_KEYS = (
    "review_id", "channel", "target", "description", "severity",
    "file_path", "line", "strategy", "rule_id", "rule_id_canonical",
    "finding_id",
    "code_context", "orig_status",
    "fix_guidance", "cv_context", "diagnosis_evidence",
    "function_summary", "fixer_risk", "fix_precheck",
    "fix_experience", "fix_plan", "treatment_history",
    "plan", "entry", "proposal",
    "cv_evidence",
    "provenance", "provenance_strata", "evidence_completeness",
    "rule_fp_history", "adjustment_history", "enhancement_history",
    "feedback_history",
    "suggested_value", "expected_impact", "confidence",
    "item_kind", "target_kind",
    "kind", "level",
    "index",
    "fixed_source", "safety_gate", "source",
    "requires_fixed_source", "apply_hint",
)
def build_review_target_digest(target) -> dict:
    t = target if isinstance(target, dict) else {}
    return {k: t.get(k) for k in _CONTEXT_DIGEST_KEYS
            if t.get(k) not in (None, "", [], {})}
_VERDICTS_JSONL_NAME = "ai_review_verdicts.jsonl"
# 审核留痕总量预算：4MB ≈ 850 条（分级摘要后单条中位 4.7KB）。
# 原 8MB 在 219 条/24 分钟的写入速率下约 11 小时才触顶，实际长期无界。
_VERDICTS_JSONL_MAX_BYTES = 4 * 1024 * 1024
def _abs_file_path_for_trace(file_path, skill_dir: str) -> str:
    fp = file_path if isinstance(file_path, str) else ""
    if not fp:
        return ""
    if os.path.isabs(fp):
        return fp
    if not skill_dir:
        return ""
    return os.path.abspath(os.path.join(skill_dir, fp))
_VERDICT_TRACE_VERSION = 5
def _build_verdict_trace_entry(review: dict, assessment: dict | None,
                               result: dict, skill_dir: str | None,
                               fixed_source_sha256: str) -> dict:
    _at_iso = time.strftime(FMT_DATETIME_ISO)
    _sd = normalize_text(skill_dir)
    _result = as_dict(result)
    return {
        "trace_version": _VERDICT_TRACE_VERSION,
        "timestamp": _at_iso,
        "review_id": normalize_text(review.get("review_id")),
        "channel": normalize_text(review.get("channel")),
        "target": normalize_text(review.get("target")),
        "rule_id": normalize_text(review.get("rule_id")),
        "finding_id": normalize_text(review.get("finding_id")),
        "file_path": normalize_text(review.get("file_path")),
        "file_path_abs": _abs_file_path_for_trace(
            review.get("file_path", ""), _sd),
        "line": normalize_line_no(review.get("line")),
        "skill_dir": _sd,
        "original_severity": normalize_text(review.get("severity")),
        "assessment": as_dict(assessment),
        "execution_status": normalize_text(_result.get("status")),
        "execution_reason": normalize_text(_result.get("reason"))[:800],
        "targeted_regression": as_dict(_result.get("targeted_regression")),
        "fixed_source_sha256": normalize_text(fixed_source_sha256),
        "fix_result_path": normalize_text(_result.get("fix_result_path")),
        "fix_evidence": as_dict(_result.get("fix_evidence")),
        "review_target_digest": _digest_for_verdict_log(review),
        "at": _at_iso,
        "at_ts": timestamp_ms(),
        "round_start_ts": peek_round_start_ts(_sd),
        "phase": peek_pipeline_phase(_sd),
    }
def _append_verdict_trace(entry: dict, skill_dir: str | None) -> None:
    if not skill_dir:
        return
    try:
        _vlog = ai_review_verdicts_path(skill_dir)
    except Exception as exc:  # noqa: BLE001
        logger.warning(
            "[AIReview] 审核留痕路径解析失败（不影响执行）: %s", exc)
        return
    try:
        _line = json.dumps(entry, ensure_ascii=False, default=str)
    except (TypeError, ValueError, RecursionError) as _ve:
        logger.warning("[AIReview] 审核留痕序列化失败（不影响执行）: %s", _ve)
        return
    if not append_jsonl_locked(_vlog, _line):
        logger.warning("[AIReview] 审核留痕持久化失败（不影响执行）: %s", _vlog)
        return
    try:
        prune_jsonl_file(_vlog, _VERDICTS_JSONL_MAX_BYTES)
    except Exception as _pe:  # noqa: BLE001
        logger.warning("[AIReview] 审核留痕裁剪失败（条目已落盘）: %s", _pe)
def write_verdict_trace(review: dict, assessment: dict | None, result: dict,
                        skill_dir: str | None = None,
                        fixed_source_sha256: str = "") -> None:
    try:
        entry = _build_verdict_trace_entry(
            review, assessment, result, skill_dir, fixed_source_sha256)
    except Exception as e:  # noqa: BLE001
        logger.warning("[AIReview] 审核留痕条目构造失败（不影响执行结果）: %s", e)
        return
    try:
        logger.info("[AIReview] verdict %s",
                    json.dumps(entry, ensure_ascii=False, default=str))
    except Exception as e:  # noqa: BLE001
        logger.warning("[AIReview] 审核留痕日志通道失败（持久化通道继续）: %s", e)
    _append_verdict_trace(entry, skill_dir)
_VERDICT_TRACE_STR_KEYS = (
    "review_id", "channel", "target", "rule_id", "finding_id",
    "file_path", "file_path_abs", "skill_dir",
    "original_severity", "execution_status", "execution_reason",
    "fixed_source_sha256", "fix_result_path",
    "at", "at_ts", "timestamp", "round_start_ts", "phase",
)
_VERDICT_TRACE_DICT_KEYS = (
    "assessment", "targeted_regression", "fix_evidence",
    "review_target_digest",
)
def _normalize_trace_version(value) -> int:
    if isinstance(value, int) and not isinstance(value, bool) and value >= 1:
        return value
    return 1
def _normalize_verdict_trace_entry(entry: dict) -> dict:
    out = dict(entry) if isinstance(entry, dict) else {}
    for key in _VERDICT_TRACE_STR_KEYS:
        out[key] = normalize_text(out.get(key))
    for key in _VERDICT_TRACE_DICT_KEYS:
        out[key] = as_dict(out.get(key))
    out["line"] = normalize_line_no(out.get("line"))
    out["trace_version"] = _normalize_trace_version(out.get("trace_version"))
    if not out["timestamp"] and out["at"]:
        out["timestamp"] = out["at"]
    return out
def _read_verdict_lines(path: str) -> list[str]:
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as f:
            return f.readlines()
    except OSError as _e:
        log_swallowed(__name__, _e, context='get_ai_review_verdicts:OSError')
        return []
def _filter_value_matches(raw: Any, wanted: Any) -> bool:
    if raw is None:
        return False
    return normalize_text(raw).strip().lower() == normalize_text(
        wanted).strip().lower()
def _verdict_matches_filters(entry: dict, round_start_ts, channel,
                             phase) -> bool:
    round_mismatch = (
        bool(normalize_text(round_start_ts).strip())
        and not (
            _filter_value_matches(entry.get("round_start_ts"), round_start_ts)
            or round_anchor_equiv_form(entry.get("round_start_ts"))
            == round_anchor_equiv_form(round_start_ts)))
    channel_mismatch = (channel is not None
                        and not _filter_value_matches(
                            entry.get("channel"), channel))
    phase_mismatch = (phase is not None
                      and not _filter_value_matches(
                          entry.get("phase"), phase))
    return not (round_mismatch or channel_mismatch or phase_mismatch)
def _parse_verdict_line(line: str) -> dict | None:
    line = line.strip()
    if not line:
        return None
    try:
        entry = json.loads(line)
    except (ValueError, RecursionError) as exc:
        log_swallowed(__name__, exc,
                      context='get_ai_review_verdicts:BadLine')
        return None
    return entry if isinstance(entry, dict) else None
def get_ai_review_verdicts(skill_dir: str,
                           round_start_ts: str | None = None,
                           channel: str | None = None,
                           phase: str | None = None) -> list[dict]:
    sd = normalize_skill_dir(skill_dir)
    if round_start_ts is None:
        round_start_ts = peek_round_start_ts(sd)
    try:
        path = ai_review_verdicts_path(sd)
    except Exception as exc:  # noqa: BLE001
        logger.warning(
            "[AIReview] 裁决留痕路径解析失败（按无留痕处理）: %s", exc)
        return []
    if not os.path.isfile(path):
        return []
    out: list[dict] = []
    for line in _read_verdict_lines(path):
        entry = _parse_verdict_line(line)
        if entry is None:
            continue
        if not _verdict_matches_filters(entry, round_start_ts, channel, phase):
            continue
        out.append(_normalize_verdict_trace_entry(entry))
    return out
class _VerdictStats(NamedTuple):
    by_verdict: dict[str, int]
    fp_count: int
    exec_failed: list[dict[str, Any]]
    rule_freq: dict[str, int]
def _index_latest_approved(entries: list[dict[str, Any]]) -> dict[str, int]:
    latest_approved_idx: dict[str, int] = {}
    for index, event in enumerate(entries):
        assessment = event.get("assessment")
        verdict = (str_or(assessment.get("verdict")).strip().lower()
                   if isinstance(assessment, dict) else "")
        if (verdict in ("approve_and_fix", "approve")
                and str_or(event.get("execution_status")).strip()):
            review_id = str_or(event.get("review_id")).strip()
            if review_id:
                latest_approved_idx[review_id] = index
    return latest_approved_idx
def _is_broken_exec_link(verdict: str, status: str, event: dict[str, Any],
                         index: int, latest_approved_idx: dict[str, int]) -> bool:
    if verdict not in _EXECUTION_REQUIRED_VERDICTS or not status:
        return False
    ok_statuses = (_APPROVE_AND_FIX_EXECUTION_OK_STATUSES
                   if verdict == "approve_and_fix"
                   else APPROVED_EXECUTION_OK_STATUSES)
    if status in ok_statuses:
        return False
    review_id = str_or(event.get("review_id")).strip()
    return not (
        review_id and latest_approved_idx.get(review_id, index) != index)
def _collect_verdict_stats(
        entries: list[dict[str, Any]],
        latest_approved_idx: dict[str, int]) -> _VerdictStats:
    by_verdict: dict[str, int] = {}
    fp_count = 0
    exec_failed: list[dict[str, Any]] = []
    rule_freq: dict[str, int] = {}
    for index, event in enumerate(entries):
        assessment = event.get("assessment")
        verdict = (str_or(assessment.get("verdict")).strip().lower()
                   if isinstance(assessment, dict) else "") or "unknown"
        by_verdict[verdict] = by_verdict.get(verdict, 0) + 1
        if verdict == "reject_as_fp":
            fp_count += 1
        status = str_or(event.get("execution_status")).strip().lower()
        if _is_broken_exec_link(
                verdict, status, event, index, latest_approved_idx):
            exec_failed.append(event)
        rule_id = str_or(event.get("rule_id")).strip()
        if rule_id:
            rule_freq[rule_id] = rule_freq.get(rule_id, 0) + 1
    return _VerdictStats(by_verdict, fp_count, exec_failed, rule_freq)
def load_ai_review_summary(skill_dir: str | None = None) -> dict[str, Any]:
    base = {"total": 0, "by_verdict": {}, "fp_count": 0, "fp_ratio": 0.0,
            "exec_failed": [], "exec_failed_count": 0,
            "top_rules": [], "latest": []}
    if not skill_dir:
        return base
    try:
        entries: list[dict[str, Any]] = get_ai_review_verdicts(
            skill_dir, round_start_ts="")
        if not entries:
            return base
        latest_approved_idx = _index_latest_approved(entries)
        stats = _collect_verdict_stats(entries, latest_approved_idx)
        total = len(entries)
        top = sorted(stats.rule_freq.items(),
                     key=lambda item: (-item[1], item[0]))[:5]
        return {
            "total": total,
            "by_verdict": stats.by_verdict,
            "fp_count": stats.fp_count,
            "fp_ratio": round(stats.fp_count / total, 3) if total else 0.0,
            "exec_failed": stats.exec_failed[-10:],
            "exec_failed_count": len(stats.exec_failed),
            "top_rules": top,
            "latest": entries[-5:],
        }
    except Exception as exc:
        logger.warning("[fupan] AI审核裁决摘要读取跳过（按空摘要继续）: %s",
                       exc, exc_info=True)
        return base
VERDICT_TRACE_KEY_SPEC: dict[str, str] = {
    "trace_version": f"留痕 schema 版本（v2 起写入，当前 v{_VERDICT_TRACE_VERSION}；v1 历史条目读侧回填 1，v2-v4 读侧可辨；演进锚点 SSOT=_VERDICT_TRACE_VERSION）",
    "timestamp": "裁决时间（ISO 格式，与 at 同源；与阶段留痕同名时间键，双链按 round_start_ts+timestamp 对齐追溯）",
    "review_id": "审核项标识（TREAT-/FDB-/ENH- 等通道前缀编号）",
    "channel": "审核通道（treatment/feedback/enhancement/adjustment/cleanup/cv_uncertain/security）",
    "target": "审核目标（语义随通道：rule_id/locator/adjustment_key，收频道 target_kind 标注）",
    "rule_id": "规则号（误报固化/规则历史 FP 率关联键）",
    "finding_id": "finding 身份锚（v5 起写入：诊断→治疗→审核→裁决全链 join 主键；"
                "treatment 通道为 CV 收集期生成格式 {mid}:{file}:{line}:{rule_id}，"
                "凭本键直接回查诊断 finding 与归零台账事件；无 finding 级定位的通道恒空串；"
                "v1-v4 历史条目读侧回填空串=归属不可考，不臆造）",
    "file_path": "目标文件路径（技能根相对或绝对；v3 起完整路径另见 file_path_abs）",
    "file_path_abs": "目标文件绝对路径（v3 起写入；v1/v2 历史条目读侧回填空串——相对入库形态跨会话脱离原 cwd 即失锚，本键为追溯定位锚，确定性消引不经文件系统查找）",
    "skill_dir": "目标技能根归属锚（v4 起写入，与阶段留痕 v3 同词；无文件通道 file_path_abs 恒空时单条裁决跨会话仍可自明归属；v1-v3 历史条目读侧回填空串=归属不可考，不臆造）",
    "line": "目标行号（非负 int，0=文件级）",
    "original_severity": "通道原始严重性（P0-P3）",
    "assessment": "四维审核结构化裁决（verdict/severity_assessment/fixability/trade_off/fp_or_real/fix_approach 等）",
    "execution_status": "裁决执行结果终态（ai_fixed/applied/approved/needs_fixed_source/failed 等；成功词汇表 SSOT=APPROVED_EXECUTION_OK_STATUSES）",
    "execution_reason": "执行结果原因说明（截断 800 字符）",
    "targeted_regression": "写盘后定向回归证据（status/tests/reason；绝不跑全量回归）",
    "fixed_source_sha256": "修复源码全文指纹（写盘源码可追溯锚）",
    "fix_result_path": "修复源码对快照路径（修复前后对照留证）",
    "fix_evidence": "改码执行证据（写盘/回滚/验证明细）",
    "review_target_digest": "审核时 AI 所见候选依据摘要（超 20K 降为键清单占位；键集 SSOT=_CONTEXT_DIGEST_KEYS）",
    "at": "裁决时间（ISO 格式，兼容键；统一消费键为 timestamp）",
    "at_ts": "裁决时间（17 位毫秒戳，跨文件时序免双格式解析）",
    "round_start_ts": "管线轮次标识（与阶段留痕同源的全链追溯锚）",
    "phase": "裁决发生时的管线相位（ai_fix_pending 阶段4b / evolution_pending 阶段6e 等裁决语义可复原）",
}
def describe_verdict_trace_keys() -> dict:
    return dict(VERDICT_TRACE_KEY_SPEC)
def fixed_source_sha256(fixed_source) -> str:
    if not fixed_source:
        return ""
    try:
        return hashlib.sha256(
            str(fixed_source).encode("utf-8", errors="replace")).hexdigest()
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='fixed_source_sha256:Exc')
        return ""
# 单条留痕配额。实测全量 digest 中位数 13.8KB（``provenance`` 7.2KB +
# ``fix_plan`` 6.2KB + ``code_context`` 1.4KB 占 86%），原 20KB 配额下几乎
# 从不降级，219 条即 2.7MB。降为 8KB 后由 ``_shrink_digest_value`` 做
# 分级摘要，保留可追溯骨架（字段名/键清单/标量），体积中位降至 4.7KB。
_VERDICT_LOG_DIGEST_LIMIT = 8 * 1024
# 分级摘要参数：字符串字段截断长度、嵌套 dict 保留键数、嵌套深度上限。
# 三者共同决定“可追溯骨架”的粒度：够看清有哪些依据，不够还原本体载荷。
_DIGEST_STR_SHRINK_CHARS = 256
_DIGEST_DICT_SHRINK_ITEMS = 12
_DIGEST_SHRINK_MAX_DEPTH = 2
_DIGEST_CORE_KEYS = (
    "review_id", "channel", "target", "rule_id", "rule_id_canonical",
    "finding_id",
    "file_path", "line", "severity", "description",
    "item_kind", "target_kind", "index", "strategy")
def _shrink_digest_value(value, depth: int = 0):
    """把单个 digest 字段压到可追溯骨架。

    标量原样保留；字符串截断到 ``_DIGEST_STR_SHRINK_CHARS``；嵌套 dict 在
    ``_DIGEST_SHRINK_MAX_DEPTH`` 层以内保留前 ``_DIGEST_DICT_SHRINK_ITEMS``
    个键，更深的降为 ``{"_key_count": n}``；列表同构截断。这样留痕仍能
    回答“审核时 AI 看了哪些依据”，但不再携带完整载荷。
    """
    if isinstance(value, str):
        if len(value) <= _DIGEST_STR_SHRINK_CHARS:
            return value
        return value[:_DIGEST_STR_SHRINK_CHARS] + "…<已截断>"
    if isinstance(value, (int, float, bool)) or value is None:
        return value
    if isinstance(value, dict):
        if depth >= _DIGEST_SHRINK_MAX_DEPTH:
            return {"_key_count": len(value)}
        shrunk = {
            str(key): _shrink_digest_value(item, depth + 1)
            for key, item in list(value.items())[:_DIGEST_DICT_SHRINK_ITEMS]}
        if len(value) > _DIGEST_DICT_SHRINK_ITEMS:
            shrunk["_more_keys"] = len(value) - _DIGEST_DICT_SHRINK_ITEMS
        return shrunk
    if isinstance(value, (list, tuple)):
        kept = [_shrink_digest_value(item, depth + 1)
                for item in value[:_DIGEST_DICT_SHRINK_ITEMS]]
        if len(value) > _DIGEST_DICT_SHRINK_ITEMS:
            kept.append(f"…<余 {len(value) - _DIGEST_DICT_SHRINK_ITEMS} 项>")
        return kept
    text = str(value)
    return (text[:_DIGEST_STR_SHRINK_CHARS] + "…<已截断>"
            if len(text) > _DIGEST_STR_SHRINK_CHARS else text)
def _digest_for_verdict_log(review) -> dict:
    try:
        d = build_review_target_digest(review if isinstance(review, dict) else {})
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_digest_for_verdict_log:Exc')
        return {}
    try:
        if len(json.dumps(d, ensure_ascii=False, default=str).encode(
                "utf-8")) <= _VERDICT_LOG_DIGEST_LIMIT:
            return d
        # 一级降级：逐字段摘要（保留全部字段名，重载荷降为骨架）。
        shrunk = {
            str(key): _shrink_digest_value(item)
            for key, item in d.items()}
        shrunk["_truncated"] = True
        shrunk["_reason"] = (
            f"digest 超过留痕配额（{_VERDICT_LOG_DIGEST_LIMIT} 字节），"
            "重字段已降为可追溯摘要；完整载荷见同 review_id 的审核治疗"
            "阶段文件条目")
        if len(json.dumps(shrunk, ensure_ascii=False, default=str).encode(
                "utf-8")) <= _VERDICT_LOG_DIGEST_LIMIT:
            return shrunk
        # 二级降级：只留标量核心 + 键清单（防未来字段膨胀突破一级预算）。
        _core = {k: d[k] for k in _DIGEST_CORE_KEYS
                 if k in d and isinstance(d[k], (str, int, float, bool))}
        _core["_truncated"] = True
        _core["_reason"] = ("digest 超过留痕配额且一级摘要仍超限，"
                            "仅保留标量核心与键清单")
        _core["keys"] = sorted(d.keys())
        return _core
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_digest_for_verdict_log:Exc')
        return {"_error": "digest 序列化探测失败"}

from __future__ import annotations

import copy
import errno
import hashlib
import json
import logging
import math
import os
import re
import tempfile
import threading
from collections.abc import Callable
from datetime import datetime, timedelta
from typing import Any, NamedTuple

from jwsgj.diag_guard_io import (
    replace_with_retry,
    two_level_unlink,
)
from jwsgj.diag_types_normalize import (
    int_or,
    signal_bool,
)
from jwsgj.log_config import (
    AUDIT_FILE,
    CONSUMPTION_FILE,
    MAIN_LOG_FILE,
    TEST_CASE_EVENT,
    TEST_RUNS_FILE,
    get_log_dir,
    locked_artifact,
    log_swallowed,
    parse_log_ts,
    setup_logging,
    write_audit,
)
from jwsgj.runtime_paths import (
    consumption_state_path,
    own_skill_root,
    resolve_session_root_from_artifact_path,
)
from jwsgj.runtime_scope import (
    is_backup_snapshot_dir,
    is_runtime_temp_path,
    is_temp_artifact_dir,
)

__all__ = [
    "DEFAULT_MAX_LOG_ENTRIES",
    "QueryFilter",
    "advance_cursor",
    "analyze_log_patterns",
    "analyze_perf_bottlenecks",
    "check_log_quality",
    "cleanup_consumption_state",
    "compute_issue_signature",
    "detect_phase_degradation",
    "get_unconsumed",
    "group_perf_durations",
    "is_delete_event",
    "is_high_risk_audit_event",
    "is_production_audit_target",
    "is_resolved",
    "is_rollback_event",
    "is_test_artifact_path",
    "load_audit_events",
    "load_bug_intercepts",
    "load_defense_feedback_events",
    "load_detector_liveness_events",
    "load_json_file",
    "load_json_logs",
    "load_perf_traces",
    "load_swallowed_exceptions",
    "load_test_runs",
    "normalize_group_key",
    "parse_duration_ms",
    "phase_of",
    "query_logs",
    "reconstruct_pipeline_execution",
    "register_resolution",
    "summarize_test_runs",
]
logger = logging.getLogger(__name__)
_JSON_DECODE_ERRORS: tuple[type[Exception], ...] = (ValueError, RecursionError)
_JSON_LOAD_ERRORS: tuple[type[Exception], ...] = (OSError, *_JSON_DECODE_ERRORS)
_CONSUMPTION_SAVE_ERRORS: tuple[type[Exception], ...] = (
    OSError, ValueError, TypeError, RecursionError)
DEFAULT_MAX_LOG_ENTRIES = 20000
_DEFAULT_DEGRADATION_RATIO = 1.5
_DEFAULT_BOTTLENECK_THRESHOLD_MS = 5000.0
def _normalize_entry_limit(max_entries: int | None) -> int:
    return (DEFAULT_MAX_LOG_ENTRIES if max_entries is None
            else max(0, int_or(max_entries, DEFAULT_MAX_LOG_ENTRIES)))
def _normalize_page_limit(raw: Any,
                          default: int | None = None) -> int | None:
    if raw is None:
        return default
    value = int_or(raw, -1)
    if value < 0:
        logger.warning("分页条数 %r 非法，按默认 %r 处理", raw, default)
        return default
    return value
def _normalize_page_offset(raw: Any) -> int:
    return max(0, int_or(raw, 0))
def _parse_jsonl_line(line: str, fpath: str) -> dict[str, Any] | None:
    try:
        parsed = json.loads(line)
    except _JSON_DECODE_ERRORS as e:
        logger.debug("_parse_jsonl_line: JSON parse failed in %s: %s", fpath, e)
        return None
    if isinstance(parsed, dict):
        return parsed
    logger.debug("_parse_jsonl_line: non-dict line skipped in %s", fpath)
    return None
def _load_jsonl_one(
    fpath: str, *, propagate_io: bool = False,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    try:
        with open(fpath, encoding="utf-8-sig", errors="replace") as f:
            for raw_line in f:
                line = raw_line.strip()
                if not line:
                    continue
                parsed = _parse_jsonl_line(line, fpath)
                if parsed is not None:
                    rows.append(parsed)
    except OSError as e:
        if propagate_io:
            raise
        logger.debug("_load_jsonl_one: read failed for %s: %s", fpath, e)
    return rows
def _backup_paths(
    base_dir: str, base_name: str, *, propagate_io: bool = False,
) -> list[str]:
    try:
        dir_names = os.listdir(base_dir)
    except OSError as _e:
        if propagate_io:
            raise
        logger.debug("_backup_paths: listdir failed for %s: %s", base_dir, _e)
        return []
    numbered: list[tuple[int, str]] = []
    prefix_len = len(base_name) + 1
    for fname in dir_names:
        if not fname.startswith(base_name + "."):
            continue
        suffix = fname[prefix_len:]
        if not (suffix.isascii() and suffix.isdigit()):
            continue
        try:
            number = int(suffix)
        except (TypeError, ValueError) as _e:
            logger.debug("_backup_paths: 跳过不可解析的序号 %s: %s", fname, _e)
            continue
        numbered.append((number, fname))
    numbered.sort(key=lambda item: (item[0], item[1]), reverse=True)
    return [os.path.join(base_dir, fname) for _number, fname in numbered]
def _load_jsonl_backups(
    path: str, *, propagate_io: bool = False,
) -> list[dict[str, Any]]:
    """按轮转序读取 ``path`` 的编号备份文件；不含主文件本身。"""
    results: list[dict[str, Any]] = []
    base_dir = os.path.dirname(path)
    if not os.path.isdir(base_dir):
        return results
    for fpath in _backup_paths(
            base_dir, os.path.basename(path), propagate_io=propagate_io):
        if propagate_io:
            try:
                results.extend(_load_jsonl_one(fpath, propagate_io=True))
            except FileNotFoundError:
                continue
        elif os.path.isfile(fpath):
            results.extend(_load_jsonl_one(fpath))
    return results
def _load_jsonl_all(
    path: str, *, propagate_io: bool = False,
) -> list[dict[str, Any]]:
    results = _load_jsonl_backups(path, propagate_io=propagate_io)
    if not propagate_io and not os.path.isfile(path):
        return results
    try:
        results.extend(_load_jsonl_one(path, propagate_io=propagate_io))
    except FileNotFoundError:
        # 主文件缺失与备份同样容忍（propagate_io 下原实现亦 continue）
        return results
    return results
def load_json_file(path: str, log_tag: str = "log_analysis") -> Any | None:
    if not path or not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8-sig") as f:
            return json.load(f)
    except _JSON_LOAD_ERRORS as e:
        logger.warning("[%s] JSON 加载失败 %s: %s", log_tag, path, e)
        return None
_MainLogFingerprint = tuple[
    str, int, int, tuple[tuple[str, int, int], ...]]
_main_log_snapshot: tuple[
    _MainLogFingerprint, list[dict[str, Any]]] | None = None
_MAIN_LOG_HASH_CHUNK_BYTES = 1024 * 1024

class _MainLogTail(NamedTuple):
    """主日志增量游标：只读追加部分，避免每次都重扫全量条目。"""

    path: str
    offset: int
    entries: tuple[dict[str, Any], ...]
    backup_fingerprints: tuple[tuple[str, int, int], ...]
    prefix: bytes | None

_main_log_tail: _MainLogTail | None = None
_main_log_snapshot_lock = threading.Lock()
def _main_log_fingerprint(
        log_path: str,
) -> _MainLogFingerprint | None:
    try:
        stat = os.stat(log_path)
    except OSError as e:
        logger.debug("_main_log_fingerprint: stat failed for %s: %s", log_path, e)
        return None
    backup_fingerprints: list[tuple[str, int, int]] = []
    for backup_path in _backup_paths(
            os.path.dirname(log_path), os.path.basename(log_path)):
        try:
            backup_stat = os.stat(backup_path)
        except OSError as e:
            logger.debug(
                "_main_log_fingerprint: backup stat failed for %s: %s",
                backup_path, e)
            return None
        backup_fingerprints.append((
            os.path.normcase(os.path.abspath(backup_path)),
            backup_stat.st_mtime_ns, backup_stat.st_size))
    return (os.path.normcase(os.path.abspath(log_path)),
            stat.st_mtime_ns, stat.st_size, tuple(backup_fingerprints))
def _resolve_log_dir(log_dir: str | None = None) -> str | None:
    return get_log_dir() if log_dir is None else log_dir
def _main_log_prefix(path: str, offset: int) -> bytes | None:
    """返回游标前完整内容的摘要，可靠区分纯追加与同路径改写。"""
    digest = hashlib.sha256()
    remaining = offset
    try:
        with open(path, "rb") as handle:
            while remaining > 0:
                chunk = handle.read(min(remaining, _MAIN_LOG_HASH_CHUNK_BYTES))
                if not chunk:
                    return None
                digest.update(chunk)
                remaining -= len(chunk)
    except OSError as exc:
        logger.debug("_main_log_prefix: read failed for %s: %s", path, exc)
        return None
    return digest.digest()

def _load_jsonl_tail(
    path: str, offset: int, *, propagate_io: bool = False,
) -> tuple[list[dict[str, Any]], int]:
    """从 ``offset`` 起读取追加的完整行，返回 ``(新增条目, 新游标)``。

    主日志的全量与增量路径都以本函数解析主文件：条目与游标出自同一次
    字节读取，游标不可能越过尚未解析的行。
    完整换行行直接消费；无换行尾部仅在能完整解析为 JSON 对象时消费。
    管线运行期日志随时可能写到半行，把残缺尾部算进游标会让它下次被截断成
    非法 JSON 而静默丢一条；合法无换行尾记录则同样被消费。
    行边界只认 ``\\n``（与游标口径一致）：``str.splitlines`` 还会把 JSON
    字符串内裸露的 U+2028/U+0085 等当作行边界，把一条合法记录拆成两段非法 JSON。
    """
    rows: list[dict[str, Any]] = []
    try:
        with open(path, "rb") as handle:
            handle.seek(offset)
            chunk = handle.read()
    except OSError as exc:
        if propagate_io:
            raise
        logger.debug("_load_jsonl_tail: read failed for %s: %s", path, exc)
        return rows, offset
    complete_end = chunk.rfind(b"\n") + 1
    encoding = "utf-8-sig" if offset == 0 else "utf-8"
    for raw_line in chunk[:complete_end].decode(
            encoding, errors="replace").split("\n"):
        line = raw_line.strip()
        if not line:
            continue
        parsed = _parse_jsonl_line(line, path)
        if parsed is not None:
            rows.append(parsed)
    trailing = chunk[complete_end:]
    if trailing.strip():
        try:
            parsed = json.loads(trailing.decode(
                encoding, errors="replace").strip())
        except _JSON_DECODE_ERRORS:
            parsed = None
        if isinstance(parsed, dict):
            rows.append(parsed)
            complete_end = len(chunk)
    return rows, offset + complete_end


def _main_log_entries(
    log_dir: str | None = None, *, propagate_io: bool = False,
) -> list[dict[str, Any]]:
    global _main_log_snapshot, _main_log_tail
    _dir = _resolve_log_dir(log_dir)
    if not _dir:
        return []
    log_path = os.path.join(_dir, MAIN_LOG_FILE)
    fingerprint = _main_log_fingerprint(log_path)
    if fingerprint is None:
        return _load_jsonl_all(log_path, propagate_io=propagate_io)
    with _main_log_snapshot_lock:
        snapshot = _main_log_snapshot
        if snapshot is not None and snapshot[0] == fingerprint:
            # 条目在快照内以只读方式共享，调用方只做过滤/遍历/切片：
            # 浅拷贝已足以隔离列表级变更，无需 53,502 条逐条 deepcopy。
            return list(snapshot[1])
        tail = _main_log_tail
        if (tail is not None and tail.path == log_path
                and tail.backup_fingerprints == fingerprint[3]
                and fingerprint[2] >= tail.offset
                and tail.prefix is not None
                and _main_log_prefix(log_path, tail.offset) == tail.prefix):
            # 完整前缀摘要与备份均未变且主文件只增长：只解析追加部分。管线运行期每秒
            # 数十条 perf/audit 写入会让整份快照的指纹持续失效，原实现每次
            # 重扫 5 万条（实测 8 次 3.5s）。
            new_rows, new_offset = _load_jsonl_tail(
                log_path, tail.offset, propagate_io=propagate_io)
            merged = (*tail.entries, *new_rows)
            _main_log_snapshot = (fingerprint, merged)
            _main_log_tail = _MainLogTail(
                log_path, new_offset, merged, fingerprint[3],
                _main_log_prefix(log_path, new_offset))
            return list(merged)
    # 全量路径：主文件只做一次字节读取，条目与游标出自同一次解析。原实现在读完
    # 之后再读一次文件来量游标，两次读取之间被管线追加的完整行既未解析又被游标
    # 越过，之后的增量读取永久跳过它们（静默丢日志）。
    backup_rows = _load_jsonl_backups(log_path, propagate_io=propagate_io)
    try:
        main_rows, offset = _load_jsonl_tail(
            log_path, 0, propagate_io=propagate_io)
    except FileNotFoundError:
        # 主文件在全量读取前被轮转删除：与原实现一致，只消费备份
        main_rows, offset = [], 0
    entries = (*backup_rows, *main_rows)
    with _main_log_snapshot_lock:
        _main_log_snapshot = (fingerprint, entries)
        _main_log_tail = _MainLogTail(
            log_path, offset, entries, fingerprint[3],
            _main_log_prefix(log_path, offset))
    return list(entries)
def load_json_logs(max_entries: int | None = None,
                   log_dir: str | None = None, *,
                   propagate_io: bool = False) -> list[dict[str, Any]]:
    results = _main_log_entries(log_dir, propagate_io=propagate_io)
    cap = _normalize_entry_limit(max_entries)
    if len(results) > cap:
        logger.debug("load_json_logs: %d entries found, limiting to %d most recent",
                       len(results), cap)
        results = results[-cap:] if cap else []
    return results
def load_audit_events() -> list[dict[str, Any]]:
    _dir = get_log_dir()
    jsonl_entries = (_load_jsonl_all(os.path.join(_dir, AUDIT_FILE))
                     if _dir else [])
    log_entries = [e for e in _main_log_entries()
                   if e.get("logger") == "jwsgj.audit"]
    merged = _merge_audit_log_entries(jsonl_entries, log_entries)
    merged.sort(key=lambda e: _ts_order_key(e.get("ts", "")))
    return merged
def _merge_audit_log_entries(jsonl_entries: list, log_entries: list) -> list:
    merged: list[dict[str, Any]] = []
    seen_seqs: set[str] = set()
    for entries in (jsonl_entries, log_entries):
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            seq = entry.get("audit_seq")
            if seq is not None:
                seq_key = str(seq)
                if seq_key in seen_seqs:
                    continue
                seen_seqs.add(seq_key)
            merged.append(entry)
    return merged
def _filter_main_log(field: str, value: str) -> list[dict[str, Any]]:
    return [e for e in _main_log_entries() if e.get(field) == value]
def load_perf_traces() -> list[dict[str, Any]]:
    return _filter_main_log("logger", "jwsgj.perf")
def load_swallowed_exceptions() -> list[dict[str, Any]]:
    return _filter_main_log("event", "swallowed_exception")
def load_detector_liveness_events() -> list[dict[str, Any]]:
    return _filter_main_log("event", "detector_liveness")
def load_bug_intercepts() -> list[dict[str, Any]]:
    return _filter_main_log("event", "bug_intercept")
def load_defense_feedback_events() -> list[dict[str, Any]]:
    return _filter_main_log("event", "defense_feedback")
def _test_runs_path(log_dir: str | None = None) -> str:
    _dir = _resolve_log_dir(log_dir)
    return os.path.join(_dir, TEST_RUNS_FILE) if _dir else ""
def _read_test_run_lines(
    path: str, *, propagate_io: bool = False,
) -> list[str] | None:
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as f:
            return f.readlines()
    except OSError as e:
        if propagate_io:
            raise
        log_swallowed(__name__, e, context='load_test_runs:OSError')
        return None
def _parse_test_run_records(lines: list[str]) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for raw_line in lines:
        line = raw_line.strip()
        if not line:
            continue
        try:
            record = json.loads(line)
        except (*_JSON_DECODE_ERRORS, TypeError) as e:
            log_swallowed(
                __name__, e,
                context=f'load_test_runs:{type(e).__name__}')
            continue
        if isinstance(record, dict):
            entries.append(record)
    return entries
def load_test_runs(max_entries: int | None = None,
                   log_dir: str | None = None, *,
                   propagate_io: bool = False) -> list[dict[str, Any]]:
    path = _test_runs_path(log_dir)
    if not path:
        return []
    limit = _normalize_entry_limit(max_entries)
    if limit <= 0:
        return []
    if not propagate_io and not os.path.isfile(path):
        return []
    try:
        lines = _read_test_run_lines(path, propagate_io=propagate_io)
    except FileNotFoundError:
        return []
    if lines is None:
        return []
    return _parse_test_run_records(lines)[-limit:]
def _new_test_run_summary() -> dict[str, Any]:
    return {
        "cases": 0,
        "by_outcome": {},
        "modules": set(),
        "run_ids": set(),
        "slow_cases": [],
        "failures": [],
    }
def _record_test_run_identity(summary: dict[str, Any],
                              payload: dict[str, Any], nodeid: str) -> None:
    module = nodeid.split("::", 1)[0].replace("\\", "/")
    if module:
        summary["modules"].add(module)
    run_id = payload.get("run_id")
    if isinstance(run_id, str) and run_id:
        summary["run_ids"].add(run_id)
def _accumulate_test_run_summary(summary: dict[str, Any],
                                 entry: dict[str, Any]) -> None:
    if entry.get("event") != TEST_CASE_EVENT:
        return
    payload = _payload_of(entry)
    outcome = normalize_group_key(payload.get("outcome"))
    nodeid = _evidence_text(payload.get("nodeid"))
    summary["cases"] += 1
    by_outcome = summary["by_outcome"]
    by_outcome[outcome] = by_outcome.get(outcome, 0) + 1
    _record_test_run_identity(summary, payload, nodeid)
    if signal_bool(payload.get("slow")):
        summary["slow_cases"].append({
            "nodeid": nodeid,
            "duration_ms": parse_duration_ms(
                payload.get("duration_ms"),
                label="summarize_test_runs")})
    if outcome in ("failed", "error"):
        summary["failures"].append({
            "nodeid": nodeid,
            "outcome": outcome,
            "when": _evidence_text(payload.get("when")),
            "detail": _evidence_text(payload.get("detail"))[:200],
        })
def summarize_test_runs(
    entries: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    if entries is None:
        entries = load_test_runs()
    summary = _new_test_run_summary()
    for entry in entries:
        _accumulate_test_run_summary(summary, entry)
    slow_cases = summary["slow_cases"]
    slow_cases.sort(key=lambda x: -(x.get("duration_ms") or 0.0))
    return {
        "cases": summary["cases"],
        "by_outcome": dict(sorted(summary["by_outcome"].items())),
        "modules": sorted(summary["modules"]),
        "module_count": len(summary["modules"]),
        "run_ids": sorted(summary["run_ids"]),
        "slow_cases": slow_cases[:10],
        "recent_failures": summary["failures"][-10:],
    }
_LOG_TYPE_LOADERS: dict[str, Callable[[], list[dict[str, Any]]]] = {
    "audit": load_audit_events,
    "perf": load_perf_traces,
    "swallowed": load_swallowed_exceptions,
    "json_log": _main_log_entries,
}
_consumption_lock = threading.Lock()
_consumption_cache: dict[str, Any] | None = None
_consumption_cache_path: str | None = None
_CACHE_FP_UNSET = object()
_consumption_cache_fingerprint: Any = _CACHE_FP_UNSET
def _is_wellformed_ts(value: Any) -> bool:
    return isinstance(value, str) and parse_log_ts(value) is not None
def _now_ts(days_ago: int = 0) -> str:
    moment = datetime.now() - timedelta(days=days_ago)
    return moment.isoformat(timespec="milliseconds")
def _normalize_ts_entry(entry: dict[str, Any],
                        ts_fields: tuple[str, ...]) -> None:
    for field in ts_fields:
        if field in entry and not isinstance(entry[field], str):
            entry[field] = ""
def _normalize_ts_entry_map(consumer: dict[str, Any], key: str,
                            ts_fields: tuple[str, ...]) -> None:
    entries = consumer[key]
    if not isinstance(entries, dict):
        consumer[key] = {}
        return
    for entry_key in list(entries.keys()):
        entry = entries[entry_key]
        if not isinstance(entry, dict):
            del entries[entry_key]
            continue
        _normalize_ts_entry(entry, ts_fields)
def _normalize_consumption_state(state: dict[str, Any]) -> None:
    for consumer_id in list(state.keys()):
        consumer = state[consumer_id]
        if not isinstance(consumer, dict):
            del state[consumer_id]
            continue
        if "cursors" in consumer:
            _normalize_ts_entry_map(consumer, "cursors", ("last_ts", "updated_at"))
        if "resolutions" in consumer:
            _normalize_ts_entry_map(consumer, "resolutions", ("resolved_at",))
def _consumption_state_fingerprint(state_path: str) -> tuple[int, int] | None:
    try:
        stat = os.stat(state_path)
    except OSError as e:
        if getattr(e, "errno", None) != errno.ENOENT:
            logger.debug("_consumption_state_fingerprint: stat failed: %s", e)
        return None
    return (stat.st_mtime_ns, stat.st_size)
def _read_consumption_state_file(
    state_path: str, *, propagate_io: bool = False,
) -> dict[str, Any]:
    try:
        with open(state_path, encoding="utf-8-sig") as f:
            state = json.load(f)
    except FileNotFoundError:
        return {}
    except OSError as e:
        if propagate_io:
            raise
        logger.debug("_load_consumption_state: read failed, falling back to empty state: %s", e)
        return {}
    except _JSON_DECODE_ERRORS as e:
        if propagate_io:
            raise
        logger.debug("_load_consumption_state: load failed, falling back to empty state: %s", e)
        return {}
    if not isinstance(state, dict):
        if propagate_io:
            raise ValueError(
                f"consumption state root must be an object: {state_path}")
        return {}
    _normalize_consumption_state(state)
    return state
def _load_consumption_state(state_path: str | None = None) -> dict[str, Any]:
    global _consumption_cache, _consumption_cache_path
    global _consumption_cache_fingerprint
    if state_path is None:
        state_path = consumption_state_path(own_skill_root())
    if not state_path:
        return {}
    if _consumption_cache is not None and _consumption_cache_path == state_path:
        if _consumption_cache_fingerprint is _CACHE_FP_UNSET:
            return _consumption_cache
        if (_consumption_cache_fingerprint
                == _consumption_state_fingerprint(state_path)):
            return _consumption_cache
    state = _read_consumption_state_file(state_path)
    _consumption_cache = state
    _consumption_cache_path = state_path
    _consumption_cache_fingerprint = _consumption_state_fingerprint(state_path)
    return state
def _commit_consumption_cache(state: dict[str, Any], state_path: str) -> None:
    global _consumption_cache, _consumption_cache_path
    global _consumption_cache_fingerprint
    _consumption_cache = state
    _consumption_cache_path = state_path
    _consumption_cache_fingerprint = _consumption_state_fingerprint(state_path)
def _invalidate_consumption_cache() -> None:
    global _consumption_cache, _consumption_cache_path
    global _consumption_cache_fingerprint
    _consumption_cache = None
    _consumption_cache_path = None
    _consumption_cache_fingerprint = _CACHE_FP_UNSET
def _merge_cursor_bucket(
    bucket: dict[str, Any], values: dict[str, Any],
) -> None:
    for log_type, incoming in values.items():
        current = bucket.get(log_type)
        if isinstance(current, dict):
            current_ts = current.get("last_ts", "")
            incoming_ts = (incoming.get("last_ts", "")
                           if isinstance(incoming, dict) else None)
            if _is_wellformed_ts(current_ts) and (
                    not _is_wellformed_ts(incoming_ts)
                    or _ts_order_key(incoming_ts) <= _ts_order_key(current_ts)):
                continue
        bucket[log_type] = copy.deepcopy(incoming)
def _merge_resolution_bucket(
    bucket: dict[str, Any], values: dict[str, Any],
) -> None:
    for issue_signature, incoming in values.items():
        current = bucket.get(issue_signature)
        if isinstance(current, dict) and isinstance(incoming, dict):
            current_ts = current.get("resolved_at", "")
            incoming_ts = incoming.get("resolved_at", "")
            if _is_wellformed_ts(current_ts) and (
                    not _is_wellformed_ts(incoming_ts)
                    or _ts_order_key(incoming_ts) < _ts_order_key(current_ts)):
                continue
        bucket[issue_signature] = copy.deepcopy(incoming)
def _merged_consumption_state_for_write(
    local: dict[str, Any], state_path: str,
) -> dict[str, Any]:
    disk = _read_consumption_state_file(state_path, propagate_io=True)
    merged = copy.deepcopy(disk)
    for consumer_id, consumer in local.items():
        if not isinstance(consumer, dict):
            continue
        target = merged.get(consumer_id)
        if not isinstance(target, dict):
            target = {}
            merged[consumer_id] = target
        for key in ("cursors", "resolutions"):
            values = consumer.get(key)
            if isinstance(values, dict):
                bucket = target.get(key)
                if not isinstance(bucket, dict):
                    bucket = {}
                    target[key] = bucket
                if key == "cursors":
                    _merge_cursor_bucket(bucket, values)
                else:
                    _merge_resolution_bucket(bucket, values)
            elif key not in target:
                target[key] = {}
    return merged
def _save_consumption_state(state: dict[str, Any], state_path: str | None = None) -> bool:
    if state_path is None:
        state_path = consumption_state_path(own_skill_root())
    if not state_path:
        return False
    tmp_path = f"{state_path}.{os.getpid()}.{threading.get_ident()}.tmp"
    replace_succeeded = False
    try:
        _dump_consumption_state(state, tmp_path)
        replace_with_retry(tmp_path, state_path)
        replace_succeeded = True
        _commit_consumption_cache(state, state_path)
        return True
    except _CONSUMPTION_SAVE_ERRORS as save_err:
        logger.warning(
            "_save_consumption_state: atomic write failed; original preserved: %s",
            save_err, exc_info=True)
        return False
    finally:
        if not replace_succeeded:
            two_level_unlink(tmp_path)
def _dump_consumption_state(state: dict[str, Any], path: str) -> None:
    state_dir = os.path.dirname(path)
    if state_dir:
        os.makedirs(state_dir, exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(state, fh, ensure_ascii=False, default=str, indent=2)
def _persist_consumption_state(state: dict[str, Any],
                                state_path: str | None = None,
                                *, merge: bool = True) -> bool:
    resolved_path = (
        state_path if state_path is not None
        else consumption_state_path(own_skill_root()))
    if not resolved_path:
        _invalidate_consumption_cache()
        return False
    success = False
    try:
        state_dir = os.path.dirname(resolved_path)
        if state_dir:
            os.makedirs(state_dir, exist_ok=True)
    except OSError as e:
        logger.warning(
            "_persist_consumption_state: 状态目录准备失败: %s", e)
    else:
        with locked_artifact(resolved_path) as locked:
            if not locked:
                logger.warning(
                    "_persist_consumption_state: 跨进程锁不可用，"
                    "跳过状态重写: %s", resolved_path)
            else:
                try:
                    if merge:
                        state = _merged_consumption_state_for_write(
                            state, resolved_path)
                    success = _save_consumption_state(state, resolved_path)
                except _JSON_LOAD_ERRORS as e:
                    logger.warning(
                        "_persist_consumption_state: 写前读取失败，保留原状态: %s", e)
    if not success:
        _invalidate_consumption_cache()
    return success
def _consumer_state(state: dict[str, Any], consumer_id: str) -> dict[str, Any]:
    consumer = state.setdefault(consumer_id, {"cursors": {}, "resolutions": {}})
    consumer.setdefault("cursors", {})
    consumer.setdefault("resolutions", {})
    return consumer
def _audit_consumption_event(event: str, **fields: Any) -> None:
    try:
        write_audit(event, **fields)
    except Exception:
        logger.debug("consumption audit failed: %s %r", event, fields)
def compute_issue_signature(
    log_type: str,
    error_pattern: str,
    method_id: str | None = None,
    rule_id: str | None = None,
    error_type: str | None = None,
) -> str:
    parts = [str(log_type), str(error_pattern or "")]
    if method_id:
        parts.append(f"method:{method_id}")
    if rule_id:
        parts.append(f"rule:{rule_id}")
    if error_type:
        parts.append(f"error:{error_type}")
    if any("|" in part for part in parts):
        # 保留无歧义输入的历史签名；歧义输入按真实字段边界编码。
        raw = "v2:" + json.dumps(
            parts, ensure_ascii=False, separators=(",", ":"))
    else:
        raw = "|".join(parts)
    return hashlib.md5(raw.encode("utf-8"), usedforsecurity=False).hexdigest()[:16]
def _entry_to_signature(log_type: str, entry: dict[str, Any]) -> str:
    payload = _payload_of(entry)
    event = entry.get("event", "")
    method_id = entry.get("method_id") or payload.get("method_id")
    rule_id = payload.get("rule_id") or payload.get("rule_family")
    error_type = payload.get("exc_type") or payload.get("error_type")
    error_pattern = event or str(entry.get("message") or "")[:100]
    return compute_issue_signature(log_type, error_pattern, method_id, rule_id, error_type)
def _resolution_record(consumer_id: str,
                       issue_signature: str) -> dict[str, Any] | None:
    with _consumption_lock:
        state = _load_consumption_state()
        consumer_state = state.get(consumer_id, {})
        resolution = consumer_state.get("resolutions", {}).get(issue_signature)
        return copy.deepcopy(resolution) if isinstance(resolution, dict) else None
def _resolution_covers_ts(resolution: dict[str, Any] | None,
                          entry_ts: Any) -> bool:
    if not isinstance(resolution, dict):
        return False
    resolved_at = resolution.get("resolved_at", "")
    if not _is_wellformed_ts(resolved_at):
        return True
    if not _is_wellformed_ts(entry_ts):
        return True
    return _ts_order_key(entry_ts) <= _ts_order_key(resolved_at)
def _partition_unconsumed(
    log_type: str,
    entries: list[dict[str, Any]],
    last_ts: str,
    resolutions: dict[str, Any],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], int]:
    new_entries: list[dict[str, Any]] = []
    resolved_skipped: list[dict[str, Any]] = []
    skipped_malformed = 0
    for entry in entries:
        entry_ts = entry.get("ts", "")
        if not _is_wellformed_ts(entry_ts):
            skipped_malformed += 1
            continue
        if last_ts and _ts_order_key(entry_ts) <= _ts_order_key(last_ts):
            continue
        sig = _entry_to_signature(log_type, entry)
        resolved = resolutions.get(sig)
        if _resolution_covers_ts(resolved, entry_ts):
            resolved_skipped.append({
                "ts": entry_ts,
                "issue_signature": sig,
                "event": entry.get("event", ""),
                "resolved_at": resolved.get("resolved_at", ""),
            })
        else:
            entry_copy = dict(entry)
            entry_copy["issue_signature"] = sig
            new_entries.append(entry_copy)
    if skipped_malformed:
        logger.debug(
            "_partition_unconsumed: %s 有 %d 条时间戳不可解析的条目未参与消费",
            log_type, skipped_malformed)
    return new_entries, resolved_skipped, skipped_malformed
def _truncate_at_ts_group(
    new_entries: list[dict[str, Any]],
    limit: int,
) -> list[dict[str, Any]]:
    _cap = max(0, limit)
    if 0 < _cap < len(new_entries):
        _cut_key = _ts_order_key(new_entries[_cap - 1].get("ts"))
        while (_cap < len(new_entries)
               and _ts_order_key(new_entries[_cap].get("ts")) == _cut_key):
            _cap += 1
    return new_entries[:_cap]
def _consumption_result(
    consumer_id: str,
    log_type: str,
    cursor: dict[str, Any],
    new_entries: list[dict[str, Any]],
    resolved_skipped: list[dict[str, Any]],
    error: str | None = None,
    skipped_malformed: int = 0,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "new_entries": new_entries,
        "resolved_skipped": resolved_skipped,
        "cursor": cursor,
        "consumer_id": consumer_id,
        "log_type": log_type,
        "new_count": len(new_entries),
        "resolved_count": len(resolved_skipped),
        "skipped_malformed": skipped_malformed,
    }
    if error is not None:
        result["error"] = error
    return result
def _read_cursor_view(
    consumer_id: str, log_type: str,
) -> tuple[dict[str, Any], str, dict[str, Any]]:
    with _consumption_lock:
        state = _load_consumption_state()
        consumer_state = state.get(consumer_id, {})
        cursor = consumer_state.get("cursors", {}).get(log_type, {})
        last_ts = cursor.get("last_ts", "")
        if not _is_wellformed_ts(last_ts):
            last_ts = ""
        resolutions = consumer_state.get("resolutions", {})
        cursor = copy.deepcopy(cursor)
        resolutions = copy.deepcopy(resolutions)
    return cursor, last_ts, resolutions
def _load_consumption_view(
    consumer_id: str, log_type: str,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    loader = _LOG_TYPE_LOADERS.get(log_type)
    if loader is None:
        return [], _consumption_result(
            consumer_id, log_type, {}, [], [],
            f"unknown log_type: {log_type}")
    entries = loader()
    cursor, last_ts, resolutions = _read_cursor_view(consumer_id, log_type)
    new_entries, resolved_skipped, skipped_malformed = _partition_unconsumed(
        log_type, entries, last_ts, resolutions)
    result = _consumption_result(
        consumer_id, log_type, dict(cursor), new_entries, resolved_skipped,
        skipped_malformed=skipped_malformed)
    return entries, result
def get_unconsumed(
    consumer_id: str,
    log_type: str,
    limit: int | None = None,
) -> dict[str, Any]:
    consumer_id = normalize_group_key(consumer_id, str(consumer_id))
    try:
        cleanup_consumption_state()
    except Exception as e:
        logger.debug("get_unconsumed: cleanup_consumption_state failed: %s", e)
    _entries, result = _load_consumption_view(consumer_id, log_type)
    limit = _normalize_page_limit(limit)
    if limit is not None:
        ordered_entries = sorted(
            result["new_entries"],
            key=lambda entry: _ts_order_key(entry.get("ts")))
        new_entries = _truncate_at_ts_group(ordered_entries, limit)
        result["new_entries"] = new_entries
        result["new_count"] = len(new_entries)
    return result
def advance_cursor(
    consumer_id: str,
    log_type: str,
    last_entry_ts: str,
) -> bool:
    if not _is_wellformed_ts(last_entry_ts):
        logger.warning(
            "[advance_cursor] last_entry_ts 非 ISO 形态（撕裂/异构态），拒绝推进: %r",
            last_entry_ts)
        return False
    consumer_id = normalize_group_key(consumer_id, str(consumer_id))
    log_type = normalize_group_key(log_type, str(log_type))
    with _consumption_lock:
        state = _load_consumption_state()
        consumer_state = _consumer_state(state, consumer_id)
        cursor = consumer_state["cursors"].get(log_type, {})
        old_ts = cursor.get("last_ts", "")
        if (_is_wellformed_ts(old_ts)
                and _ts_order_key(last_entry_ts) <= _ts_order_key(old_ts)):
            return True
        consumer_state["cursors"][log_type] = {
            "last_ts": last_entry_ts,
            "updated_at": _now_ts(),
        }
        success = _persist_consumption_state(state)
    if success:
        _audit_consumption_event(
            "consumption_cursor_advance", consumer_id=consumer_id,
            log_type=log_type, last_entry_ts=last_entry_ts)
    return success
def register_resolution(
    consumer_id: str,
    issue_signature: str,
    resolution_summary: str = "",
) -> bool:
    consumer_id = normalize_group_key(consumer_id, str(consumer_id))
    issue_signature = normalize_group_key(issue_signature, str(issue_signature))
    if not isinstance(resolution_summary, str):
        resolution_summary = ("" if resolution_summary is None
                              else str(resolution_summary))
    now_str = _now_ts()
    with _consumption_lock:
        state = _load_consumption_state()
        consumer_state = _consumer_state(state, consumer_id)
        consumer_state["resolutions"][issue_signature] = {
            "resolution_summary": resolution_summary,
            "resolved_at": now_str,
        }
        success = _persist_consumption_state(state)
    if success:
        _audit_consumption_event(
            "consumption_resolution_register", consumer_id=consumer_id,
            issue_signature=issue_signature,
            resolution_summary=resolution_summary[:200])
    return success
def is_resolved(consumer_id: str, issue_signature: str) -> bool:
    consumer_id = normalize_group_key(consumer_id, str(consumer_id))
    issue_signature = normalize_group_key(issue_signature, str(issue_signature))
    return _resolution_record(consumer_id, issue_signature) is not None
def _delete_expired_ts_entries(entries: dict[str, Any], ts_field: str,
                               cutoff: str) -> int:
    cutoff_key = _ts_order_key(cutoff)
    deleted = 0
    for key in list(entries.keys()):
        ts = entries[key].get(ts_field)
        if not _is_wellformed_ts(ts) or _ts_order_key(ts) < cutoff_key:
            del entries[key]
            deleted += 1
    return deleted
def _prune_consumer(consumer: dict[str, Any], cutoff: str) -> tuple[int, int, bool]:
    cleaned_cursors = _delete_expired_ts_entries(
        consumer.get("cursors", {}), "updated_at", cutoff)
    cleaned_resolutions = _delete_expired_ts_entries(
        consumer.get("resolutions", {}), "resolved_at", cutoff)
    empty = not consumer.get("cursors") and not consumer.get("resolutions")
    return cleaned_cursors, cleaned_resolutions, empty
def _empty_prune_counts() -> dict[str, int]:
    return {"cleaned_cursors": 0, "cleaned_resolutions": 0,
            "cleaned_consumers": 0}
def _prune_state(state: dict[str, Any], cutoff: str) -> dict[str, int]:
    counts = _empty_prune_counts()
    for consumer_id in list(state.keys()):
        n_cur, n_res, drop = _prune_consumer(state[consumer_id], cutoff)
        counts["cleaned_cursors"] += n_cur
        counts["cleaned_resolutions"] += n_res
        if drop:
            del state[consumer_id]
            counts["cleaned_consumers"] += 1
    return counts
_DEFAULT_CONSUMPTION_RETENTION_DAYS = 30
def _normalize_consumption_retention_days(raw: Any) -> int:
    numeric = int_or(raw, _DEFAULT_CONSUMPTION_RETENTION_DAYS)
    if numeric >= 0:
        return numeric
    logger.warning(
        "cleanup_consumption_state: 负保留期 %r 会令 cutoff 落在未来，"
        "已回退默认保留期 %d 天", raw, _DEFAULT_CONSUMPTION_RETENTION_DAYS)
    return _DEFAULT_CONSUMPTION_RETENTION_DAYS
def _prune_consumption_state_locked(
    state_path: str, cutoff: str,
) -> dict[str, int]:
    counts = _empty_prune_counts()
    try:
        state_dir = os.path.dirname(state_path)
        if state_dir:
            os.makedirs(state_dir, exist_ok=True)
    except OSError as e:
        logger.warning("cleanup_consumption_state: 状态目录准备失败: %s", e)
        _invalidate_consumption_cache()
        return counts
    with locked_artifact(state_path) as locked:
        if not locked:
            logger.warning(
                "cleanup_consumption_state: 跨进程锁不可用，"
                "跳过状态清理: %s", state_path)
            _invalidate_consumption_cache()
            return counts
        state = _read_consumption_state_file(state_path)
        counts = _prune_state(state, cutoff)
        if not any(counts.values()):
            _commit_consumption_cache(state, state_path)
            return counts
        if not _save_consumption_state(state, state_path):
            _invalidate_consumption_cache()
            return _empty_prune_counts()
    return counts
def cleanup_consumption_state(
    retention_days: int | None = None,
    log_dir: str | None = None,
) -> dict[str, Any]:
    retention_days = _normalize_consumption_retention_days(retention_days)
    if log_dir is not None:
        if not log_dir:
            return {"cleaned_cursors": 0, "cleaned_resolutions": 0,
                    "cleaned_consumers": 0, "retention_days": retention_days}
        state_path = os.path.join(log_dir, CONSUMPTION_FILE)
    else:
        state_path = consumption_state_path(own_skill_root())
    cutoff = _now_ts(retention_days)
    with _consumption_lock:
        state = _load_consumption_state(state_path)
        counts = _prune_state(state, cutoff)
        if any(counts.values()):
            counts = _prune_consumption_state_locked(state_path, cutoff)
    if any(counts.values()):
        logger.info(
            "cleanup_consumption_state: cursors=%d, resolutions=%d, retention=%dd",
            counts["cleaned_cursors"], counts["cleaned_resolutions"],
            retention_days,
        )
    return {**counts, "retention_days": retention_days}
_VOLUME_ANOMALY_BYTES = 100 * 1024 * 1024
_PHASE_GAP_THRESHOLD_SECONDS = 300
_FIELD_MISSING_SAMPLE_LIMIT = 5
def _normalize_time_bound(raw: str | None, label: str) -> str | None:
    if not isinstance(raw, str) or not raw.strip():
        return None
    if parse_log_ts(raw) is None:
        logger.warning("query_logs: %s 不是可解析时间戳，已忽略该边界: %r",
                       label, raw)
        return None
    return raw
def _entry_in_time_window(entry: dict[str, Any], time_start: str | None,
                          time_end: str | None) -> bool:
    if time_start is None and time_end is None:
        return True
    if not _is_wellformed_ts(entry.get("ts")):
        return False
    ts_key = _ts_order_key(entry.get("ts", ""))
    if time_start and ts_key < _ts_order_key(time_start):
        return False
    return not (time_end and ts_key > _ts_order_key(time_end))
def _level_of(entry: dict[str, Any]) -> str:
    level = entry.get("level")
    return level.strip().upper() if isinstance(level, str) else ""
def _logger_prefix_matches(entry: dict[str, Any], logger_name: str | None) -> bool:
    if not logger_name:
        return True
    if not isinstance(logger_name, str):
        return False
    lg = entry.get("logger", "")
    return (isinstance(lg, str)
            and (lg == logger_name or lg.startswith(logger_name + ".")))
class QueryFilter(NamedTuple):
    phase: str | None = None
    method_id: str | None = None
    level: str | None = None
    event: str | None = None
    logger_name: str | None = None
_EMPTY_QUERY_FILTER = QueryFilter()
def _normalized_filter(value: Any) -> Any:
    if isinstance(value, str):
        text = value.strip()
        return text or None
    return value
def _passes_query_filters(entry: dict[str, Any],
                          filters: QueryFilter) -> bool:
    level = _normalized_filter(filters.level)
    if isinstance(level, str) and _level_of(entry) != level.upper():
        return False
    expected = (
        ("phase", _normalized_filter(filters.phase)),
        ("method_id", _normalized_filter(filters.method_id)),
        ("event", _normalized_filter(filters.event)),
    )
    return (
        all(value is None or entry.get(field) == value
            for field, value in expected)
        and _logger_prefix_matches(entry, _normalized_filter(filters.logger_name))
    )
def query_logs(
    filters: QueryFilter = _EMPTY_QUERY_FILTER,
    *,
    time_start: str | None = None,
    time_end: str | None = None,
    limit: int | None = None,
    offset: int = 0,
) -> list[dict[str, Any]]:
    entries = _main_log_entries()
    filtered: list[dict[str, Any]] = []
    if not isinstance(filters, QueryFilter):
        logger.warning(
            "query_logs: filters 非 QueryFilter（%s），按无过滤处理",
            type(filters).__name__)
        dimensions = QueryFilter()
    else:
        dimensions = filters
    time_start = _normalize_time_bound(time_start, "time_start")
    time_end = _normalize_time_bound(time_end, "time_end")
    for entry in entries:
        if not _entry_in_time_window(entry, time_start, time_end):
            continue
        if not _passes_query_filters(entry, dimensions):
            continue
        filtered.append(entry)
    offset = _normalize_page_offset(offset)
    if offset > 0:
        filtered = filtered[offset:]
    limit = _normalize_page_limit(limit)
    if limit is not None:
        filtered = filtered[:limit]
    return filtered
def phase_of(entry: dict[str, Any], *, fallback_event: bool = False) -> str:
    phase = entry.get("phase")
    if isinstance(phase, str) and phase:
        return phase
    if fallback_event:
        event = entry.get("event")
        if isinstance(event, str) and event:
            return event
    return "unknown"
def _ts_order_key(raw: Any) -> tuple[int, Any]:
    if isinstance(raw, str):
        parsed = parse_log_ts(raw)
        if parsed is not None:
            return (0, parsed)
        return (1, raw)
    return (2, "")
def parse_duration_ms(raw: Any, *, label: str) -> float | None:
    if raw is None or isinstance(raw, bool):
        return None
    try:
        value = float(raw)
    except (TypeError, ValueError, OverflowError) as _e:
        logger.debug("%s: skip invalid duration_ms %r: %s", label, raw, _e)
        return None
    if not math.isfinite(value):
        logger.debug("%s: skip non-finite duration_ms %r", label, raw)
        return None
    if value < 0:
        logger.debug("%s: skip negative duration_ms %r", label, raw)
        return None
    return value
def _quality_issue(issue_type: str, severity: str, detail: str,
                   count: int, **extra: Any) -> dict[str, Any]:
    return {"type": issue_type, "severity": severity,
            "detail": detail, "count": count, **extra}
def _collect_phase_durations(ph_entries: list[dict[str, Any]]) -> list[float]:
    durations: list[float] = []
    for e in ph_entries:
        duration = parse_duration_ms(e.get("duration_ms"), label="reconstruct")
        if duration is not None:
            durations.append(duration)
    return durations
def _phase_gap_seconds(prev_end: str, curr_start: str) -> float | None:
    if not (prev_end and curr_start):
        return None
    prev_dt = parse_log_ts(prev_end)
    curr_dt = parse_log_ts(curr_start)
    if prev_dt is None or curr_dt is None:
        return None
    return (curr_dt - prev_dt).total_seconds()
def _detect_phase_gaps(sorted_phases: list[str],
                       phases: dict[str, Any]) -> list[dict[str, Any]]:
    gaps: list[dict[str, Any]] = []
    for i in range(1, len(sorted_phases)):
        prev_end = phases[sorted_phases[i - 1]].get("end_ts", "")
        curr_start = phases[sorted_phases[i]].get("start_ts", "")
        gap_seconds = _phase_gap_seconds(prev_end, curr_start)
        if (gap_seconds is not None
                and gap_seconds > _PHASE_GAP_THRESHOLD_SECONDS):
            gaps.append({
                "from_phase": sorted_phases[i - 1],
                "to_phase": sorted_phases[i],
                "gap_seconds": gap_seconds,
                "from_ts": prev_end,
                "to_ts": curr_start,
            })
    return gaps
def _timeline_entry(entry: dict[str, Any]) -> dict[str, Any]:
    return {
        "ts": entry.get("ts", ""),
        "phase": phase_of(entry),
        "event": entry.get("event", ""),
        "method_id": entry.get("method_id", ""),
        "level": entry.get("level", ""),
        "message": entry.get("message", ""),
        "duration_ms": entry.get("duration_ms"),
    }
def _group_entries_by_phase(
    entries: list[dict[str, Any]],
) -> tuple[dict[str, list[dict[str, Any]]], list[dict[str, Any]]]:
    phase_entries: dict[str, list[dict[str, Any]]] = {}
    timeline: list[dict[str, Any]] = []
    for entry in entries:
        phase_entries.setdefault(phase_of(entry), []).append(entry)
        timeline.append(_timeline_entry(entry))
    return phase_entries, timeline
def _valid_ts_strings(entries: list[dict[str, Any]]) -> list[str]:
    return [ts for e in entries
            if _is_wellformed_ts(ts := e.get("ts"))]
def _phase_aggregate(ph_entries: list[dict[str, Any]]) -> dict[str, Any]:
    timestamps = _valid_ts_strings(ph_entries)
    durations = _collect_phase_durations(ph_entries)
    error_count = sum(1 for e in ph_entries
                      if _level_of(e) in ("ERROR", "CRITICAL"))
    return {
        "entries": ph_entries,
        "entry_count": len(ph_entries),
        "start_ts": min(timestamps, key=_ts_order_key) if timestamps else "",
        "end_ts": max(timestamps, key=_ts_order_key) if timestamps else "",
        "total_duration_ms": sum(durations),
        "error_count": error_count,
    }
def _pipeline_gaps(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    trace_groups: dict[str, list[dict[str, Any]]] = {}
    for entry in entries:
        trace_id = entry.get("trace_id")
        trace_key = trace_id if isinstance(trace_id, str) and trace_id else ""
        trace_groups.setdefault(trace_key, []).append(entry)
    gaps: list[dict[str, Any]] = []
    for trace_entries in trace_groups.values():
        phase_entries: dict[str, list[dict[str, Any]]] = {}
        for entry in trace_entries:
            phase_entries.setdefault(phase_of(entry), []).append(entry)
        phases = {ph: _phase_aggregate(ph_entries)
                  for ph, ph_entries in phase_entries.items()}
        ordered = sorted(
            phases, key=lambda p: _ts_order_key(phases[p].get("start_ts", "")))
        gaps.extend(_detect_phase_gaps(ordered, phases))
    return gaps
def _reconstruct_from_entries(
    entries: list[dict[str, Any]], trace_id: str | None,
) -> dict[str, Any]:
    entries = [e for e in entries if _is_wellformed_ts(e.get("ts"))]
    if trace_id is not None:
        entries = [e for e in entries if e.get("trace_id") == trace_id]
    phase_entries, timeline = _group_entries_by_phase(entries)
    phases = {ph: _phase_aggregate(ph_entries)
              for ph, ph_entries in phase_entries.items()}
    sorted_phases = sorted(
        phases, key=lambda p: _ts_order_key(phases[p].get("start_ts", "")))
    gaps = _pipeline_gaps(entries)
    return {
        "phases": phases,
        "timeline": timeline,
        "total_entries": len(entries),
        "phase_order": sorted_phases,
        "gaps": gaps,
        "trace_id": trace_id,
    }
def reconstruct_pipeline_execution(
    trace_id: str | None = None,
    time_start: str | None = None,
    time_end: str | None = None,
) -> dict[str, Any]:
    entries = query_logs(time_start=time_start, time_end=time_end)
    return _reconstruct_from_entries(entries, trace_id)
def _parse_perf_sample(
    trace: dict[str, Any],
) -> tuple[str, datetime | None, float] | None:
    if not isinstance(trace, dict):
        logger.debug("group_perf_durations: skip non-dict trace %r", trace)
        return None
    phase = phase_of(trace, fallback_event=True)
    duration = parse_duration_ms(
        trace.get("duration_ms"), label=f"group_perf_durations[{phase}]")
    if duration is None:
        return None
    _ts_raw = trace.get("ts")
    ts_dt = (parse_log_ts(_ts_raw)
             if isinstance(_ts_raw, str) and _ts_raw else None)
    return phase, ts_dt, duration
def group_perf_durations(traces: list[dict[str, Any]]) -> dict[str, list[float]]:
    phase_samples: dict[str, list[tuple[datetime | None, float]]] = {}
    for t in traces:
        sample = _parse_perf_sample(t)
        if sample is None:
            continue
        phase, ts_dt, duration = sample
        phase_samples.setdefault(phase, []).append((ts_dt, duration))
    phase_data: dict[str, list[float]] = {}
    for phase, samples in phase_samples.items():
        samples.sort(key=lambda _p: (
            _p[0] is not None, _p[0] or datetime.min))
        phase_data[phase] = [_dur for _dt, _dur in samples]
    return phase_data
_ZERO_BASELINE_DEGRADATION_PCT = 100000.0
def _degradation_result(recent: float, historical_avg: float,
                        pct: float) -> dict[str, float]:
    return {
        "recent_ms": recent,
        "historical_avg_ms": historical_avg,
        "degradation_pct": pct,
    }
def _normalize_degradation_ratio(raw: Any) -> float:
    try:
        value = float(raw)
    except (TypeError, ValueError, OverflowError):
        value = float("nan")
    if isinstance(raw, bool) or not math.isfinite(value) or value <= 0:
        logger.warning(
            "detect_phase_degradation: 非法降级倍率 %r，回退默认 %.2f",
            raw, _DEFAULT_DEGRADATION_RATIO)
        return _DEFAULT_DEGRADATION_RATIO
    return value
def _normalize_threshold_ms(raw: Any) -> float:
    try:
        value = float(raw)
    except (TypeError, ValueError, OverflowError):
        value = float("nan")
    if isinstance(raw, bool) or not math.isfinite(value) or value < 0:
        logger.warning(
            "analyze_perf_bottlenecks: 非法阈值 %r，回退默认 %.0fms",
            raw, _DEFAULT_BOTTLENECK_THRESHOLD_MS)
        return _DEFAULT_BOTTLENECK_THRESHOLD_MS
    return value
def detect_phase_degradation(
    durations: list[float], ratio: float = _DEFAULT_DEGRADATION_RATIO,
) -> dict[str, float] | None:
    if len(durations) < 3:
        return None
    ratio = _normalize_degradation_ratio(ratio)
    recent = durations[-1]
    historical_avg = sum(durations[:-1]) / max(len(durations) - 1, 1)
    if not (math.isfinite(recent) and math.isfinite(historical_avg)):
        return None
    if recent <= 0 or historical_avg < 0:
        return None
    if historical_avg == 0:
        return _degradation_result(recent, 0.0, _ZERO_BASELINE_DEGRADATION_PCT)
    if recent > historical_avg * ratio:
        return _degradation_result(
            recent, historical_avg, (recent / historical_avg - 1) * 100)
    return None
def _bottleneck_record(phase: str, avg_dur: float, max_dur: float,
                       call_count: int, threshold_ms: float,
                       ) -> tuple[dict[str, Any], dict[str, Any]] | None:
    if avg_dur <= threshold_ms:
        return None
    priority = "high" if avg_dur > threshold_ms * 2 else "medium"
    bottleneck = {
        "phase": phase,
        "avg_ms": round(avg_dur, 1),
        "max_ms": round(max_dur, 1),
        "calls": call_count,
        "priority": priority,
        "suggestion": f"阶段 {phase} 平均耗时 {avg_dur:.1f}ms 超过阈值 {threshold_ms}ms，建议优化I/O或减少重复计算",
    }
    suggestion = {
        "target": phase,
        "direction": "reduce_io_or_cache",
        "priority": priority,
        "data": {"avg_ms": round(avg_dur, 1), "max_ms": round(max_dur, 1),
                 "calls": call_count},
    }
    return bottleneck, suggestion
def _degradation_record(
    phase: str, durations: list[float], degradation_ratio: float,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    deg = detect_phase_degradation(durations, ratio=degradation_ratio)
    if not deg:
        return None, None
    degradation_pct = deg["degradation_pct"]
    signal = {
        "phase": phase,
        "recent_ms": round(deg["recent_ms"], 1),
        "historical_avg_ms": round(deg["historical_avg_ms"], 1),
        "degradation_pct": round(degradation_pct, 1),
    }
    suggestion = None
    if degradation_pct > 100:
        suggestion = {
            "target": phase,
            "direction": "investigate_regression",
            "priority": "high",
            "data": {"recent_ms": round(deg["recent_ms"], 1),
                     "historical_avg_ms": round(deg["historical_avg_ms"], 1),
                     "degradation_pct": round(degradation_pct, 1)},
        }
    return signal, suggestion
def _collect_phase_signals(
    phase: str, durations: list[float], threshold_ms: float,
    degradation_ratio: float,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, list[dict[str, Any]]]:
    if not durations:
        return None, None, []
    avg_dur = sum(durations) / len(durations)
    hit = _bottleneck_record(phase, avg_dur, max(durations), len(durations),
                             threshold_ms)
    bottleneck = hit[0] if hit is not None else None
    suggestions: list[dict[str, Any]] = [hit[1]] if hit is not None else []
    deg_signal, deg_suggestion = _degradation_record(
        phase, durations, degradation_ratio)
    if deg_suggestion is not None:
        suggestions.append(deg_suggestion)
    return bottleneck, deg_signal, suggestions
def analyze_perf_bottlenecks(
    threshold_ms: float = _DEFAULT_BOTTLENECK_THRESHOLD_MS,
    degradation_ratio: float = _DEFAULT_DEGRADATION_RATIO,
) -> dict[str, Any]:
    threshold_ms = _normalize_threshold_ms(threshold_ms)
    degradation_ratio = _normalize_degradation_ratio(degradation_ratio)
    traces = load_perf_traces()
    if not traces:
        return {
            "bottlenecks": [],
            "degradation_signals": [],
            "optimization_suggestions": [],
            "summary": {"total_phases": 0, "bottleneck_count": 0, "degraded_count": 0},
        }
    phase_data = group_perf_durations(traces)
    bottlenecks: list[dict[str, Any]] = []
    degradation_signals: list[dict[str, Any]] = []
    optimization_suggestions: list[dict[str, Any]] = []
    for phase, durations in phase_data.items():
        if not durations:
            continue
        bottleneck, deg_signal, suggestions = _collect_phase_signals(
            phase, durations, threshold_ms, degradation_ratio)
        if bottleneck is not None:
            bottlenecks.append(bottleneck)
        if deg_signal is not None:
            degradation_signals.append(deg_signal)
        optimization_suggestions.extend(suggestions)
    return {
        "bottlenecks": bottlenecks,
        "degradation_signals": degradation_signals,
        "optimization_suggestions": optimization_suggestions,
        "summary": {
            "total_phases": len(phase_data),
            "bottleneck_count": len(bottlenecks),
            "degraded_count": len(degradation_signals),
        },
    }
def _iter_jsonl_raw_lines(fpath: str):
    try:
        with open(fpath, encoding="utf-8-sig", errors="replace") as f:
            yield from f
    except OSError as _e:
        logger.debug("check_log_quality: read failed for %s: %s", fpath, _e)
def _count_json_parse_errors(fpath: str) -> int:
    errors = 0
    for line in _iter_jsonl_raw_lines(fpath):
        stripped = line.strip()
        if not stripped:
            continue
        try:
            record = json.loads(stripped)
        except _JSON_DECODE_ERRORS as e:
            logger.debug("check_log_quality: JSON parse failed in %s: %s", fpath, e)
            errors += 1
            continue
        if not isinstance(record, dict):
            logger.debug("check_log_quality: non-object JSON record in %s", fpath)
            errors += 1
    return errors
_TS_DISORDER_TOLERANCE_SECONDS = 1.0
def _scan_ts_malformed(entries: list[dict[str, Any]]) -> int:
    malformed = 0
    for entry in entries:
        ts = entry.get("ts")
        if ts is None or (isinstance(ts, str) and not ts.strip()):
            continue
        if not _is_wellformed_ts(ts):
            malformed += 1
    return malformed
def _scan_ts_disorder(entries: list[dict[str, Any]]) -> int:
    disorder_count = 0
    max_seen: datetime | None = None
    for entry in entries:
        ts = entry.get("ts", "")
        if not _is_wellformed_ts(ts):
            continue
        current = parse_log_ts(ts)
        if current is None:
            continue
        if max_seen is not None and current < max_seen:
            if (max_seen - current).total_seconds() > _TS_DISORDER_TOLERANCE_SECONDS:
                disorder_count += 1
            continue
        max_seen = current
    return disorder_count
_REQUIRED_LOG_FIELDS: frozenset[str] = frozenset({"ts", "level", "logger"})
def _collect_field_issues(entries: list[dict[str, Any]],
                          ) -> tuple[list[dict[str, Any]], int, int, int]:
    issues: list[dict[str, Any]] = []
    field_missing_count = 0
    for entry in entries:
        missing = {
            field for field in _REQUIRED_LOG_FIELDS
            if field not in entry or entry[field] is None
            or (isinstance(entry[field], str) and not entry[field].strip())
        }
        if missing:
            field_missing_count += 1
            if field_missing_count <= _FIELD_MISSING_SAMPLE_LIMIT:
                issues.append(_quality_issue(
                    "field_missing", "medium",
                    f"缺少字段: {', '.join(sorted(missing))}", 1))
    if field_missing_count > _FIELD_MISSING_SAMPLE_LIMIT:
        issues.append(_quality_issue(
            "field_missing", "high",
            f"共 {field_missing_count} 条日志缺少必要字段", field_missing_count))
    timestamp_disorder_count = _scan_ts_disorder(entries)
    if timestamp_disorder_count > 0:
        issues.append(_quality_issue(
            "timestamp_disorder",
            "low" if timestamp_disorder_count <= 2 else "medium",
            f"共 {timestamp_disorder_count} 条日志时间戳显著乱序"
            f"（回溯>{_TS_DISORDER_TOLERANCE_SECONDS:g}s）",
            timestamp_disorder_count))
    timestamp_malformed_count = _scan_ts_malformed(entries)
    if timestamp_malformed_count > 0:
        issues.append(_quality_issue(
            "timestamp_malformed", "medium",
            f"共 {timestamp_malformed_count} 条日志时间戳不可解析，无法参与时间线与消费",
            timestamp_malformed_count))
    return (issues, field_missing_count, timestamp_disorder_count,
            timestamp_malformed_count)
def _scan_parse_errors(log_dir: str) -> int:
    if not log_dir or not os.path.isdir(log_dir):
        return 0
    main_files = _backup_paths(log_dir, MAIN_LOG_FILE)
    main_files.append(os.path.join(log_dir, MAIN_LOG_FILE))
    parse_error_count = 0
    for fpath in main_files:
        parse_error_count += _count_json_parse_errors(fpath)
    return parse_error_count
def _check_volume_anomaly(log_dir: str) -> tuple[bool, int]:
    if not log_dir or not os.path.isdir(log_dir):
        return False, 0
    try:
        entries = os.listdir(log_dir)
    except OSError as _e:
        logger.debug("check_log_quality: listdir failed for %s: %s", log_dir, _e)
        return False, 0
    total_size = 0
    for fname in entries:
        fpath = os.path.join(log_dir, fname)
        if not os.path.isfile(fpath):
            continue
        try:
            total_size += os.path.getsize(fpath)
        except OSError as _e:
            logger.debug("check_log_quality: getsize failed for %s: %s", fname, _e)
            continue
    return total_size > _VOLUME_ANOMALY_BYTES, total_size
class _QualitySignals(NamedTuple):
    field_missing_count: int
    parse_error_count: int
    chain_break_count: int
    timestamp_disorder_count: int
    timestamp_malformed_count: int
    volume_anomaly: bool
    total_size: int
    total_entries: int
def _compute_quality_score(signals: _QualitySignals) -> float:
    quality_score = 100.0
    quality_score -= min(signals.field_missing_count * 2, 30)
    quality_score -= min(signals.parse_error_count * 3, 20)
    quality_score -= min(signals.timestamp_disorder_count * 1, 10)
    quality_score -= min(signals.timestamp_malformed_count * 2, 20)
    quality_score -= min(signals.chain_break_count * 5, 20)
    if signals.volume_anomaly:
        quality_score -= 15
    return max(0.0, quality_score)
def _collect_quality_signals(
    entries: list[dict[str, Any]], log_dir: str,
) -> tuple[_QualitySignals, list[dict[str, Any]]]:
    issues: list[dict[str, Any]] = []
    (field_issues, field_missing_count, timestamp_disorder_count,
     timestamp_malformed_count) = _collect_field_issues(entries)
    issues.extend(field_issues)
    parse_error_count = _scan_parse_errors(log_dir)
    if parse_error_count > 0:
        issues.append(_quality_issue(
            "parse_error", "medium",
            f"共 {parse_error_count} 行 JSON 解析失败或记录不是对象", parse_error_count))
    gaps = _pipeline_gaps(entries)
    chain_break_count = len(gaps)
    if chain_break_count > 0:
        issues.append(_quality_issue(
            "chain_break", "medium",
            f"共 {chain_break_count} 处管道阶段间日志断裂"
            f"（间隔>{_PHASE_GAP_THRESHOLD_SECONDS // 60}分钟）",
            chain_break_count, gaps=gaps[:5]))
    volume_anomaly, total_size = _check_volume_anomaly(log_dir)
    if volume_anomaly:
        issues.append(_quality_issue(
            "volume_anomaly", "high",
            f"日志目录总体积 {total_size / 1024 / 1024:.1f}MB "
            f"超过 {_VOLUME_ANOMALY_BYTES // 1024 // 1024}MB 阈值", 1))
    signals = _QualitySignals(
        field_missing_count=field_missing_count,
        parse_error_count=parse_error_count,
        chain_break_count=chain_break_count,
        timestamp_disorder_count=timestamp_disorder_count,
        timestamp_malformed_count=timestamp_malformed_count,
        volume_anomaly=volume_anomaly,
        total_size=total_size,
        total_entries=len(entries),
    )
    return signals, issues
def check_log_quality() -> dict[str, Any]:
    setup_logging()
    log_dir = get_log_dir()
    entries = _main_log_entries()
    signals, issues = _collect_quality_signals(entries, log_dir)
    has_evidence = signals.total_entries > 0
    if not has_evidence:
        issues.insert(0, _quality_issue(
            "no_entries", "high",
            "日志为空（零条记录），质量无法评估：无证据不等于满分", 0))
    field_completeness = (
        1.0 - (signals.field_missing_count / signals.total_entries)
        if has_evidence else 0.0)
    quality_score = (_compute_quality_score(signals) if has_evidence else 0.0)
    return {
        "quality_score": round(quality_score, 1),
        "issues": issues,
        "field_completeness": round(field_completeness, 4),
        "parse_error_count": signals.parse_error_count,
        "timestamp_disorder_count": signals.timestamp_disorder_count,
        "timestamp_malformed_count": signals.timestamp_malformed_count,
        "chain_break_count": signals.chain_break_count,
        "volume_anomaly": signals.volume_anomaly,
        "total_entries": signals.total_entries,
    }
def _payload_of(ev: dict[str, Any]) -> dict[str, Any]:
    payload = ev.get("payload")
    return payload if isinstance(payload, dict) else {}
def _ts_of(ev: dict[str, Any]) -> str:
    ts = ev.get("ts")
    return ts if isinstance(ts, str) else ""
def _evidence_text(value: Any) -> str:
    return "" if value in (None, "") else str(value)
def normalize_group_key(value: Any, fallback: str = "unknown") -> str:
    if isinstance(value, str):
        return value or fallback
    if not value:
        return fallback
    return str(value)
def _explicit_audit_target(ev: dict[str, Any]) -> str:
    payload = _payload_of(ev)
    return str(
        payload.get("path") or payload.get("target") or payload.get("file")
        or payload.get("file_path") or payload.get("function") or ""
    )
def _audit_target_of(ev: dict[str, Any], ev_type: str) -> str:
    return _explicit_audit_target(ev) or ev_type
_ACTION_TOKENS = (
    r"rollback(?:s|ing)?|rolled_back|revert(?:ed|s|ing)?|"
    r"restore(?:d|s|ing)?|recover(?:ed|s|ing|y)?|"
    r"delete(?:d|s|ing)?|(?:hot)?fix(?:er|ing|ed|es)?|apply|applied")
_NEGATION_PREFIXES = (
    r"not|no|never|cannot|can_not|unable|unable_to|failed|failed_to|"
    r"fail_to|skip|skipped")
_NEGATION_SUFFIXES = (
    r"failed|failure|error|rejected|aborted|skipped|cancelled|canceled|"
    r"denied|blocked|not_applied|did_not_apply|not_performed|not_done|"
    r"not_needed|not_required|not_necessary|no_need")
_NEGATED_ACTION_RE = re.compile(
    rf"(?:^|[^a-z0-9])(?:{_NEGATION_PREFIXES})[_-]?(?:{_ACTION_TOKENS})"
    rf"(?:[^a-z0-9]|$)"
    rf"|(?:^|[^a-z0-9])(?:{_ACTION_TOKENS})[_-]?(?:{_NEGATION_SUFFIXES})"
    rf"(?:[^a-z0-9]|$)")
_FIX_TOKEN_RE = re.compile(
    r"(?:^|[^a-z0-9])(?:hot)?fix(?:er|ing|ed|es)?(?:[^a-z0-9]|$)")
_DELETE_TOKEN_RE = re.compile(
    r"(?:^|[^a-z0-9])delete(?:d|s|ing)?(?:[^a-z0-9]|$)")
_ROLLBACK_TOKEN_RE = re.compile(
    r"(?:^|[^a-z0-9])(?:rollback(?:s|ing)?|rolled_back|revert(?:ed|s|ing)?)"
    r"(?:[^a-z0-9]|$)")
_RESTORE_TOKEN_RE = re.compile(
    r"(?:^|[^a-z0-9])(?:restore(?:d|s|ing)?|recover(?:ed|s|ing|y)?)"
    r"(?:[^a-z0-9]|$)")
def _event_name_is_not_applied(lowered: str, action_re=None) -> bool:
    return any(
        action_re is None or action_re.search(match.group(0))
        for match in _NEGATED_ACTION_RE.finditer(lowered))
def is_rollback_event(event_name: str) -> bool:
    lowered = str(event_name).lower()
    return (bool(_ROLLBACK_TOKEN_RE.search(lowered))
            and not _event_name_is_not_applied(lowered, _ROLLBACK_TOKEN_RE))
def _is_restore_event(event_name: str) -> bool:
    lowered = str(event_name).lower()
    return (bool(_RESTORE_TOKEN_RE.search(lowered))
            and not _event_name_is_not_applied(lowered, _RESTORE_TOKEN_RE))
def _error_evidence(errors: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {"ts": _ts_of(e), "event": _evidence_text(e.get("event")),
         "message": _evidence_text(e.get("message"))[:200]}
        for e in errors[-5:]
    ]
def _swallow_evidence(events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {"ts": _ts_of(e),
         "exc_type": normalize_group_key(_payload_of(e).get("exc_type")),
         "context": _evidence_text(_payload_of(e).get("context"))}
        for e in events[-3:]
    ]
def _error_groups(all_logs: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    groups: dict[str, list[dict[str, Any]]] = {}
    for entry in all_logs:
        if _level_of(entry) not in ("ERROR", "CRITICAL"):
            continue
        key = normalize_group_key(entry.get("method_id") or entry.get("logger"))
        groups.setdefault(key, []).append(entry)
    return groups
def _repeated_failure_finding(mid: str,
                              errors: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "type": "repeated_failure",
        "severity": "high",
        "source_logs": _error_evidence(errors),
        "suggestion": f"方法 {mid} 出现 {len(errors)} 次错误，建议检查异常处理逻辑",
        "issue_signature": compute_issue_signature(
            "json_log", "repeated_failure", method_id=mid),
        "method_id": mid,
        "error_count": len(errors),
    }
def _detect_grouped_findings(
    groups: dict[Any, list[dict[str, Any]]],
    min_count: int,
    build_finding: Callable[[Any, list[dict[str, Any]]], dict[str, Any]],
    consumer_id: str,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for key, events in groups.items():
        if len(events) < min_count:
            continue
        finding = build_finding(key, events)
        resolution = _resolution_record(
            consumer_id, finding["issue_signature"])
        if resolution is not None:
            events = [event for event in events
                      if not _resolution_covers_ts(
                          resolution, _ts_of(event))]
            if len(events) < min_count:
                continue
            finding = build_finding(key, events)
        findings.append(finding)
    return findings
def _swallowed_module(ev: dict[str, Any]) -> str:
    return normalize_group_key(
        _payload_of(ev).get("module") or ev.get("logger") or "unknown")
def _swallowed_groups(
        swallowed: list[dict[str, Any]],
) -> dict[tuple[str, str], list[dict[str, Any]]]:
    groups: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for ev in swallowed:
        module = _swallowed_module(ev)
        exc_type = normalize_group_key(_payload_of(ev).get("exc_type"))
        groups.setdefault((module, exc_type), []).append(ev)
    return groups
def _silent_exception_finding(module: str,
                              events: list[dict[str, Any]]) -> dict[str, Any]:
    exc_type = normalize_group_key(_payload_of(events[0]).get("exc_type"))
    return {
        "type": "silent_exception",
        "severity": "medium",
        "source_logs": _swallow_evidence(events),
        "suggestion": f"模块 {module} 有 {len(events)} 次静默异常（{exc_type}），建议添加显式异常处理",
        "issue_signature": compute_issue_signature(
            "swallowed", "silent_exception",
            method_id=module, error_type=exc_type),
        "module": module,
        "exception_count": len(events),
    }
def _detect_audit_anomalies(audit_events: list[dict[str, Any]],
                            consumer_id: str) -> list[dict[str, Any]]:
    audit_events = [ev for ev in audit_events
                    if isinstance(ev, dict) and is_production_audit_target(ev)]
    reported_signatures: set[str] = set()
    findings = _scan_fix_then_rollback(audit_events, consumer_id,
                                       reported_signatures)
    findings += _scan_delete_without_restore(audit_events, consumer_id,
                                             reported_signatures)
    return findings
def _audit_correlation_key(target: str) -> str:
    text = str(target or "").strip()
    if not text:
        return ""
    if not any(sep in text for sep in ("/", "\\")) and not os.path.isabs(text):
        return text
    return os.path.normcase(os.path.normpath(text))
def _first_landed_event_after(
    audit_events: list[dict[str, Any]],
    start: int,
    window: int,
    trigger_target: str,
    predicate: Callable[[str], bool],
) -> dict[str, Any] | None:
    target_key = _audit_correlation_key(trigger_target)
    if not target_key:
        return None
    for j in range(start + 1, min(start + window + 1, len(audit_events))):
        next_ev = audit_events[j]
        if _payload_failed(next_ev):
            continue
        if not predicate(str(next_ev.get("event", ""))):
            continue
        if _audit_correlation_key(_explicit_audit_target(next_ev)) == target_key:
            return next_ev
    return None
def _is_fix_event(event_name: str) -> bool:
    lowered = event_name.lower()
    if not _FIX_TOKEN_RE.search(lowered) or is_rollback_event(lowered):
        return False
    return not _event_name_is_not_applied(lowered, _FIX_TOKEN_RE)
def is_delete_event(event_name: str) -> bool:
    lowered = str(event_name).lower()
    return (bool(_DELETE_TOKEN_RE.search(lowered))
            and not _event_name_is_not_applied(lowered, _DELETE_TOKEN_RE))
_HIGH_RISK_FIX_MARKERS: tuple[str, ...] = ("fix_apply", "fix_applied")
def _is_fix_apply_event(event_name: str) -> bool:
    lowered = str(event_name).lower()
    return (_is_fix_event(lowered)
            and any(marker in lowered for marker in _HIGH_RISK_FIX_MARKERS))
def _transient_path_segment(segment: str) -> bool:
    return (is_temp_artifact_dir(segment)
            or bool(is_backup_snapshot_dir(segment)))
def is_test_artifact_path(path: str) -> bool:
    text = str(path or "").replace("\\", "/").strip()
    if not text:
        return False
    if is_runtime_temp_path(text):
        return True
    raw_segments = [seg for seg in text.split("/") if seg]
    lowered = [seg.lower() for seg in raw_segments]
    if "_pytest_basetemp" in lowered or any(
            seg.startswith("pytest-of-") for seg in lowered):
        return True
    if any(_transient_path_segment(seg) for seg in raw_segments):
        return True
    if resolve_session_root_from_artifact_path(text):
        return True
    try:
        norm = os.path.realpath(os.path.abspath(text))
        sys_tmp = os.path.realpath(os.path.abspath(tempfile.gettempdir()))
    except (OSError, ValueError) as _e:
        log_swallowed(__name__, _e, context='is_test_artifact_path:resolve')
        return False
    return norm == sys_tmp or norm.startswith(sys_tmp + os.sep)
def is_production_audit_target(entry: dict[str, Any]) -> bool:
    if not isinstance(entry, dict):
        return True
    return not is_test_artifact_path(_explicit_audit_target(entry))
def _payload_failed(entry: dict[str, Any]) -> bool:
    payload = _payload_of(entry)
    if "ok" not in payload:
        return False
    ok = payload.get("ok")
    if isinstance(ok, str) and ok.strip().lower() == "failed":
        return True
    return not signal_bool(ok)
def is_high_risk_audit_event(entry: dict[str, Any]) -> bool:
    if not isinstance(entry, dict):
        return False
    event_name = str(entry.get("event") or "")
    if not (is_delete_event(event_name) or is_rollback_event(event_name)
            or _is_fix_apply_event(event_name)):
        return False
    if _payload_failed(entry):
        return False
    return is_production_audit_target(entry)
def _already_reported(sig: str, reported_signatures: set[str],
                      consumer_id: str, finding: dict[str, Any]) -> bool:
    if sig in reported_signatures:
        return True
    resolution = _resolution_record(consumer_id, sig)
    if resolution is None:
        return False
    return all(
        _resolution_covers_ts(resolution, evidence.get("ts", ""))
        for evidence in finding.get("source_logs", []))
def _fix_rollback_finding(ev: dict[str, Any], next_ev: dict[str, Any],
                          ev_type: str, next_type: str) -> dict[str, Any]:
    return {
        "type": "audit_anomaly_sequence",
        "severity": "high",
        "source_logs": [
            {"ts": _ts_of(ev), "event": ev_type},
            {"ts": _ts_of(next_ev), "event": next_type},
        ],
        "suggestion": "修复后立即回滚，建议检查修复安全网验证逻辑",
        "issue_signature": compute_issue_signature(
            "audit", "fix_then_rollback",
            method_id=_audit_target_of(ev, ev_type)),
    }
def _delete_without_restore_finding(ev: dict[str, Any],
                                    ev_type: str) -> dict[str, Any]:
    return {
        "type": "audit_anomaly_sequence",
        "severity": "medium",
        "source_logs": [{"ts": _ts_of(ev), "event": ev_type}],
        "suggestion": "删除操作后未检测到恢复操作，建议确认是否有备份回滚机制",
        "issue_signature": compute_issue_signature(
            "audit", "delete_without_restore",
            method_id=_audit_target_of(ev, ev_type)),
    }
_RECOVERABLE_DELETE_MARKER_RE = re.compile(
    r"(?:^|[^a-z0-9])(?:safe_delete|recycle|trash)(?:[^a-z0-9]|$)")
def _is_recoverable_delete_event(event_name: str) -> bool:
    lowered = str(event_name).lower()
    return (is_delete_event(lowered)
            and bool(_RECOVERABLE_DELETE_MARKER_RE.search(lowered)))
def _scan_fix_then_rollback(audit_events: list[dict[str, Any]],
                            consumer_id: str,
                            reported_signatures: set[str],
                            ) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for i, ev in enumerate(audit_events):
        ev_type = str(ev.get("event", ""))
        if not _is_fix_event(ev_type):
            continue
        if _payload_failed(ev):
            continue
        next_ev = _first_landed_event_after(
            audit_events, i, 10, _explicit_audit_target(ev), is_rollback_event)
        if next_ev is None:
            continue
        finding = _fix_rollback_finding(
            ev, next_ev, ev_type, str(next_ev.get("event", "")))
        sig = finding["issue_signature"]
        if _already_reported(sig, reported_signatures, consumer_id, finding):
            continue
        findings.append(finding)
        reported_signatures.add(sig)
    return findings
def _scan_delete_without_restore(audit_events: list[dict[str, Any]],
                                 consumer_id: str,
                                 reported_signatures: set[str],
                                 ) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for i, ev in enumerate(audit_events):
        ev_type = str(ev.get("event", ""))
        if not is_delete_event(ev_type):
            continue
        if _payload_failed(ev):
            continue
        if _is_recoverable_delete_event(ev_type):
            continue
        if _first_landed_event_after(
                audit_events, i, 20, _explicit_audit_target(ev),
                _is_restore_event) is not None:
            continue
        finding = _delete_without_restore_finding(ev, ev_type)
        sig = finding["issue_signature"]
        if _already_reported(sig, reported_signatures, consumer_id, finding):
            continue
        findings.append(finding)
        reported_signatures.add(sig)
    return findings
def _advance_consumer_cursor_once(consumer_id: str, log_type: str,
                                 entries: list[dict[str, Any]]) -> bool:
    last_ts = max(_valid_ts_strings(entries), key=_ts_order_key, default="")
    if not last_ts:
        return True
    try:
        return advance_cursor(consumer_id, log_type, last_ts)
    except Exception as _e:
        logger.debug("analyze_log_patterns: advance_cursor failed for %s/%s: %s", consumer_id, log_type, _e)
        return False
def _advance_consumption_cursors(consumer_id: str,
                                 json_entries: list[dict[str, Any]],
                                 swallowed: list[dict[str, Any]],
                                 audit_events: list[dict[str, Any]]) -> bool:
    cursor_advanced = True
    for log_type, entries in (
        ("json_log", json_entries),
        ("swallowed", swallowed),
        ("audit", audit_events),
    ):
        if not _advance_consumer_cursor_once(consumer_id, log_type, entries):
            cursor_advanced = False
    return cursor_advanced
def _findings_summary(findings: list[dict[str, Any]]) -> dict[str, Any]:
    by_type: dict[str, int] = {}
    by_severity: dict[str, int] = {}
    for finding in findings:
        ftype = finding["type"]
        severity = finding["severity"]
        by_type[ftype] = by_type.get(ftype, 0) + 1
        by_severity[severity] = by_severity.get(severity, 0) + 1
    return {"total": len(findings), "by_type": by_type, "by_severity": by_severity}
def _findings_after_cursor(
    findings: list[dict[str, Any]], cursor: dict[str, Any],
) -> list[dict[str, Any]]:
    last_ts = cursor.get("last_ts", "")
    if not _is_wellformed_ts(last_ts):
        return findings
    cursor_key = _ts_order_key(last_ts)
    fresh: list[dict[str, Any]] = []
    for finding in findings:
        for evidence in finding.get("source_logs", []):
            ts = evidence.get("ts", "")
            if (_is_wellformed_ts(ts)
                    and _ts_order_key(ts) > cursor_key):
                fresh.append(finding)
                break
    return fresh
def analyze_log_patterns(
    consumer_id: str = "log_analyzer_v1",
    *,
    advance_cursor: bool = True,
) -> dict[str, Any]:
    consumer_id = normalize_group_key(consumer_id, str(consumer_id))
    try:
        cleanup_consumption_state()
    except Exception as e:
        logger.debug("analyze_log_patterns: cleanup_consumption_state failed: %s", e)
    json_entries, json_result = _load_consumption_view(consumer_id, "json_log")
    swallowed_entries, swallowed_result = _load_consumption_view(
        consumer_id, "swallowed")
    audit_entries, audit_result = _load_consumption_view(consumer_id, "audit")
    all_logs = [entry for entry in json_entries
                if _is_wellformed_ts(entry.get("ts"))]
    swallowed = [entry for entry in swallowed_entries
                 if _is_wellformed_ts(entry.get("ts"))]
    audit_events = [entry for entry in audit_entries
                    if _is_wellformed_ts(entry.get("ts"))]
    findings: list[dict[str, Any]] = []
    repeated = _detect_grouped_findings(
        _error_groups(all_logs), 3, _repeated_failure_finding, consumer_id)
    findings.extend(_findings_after_cursor(
        repeated, json_result["cursor"]))
    silent = _detect_grouped_findings(
        _swallowed_groups(swallowed), 2,
        lambda key, events: _silent_exception_finding(key[0], events),
        consumer_id)
    findings.extend(_findings_after_cursor(
        silent, swallowed_result["cursor"]))
    audit_findings = _detect_audit_anomalies(audit_events, consumer_id)
    findings.extend(_findings_after_cursor(
        audit_findings, audit_result["cursor"]))
    cursor_advanced = (
        _advance_consumption_cursors(
            consumer_id, json_entries, swallowed_entries, audit_entries)
        if advance_cursor else False)
    return {
        "findings": findings,
        "summary": _findings_summary(findings),
        "consumer_id": consumer_id,
        "cursor_advanced": cursor_advanced,
        "resolved_skipped": {
            "json_log": json_result.get("resolved_count", 0),
            "swallowed": swallowed_result.get("resolved_count", 0),
            "audit": audit_result.get("resolved_count", 0),
        },
    }
logger.info("log_analysis 日志分析域已加载: %d 项导出", len(__all__))

from __future__ import annotations

import contextlib
import copy
import glob
import hashlib as _hashlib
import json
import logging
import os
import re
import threading
import time
from typing import Any

from jwsgj.diag_guard_io import (
    guarded_open,
    replace_with_retry,
    safe_delete,
    two_level_unlink,
)
from jwsgj.diag_guard_state import (
    ProcessLock,
    read_json_artifact,
)
from jwsgj.diag_types_normalize import (
    coerce_round_anchor,
    compact_ts_to_ms,
    dict_or_empty,
    entry_round_anchor,
    finding_file_key,
    format_compact_ts,
    has_finding_entries,
    normalize_severity_rank,
    severity_literal_from_rank,
    str_or_empty,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    DIAG_REPORT_DIRNAME,
    DIAGNOSE_TO_P,
    HASH_PREFIX_LEN,
    LEGACY_TO_MAIN,
    SEVERITY_RANK,
    STAGE_METRICS_KEY_SPEC,
    diag_severity_to_p,
    is_finding_carrier_key,
)
from jwsgj.fp_rules_judge import (
    get_fp_rule_ids,
    is_static_fp_rule,
)
from jwsgj.log_config import (
    append_jsonl_locked,
    log_swallowed,
    perf_trace,
    prune_jsonl_file,
)
from jwsgj.runtime_paths import (
    PIPELINE_STATE_FILENAME,
    canonical_json_artifact_dir,
    diag_intermediate_dir,
    first_json_artifact,
    get_temp_base,
    is_path_within_skill,
    json_artifact_dir,
    resolve_workspace_root,
)
from jwsgj.runtime_scope import (
    RUNTIME_DIR_NAME,
    canonical_path,
    is_diagnosis_out_of_scope,
    is_test_dir_name,
    normalize_skill_dir,
    prune_walk_dirs,
)
from jwsgj.shared_cache import (
    handoff_persistence_enabled,
    load_code_hash_lines,
    mem_bus_peek,
    mem_bus_put,
    mem_bus_take,
    require_warmed,
)

logger = logging.getLogger(__name__)
HASH_CONTEXT_LINES = 50
def _content_hash(context: str) -> str:
    return _hashlib.md5(context.encode("utf-8"), usedforsecurity=False).hexdigest()[:HASH_PREFIX_LEN]
_CONTAINER_HEAD_PREFIXES = ("def ", "class ", "async def ")
def _line_indent(line: str) -> int:
    return len(line) - len(line.lstrip())
def _is_container_head(stripped: str, indent: int, f_indent: int,
                       min_passed: int | None) -> bool:
    return (stripped.startswith(_CONTAINER_HEAD_PREFIXES)
            and indent < f_indent
            and (min_passed is None or min_passed > indent))
def _find_container_head(lines: list[str], f_idx: int, f_indent: int) -> int:
    func_start = -1
    min_passed: int | None = None
    idx = f_idx - 1
    while idx >= 0:
        s = lines[idx].strip()
        if s and not s.startswith("#"):
            ind = _line_indent(lines[idx])
            if _is_container_head(s, ind, f_indent, min_passed):
                func_start = idx
                break
            if min_passed is None or ind < min_passed:
                min_passed = ind
        idx -= 1
    return func_start
def _find_container_end(lines: list[str], func_start: int, line: int) -> int:
    head_indent = _line_indent(lines[func_start])
    func_end = max(0, line)
    while func_end < len(lines):
        stripped = lines[func_end].strip()
        if stripped and not stripped.startswith("#"):
            indent = _line_indent(lines[func_end])
            if indent <= head_indent:
                break
        func_end += 1
    return func_end
def _indent_container_span(lines: list[str], line: int) -> tuple[int, int] | None:
    if line < 1:
        return None
    f_idx = line - 1
    stripped = lines[f_idx].strip()
    if not stripped:
        return None
    f_indent = _line_indent(lines[f_idx])
    if stripped.startswith(_CONTAINER_HEAD_PREFIXES):
        func_start = f_idx
    elif f_indent == 0:
        return None
    else:
        func_start = _find_container_head(lines, f_idx, f_indent)
        if func_start < 0:
            return None
    func_end = _find_container_end(lines, func_start, line)
    return (func_start, func_end) if func_end - func_start > 1 else None
def _indent_window_hash(lines: list[str], line: int) -> str | None:
    span = _indent_container_span(lines, line)
    if span is None:
        return None
    return _content_hash("".join(lines[span[0]:span[1]]))
def _ast_boundary_hash(func_spans: list, lines: list[str], line: int) -> str | None:
    innermost = None
    innermost_span = 0
    for node_lineno, node_end in func_spans:
        if node_lineno <= line <= node_end:
            span = node_end - node_lineno
            if innermost is None or span < innermost_span:
                innermost = (node_lineno, node_end)
                innermost_span = span
    if innermost is None:
        return None
    context = "".join(lines[innermost[0] - 1:innermost[1]])
    return _content_hash(context)
def _fixed_window_hash(lines: list[str], line: int) -> str:
    start = max(0, line - 1 - HASH_CONTEXT_LINES)
    end = min(len(lines), line + HASH_CONTEXT_LINES)
    context = "".join(lines[start:end])
    return _content_hash(context)
def _window_hash_or_err(lines: list[str], line: int) -> str:
    try:
        window_hash = _indent_window_hash(lines, line)
    except (IndexError, ValueError):
        logger.warning("compute_code_hash: 缩进边界推断失败，返回 err_hash", exc_info=True)
        return "err_hash"
    return window_hash if window_hash is not None else _fixed_window_hash(lines, line)
def compute_code_hash(filepath: str, line: int) -> str:
    try:
        lines, tree, func_spans = load_code_hash_lines(filepath)
        if lines is None or line < 1 or line > len(lines):
            return "err_hash"
        if tree is not None:
            ast_hash = _ast_boundary_hash(func_spans, lines, line)
            if ast_hash is not None:
                return ast_hash
        return _window_hash_or_err(lines, line)
    except (OSError, IndexError) as _e:
        log_swallowed(__name__, _e, context='compute_code_hash:OSError')
        return "err_hash"
__all__ = [
    'HASH_CONTEXT_LINES',
    'append_stage_trace_entry',
    'artifact_ts',
    'atomic_save_json',
    'build_ai_fix_list',
    'canonical_cv_path',
    'clear_regression_handoff',
    'collect_cv_confirmed_scope',
    'collect_round_p0_findings',
    'collect_scale_baseline',
    'compute_code_hash',
    'compute_skill_source_hash',
    'cv_artifact_fresh',
    'get_round_start_ts',
    'list_source_files',
    'load_all_intermediates',
    'load_called_symbols',
    'load_cv_findings_channel',
    'load_cv_findings_index',
    'load_intermediate',
    'load_intermediate_fused',
    'load_retrospective_context',
    'load_review_result_summary',
    'locate_sub_results',
    'normalize_regression_handoff',
    'normalize_round_start_ts',
    'peek_pipeline_phase',
    'peek_round_start_ts',
    'persist_cv_reports',
    'read_stage_trace_entries',
    'regression_handoff_path',
    'resolve_intermediate_dirs',
    'round_anchor_equiv_form',
    'save_intermediate',
    'save_regression_handoff',
    'take_regression_handoff',
]
_PIPELINE_PROVENANCE = f"{__name__.split('.', 1)[0]}_pipeline"
_PIPELINE_STATE_FILE = PIPELINE_STATE_FILENAME
_CALLGRAPH_METHOD_CANDIDATES = ("C", "D1", "C1")
_CALLGRAPH_GROUP_SUB_METHOD = "C1"
_CONSOLIDATED_SCHEMA = "2.0"
_METHOD_SCHEMA_VERSION = "1.0"
_CONSOLIDATED_PREFIX = "round_"
_CONSOLIDATED_KEEP_ROUNDS = 2
_CONSOLIDATED_QUARANTINE_KEEP = 5
_SCATTERED_KEEP_VERSIONS = 2
_CV_ARTIFACT_KEEP_VERSIONS = 3
_CFD_LOCK_OFFSET = 1 << 30
_CONSOLIDATED_LOCK_FILENAME = ".consolidated.lock"
_DEFAULT_STRICT_PROVENANCE = True
_DEFAULT_TIMESTAMP = ""
_DEFAULT_PHASE: str | None = None
_DEFAULT_CACHE: Any = None
_DEFAULT_SKILL_DIR: str | None = None
_ANCHOR_DIRNAMES = frozenset(
    os.path.normcase(name) for name in (RUNTIME_DIR_NAME, DIAG_REPORT_DIRNAME))
_SESSION_LATEST: dict[tuple[str, str], tuple[str, dict, tuple[int, int]]] = {}
def _consolidated_round_key(skill_dir: str) -> str:
    if not skill_dir:
        return ""
    try:
        return get_round_start_ts(normalize_skill_dir(skill_dir)) or ""
    except Exception as _e:  # noqa: BLE001
        logger.debug("[Runner] 轮次键解析失败(降级续写): %s", _e)
        return ""
def _consolidated_suffix(path: str) -> str:
    stem = os.path.basename(path).removesuffix(".json")
    return stem[len(_CONSOLIDATED_PREFIX):]
def _consolidated_recency_key(suffix: str) -> tuple[int, str]:
    timestamped = len(suffix) == 17 and suffix.isdecimal()
    return int(timestamped), suffix
def _consolidated_pick_path(intermediate_dir: str, round_key: str) -> str:
    if round_key:
        return os.path.join(
            intermediate_dir, f"{_CONSOLIDATED_PREFIX}{round_key}.json")
    try:
        for cand in sorted(
                glob.glob(os.path.join(
                    intermediate_dir, f"{_CONSOLIDATED_PREFIX}*.json")),
                key=lambda path: _consolidated_recency_key(
                    _consolidated_suffix(path)), reverse=True):
            doc = _read_consolidated(cand)
            if doc is not None and not str(doc.get("_round_ts") or ""):
                return cand
    except Exception as _e:  # noqa: BLE001
        logger.debug("[Runner] consolidated 续写挑选失败(开新): %s", _e)
    return os.path.join(
        intermediate_dir,
        f"{_CONSOLIDATED_PREFIX}{timestamp_ms()}.json")
def _is_consolidated_doc(doc) -> bool:
    return (isinstance(doc, dict)
            and doc.get("_schema_version") == _CONSOLIDATED_SCHEMA
            and isinstance(doc.get("methods"), dict))
_CONSOLIDATED_READ_CACHE: dict[str, tuple[tuple[int, int], dict | None]] = {}
_CONSOLIDATED_READ_LOCK = threading.Lock()


def _read_consolidated(path: str) -> dict | None:
    """读取 consolidated 文档（按文件指纹缓存解析结果）。

    同一批次内 `_iter_consolidated_paths` 会被多个通道反复遍历，原实现每次
    都重新打开并全量 `json.load`：实测单轮 69 次调用只对应 **1 个**文件
    （重复率 98.6%）。文件只在 `_cfd_merge_and_write` 写盘时变化，故以
    ``(mtime_ns, size)`` 作指纹缓存，写盘后主动失效。缓存文档仅供内部
    持有，每次返回深拷贝，避免调用方修改加载结果后污染后续读取。
    """
    try:
        stat = os.stat(path)
    except OSError as e:
        logger.debug("[Runner] consolidated 读取失败(跳过): %s: %s", path, e)
        return None
    fingerprint = (stat.st_mtime_ns, stat.st_size)
    with _CONSOLIDATED_READ_LOCK:
        cached = _CONSOLIDATED_READ_CACHE.get(path)
        if cached is not None and cached[0] == fingerprint:
            return copy.deepcopy(cached[1])
    try:
        with open(path, encoding="utf-8-sig") as f:
            doc = json.load(f)
    except (OSError, ValueError, RecursionError) as e:
        logger.debug("[Runner] consolidated 读取失败(跳过): %s: %s", path, e)
        return None
    result = doc if _is_consolidated_doc(doc) else None
    with _CONSOLIDATED_READ_LOCK:
        _CONSOLIDATED_READ_CACHE[path] = (fingerprint, result)
    return copy.deepcopy(result)
def _cfd_doc_or_skeleton(doc, round_key: str) -> dict:
    if _is_consolidated_doc(doc):
        return doc
    return {"_schema_version": _CONSOLIDATED_SCHEMA,
            "_provenance": _PIPELINE_PROVENANCE,
            "_round_ts": round_key,
            "methods": {}}
def _cfd_read_doc_lenient(path: str) -> dict | None:
    if not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as _rf:
            raw = _rf.read()
        return json.loads(raw) if raw.strip() else None
    except FileNotFoundError:
        return None
    except OSError:
        raise
    except (ValueError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_cfd_read_doc_lenient:parse')
        return None
def _cfd_atomic_write(path: str, blob: bytes) -> None:
    tmp = f"{path}.{os.getpid()}.{threading.get_ident()}.tmp"
    try:
        with open(tmp, "wb") as _wf:
            _wf.write(blob)
            _wf.flush()
            os.fsync(_wf.fileno())
        replace_with_retry(tmp, path)
    except BaseException:
        two_level_unlink(tmp)
        raise
    finally:
        with _CONSOLIDATED_READ_LOCK:
            _CONSOLIDATED_READ_CACHE.pop(path, None)
def _cfd_quarantine(path: str, ts: str, reason: str) -> None:
    backup = f"{path}.{reason}.{ts}.{os.getpid()}"
    replace_with_retry(path, backup)
    logger.error("[Runner] consolidated 文档%s，已隔离备份: %s -> %s",
                 reason, path, backup)
def _cfd_merge_and_write(path: str, mid: str, data: dict,
                         round_key: str, ts: str) -> None:
    raw_doc = _cfd_read_doc_lenient(path)
    if raw_doc is not None and not _is_consolidated_doc(raw_doc):
        _cfd_quarantine(path, ts, "legacy")
        raw_doc = None
    elif raw_doc is None and os.path.isfile(path) and os.path.getsize(path) > 0:
        _cfd_quarantine(path, ts, "corrupt")
    doc = _cfd_doc_or_skeleton(raw_doc, round_key)
    if round_key:
        doc["_round_ts"] = round_key
    doc["methods"][mid] = data
    doc["_updated_ts"] = ts
    blob = json.dumps(doc, ensure_ascii=False, indent=2,
                      default=str).encode("utf-8")
    _cfd_atomic_write(path, blob)
def _unlock_quiet(fd: int) -> None:
    try:
        ProcessLock.unlock_region(fd, _CFD_LOCK_OFFSET)
    except OSError as e:
        logger.debug("[Runner] consolidated 解锁失败: %s", e)
@contextlib.contextmanager
def _quiet_close(handle):
    try:
        yield handle
    finally:
        try:
            handle.close()
        except OSError as e:
            logger.debug("[Runner] consolidated fd 关闭失败: %s", e)
def _session_consolidated_signature(intermediate_dir: str,
                                    round_key: str) -> tuple[int, int] | None:
    if not round_key:
        return None
    path = os.path.join(
        intermediate_dir, f"{_CONSOLIDATED_PREFIX}{round_key}.json")
    if not os.path.isfile(path):
        return None
    try:
        stat = os.stat(path)
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_session_consolidated_signature:OSError')
        return None
    return stat.st_mtime_ns, stat.st_size
def _session_has_newer_consolidated(intermediate_dir: str,
                                    round_key: str) -> bool:
    try:
        _round_order = _consolidated_recency_key(round_key)
        return any(_consolidated_recency_key(suffix) > _round_order
                   for _path, suffix in _iter_consolidated_paths(intermediate_dir))
    except OSError as e:
        logger.debug("[Runner] 会话缓存轮次校验失败(绕过缓存): %s", e)
        return True
def _session_data_snapshot(data: dict, operation: str) -> dict | None:
    try:
        snapshot = copy.deepcopy(data)
    except Exception as exc:  # noqa: BLE001
        logger.debug("[Runner] 会话缓存%s快照不可复制，绕过内存缓存: %s",
                     operation, exc)
        return None
    return snapshot if isinstance(snapshot, dict) else None
def _session_cache_store(intermediate_dir: str, mid: str, round_key: str,
                         data: dict) -> None:
    signature = _session_consolidated_signature(intermediate_dir, round_key)
    if signature is None:
        return
    snapshot = _session_data_snapshot(data, "写入")
    if snapshot is None:
        return
    with contextlib.suppress(TypeError):
        _SESSION_LATEST[(intermediate_dir, mid)] = (
            round_key, snapshot, signature)
def _save_consolidated(intermediate_dir: str, mid: str, data: dict,
                       round_key: str, ts: str) -> bool:
    try:
        os.makedirs(intermediate_dir, exist_ok=True)
    except OSError:
        logger.exception("[Runner] consolidated 目录创建失败 %s",
                     intermediate_dir)
        return False
    lock_path = os.path.join(intermediate_dir, _CONSOLIDATED_LOCK_FILENAME)
    try:
        data = dict(data)
        with _quiet_close(open(lock_path, "ab")) as handle:
            fd = handle.fileno()
            ProcessLock.lock_region(fd, _CFD_LOCK_OFFSET, blocking=True)
            try:
                path = _consolidated_pick_path(intermediate_dir, round_key)
                data["_round_ref"] = os.path.basename(path)
                _cfd_merge_and_write(path, mid, data, round_key, ts)
            finally:
                _unlock_quiet(fd)
    except (OSError, TypeError, ValueError, RecursionError):
        logger.exception("[Runner] consolidated 写入失败 %s", mid)
        return False
    _prune_globbed(intermediate_dir, f"{_CONSOLIDATED_PREFIX}*.json",
                   _CONSOLIDATED_KEEP_ROUNDS, "轮级 consolidated")
    for _reason in ("legacy", "corrupt"):
        _prune_globbed(
            intermediate_dir,
            f"{_CONSOLIDATED_PREFIX}*.json.{_reason}.*",
            _CONSOLIDATED_QUARANTINE_KEEP, f" consolidated 隔离({_reason})")
    _session_cache_store(intermediate_dir, mid, round_key, data)
    return True
def _prune_order(path: str) -> tuple[float, str]:
    try:
        mtime = os.path.getmtime(path)
    except OSError:
        mtime = 0.0
    return mtime, os.path.basename(path)
def _prune_globbed(directory: str, pattern: str, keep: int,
                   label: str) -> int:
    try:
        candidates = glob.glob(os.path.join(directory, pattern))
        if len(candidates) <= keep:
            return 0
        candidates.sort(key=_prune_order)
        obsolete = candidates[:-keep] if keep > 0 else candidates
        removed = 0
        for old_path in obsolete:
            if safe_delete(old_path):
                removed += 1
            else:
                logger.debug("[Runner] 清理历史%s失败: %s", label, old_path)
        if removed:
            logger.info("[Runner] 清理历史%s %d 份（保留最近 %d 份）",
                        label, removed, keep)
        return removed
    except OSError as e:
        logger.debug("[Runner] %s清理异常(不阻断): %s", label, e)
        return 0
def _iter_consolidated_paths(intermediate_dir: str,
                              freshness_cutoff: str = _DEFAULT_TIMESTAMP):
    _paths: list[str] = []
    for _dir in (intermediate_dir, *_legacy_candidate_dirs(intermediate_dir)):
        _paths.extend(glob.glob(os.path.join(
            _dir, f"{_CONSOLIDATED_PREFIX}*.json")))
    _ordered: list[tuple[str, str]] = []
    for cpath in dict.fromkeys(_paths):
        suffix = _consolidated_suffix(cpath)
        if freshness_cutoff and not _freshness_candidate_ok(
                suffix, freshness_cutoff):
            continue
        _ordered.append((suffix, cpath))
    for suffix, cpath in sorted(
            _ordered, key=lambda item: _consolidated_recency_key(item[0]),
            reverse=True):
        yield cpath, suffix
def _load_from_consolidated(intermediate_dir: str, mid: str,
                            strict_provenance: bool = _DEFAULT_STRICT_PROVENANCE,
                            freshness_cutoff: str = _DEFAULT_TIMESTAMP) -> dict | None:
    corrupted = None
    try:
        for cpath, _suffix in _iter_consolidated_paths(
                intermediate_dir, freshness_cutoff):
            doc = _read_consolidated(cpath)
            if doc is None:
                corrupted = corrupted or _corrupted_entry(
                    mid, f"consolidated unreadable or incompatible: {cpath}")
                continue
            data = doc.get("methods", {}).get(mid)
            if data is None:
                continue
            if not isinstance(data, dict):
                logger.warning("[Runner] consolidated 方法载荷非 dict %s: %s",
                               mid, type(data).__name__)
                corrupted = corrupted or _corrupted_entry(
                    mid, f"consolidated payload {type(data).__name__}")
                continue
            if strict_provenance and data.get("_provenance") != _PIPELINE_PROVENANCE:
                logger.warning("[Runner] %s 缺少 _provenance (consolidated, "
                               "got=%s), 忽略", mid, data.get("_provenance"))
                continue
            if data.get("status") == "corrupted":
                corrupted = corrupted or data
                continue
            return data
    except OSError as e:
        logger.debug("[Runner] consolidated 扫描失败(降级旧格式): %s", e)
    return corrupted
def _session_latest_hit(intermediate_dir: str, mid: str,
                        strict_provenance: bool,
                        freshness_cutoff: str) -> dict | None:
    try:
        _hit = _SESSION_LATEST.get((intermediate_dir, mid))
    except TypeError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_session_latest_hit:TypeError')
        return None
    if _hit is None:
        return None
    _round_key, _data, _signature = _hit
    if freshness_cutoff and not _freshness_candidate_ok(
            _round_key, freshness_cutoff):
        return None
    if strict_provenance and _data.get("_provenance") != _PIPELINE_PROVENANCE:
        return None
    if _data.get("status") == "corrupted":
        return None
    if (_session_consolidated_signature(intermediate_dir, _round_key) != _signature
            or _session_has_newer_consolidated(intermediate_dir, _round_key)):
        return None
    return _session_data_snapshot(_data, "读取")
def _mid_ts_suffix(candidate: str, mid: str) -> str:
    return os.path.basename(candidate).rsplit(".", 1)[0][len(mid) + 1:]
def _legacy_candidate_dirs(intermediate_dir: str) -> list[str]:
    base = os.path.abspath(intermediate_dir)
    ws = ""
    cursor = base
    while True:
        if os.path.normcase(os.path.basename(cursor)) in _ANCHOR_DIRNAMES:
            ws = os.path.dirname(cursor)
            break
        parent = os.path.dirname(cursor)
        if parent == cursor:
            break
        cursor = parent
    if not ws:
        return []
    cands = (
        os.path.join(ws, "Temp", "report_34", "_intermediate"),
        os.path.join(ws, "Temp", "report_34"),
        os.path.join(ws, "Temp"),
        os.path.join(ws, "htm"),
        os.path.join(ws, "report_34", "_intermediate"),
        os.path.join(ws, "report_34"),
    )
    seen: list[str] = []
    for cand in cands:
        real = canonical_path(cand)
        if not os.path.isdir(cand) or real in seen:
            continue
        seen.append(real)
    return [c for c in cands if canonical_path(c) in seen]
def _scattered_candidates(intermediate_dir: str, mid: str,
                          freshness_cutoff: str) -> list[str]:
    _dirs = [intermediate_dir, *_legacy_candidate_dirs(intermediate_dir)]
    candidates: list[str] = []
    for _dir in _dirs:
        candidates.extend(glob.glob(os.path.join(_dir, f"{mid}_*.json")))
    candidates = list(dict.fromkeys(candidates))
    if freshness_cutoff:
        candidates = [
            c for c in candidates
            if _freshness_candidate_ok(_mid_ts_suffix(c, mid), freshness_cutoff)]
    if not candidates:
        return []
    def suffix_of(candidate: str) -> str:
        return _mid_ts_suffix(candidate, mid)
    timestamped = [c for c in candidates
                   if len(suffix_of(c)) == 17 and suffix_of(c).isdecimal()]
    ts_set = set(timestamped)
    others = [c for c in candidates if c not in ts_set]
    return (sorted(timestamped, key=suffix_of, reverse=True)
            + sorted(others, key=suffix_of, reverse=True))
def _corrupted_entry(mid: str, detail: str) -> dict:
    return {"method_id": mid, "status": "corrupted", "error": detail}
def _channel_meta_ok(data: dict, mid: str, strict_provenance: bool,
                     log_tag: str) -> bool:
    if not log_tag:
        _ver = data.get("_schema_version")
        if _ver and _ver != _METHOD_SCHEMA_VERSION:
            logger.warning("[Runner] schema version mismatch %s: "
                           "got=%s expected=%s", mid, _ver,
                           _METHOD_SCHEMA_VERSION)
    _prov = data.get("_provenance")
    if strict_provenance and _prov != _PIPELINE_PROVENANCE:
        logger.warning("[Runner] %s%s 缺少 _provenance (got=%s), 忽略",
                       f"{log_tag} " if log_tag else "", mid, _prov)
        return False
    return True
def _read_channel_payload(path: str, mid: str, strict_provenance: bool,
                          log_tag: str = "") -> dict | None:
    try:
        with open(path, encoding="utf-8-sig") as f:
            data = json.load(f)
    except (OSError, ValueError, RecursionError) as e:
        logger.warning("[Runner] 读取中间结果失败 %s: %s", mid, e)
        return _corrupted_entry(mid, str(e))
    if not isinstance(data, dict):
        logger.warning("[Runner] %s中间结果顶层非 dict %s: %s",
                       log_tag, mid, type(data).__name__)
        return _corrupted_entry(mid, f"top-level {type(data).__name__}")
    if not _channel_meta_ok(data, mid, strict_provenance, log_tag):
        return None
    return data
def load_intermediate(intermediate_dir: str, mid: str,
                      strict_provenance: bool = _DEFAULT_STRICT_PROVENANCE,
                      freshness_cutoff: str = _DEFAULT_TIMESTAMP) -> dict | None:
    _hit = _session_latest_hit(intermediate_dir, mid,
                               strict_provenance, freshness_cutoff)
    if _hit is not None:
        logger.debug("[Runner] 中间结果内存命中 %s (round=%s)", mid,
                     _hit.get("_round_ref") or "")
        return _hit
    _cfd = _load_from_consolidated(intermediate_dir, mid,
                                   strict_provenance, freshness_cutoff)
    if _cfd is not None and _cfd.get("status") != "corrupted":
        return _cfd
    corrupted = _cfd
    for path in _scattered_candidates(intermediate_dir, mid, freshness_cutoff):
        entry = _read_channel_payload(path, mid, strict_provenance)
        if entry is None:
            continue
        if entry.get("status") == "corrupted":
            corrupted = corrupted or entry
            continue
        return entry
    if not freshness_cutoff:
        path = os.path.join(intermediate_dir, f"{mid}.json")
        if os.path.exists(path):
            legacy = _read_channel_payload(
                path, mid, strict_provenance, log_tag="旧格式")
            if legacy is not None:
                if legacy.get("status") == "corrupted":
                    corrupted = corrupted or legacy
                else:
                    return legacy
    return corrupted
def load_intermediate_fused(intermediate_dir: str, legacy_mid: str,
                            strict_provenance: bool = _DEFAULT_STRICT_PROVENANCE,
                            freshness_cutoff: str = _DEFAULT_TIMESTAMP) -> dict | None:
    main_id = LEGACY_TO_MAIN.get(legacy_mid, legacy_mid)
    _corrupted = None
    if main_id != legacy_mid:
        data = load_intermediate(intermediate_dir, main_id,
                                 strict_provenance, freshness_cutoff)
        if data is not None and data.get("status") != "corrupted":
            return data
        if data is not None:
            _corrupted = data
    legacy = load_intermediate(intermediate_dir, legacy_mid,
                               strict_provenance, freshness_cutoff)
    if legacy is not None:
        return legacy
    return _corrupted
def _admit_result_entry(results: dict, mid: str, entry) -> bool:
    if not entry:
        return False
    if entry.get("status") == "corrupted":
        logger.warning("[Runner] 跳过损坏中间结果: %s", mid)
        return False
    if entry.get("status") == "error":
        entry = dict(entry, _degraded=True)
        logger.warning("[Runner] 降级加载 error 结果: %s", mid)
    results[mid] = entry
    return True
def _merge_session_latest_channel(results: dict, seen_mids: set,
                                  intermediate_dir: str,
                                  freshness_cutoff: str) -> None:
    for _sdir, _smid in list(_SESSION_LATEST):
        if _sdir != intermediate_dir or _smid in seen_mids:
            continue
        _sdata = _session_latest_hit(
            _sdir, _smid, strict_provenance=True,
            freshness_cutoff=freshness_cutoff)
        if _sdata is not None and _admit_result_entry(results, _smid, _sdata):
            seen_mids.add(_smid)
def _consolidated_method_entry(mid: str, data) -> dict | None:
    if not isinstance(data, dict):
        return None
    if data.get("_provenance") != _PIPELINE_PROVENANCE:
        logger.warning("[Runner] consolidated %s 缺少 _provenance（忽略）", mid)
        return None
    return data
def _merge_consolidated_channel(results: dict, seen_mids: set,
                                intermediate_dir: str,
                                freshness_cutoff: str) -> bool:
    corrupted = False
    for cpath, _suffix in _iter_consolidated_paths(
            intermediate_dir, freshness_cutoff):
        doc = _read_consolidated(cpath)
        if doc is None:
            corrupted = True
            continue
        for mid, data in doc["methods"].items():
            if mid in seen_mids:
                continue
            if not isinstance(data, dict):
                corrupted = True
                continue
            entry = _consolidated_method_entry(mid, data)
            if entry is None:
                continue
            if _admit_result_entry(results, mid, entry):
                seen_mids.add(mid)
            else:
                corrupted = True
    return corrupted
def _scattered_mid_admitted(fname: str, freshness_cutoff: str) -> str | None:
    if not fname.endswith(".json") or fname.startswith("_"):
        return None
    m = re.match(r'^([A-Z][A-Z0-9]*)', fname)
    if not m:
        return None
    mid = m.group(1)
    if freshness_cutoff:
        _stem = fname.removesuffix(".json")
        if not _freshness_candidate_ok(_stem[len(mid) + 1:],
                                       freshness_cutoff):
            return None
    return mid
def _merge_scattered_channel(results: dict, seen_mids: set,
                             intermediate_dir: str,
                             freshness_cutoff: str) -> bool:
    corrupted = False
    scattered_mids: set[str] = set()
    for directory in (intermediate_dir, *_legacy_candidate_dirs(intermediate_dir)):
        if not os.path.isdir(directory):
            continue
        for fname in os.listdir(directory):
            mid = _scattered_mid_admitted(fname, freshness_cutoff)
            if mid is not None:
                scattered_mids.add(mid)
    for mid in sorted(scattered_mids, reverse=True):
        if mid in seen_mids:
            continue
        r = load_intermediate(intermediate_dir, mid,
                              freshness_cutoff=freshness_cutoff)
        if _admit_result_entry(results, mid, r):
            seen_mids.add(mid)
        elif isinstance(r, dict) and r.get("status") == "corrupted":
            corrupted = True
    return corrupted
def load_all_intermediates(intermediate_dir: str,
                           freshness_cutoff: str = _DEFAULT_TIMESTAMP) -> dict[str, dict]:
    results: dict[str, dict] = {}
    try:
        seen_mids = set()
        _merge_session_latest_channel(results, seen_mids,
                                      intermediate_dir, freshness_cutoff)
        consolidated_corrupted = _merge_consolidated_channel(
            results, seen_mids, intermediate_dir, freshness_cutoff)
        scattered_corrupted = _merge_scattered_channel(
            results, seen_mids, intermediate_dir, freshness_cutoff)
        if consolidated_corrupted or scattered_corrupted:
            if not results:
                results["_error"] = True
            results["_partial"] = True
        return results
    except Exception:
        logger.exception("[load_all_intermediates] 异常降级")
        partial = dict(results)
        partial["_error"] = True
        partial["_partial"] = True
        return partial
def _try_parse_date(digits: str, fmt: str, label: str) -> str | None:
    try:
        time.strptime(digits, fmt)
        return digits
    except ValueError as e:
        logger.debug("normalize_round_start_ts: %s 解析失败，"
                     "转入 epoch 分支: %s", label, e)
        return None
def _ts_from_epoch_ms(digits: str) -> str:
    if not (12 <= len(digits) <= 13):
        return ""
    try:
        return format_compact_ts(int(digits))
    except (OverflowError, OSError, ValueError) as e:
        logger.debug("normalize_round_start_ts: epoch 转换失败（%s），"
                     "视为无轮次标记", e)
        return ""
_ROUND_TS_FORMATS = (
    (17, 14, "%Y%m%d%H%M%S", "17 位日期", "", "20"),
    (14, 14, "%Y%m%d%H%M%S", "14 位日期", "000", ""),
    (8, 8, "%Y%m%d", "8 位日期", "000000000", ""),
)
def normalize_round_start_ts(ts: str) -> str:
    if not isinstance(ts, str) or not ts or not ts.isdecimal():
        return ""
    for length, date_length, fmt, label, suffix, prefix in _ROUND_TS_FORMATS:
        if len(ts) != length or not ts.startswith(prefix):
            continue
        if _try_parse_date(ts[:date_length], fmt, label) is not None:
            return ts + suffix
    return _ts_from_epoch_ms(ts.lstrip("0"))
def round_anchor_equiv_form(anchor: Any) -> str:
    _anchor = coerce_round_anchor(anchor)
    return normalize_round_start_ts(_anchor) or _anchor
def resolve_intermediate_dirs(skill_dir: str,
                              output_dir: str | None = None) -> tuple[str, str, str]:
    skill_abs = normalize_skill_dir(skill_dir)
    out_abs = (
        canonical_json_artifact_dir(skill_abs, output_dir))
    return skill_abs, out_abs, diag_intermediate_dir(out_abs)
def _freshness_candidate_ok(suffix: str, freshness_cutoff: str) -> bool:
    if not suffix or not suffix.isdecimal():
        return False
    timestamp_ms = normalize_round_start_ts(suffix)
    _cut = normalize_round_start_ts(str(freshness_cutoff))
    return bool(timestamp_ms) and bool(_cut) and timestamp_ms >= _cut
def _iter_source_files(skill_abs: str):
    for root, dirs, files in os.walk(skill_abs):
        prune_walk_dirs(dirs, root_dir=skill_abs)
        dirs[:] = sorted(d for d in dirs if not is_test_dir_name(d))
        for fn in sorted(files):
            if fn.lower().endswith(".py"):
                fpath = os.path.join(root, fn)
                rel = os.path.relpath(fpath, skill_abs).replace(os.sep, "/")
                yield rel, fpath
def list_source_files(skill_dir: str) -> list[tuple[str, str]]:
    return list(_iter_source_files(normalize_skill_dir(skill_dir)))
def compute_skill_source_hash(skill_dir: str) -> str:
    sd = normalize_skill_dir(skill_dir)
    hasher = _hashlib.sha256()
    for rel, fpath in _iter_source_files(sd):
        try:
            with open(fpath, "rb") as fh:
                rel_bytes = rel.encode("utf-8")
                content = fh.read()
                hasher.update(len(rel_bytes).to_bytes(8, "big"))
                hasher.update(rel_bytes)
                hasher.update(len(content).to_bytes(8, "big"))
                hasher.update(content)
        except OSError:
            logger.warning("[Pipeline] 源码哈希计算遇到不可读文件", exc_info=True)
            raise
    return hasher.hexdigest()
def _verified_pipeline_state(skill_dir: str) -> dict:
    try:
        # 延迟导入避免 pipeline_round_trace -> xv_intermediate_store 的模块循环；
        # 所有轮次字段都必须经过同一个签名验证入口，不得直读未验证正文。
        from jwsgj.pipeline_round_trace import load_pipeline_state
        state = load_pipeline_state(skill_dir)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_verified_pipeline_state:Exc')
        return {}
    if not isinstance(state, dict) or state.get("_state_load_error"):
        return {}
    return state
def get_round_start_ts(skill_dir: str) -> str:
    _sd = normalize_skill_dir(skill_dir)
    data = _verified_pipeline_state(_sd)
    if not data:
        return ""
    try:
        ts = data.get("round_start_ts", "")
        ts = str(ts).strip() if ts not in ("", None) else ""
        norm = normalize_round_start_ts(ts)
        if not norm:
            if ts:
                logger.warning(
                    "[get_round_start_ts] 非规范轮次时间戳 %r"
                    "（应为17位 YYYYMMDDHHMMSSfff 或 epoch 毫秒），"
                    "视为无轮次标记",
                    ts,
                )
            return ""
        return norm
    except (OSError, ValueError, TypeError, RecursionError) as e:
        logger.warning("[get_round_start_ts] 读取轮次状态失败，视为无轮次标记: %s", e)
        return ""
def _peek_pipeline_field(skill_dir: str, key: str) -> str:
    try:
        _st = _verified_pipeline_state(skill_dir)
        _v = _st.get(key, "") if isinstance(_st, dict) else ""
        return str(_v) if _v else ""
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context=f'peek_pipeline_field:{key}')
        return ""
def peek_round_start_ts(skill_dir: str) -> str:
    return _peek_pipeline_field(skill_dir, "round_start_ts")
def peek_pipeline_phase(skill_dir: str) -> str:
    return _peek_pipeline_field(skill_dir, "phase")
_STAGE_TRACE_MAX_BYTES = 8 * 1024 * 1024
_STAGE_TRACE_VERSION = 3
_STAGE_TRACE_TAIL_BYTES = 65536
_ADVANCE_KINDS = ("advance", "rewind_resume", "self_heal")
def _stage_trace_path(skill_dir: str) -> str:
    return os.path.join(get_temp_base(skill_dir), "pipeline_stages.jsonl")
def _parse_trace_line(raw: str) -> dict | None:
    ln = raw.strip()
    if not ln:
        return None
    try:
        entry = json.loads(ln)
    except (ValueError, RecursionError) as _e:
        logger.debug('静默降级[stage_trace 行解析:ValueError+]: %s: %s',
                     type(_e).__name__, _e)
        return None
    return entry if isinstance(entry, dict) else None
def _read_tail_text(path: str, limit: int = _STAGE_TRACE_TAIL_BYTES) -> str | None:
    if not os.path.isfile(path):
        return None
    try:
        with open(path, "rb") as bf:
            bf.seek(0, 2)
            size = bf.tell()
            bf.seek(max(0, size - limit))
            return bf.read().decode("utf-8", errors="replace")
    except FileNotFoundError:
        return None
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_read_tail_text:OSError')
        return None
def _trace_entry_matches(entry: dict, round_start_ts: str,
                         phase: str | None = _DEFAULT_PHASE) -> bool:
    _filter_anchor = round_anchor_equiv_form(round_start_ts)
    round_matches = not round_start_ts or (
        bool(_filter_anchor)
        and round_anchor_equiv_form(entry_round_anchor(entry)) == _filter_anchor)
    phase_matches = phase is None or entry.get("phase") == phase
    return bool(round_matches and phase_matches)
def _prev_round_trace_ts(path: str, round_start_ts: str) -> str:
    tail = _read_tail_text(path)
    if tail is None:
        return ""
    for _ln in reversed(tail.splitlines()):
        _e = _parse_trace_line(_ln)
        if _e is None or not _trace_entry_matches(_e, round_start_ts):
            continue
        _tsv = _e.get("timestamp")
        if isinstance(_tsv, str) and _tsv:
            return _tsv
    return ""
def _stage_trace_duration_ms(path: str, round_start_ts: str,
                             timestamp: str) -> int | None:
    if not round_start_ts:
        return None
    _prev_ts = _prev_round_trace_ts(path, round_start_ts) or round_start_ts
    _prev_ts = normalize_round_start_ts(_prev_ts) or _prev_ts
    _timestamp = normalize_round_start_ts(timestamp) or timestamp
    _t0ms = compact_ts_to_ms(_prev_ts)
    _t1ms = compact_ts_to_ms(_timestamp)
    if _t0ms is None or _t1ms is None or _t1ms < _t0ms:
        return None
    return _t1ms - _t0ms
def append_stage_trace_entry(skill_dir: str, entry: dict) -> None:
    _e = dict(entry)
    _e["trace_version"] = _STAGE_TRACE_VERSION
    _d = _e.get("direction")
    _e["direction"] = _d if _d in _ADVANCE_KINDS else "advance"
    _e["round_start_ts"] = coerce_round_anchor(_e.get("round_start_ts"))
    _path = _stage_trace_path(skill_dir)
    _e["phase_duration_ms"] = _stage_trace_duration_ms(
        _path, _e["round_start_ts"], str(_e.get("timestamp") or ""))
    _line = json.dumps(_e, ensure_ascii=False, default=str)
    if append_jsonl_locked(_path, _line):
        prune_jsonl_file(_path, _STAGE_TRACE_MAX_BYTES)
def _normalize_stage_trace_entry(entry: dict) -> dict:
    out = dict(entry)
    for _k in ("from_phase", "phase", "timestamp", "skill_dir"):
        out[_k] = str_or_empty(out.get(_k))
    out["round_start_ts"] = coerce_round_anchor(out.get("round_start_ts"))
    _d = out.get("direction")
    out["direction"] = _d if _d in _ADVANCE_KINDS else "legacy"
    out["metrics"] = dict_or_empty(entry.get("metrics"))
    out["artifacts"] = dict_or_empty(entry.get("artifacts"))
    _dur = entry.get("phase_duration_ms")
    out["phase_duration_ms"] = (
        _dur if isinstance(_dur, int) and not isinstance(_dur, bool)
        and _dur >= 0 else None)
    out["phase_in_spec"] = out["phase"] in STAGE_METRICS_KEY_SPEC
    return out
def _select_stage_trace_entries(
    lines: list[str],
    round_start_ts: str,
    phase: str | None,
) -> list[dict]:
    out: list[dict] = []
    for ln in lines:
        entry = _parse_trace_line(ln)
        if entry is not None and _trace_entry_matches(
                entry, round_start_ts, phase):
            out.append(_normalize_stage_trace_entry(entry))
    return out
def read_stage_trace_entries(skill_dir: str, round_start_ts: str = _DEFAULT_TIMESTAMP,
                             phase: str | None = _DEFAULT_PHASE) -> list[dict]:
    sd = normalize_skill_dir(skill_dir)
    path = _stage_trace_path(sd)
    if not os.path.isfile(path):
        return []
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
    except OSError as _e:
        logger.debug(
            '静默降级[read_stage_trace_entries:OSError]: %s: %s',
            type(_e).__name__, _e)
        return []
    return _select_stage_trace_entries(lines, round_start_ts, phase)
_REVIEW_PROFILE_FIELDS = ("overall_score", "risk_level", "timestamp")
def _project_review_fields(raw: dict) -> dict:
    return {k: raw[k] for k in _REVIEW_PROFILE_FIELDS
            if raw.get(k) not in (None, "")}
def _task_result_view(skill_dir: str) -> dict:
    raw = mem_bus_peek("review_result", skill_dir)
    if isinstance(raw, dict) and raw:
        return raw
    rv_path = first_json_artifact(skill_dir, "_review_result.json")
    if not rv_path:
        return {}
    data, kind, _err = read_json_artifact(rv_path)
    return data if kind == "ok" and isinstance(data, dict) else {}
def _review_view_guarded(skill_dir: str, caller: str) -> dict:
    try:
        return _task_result_view(skill_dir)
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context=f'{caller}:{type(exc).__name__}')
        return {}
def load_review_result_summary(skill_dir: str) -> dict:
    return _project_review_fields(
        _review_view_guarded(skill_dir, "load_review_result_summary"))
def load_retrospective_context(skill_dir: str) -> dict:
    return _project_review_fields(
        _review_view_guarded(skill_dir, "load_retrospective_context"))
def _is_valid_compact_ts17(value: Any) -> bool:
    return (isinstance(value, str) and len(value) == 17
            and value.isdecimal() and compact_ts_to_ms(value) is not None)
def artifact_ts(path: str) -> str:
    timestamp_ms = os.path.basename(path).rsplit('.', 1)[0].rsplit('_', 1)[-1]
    return timestamp_ms if _is_valid_compact_ts17(timestamp_ms) else ""
def cv_artifact_fresh(path: str, freshness_cutoff: str) -> bool:
    if not freshness_cutoff:
        return True
    return _freshness_candidate_ok(artifact_ts(path), freshness_cutoff)
def _channel_data_ts(payload, path: str) -> str:
    if isinstance(payload, dict):
        _t = payload.get('timestamp')
        if _is_valid_compact_ts17(_t):
            return _t
    return artifact_ts(path)
def _json_scan_dirs(base: str) -> list[str]:
    dirs: list[str] = []
    def _add(path: str) -> None:
        if not path:
            return
        absolute = os.path.abspath(path)
        if os.path.normcase(absolute) not in {os.path.normcase(d) for d in dirs}:
            dirs.append(absolute)
    _add(base)
    for legacy in _legacy_candidate_dirs(base):
        _add(legacy)
    try:
        ws = resolve_workspace_root()
    except (RuntimeError, ValueError) as _ws_e:
        log_swallowed(__name__, _ws_e, context='_json_scan_dirs:workspace')
        ws = ""
    if ws:
        _add(os.path.join(ws, RUNTIME_DIR_NAME, "report_34", "_intermediate"))
        _add(os.path.join(ws, RUNTIME_DIR_NAME, "report_34"))
        _add(os.path.join(ws, RUNTIME_DIR_NAME))
    return [d for d in dirs if os.path.isdir(d)]
def _cv_pool(temp_base: str) -> list[str]:
    cands: list[str] = []
    for directory in _json_scan_dirs(temp_base):
        for pattern in ("cv_final_report_*.json", "cv_findex_*.json"):
            cands.extend(glob.glob(os.path.join(directory, pattern)))
    return list(dict.fromkeys(cands))
def _cv_index_candidates(pool: list[str], freshness_cutoff: str) -> list[str]:
    cands = [path for path in pool
             if not freshness_cutoff or cv_artifact_fresh(path, freshness_cutoff)]
    cands.sort(key=artifact_ts, reverse=True)
    return cands
def _cv_index_candidate(path: str):
    try:
        with open(path, encoding="utf-8-sig") as handle:
            data = json.load(handle)
    except (OSError, ValueError, RecursionError):
        logger.warning(
            "[load_cv_findings_index] 候选产物解析失败，降级更旧候选: %s",
            path, exc_info=True)
        return False, None
    if not isinstance(data, dict):
        logger.warning(
            "[load_cv_findings_index] 候选产物顶层非 dict（%s），"
            "降级更旧候选: %s", type(data).__name__, path)
        return False, None
    findings = data.get("findings_index")
    if not isinstance(findings, list):
        logger.warning(
            "[load_cv_findings_index] 候选产物缺失 findings_index 或非 list，"
            "降级更旧候选: %s", path)
        return False, None
    if findings and not has_finding_entries(findings):
        logger.warning(
            "[load_cv_findings_index] 候选产物 findings_index 无 dict 条目"
            "（撕裂态），降级更旧候选: %s", path)
        return False, None
    return True, {"findings_index": findings, "source_path": path,
                  "source_ts": artifact_ts(path),
                  "data_ts": _channel_data_ts(data, path)}
def _load_cv_findings_meta(pool: list[str], freshness_cutoff: str) -> dict:
    best = None
    best_key = ("", "")
    for path in _cv_index_candidates(pool, freshness_cutoff):
        hit, payload = _cv_index_candidate(path)
        if not hit:
            continue
        key = (payload["data_ts"] or payload["source_ts"],
               payload["source_ts"])
        if best is None or key > best_key:
            best, best_key = payload, key
    if best is not None:
        return best
    return {"findings_index": [], "source_path": "", "source_ts": "",
            "data_ts": ""}
def load_cv_findings_index(temp_base: str,
                           freshness_cutoff: str = _DEFAULT_TIMESTAMP,
                           return_meta: bool = False):
    meta = _load_cv_findings_meta(_cv_pool(temp_base), freshness_cutoff)
    return meta if return_meta else meta["findings_index"]
def _cv_findings_usable(cv_data) -> bool:
    if not isinstance(cv_data, dict):
        return False
    findings = cv_data.get('findings_index')
    if not isinstance(findings, list):
        return False
    return not findings or has_finding_entries(findings)
def _read_aggregate_cv(path: str):
    try:
        with open(path, encoding='utf-8-sig') as _rf:
            _diag = json.load(_rf)
        return (_diag.get(CAT_CROSS_VALIDATION, {})
                if isinstance(_diag, dict) else {})
    except (OSError, ValueError, AttributeError, RecursionError) as _agg_err:
        logger.warning("[cv-channel] 聚合报告读取失败（视为聚合不可用，回退 CV 最终报告）: %s",
                       _agg_err)
        return None
def _filter_by_round_freshness(paths, round_cutoff: str) -> tuple[list, int]:
    if not round_cutoff:
        return list(paths), 0
    _fresh = [p for p in paths if cv_artifact_fresh(p, round_cutoff)]
    return _fresh, len(paths) - len(_fresh)
def _stale_round_count(paths, round_cutoff: str) -> int:
    if not round_cutoff:
        return 0
    return len({artifact_ts(p) for p in paths
                if not cv_artifact_fresh(p, round_cutoff)})
def _fresh_report_candidates(temp_base: str, round_cutoff: str, stats: dict) -> list:
    _dirs = _json_scan_dirs(temp_base)
    if not _dirs:
        return []
    _reports = list(dict.fromkeys(
        path
        for directory in _dirs
        for path in glob.glob(os.path.join(directory, 'report_*.json'))
    ))
    _valid = [p for p in _reports if artifact_ts(p)]
    _fresh, _stale = _filter_by_round_freshness(_valid, round_cutoff)
    stats['aggregate_stale'] = _stale + (len(_reports) - len(_valid))
    return _fresh
def _load_aggregate_channel(temp_base: str, round_cutoff: str, stats: dict,
                            cv_data_ts: str) -> tuple:
    _agg_hold = None
    _fresh_reports = _fresh_report_candidates(temp_base, round_cutoff, stats)
    if not _fresh_reports:
        return None, "", _agg_hold
    _fresh_reports.sort(key=artifact_ts, reverse=True)
    _agg_best = None
    for _path in _fresh_reports:
        _report_cv = _read_aggregate_cv(_path)
        if not _cv_findings_usable(_report_cv):
            logger.info("[cv-channel] 聚合报告无可用 findings_index（空壳/撕裂），降级更旧候选: %s",
                        _path)
            continue
        _agg_t = _channel_data_ts(_report_cv, _path)
        if _agg_best is None or _agg_t > _agg_best[1]:
            _agg_best = (_report_cv, _agg_t)
    if _agg_best is None:
        return None, "", _agg_hold
    if cv_data_ts and cv_data_ts > _agg_best[1]:
        _agg_hold = _agg_best
        logger.info("[cv-channel] 聚合报告（数据时刻 ts=%s）旧于 CV 最终产物池（最新 ts=%s），让位并保底待二次仲裁",
                    _agg_best[1], cv_data_ts)
        return None, "", _agg_hold
    stats['data_source'] = 'aggregate_report'
    return _agg_best[0], _agg_best[1], _agg_hold
def _cv_meta_fields(cv_meta) -> tuple[list, str, str]:
    if isinstance(cv_meta, dict):
        _idx = cv_meta.get('findings_index', [])
        _ts = cv_meta.get('source_ts', '')
        _data_ts = cv_meta.get('data_ts', '')
        return (_idx,
                _ts if isinstance(_ts, str) else '',
                _data_ts if isinstance(_data_ts, str) else '')
    return [], '', ''
def _load_cv_final_channel(stats: dict, agg_hold, cv_meta) -> tuple:
    snapshot_ts = ""
    _findings_index, _cv_hit_ts, _cv_data_ts = _cv_meta_fields(cv_meta)
    _cv_hit = bool(
        _findings_index or _cv_hit_ts
        or (isinstance(cv_meta, dict) and cv_meta.get('source_path')))
    _cv_ts = _cv_data_ts or _cv_hit_ts
    if agg_hold is not None and (not _cv_hit or not _cv_ts
                                 or _cv_ts <= agg_hold[1]):
        stats['data_source'] = 'aggregate_report'
        logger.info("[cv-channel] CV 最终产物实际命中（ts=%s）不晚于聚合报告（ts=%s）、时间戳未知或不可用，回落聚合通道",
                    _cv_ts or '(无可用候选)', agg_hold[1])
        return agg_hold[0], agg_hold[1]
    if _cv_ts:
        snapshot_ts = _cv_ts
    if _cv_hit:
        stats['data_source'] = 'cv_final_report'
        if agg_hold is not None:
            stats['aggregate_outdated'] = 1
            logger.info("[cv-channel] 聚合报告数据时刻（ts=%s）旧于 CV 最终报告（ts=%s），让位采用 CV 通道",
                        agg_hold[1], _cv_ts)
        else:
            logger.info("[cv-channel] 聚合报告不可用（缺失/陈旧/CV分类为空），采用 CV 最终报告（跨通道最新产物）")
        return {'findings_index': _findings_index}, snapshot_ts
    return None, snapshot_ts
def load_cv_findings_channel(temp_base: str, round_cutoff: str = _DEFAULT_TIMESTAMP) -> dict:
    cv_pool = _cv_pool(temp_base)
    _cv_meta = _load_cv_findings_meta(cv_pool, round_cutoff)
    _cv_data_ts = _cv_meta_fields(_cv_meta)[2]
    stats = {'data_source': '', 'aggregate_stale': 0,
             'cv_final_stale': _stale_round_count(cv_pool, round_cutoff),
             'aggregate_outdated': 0}
    _cv, _snapshot_ts, _agg_hold = _load_aggregate_channel(
        temp_base, round_cutoff, stats, _cv_data_ts)
    if not _cv_findings_usable(_cv):
        _cv, _snapshot_ts = _load_cv_final_channel(stats, _agg_hold, _cv_meta)
    _index = _cv.get('findings_index') if isinstance(_cv, dict) else None
    return {'findings_index': _index if isinstance(_index, list) else [],
            'data_source': stats['data_source'],
            'snapshot_ts': _snapshot_ts or '',
            'aggregate_stale': stats['aggregate_stale'],
            'cv_final_stale': stats['cv_final_stale'],
            'aggregate_outdated': stats['aggregate_outdated']}
def _finding_abs_path(finding: dict, skill_abs: str) -> str:
    _file = str(finding.get("file") or finding.get("file_path") or "")
    if os.path.isabs(_file):
        return _file
    return os.path.normpath(os.path.join(skill_abs, _file))
def _anchor_finding(finding: Any, skill_abs: str) -> Any:
    if (not isinstance(finding, dict)
            or not (finding.get("file") or finding.get("file_path"))):
        return finding
    return dict(finding, file_path_abs=_finding_abs_path(finding, skill_abs))
def _apply_skill_dir_anchor(data: dict, skill_dir: str) -> None:
    _abs_sd = normalize_skill_dir(skill_dir)
    data["_source_hash"] = compute_skill_source_hash(_abs_sd)
    _fl = data.get("findings_list")
    if isinstance(_fl, list):
        data["findings_list"] = [_anchor_finding(f, _abs_sd) for f in _fl]
_SUB_RESULTS_ALIAS = "sub_results"
_DETECTOR_RESULTS_KEY = "detector_results"
_A1_SLIM_PROFILE_FIELDS = (
    "filepath", "verdict", "authoritative_layer", "scanned_at",
    "scanner_version", "elapsed_ms",
)
def _slim_a1_profile(profile: Any) -> Any:
    if not isinstance(profile, dict):
        return profile
    slimmed: dict = {}
    for key, value in profile.items():
        if key in _A1_SLIM_PROFILE_FIELDS:
            slimmed[key] = value
        elif isinstance(value, (list, tuple)):
            slimmed[f"{key}_count"] = len(value)
        elif isinstance(value, dict):
            slimmed[f"{key}_keys"] = len(value)
    return slimmed
def _slim_payload_profiles(payload: Any) -> int:
    if not isinstance(payload, dict):
        return 0
    profiles = payload.get("profiles")
    if not isinstance(profiles, list) or not profiles:
        return 0
    payload["profiles"] = [_slim_a1_profile(profile) for profile in profiles]
    return len(profiles)
def _dedupe_payload_aliases(payload: Any) -> int:
    if not isinstance(payload, dict):
        return 0
    if _SUB_RESULTS_ALIAS not in payload or _DETECTOR_RESULTS_KEY not in payload:
        return 0
    _sub = payload.get(_SUB_RESULTS_ALIAS)
    _det = payload.get(_DETECTOR_RESULTS_KEY)
    if _sub is not _det and not (isinstance(_sub, dict) and _sub == _det):
        return 0
    payload.pop(_SUB_RESULTS_ALIAS, None)
    return 1
def _slim_report_payload(data: dict, mid: str) -> dict:
    _slim_profiles = mid in ("A", "A1")
    seen: set = set()
    slimmed = 0
    deduped = 0
    stack: list = [data]
    while stack:
        node = stack.pop()
        if not isinstance(node, (dict, list)):
            continue
        node_id = id(node)
        if node_id in seen:
            continue
        seen.add(node_id)
        if isinstance(node, list):
            stack.extend(value for value in node
                         if isinstance(value, (dict, list)))
            continue
        if _slim_profiles and "profiles" in node:
            slimmed += _slim_payload_profiles(node)
        deduped += _dedupe_payload_aliases(node)
        stack.extend(value for value in node.values()
                     if isinstance(value, (dict, list)))
        continue
    if slimmed:
        logger.info("[Runner] %s 报告瘦身: %d 个画像裁剪调试字段"
                    "（imports/all_symbols/exported_symbols 仅留计数）",
                    mid, slimmed)
    if deduped:
        logger.info("[Runner] %s 报告去重: %d 处 sub_results/detector_results 别名",
                    mid, deduped)
    return data
def _build_intermediate_payload(result: Any, mid: str, timestamp: str) -> dict | None:
    try:
        data = result.to_dict() if hasattr(result, "to_dict") else dict(result)
    except Exception:
        logger.exception("[Runner] 中间结果构造失败 %s: %r", mid, result)
        return None
    if not isinstance(data, dict):
        logger.error(
            "[Runner] 中间结果构造失败 %s: %r (to_dict() 返回非 dict: %s)",
            mid, result, type(data).__name__)
        return None
    try:
        data = copy.deepcopy(data)
        _slim_report_payload(data, mid)
        data["_report_timestamp"] = timestamp
        data["_schema_version"] = _METHOD_SCHEMA_VERSION
        data["_provenance"] = _PIPELINE_PROVENANCE
        json.dumps(data, ensure_ascii=False, default=str)
    except Exception:
        logger.exception("[Runner] 写入中间结果失败 %s", mid)
        return None
    return data
def save_intermediate(intermediate_dir: str, mid: str, result: Any,
                      skill_dir: str = "") -> str:
    intermediate_dir = canonical_json_artifact_dir(
        skill_dir or None, intermediate_dir)
    timestamp = timestamp_ms()
    data = _build_intermediate_payload(result, mid, timestamp)
    if data is None:
        return ""
    if skill_dir:
        try:
            _apply_skill_dir_anchor(data, skill_dir)
        except OSError:
            logger.exception("[Runner] 中间结果源码锚点构造失败 %s", mid)
            return ""
    if not _save_consolidated(intermediate_dir, mid, data,
                              _consolidated_round_key(skill_dir), timestamp):
        return ""
    _prune_globbed(intermediate_dir, mid + "_*.json",
                   _SCATTERED_KEEP_VERSIONS, f" {mid} 中间结果")
    return timestamp
def _candidate_json_paths(inter_dir: str, mid: str) -> list:
    all_cand = glob.glob(os.path.join(inter_dir, f"{mid}_*.json"))
    ts_cand = sorted((p for p in all_cand if artifact_ts(p)),
                     key=artifact_ts, reverse=True)
    other_cand = sorted(p for p in all_cand if not artifact_ts(p))
    legacy = os.path.join(inter_dir, f"{mid}.json")
    return ts_cand + other_cand + [legacy]
def _load_intermediate_any(inter_dir: str, mid: str):
    for c in _candidate_json_paths(inter_dir, mid):
        if not os.path.exists(c):
            continue
        try:
            with open(c, encoding="utf-8-sig") as f:
                return json.load(f)
        except (ValueError, OSError, RecursionError) as e:
            logger.debug("中间产物 %s 解析失败，撕裂降级尝试更旧候选: %s", c, e)
            continue
    return None
def _dict_or_none(value) -> dict | None:
    return value if isinstance(value, dict) else None
def _dict_get(value, key):
    holder = _dict_or_none(value)
    return holder.get(key) if holder is not None else None
def _dict_get_dict(value, key) -> dict | None:
    return _dict_or_none(_dict_get(value, key))
def _direct_sub_results(payload: Any) -> dict:
    """合并一层结果别名；同键由规范 detector_results 保持优先。"""
    _legacy = _dict_or_none(_dict_get(payload, _SUB_RESULTS_ALIAS))
    _canonical = _dict_or_none(_dict_get(payload, _DETECTOR_RESULTS_KEY))
    if _canonical:
        if _legacy and _legacy != _canonical:
            return {**_legacy, **_canonical}
        return _canonical
    return _legacy or {}


def locate_sub_results(payload: Any) -> dict:
    for _container in (payload, _dict_get(payload, "payload")):
        _subs = _direct_sub_results(_container)
        if _subs:
            return _subs
    return {}
def _cg_from_payload_chain(data) -> dict | None:
    payload = _dict_get(data, "payload")
    inner = _dict_get(payload, "payload")
    for container in (data, payload, inner):
        cg = _dict_get_dict(container, "callgraph")
        if cg:
            return cg
        cg = _cg_from_group_payload(container)
        if cg:
            return cg
    return None
def _cg_from_rp(rp) -> dict | None:
    return (_dict_get_dict(rp, "callgraph")
            or _dict_get_dict(rp, "call_graph"))
def _cg_from_group_payload(inner) -> dict | None:
    for _subs in _group_sub_containers(inner):
        _entry = _dict_get(_subs, _CALLGRAPH_GROUP_SUB_METHOD)
        _res = _dict_get(_entry, "result")
        _cg = _cg_from_rp(_dict_get(_res, "payload"))
        if _cg:
            return _cg
    return None
def _extract_called_symbols(data):
    cg = _cg_from_payload_chain(data)
    if cg is None:
        return set()
    callers_index = _dict_get_dict(cg, "callers_index")
    if callers_index is None:
        return set()
    return {str(k).split(".")[-1] for k in callers_index}
def _resolve_intermediate_dir(output_dir: str | None) -> str | None:
    if not output_dir or not os.path.isdir(output_dir):
        return None
    return diag_intermediate_dir(output_dir) or None
def load_called_symbols(output_dir: str | None) -> set:
    inter = _resolve_intermediate_dir(output_dir)
    if inter is None:
        return set()
    loaded_mids: set[str] = set()
    for _cand_mid in _CALLGRAPH_METHOD_CANDIDATES:
        data = load_intermediate(inter, _cand_mid)
        if data:
            if data.get("status") != "corrupted":
                loaded_mids.add(_cand_mid)
            symbols = _extract_called_symbols(data)
            if symbols:
                return symbols
    _fallback: set = set()
    for _cand_mid in _CALLGRAPH_METHOD_CANDIDATES:
        if _cand_mid in loaded_mids:
            continue
        legacy = _load_intermediate_any(inter, _cand_mid)
        if legacy:
            _fallback = _extract_called_symbols(legacy) or _fallback
            if _fallback:
                return _fallback
    return _fallback
def canonical_cv_path(filepath: str, skill_dir: str | None) -> str:
    try:
        if not filepath:
            return filepath
        p = finding_file_key(filepath)
        if os.path.isabs(p) and skill_dir:
            sd = finding_file_key(os.path.abspath(skill_dir))
            if p.startswith(sd + "/") or p == sd:
                p = os.path.relpath(p, sd)
        return p.replace("\\", "/")
    except (OSError, ValueError, TypeError) as e:
        logger.warning("[Collect] 路径归一化降级(返回原路径) %r: %s", filepath, e)
        return filepath
def _report_round_anchor(skill_dir: str, report) -> str:
    _anchor = round_anchor_equiv_form(peek_round_start_ts(skill_dir))
    if _anchor:
        return _anchor
    return round_anchor_equiv_form(
        report.get("round_start_ts") if isinstance(report, dict) else "")
def persist_cv_reports(skill_dir: str, temp_dir: str, cv_report: dict,
                       result: dict, ts: str) -> None:
    temp_dir = canonical_json_artifact_dir(skill_dir, temp_dir)
    cv_path = os.path.join(temp_dir, f"cv_final_report_{ts}.json")
    cv_full_path = os.path.join(temp_dir, f"cv_full_report_{ts}.json")
    _round_anchor = _report_round_anchor(skill_dir, cv_report)
    _full_cv_report = (dict(cv_report) if isinstance(cv_report, dict)
                       else cv_report)
    if isinstance(_full_cv_report, dict) and _round_anchor:
        _full_cv_report["round_start_ts"] = _round_anchor
    with guarded_open(cv_full_path, "w", encoding="utf-8") as _f:
        json.dump(_full_cv_report, _f, ensure_ascii=False, indent=2, default=str)
    result["full_report_path"] = cv_full_path
    slim_cv_report = _slim_cv_report_for_save(cv_report)
    if _round_anchor:
        slim_cv_report["round_start_ts"] = _round_anchor
    with guarded_open(cv_path, "w", encoding="utf-8") as f:
        json.dump(slim_cv_report, f, ensure_ascii=False, indent=2, default=str)
    result["report_path"] = cv_path
    _findex_path = os.path.join(temp_dir, f"cv_findex_{ts}.json")
    try:
        with guarded_open(_findex_path, "w", encoding="utf-8") as _fi:
            json.dump({"timestamp": ts,
                       "source_report": os.path.basename(cv_path),
                       "findings_index": slim_cv_report.get("findings_index", [])},
                      _fi, ensure_ascii=False, default=str)
        result["findex_path"] = _findex_path
    except OSError as _fi_err:
        logger.warning("[Stage2b] 伴生索引写盘失败（消费方将回退全量报告）: %s", _fi_err)
    _prune_cv_artifact_history(temp_dir)
    try:
        mem_bus_put("cv_full_report", _full_cv_report, skill_dir)
        mem_bus_put("cv_report_slim", slim_cv_report, skill_dir)
    except Exception as _mb_err:  # noqa: BLE001
        logger.debug("[Stage2b] CV报告内存直通跳过(磁盘通道兜底): %s", _mb_err)
def _slim_cv_report_for_save(cv_report: dict) -> dict:
    if not isinstance(cv_report, dict):
        logger.warning("[Stage2b] CV 报告非 dict 形态（%s），按空报告落盘",
                       type(cv_report).__name__)
        return {}
    findings_index = cv_report.get("findings_index", [])
    if not isinstance(findings_index, list):
        return dict(cv_report)
    slim_index = []
    stripped_count = 0
    for entry in findings_index:
        slim_entry, stripped = _slim_index_entry(entry)
        slim_index.append(slim_entry)
        stripped_count += int(stripped)
    slim_result = dict(cv_report)
    slim_result["findings_index"] = slim_index
    slim_result.pop("confirmed_findings", None)
    slim_result["_slim_info"] = {
        "original_entries": len(findings_index),
        "stripped_entries": stripped_count,
        "slim_note": "非confirmed/investigated条目的findings列表已剥离，仅保留sample_finding和findings_count"
    }
    logger.info("[Stage2b] CV报告瘦身: %d条目中%d条剥离findings列表",
                len(findings_index), stripped_count)
    return slim_result
def _slim_index_entry(entry) -> tuple:
    if not isinstance(entry, dict):
        return entry, False
    if entry.get("conclusion", "") in ("confirmed", "investigated"):
        return entry, False
    if "findings" not in entry:
        return entry, False
    slim_entry = {k: v for k, v in entry.items() if k != "findings"}
    slim_entry["_findings_stripped"] = True
    return slim_entry, True
def _prune_cv_artifact_history(
        temp_dir: str, keep: int = _CV_ARTIFACT_KEEP_VERSIONS) -> int:
    removed = 0
    for prefix in ("cv_final_report_", "cv_full_report_", "cv_findex_"):
        removed += _prune_globbed(temp_dir, f"{prefix}*.json", keep,
                                  f"CV {prefix.removesuffix('_')}")
    return removed
def atomic_save_json(path: str, data: dict) -> None:
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    tmp = f"{path}.{os.getpid()}.{threading.get_ident()}.tmp"
    try:
        with guarded_open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2, default=str)
            f.flush()
        replace_with_retry(tmp, path)
    except BaseException:
        two_level_unlink(tmp)
        raise
def _valid_file_count(value) -> int | None:
    return value if isinstance(value, int) and not isinstance(value, bool) and value > 0 else None
def _file_count_of(carrier) -> int | None:
    _carrier = _dict_or_none(carrier)
    return _valid_file_count(_carrier.get('file_count')) if _carrier else None
def _group_sub_file_count(inner: dict) -> int | None:
    for subs in _group_sub_containers(inner):
        entry = _dict_or_none(subs.get('A1'))
        result = _dict_or_none(entry.get('result')) if entry else None
        _fc = _file_count_of(result.get('payload') if result else None)
        if _fc is not None:
            return _fc
    return None
def _extract_file_count(payload: dict) -> int | None:
    inner = _dict_or_none(payload.get('payload'))
    direct = _file_count_of(inner) if inner is not None else None
    if direct is not None:
        return direct
    nested = _group_sub_file_count(inner) if inner is not None else None
    if nested is not None:
        return nested
    return _group_sub_file_count(payload) or _file_count_of(payload)
def collect_scale_baseline(skill_dir: str) -> dict:
    baseline: dict = {}
    try:
        intermediate_dir = json_artifact_dir(normalize_skill_dir(skill_dir))
        for _candidate in _a1_candidates_by_recency(
                intermediate_dir, get_round_start_ts(skill_dir)):
            _pl = _load_trusted_a1_payload(_candidate)
            if _pl is None:
                continue
            _fc = _extract_file_count(_pl)
            if _fc is not None:
                baseline['file_count'] = _fc
                break
    except (OSError, ValueError, RuntimeError, TypeError) as e:
        logger.debug('[G3] 基线提取失败，门禁按无基线口径执行: %s', e)
    return baseline
def _a1_candidates_by_recency(intermediate_dir: str, round_cutoff: str) -> list:
    _candidates: list[tuple[str, int, object]] = []
    for _mid in ('A', 'A1'):
        for _mid_file in _scattered_candidates(
                intermediate_dir, _mid, round_cutoff):
            timestamp_ms = artifact_ts(_mid_file)
            if timestamp_ms:
                _candidates.append((timestamp_ms, 0, _mid_file))
    for _cpath, _suffix in _iter_consolidated_paths(
            intermediate_dir, round_cutoff):
        _doc = _read_consolidated(_cpath)
        if _doc is None:
            continue
        for _mid in ('A', 'A1'):
            _data = _doc['methods'].get(_mid)
            if _data is None:
                continue
            _report_ts = (normalize_round_start_ts(
                str(_data.get('_report_timestamp') or ''))
                if isinstance(_data, dict) else '')
            _candidates.append((_report_ts or _suffix, 1, _data))
    return [item[2] for item in sorted(
        _candidates, key=lambda item: (item[0], item[1]), reverse=True)]
def _load_trusted_a1_payload(source) -> dict | None:
    if isinstance(source, dict):
        _data, _kind, _err = source, 'ok', ''
    else:
        _data, _kind, _err = read_json_artifact(source)
    if _kind != 'ok' or not isinstance(_data, dict):
        logger.debug('[G3] A1 基线产物读取失败/形态异常(%s: %s)，基线不采信',
                     _kind, _err)
        return None
    if _data.get('status') == 'corrupted':
        logger.debug('[G3] A1 基线产物为损坏占位，基线不采信')
        return None
    if _data.get('_provenance') != _PIPELINE_PROVENANCE:
        logger.debug('[G3] A1 基线产物缺 _provenance 或形态异常，基线不采信')
        return None
    _pl = _data.get('payload')
    if not isinstance(_pl, dict):
        logger.debug('[G3] A1 基线产物 payload 非 dict 形态，基线不采信')
        return None
    return _pl
def _p0_item_identity(item: dict) -> str:
    try:
        return json.dumps(item, sort_keys=True, ensure_ascii=False,
                          separators=(',', ':'), default=repr)
    except (TypeError, ValueError, RecursionError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_p0_item_identity:TypeError')
        return f'object:{id(item)}'
def _count_p0_in_payload(payload: dict, _dynamic_fp_ids: set,
                         excluded_identities: set[str] | None = None) -> tuple[int, int]:
    p0_count = 0
    p0_fp_exempted = 0
    seen: set[str] = set()
    for item in _iter_p0_items(_collect_p0_sources(payload)):
        identity = _p0_item_identity(item)
        if identity in seen or (excluded_identities
                                and identity in excluded_identities):
            continue
        seen.add(identity)
        if _is_fp_exempted(item, _dynamic_fp_ids):
            p0_fp_exempted += 1
            continue
        p0_count += 1
    return p0_count, p0_fp_exempted
def _payload_layers(payload: dict) -> list[dict]:
    _layers: list[dict] = [payload]
    _inner = _dict_or_none(payload.get('payload'))
    if _inner is not None:
        _layers.append(_inner)
    return _layers
def _group_sub_containers(payload: Any):
    if not isinstance(payload, dict):
        return
    _subs = _direct_sub_results(payload)
    if _subs:
        yield _subs
def _sub_method_ids(payload: dict) -> set[str]:
    _ids: set[str] = set()
    for _subs in _group_sub_containers(payload):
        _ids.update(k for k in _subs if isinstance(k, str))
    return _ids
def _collect_p0_sources(payload: dict) -> list[dict]:
    _p0_sources: list[dict] = []
    for _layer in _payload_layers(payload):
        for _source in (_layer, *_group_sub_payloads(_layer)):
            _p0_sources.append(_source)
            _raw_result = _dict_or_none(_source.get('raw_result'))
            if _raw_result is not None:
                _p0_sources.append(_raw_result)
    return _p0_sources
def _group_sub_payloads(payload: dict) -> list[dict]:
    _out: list[dict] = []
    for _subs in _group_sub_containers(payload):
        for _entry in _subs.values():
            _res = _dict_or_none(_dict_get(_entry, 'result'))
            if _res is None:
                continue
            _out.append(_res)
            _inner = _dict_or_none(_res.get('payload'))
            if _inner is not None:
                _out.append(_inner)
    return _out
def _is_blocking_p0(item) -> bool:
    return (isinstance(item, dict)
            and _normalize_severity(item.get('severity')) == 'P0')
def _blocking_items(value: Any) -> list:
    if not isinstance(value, (list, tuple)):
        return []
    return [item for item in value if _is_blocking_p0(item)]
def _iter_p0_items(sources: list[dict]):
    for _src in sources:
        for key, value in _src.items():
            if is_finding_carrier_key(key):
                yield from _blocking_items(value)
def _fp_exempt(rid, dynamic_fp_ids, file_path: str = "") -> bool:
    _key = rid.strip() if isinstance(rid, str) else ""
    if not _key:
        return False
    return bool(is_static_fp_rule(_key, file_path=file_path)
                or _key in dynamic_fp_ids)
def _is_fp_exempted(item: dict, _dynamic_fp_ids: set) -> bool:
    return _fp_exempt(item.get('rule_id') or item.get('id') or '',
                      _dynamic_fp_ids,
                      str(item.get('file') or item.get('file_path') or ''))
def _iter_group_payloads(all_mid_results: dict):
    for _g_mid, _g_data in all_mid_results.items():
        if not isinstance(_g_mid, str) or len(_g_mid) != 1:
            continue
        _g_payload = (_dict_or_none(_g_data.get('payload'))
                      if isinstance(_g_data, dict) else None)
        if _g_payload is not None:
            yield _g_payload
def _covered_sub_methods(all_mid_results: dict) -> set[str]:
    _covered: set[str] = set()
    for _g_payload in _iter_group_payloads(all_mid_results):
        for _layer in _payload_layers(_g_payload):
            _covered.update(_sub_method_ids(_layer))
    return _covered
def _covered_p0_item_identities(all_mid_results: dict) -> set[str]:
    return {
        _p0_item_identity(item)
        for _g_payload in _iter_group_payloads(all_mid_results)
        for item in _iter_p0_items(_collect_p0_sources(_g_payload))
    }
def _iter_round_payloads(all_mid_results: dict, covered_subs: set[str]):
    for mid_name, diag_data in all_mid_results.items():
        if mid_name.startswith('_') or mid_name in covered_subs:
            continue
        data = _dict_or_none(diag_data)
        payload = _dict_or_none(data.get('payload')) if data else None
        if payload is not None:
            yield payload
def collect_round_p0_findings(skill_dir: str) -> tuple[int, int, str]:
    p0_count = 0
    p0_fp_exempted = 0
    try:
        intermediate_dir = json_artifact_dir(normalize_skill_dir(skill_dir))
        _round_cutoff = get_round_start_ts(skill_dir)
        _all_mid_results = load_all_intermediates(
            intermediate_dir, freshness_cutoff=_round_cutoff)
        if _all_mid_results.get('_error') or _all_mid_results.get('_partial'):
            logger.warning('[G3] 中间产物通道整体或部分读取失败，P0 取证降级（不得据此放行）')
            return 0, 0, 'intermediate channel unavailable or partial'
        _dynamic_fp_ids = get_fp_rule_ids(skill_dir)
        _covered_subs = _covered_sub_methods(_all_mid_results)
        for payload in _iter_round_payloads(_all_mid_results, _covered_subs):
            _c, _e = _count_p0_in_payload(payload, _dynamic_fp_ids)
            p0_count += _c
            p0_fp_exempted += _e
        _standalone_payloads = []
        for _mid in _covered_subs:
            _data = _dict_or_none(_all_mid_results.get(_mid))
            _payload = _dict_or_none(_data.get('payload')) if _data else None
            if _payload is not None:
                _standalone_payloads.append(_payload)
        if _standalone_payloads:
            _covered_identities = _covered_p0_item_identities(_all_mid_results)
            for _payload in _standalone_payloads:
                _c, _e = _count_p0_in_payload(
                    _payload, _dynamic_fp_ids,
                    excluded_identities=_covered_identities)
                p0_count += _c
                p0_fp_exempted += _e
    except Exception as e:
        logger.warning('[G3] P0 检查失败: %s', e, exc_info=True)
        return p0_count, p0_fp_exempted, str(e)[:300]
    return p0_count, p0_fp_exempted, ''
logger.info("xv_intermediate_store 已加载: %d 项导出", len(__all__))
_UNLOCATABLE_MESSAGE_MAX_CHARS = 120
_P_SEV_PREFIX_RE = re.compile(r"^P([0-4])(?!\d)", re.IGNORECASE)
_P0_SEVERITY_ALIASES = frozenset({"BLOCKER", "SECURITY"})
def _normalize_severity(raw) -> str:
    if not isinstance(raw, str):
        return "P3"
    _s = raw.strip().upper()
    if not _s:
        return "P3"
    if _s in _P0_SEVERITY_ALIASES:
        return "P0"
    if _s in SEVERITY_RANK or _s in DIAGNOSE_TO_P:
        return diag_severity_to_p(_s)
    _m = _P_SEV_PREFIX_RE.match(_s)
    if _m:
        return severity_literal_from_rank(int(_m.group(1)))
    return "P3"
def _severity_sort_key(detail) -> int:
    if isinstance(detail, dict):
        return normalize_severity_rank(detail.get('severity'))
    return 9
def _one_line_value(v) -> int | None:
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        if v < 0:
            return None
        if isinstance(v, float):
            return int(v) if v.is_integer() else None
        return v
    if isinstance(v, str):
        s = v.strip()
        if not s.isdecimal():
            return None
        try:
            return int(s)
        except ValueError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_one_line_value:ValueError')
            return None
    return None
def _first_line_of(candidate) -> int | None:
    if isinstance(candidate, (list, tuple)):
        for _x in candidate:
            _r = _one_line_value(_x)
            if _r:
                return _r
        return None
    return _one_line_value(candidate)
def _normalize_line(line_v, lines_v=None) -> int:
    for _candidate in (line_v, lines_v):
        _r = _first_line_of(_candidate)
        if _r:
            return _r
    return 0
def _append_unique(seq: list, value):
    if value not in seq:
        seq.append(value)
def _ts17_to_epoch(ts17: str) -> float:
    if not isinstance(ts17, str):
        return 0.0
    _ms = compact_ts_to_ms(ts17)
    if _ms is None:
        if ts17:
            log_swallowed(
                __name__, ValueError(ts17),
                context='_ts17_to_epoch:ValueError')
        return 0.0
    return _ms / 1000.0
def _cached_mtime(path: str, cache: dict) -> float:
    _mt = cache.get(path)
    if _mt is None:
        try:
            _mt = os.path.getmtime(path)
        except OSError as _e:
            log_swallowed(__name__, _e, context='_cached_mtime:OSError')
            _mt = 0.0
        cache[path] = _mt
    return _mt
class _SnapshotDrift:
    def __init__(self, snapshot_ts: str):
        self._epoch = _ts17_to_epoch(snapshot_ts)
        self._mtime_cache: dict[str, float] = {}
    def drifted(self, path: str) -> bool:
        if self._epoch <= 0:
            return False
        return _cached_mtime(path, self._mtime_cache) > self._epoch
def _src_method_of(finding: dict) -> str:
    _m = finding.get('_source_method')
    return _m if (isinstance(_m, str) and _m) else 'unknown'
def _ensure_bucket(findings_out: dict, fpath: str) -> dict:
    bucket = findings_out.setdefault(fpath, {})
    if isinstance(bucket, dict):
        return bucket
    logger.warning("[G1] %s 的文件级台账形态撕裂(%s)，按空台账重建",
                   fpath, type(bucket).__name__)
    findings_out[fpath] = {}
    return findings_out[fpath]
def _merge_copy_into(prev: dict, src: str, sev: str, msg: str) -> bool:
    _srcs = prev.get('sources')
    if not isinstance(_srcs, list):
        _srcs = prev['sources'] = []
    if src not in _srcs:
        _srcs.append(src)
    prev['source_count'] = len(_srcs)
    if normalize_severity_rank(sev) < normalize_severity_rank(prev.get('severity')):
        prev['severity'] = sev
        prev['message'] = msg
        return True
    return False
def _fold_unlocatable(bucket: dict, ukey: tuple, sev: str, src: str,
                      msg: str) -> bool:
    prev = bucket.get(ukey)
    if prev is None:
        return False
    _merge_copy_into(prev, src, sev, msg)
    return True
def _append_unlocatable(bucket: dict, finding: dict, rid: str, fpath: str,
                        msg: str) -> None:
    _ukey = (rid, fpath)
    _usev = _normalize_severity(finding.get('severity'))
    _usrc = _src_method_of(finding)
    if _fold_unlocatable(bucket, _ukey, _usev, _usrc, msg):
        return
    bucket[_ukey] = {'rule_id': rid, 'file': fpath, 'severity': _usev,
                     'line': _normalize_line(finding.get('line'), finding.get('lines')),
                     'message': msg, 'source_count': 1, 'sources': [_usrc]}
    if fpath:
        logger.warning("[G1] confirmed 项不可定位（file=%s, rule=%s），无法进入文件级修复清单: %s",
                       fpath, rid, msg[:_UNLOCATABLE_MESSAGE_MAX_CHARS])
    else:
        logger.warning("[G1] confirmed 项无 file 字段（文件级信号，rule=%s），无法进入文件级修复清单: %s",
                       rid, msg[:_UNLOCATABLE_MESSAGE_MAX_CHARS])
def _fold_located_detail(bucket: dict, key: tuple, finding: dict, rid: str,
                         sev: str, msg: str, line: int, drift: bool) -> None:
    _prev = bucket.get(key)
    if isinstance(_prev, dict):
        _prev_rule = _prev.get('rule_id')
        if _prev_rule and rid != _prev_rule:
            _append_unique(
                _prev.setdefault('co_reported_rules', [_prev_rule]), rid)
        if _merge_copy_into(_prev, _src_method_of(finding), sev, msg):
            _prev['raw'] = finding
            _prev['rule_id'] = rid
        if drift:
            _prev['drift_warning'] = True
        return
    _src_m = _src_method_of(finding)
    _detail = {'rule_id': rid, 'line': line, 'severity': sev, 'message': msg,
               'raw': finding, 'source_count': 1, 'sources': [_src_m]}
    if drift:
        _detail['drift_warning'] = True
    bucket[key] = _detail
def _collect_empty_file_signal(finding: dict, rid: str, msg: str,
                               dynamic_fp_ids, unlocatable_out,
                               unloc_bucket: dict) -> None:
    if _fp_exempt(rid, dynamic_fp_ids, str(finding.get('file') or '')):
        return
    if unlocatable_out is not None:
        _append_unlocatable(unloc_bucket, finding, rid, '', msg)
def _sanitize_finding_ref(f: dict) -> tuple[str, str, str] | None:
    _rid = f.get('rule_id') or f.get('id') or ''
    _fpath = f.get('file') or f.get('file_path', '')
    if not _rid or _rid in ('contradiction', 'GENERIC'):
        return None
    if not isinstance(_rid, str) or not isinstance(_fpath, str):
        logger.warning("[G1] confirmed 项字段撕裂（rule_id=%r, file=%r），跳过该明细",
                       _rid, _fpath)
        return None
    _msg = f.get('message', '')
    if not isinstance(_msg, str):
        _msg = ''
    return _rid, _fpath, _msg
def _entry_confirmed_findings(item):
    if not isinstance(item, dict):
        return None
    if item.get('conclusion') != 'confirmed':
        return None
    _fis = item.get('findings', [])
    if not isinstance(_fis, list):
        logger.warning("[G1] entry findings 非 list 形态（撕裂态），跳过该 entry: %s",
                       type(_fis).__name__)
        return None
    _entry_rf = item.get('rule_family')
    if not isinstance(_entry_rf, str):
        _entry_rf = ''
    return _entry_rf, _fis
def _iter_confirmed_findings(fi_items):
    for _item in fi_items:
        _entry = _entry_confirmed_findings(_item)
        if _entry is None:
            continue
        _entry_rf, _fis = _entry
        for _f in _fis:
            if isinstance(_f, dict):
                yield _entry_rf, _f
def _iter_confirmed_details(fi_items, skill_dir, dynamic_fp_ids,
                            unlocatable_out, unloc_bucket):
    for _entry_rf, _f in _iter_confirmed_findings(fi_items):
        _sanitized = _sanitize_finding_ref(_f)
        if _sanitized is None:
            continue
        _rid, _fpath, _msg = _sanitized
        if not _fpath:
            _collect_empty_file_signal(_f, _rid, _msg, dynamic_fp_ids,
                                       unlocatable_out, unloc_bucket)
            continue
        if _fp_exempt(_rid, dynamic_fp_ids, _fpath):
            continue
        if not os.path.isabs(_fpath):
            _fpath = os.path.join(skill_dir, _fpath)
        yield _entry_rf, _f, _rid, os.path.realpath(_fpath), _msg
def _finalize_collect_outputs(findings_out: dict, unlocatable_out,
                              unloc_bucket: dict) -> None:
    for _fp_key, _bucket in list(findings_out.items()):
        if isinstance(_bucket, dict):
            findings_out[_fp_key] = list(_bucket.values())
        elif not isinstance(_bucket, list):
            findings_out[_fp_key] = []
    if unlocatable_out is not None and unloc_bucket:
        unlocatable_out.extend(unloc_bucket.values())
        unlocatable_out.sort(key=_severity_sort_key)
    for _lst in findings_out.values():
        _lst.sort(key=_severity_sort_key)
def _ingest_located_detail(fpath: str, finding: dict, rid: str, msg: str,
                           entry_rf: str, files_out: list,
                           findings_out: dict, drift: _SnapshotDrift) -> None:
    files_out.append(fpath)
    _drift = drift.drifted(fpath)
    _sev = _normalize_severity(finding.get('severity'))
    _line = _normalize_line(finding.get('line'), finding.get('lines'))
    _rf = finding.get('rule_family')
    if not isinstance(_rf, str):
        _rf = ''
    _bucket = _ensure_bucket(findings_out, fpath)
    _key = (entry_rf or _rf or rid, _line)
    _fold_located_detail(_bucket, _key, finding, rid, _sev, msg,
                         _line, _drift)
def _collect_confirmed_cv_files(cv_data, skill_dir, files_out, findings_out,
                                unlocatable_out=None,
                                snapshot_ts: str = _DEFAULT_TIMESTAMP):
    if not isinstance(cv_data, dict):
        logger.warning("[G1] cv_data 非 dict 形态（撕裂态），跳过联动明细提取: %s",
                       type(cv_data).__name__)
        return
    _dynamic_fp_ids = get_fp_rule_ids(skill_dir)
    _drift = _SnapshotDrift(snapshot_ts)
    _unloc_bucket: dict[tuple[str, str], dict] = {}
    _fi_items = cv_data.get('findings_index', [])
    if not isinstance(_fi_items, list):
        logger.warning("[G1] findings_index 非 list 形态（撕裂态），跳过联动明细提取: %s",
                       type(_fi_items).__name__)
        return
    try:
        for _entry_rf, _f, _rid, _fpath, _msg in _iter_confirmed_details(
                _fi_items, skill_dir, _dynamic_fp_ids,
                unlocatable_out, _unloc_bucket):
            if not is_path_within_skill(_fpath, skill_dir):
                if unlocatable_out is not None:
                    _append_unlocatable(_unloc_bucket, _f, _rid, _fpath, _msg)
                continue
            if os.path.isfile(_fpath):
                _ingest_located_detail(
                    _fpath, _f, _rid, _msg, _entry_rf,
                    files_out, findings_out, _drift)
            elif unlocatable_out is not None:
                _append_unlocatable(_unloc_bucket, _f, _rid, _fpath, _msg)
    finally:
        _finalize_collect_outputs(findings_out, unlocatable_out, _unloc_bucket)
def _g1_file_scope(cache, diagnosis_files, n_details: int,
                   skill_dir: str) -> tuple[list, str]:
    if diagnosis_files:
        files = list(dict.fromkeys(diagnosis_files))
        logger.info("[G1] 联动模式: 提取 %d 个有confirmed问题的文件（%d 条明细，多源已聚合，误报豁免后）",
                    len(files), n_details)
        return files, "linked"
    root = normalize_skill_dir(skill_dir)
    files = list(dict.fromkeys(
        fp for fp in cache.py_files
        if not is_diagnosis_out_of_scope(fp, root)))
    logger.info("[G1] 盲扫模式: 扫描 %d 个文件（诊断范围口径，范围外文件已排除）", len(files))
    return files, "blind"
def _drifted_files(findings_by_file: dict) -> list:
    return sorted(
        fp for fp, items in findings_by_file.items()
        if any(isinstance(d, dict) and d.get('drift_warning') for d in items))
def _extract_diagnosis_files(skill_dir: str, unlocatable_out=None, stats_out=None):
    _diagnosis_files = []
    _diagnosis_findings = {}
    _stats = {'data_source': 'blind_scan', 'stale_sources_skipped': 0,
              'aggregate_stale': 0, 'cv_final_stale': 0, 'aggregate_outdated': 0}
    _sd = normalize_skill_dir(skill_dir)
    _tb = json_artifact_dir(_sd)
    try:
        _round_cutoff = get_round_start_ts(_sd)
        _chan = load_cv_findings_channel(_tb, _round_cutoff)
        _stats['data_source'] = _chan['data_source'] or 'blind_scan'
        _stats['aggregate_stale'] = _chan['aggregate_stale']
        _stats['cv_final_stale'] = _chan['cv_final_stale']
        _stats['aggregate_outdated'] = _chan['aggregate_outdated']
        _stats['stale_sources_skipped'] = _chan['aggregate_stale'] + _chan['cv_final_stale']
        if _stats['stale_sources_skipped']:
            logger.info("[G1-diag-link] 陈旧数据源已滤除（round_start_ts=%s）: 聚合报告 %d 个 / CV 最终报告 %d 个，防上一轮 confirmed 传导",
                        _round_cutoff or '(无标记)', _chan['aggregate_stale'], _chan['cv_final_stale'])
        if _chan['findings_index']:
            _collect_confirmed_cv_files(
                {'findings_index': _chan['findings_index']}, _sd,
                _diagnosis_files, _diagnosis_findings,
                unlocatable_out, snapshot_ts=_chan['snapshot_ts'])
    except Exception as _e:
        logger.warning('%s: %s', '通用(G1-diag-link)', _e, exc_info=True)
        _diagnosis_files.clear()
        _diagnosis_findings.clear()
        _stats['data_source'] = 'blind_scan'
        _stats['degraded_to_blind'] = 1
    if stats_out is not None:
        stats_out.update(_stats)
    return (_diagnosis_files, _diagnosis_findings)
def collect_cv_confirmed_scope(skill_dir: str, cache: Any = _DEFAULT_CACHE, *,
                               unlocatable_out: list | None = None,
                               stats_out: dict | None = None) -> dict:
    require_warmed(cache, "G1 待AI修复清单生成")
    _diagnosis_files, _diagnosis_findings = _extract_diagnosis_files(
        skill_dir, unlocatable_out=unlocatable_out, stats_out=stats_out)
    _n_details = sum(len(_v) for _v in _diagnosis_findings.values())
    files, _list_mode = _g1_file_scope(
        cache, _diagnosis_files, _n_details, skill_dir)
    return {"files": files,
            "findings": _diagnosis_findings,
            "details": _n_details,
            "list_mode": _list_mode,
            "linked": bool(_diagnosis_files),
            "drifted_files": _drifted_files(_diagnosis_findings)}
def _build_g1_summary(*, linked: bool, degraded: int, n_files: int,
                      data_source: str, n_unloc: int, stale_skipped: int,
                      n_drift: int) -> str:
    _unlocatable_note = (f"，另有 {n_unloc} 条 confirmed 项不可定位（文件级信号，详见日志）"
                         if n_unloc else "")
    if linked:
        _drift_note = (f"；警告: {n_drift} 个文件在 CV 快照后被修改（明细行号可能已漂移，先复核再修复）"
                       if n_drift else "")
        return (f"联动模式({data_source}): {n_files} 个文件含 confirmed 明细（豁免后），"
                f"已生成待 AI 修复清单（不再自动改码）{_unlocatable_note}{_drift_note}")
    if degraded:
        return (f"联动明细收集撕裂崩断（已退化全量盲扫兜底），全量 {n_files} 个文件清单"
                f"供 AI 审查兜底（不再自动改码）{_unlocatable_note}")
    if stale_skipped:
        return (f"无 confirmed 明细（本轮轮次内无新鲜联动数据源，已滤除 {stale_skipped} 个陈旧"
                f"数据文件防旧 confirmed 传导），全量 {n_files} 个文件清单供 AI 审查兜底"
                f"（不再自动改码）{_unlocatable_note}")
    return (f"无 confirmed 明细（联动数据源为空或全被误报豁免），全量 {n_files} 个文件清单"
            f"供 AI 审查兜底（不再自动改码）{_unlocatable_note}")
def build_ai_fix_list(skill_dir: str, cache: Any = _DEFAULT_CACHE) -> dict:
    _g1_start = time.time()
    _unlocatable: list[dict] = []
    _source_stats: dict = {}
    _scope = collect_cv_confirmed_scope(
        skill_dir, cache, unlocatable_out=_unlocatable, stats_out=_source_stats)
    files = _scope["files"]
    _findings_by_file = _scope["findings"]
    _drift_files = _scope["drifted_files"]
    ai_list = [{"file": fp, "ai_action": "AI 审核并执行修复，再验证",
                "findings": _findings_by_file.get(fp, [])} for fp in files]
    perf_trace("g1_ai_fix_list",
                    round((time.time() - _g1_start) * 1000, 1),
                    files_checked=len(files))
    _n_unloc = len(_unlocatable)
    _data_source = _source_stats['data_source']
    _stale_skipped = _source_stats['stale_sources_skipped']
    _degraded = _source_stats.get('degraded_to_blind', 0)
    _n_drift = len(_drift_files)
    return {"status": "pass", "files_checked": len(files),
            "fixed_count": 0, "fix_details": [], "findings_count": 0,
            "ai_fix_list": ai_list,
            "confirmed_findings_count": _scope["details"],
            "unlocatable_confirmed": _n_unloc,
            "unlocatable_details": list(_unlocatable),
            "data_source": _data_source, "list_mode": _scope["list_mode"],
            "drifted_files": _n_drift, "drifted_file_list": _drift_files[:20],
            "stale_sources_skipped": _stale_skipped,
            "aggregate_outdated": _source_stats['aggregate_outdated'],
            "degraded_to_blind": _degraded,
            "summary": _build_g1_summary(
                linked=_scope["linked"], degraded=_degraded,
                n_files=len(files), data_source=_data_source,
                n_unloc=_n_unloc, stale_skipped=_stale_skipped,
                n_drift=_n_drift)}
REGRESSION_HANDOFF_SLOT = "regression_ctx"
_REGRESSION_HANDOFF_FILENAME = "_regression_ctx.json"
def regression_handoff_path(temp_dir: str,
                           skill_dir: str | None = _DEFAULT_SKILL_DIR) -> str:
    return os.path.join(canonical_json_artifact_dir(skill_dir, temp_dir),
                        _REGRESSION_HANDOFF_FILENAME)
def normalize_regression_handoff(raw: Any,
                                  stage_label: str) -> dict | None:
    if not isinstance(raw, dict):
        logger.warning("[%s] 回归CV上下文非 dict 形态，忽略: %s",
                       stage_label, type(raw).__name__)
        return None
    changed = raw.get("changed_files")
    if not isinstance(changed, list):
        return None
    return raw
def _mem_regression_handoff(raw: Any) -> tuple[dict | None, bool]:
    if not isinstance(raw, dict):
        return None, raw is not None
    if not raw:
        return None, False
    if "changed_files" not in raw or not isinstance(raw.get("changed_files"),
                                                    list):
        return None, True
    return normalize_regression_handoff(raw, "Stage2b"), False
def _read_regression_handoff_disk(temp_dir: str) -> dict | None:
    path = regression_handoff_path(temp_dir)
    if not os.path.isfile(path):
        return None
    try:
        raw, kind, err = read_json_artifact(path, propagate_io=True)
    except OSError as _ctx_err:
        logger.warning("[Stage2b] 回归CV上下文加载失败: %s", _ctx_err)
        raise
    if kind != "ok":
        logger.warning("[Stage2b] 回归CV上下文加载失败: %s", err or kind)
        raise ValueError(f"[Stage2b] 回归CV上下文加载失败: {err or kind}")
    handoff = normalize_regression_handoff(raw, "Stage2b")
    if handoff is None:
        logger.warning("[Stage2b] 回归CV上下文载荷校验失败: %s", path)
        raise ValueError(f"[Stage2b] 回归CV上下文载荷校验失败: {path}")
    return handoff
def save_regression_handoff(skill_dir: str, temp_dir: str,
                            payload: dict | None) -> str:
    body = payload or {}
    path = regression_handoff_path(temp_dir, skill_dir)
    if not handoff_persistence_enabled():
        if os.path.isfile(path):
            if safe_delete(path):
                logger.info("[Stage2a] 内存交接已启用，旧磁盘副本已失效清理: %s", path)
            else:
                logger.warning("[Stage2a] 旧磁盘交接副本清理失败；memory-only 读取将禁用磁盘回退: %s", path)
        mem_bus_put(REGRESSION_HANDOFF_SLOT, body, skill_dir)
        logger.info("[Stage2a] 同进程交接走内存总线，跳过磁盘副本（零落盘）")
        return ""
    mem_bus_put(REGRESSION_HANDOFF_SLOT, body, skill_dir)
    with guarded_open(path, "w", encoding="utf-8") as f:
        json.dump(body, f, ensure_ascii=False, indent=2, default=str)
    return path
def take_regression_handoff(skill_dir: str, temp_dir: str) -> dict | None:
    temp_dir = canonical_json_artifact_dir(skill_dir, temp_dir)
    raw = mem_bus_peek(REGRESSION_HANDOFF_SLOT, skill_dir)
    handoff, torn = _mem_regression_handoff(raw)
    if torn:
        logger.warning("[Stage2b] 回归CV上下文内存载荷撕裂(%s)，按持久化策略裁决磁盘回退",
                       type(raw).__name__)
    if handoff is None and (raw is None or torn):
        if handoff_persistence_enabled():
            handoff = _read_regression_handoff_disk(temp_dir)
        elif torn:
            raise ValueError("[Stage2b] 回归CV上下文内存载荷撕裂，且磁盘回退已禁用")
    if handoff is not None:
        logger.info("[Stage2b] 加载回归CV上下文: %d changed files",
                    len(handoff["changed_files"]))
    return handoff
def clear_regression_handoff(temp_dir: str,
                             skill_dir: str | None = _DEFAULT_SKILL_DIR) -> None:
    path = regression_handoff_path(temp_dir, skill_dir)
    existed = os.path.isfile(path)
    if existed and not safe_delete(path):
        raise OSError(f"[Stage2b] 回归CV上下文清理失败，交接仍待消费: {path}")
    if skill_dir is not None:
        mem_bus_take(REGRESSION_HANDOFF_SLOT, skill_dir)
    if existed:
        logger.info("[Stage2b] 回归CV上下文已消费，清理: %s", path)

from __future__ import annotations

import ast
import gzip
import hashlib
import json
import logging
import math
import os
import threading
import time
import weakref
import zlib
from collections import OrderedDict
from collections.abc import Callable

from jwsgj.diag_guard_io import (
    atomic_write_text,
    replace_with_retry,
    safe_delete,
    two_level_rmtree,
    two_level_unlink,
)
from jwsgj.diag_guard_state import (
    ProcessLock,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    read_source_with_fingerprint,
    source_digest,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_paths import (
    get_temp_base,
    iter_sibling_session_roots,
    resolve_session_root_from_artifact_path,
)
from jwsgj.runtime_paths import (
    t5_baseline_path as _domain_t5_baseline_path,
)
from jwsgj.runtime_scope import (
    RUNTIME_DIR_NAME,
    expand_git_bash_path,
    is_diagnosis_out_of_scope,
    is_py_source_file,
    normalize_skill_dir,
    prune_ignore_dirs,
)

logger = logging.getLogger(__name__)
class CacheNotWarmedError(RuntimeError):
    pass
_PREWARM_INCOMPLETE_HINT = (
    "——LRU 逐出或人为清空已损毁全量驻留，不满足全量源码+AST "
    "前置条件，请重新预热（get_warmed_cache）后重试。")
def _coerce_fs_path(value) -> str | None:
    try:
        raw = os.fspath(value)
    except TypeError:
        return None
    if isinstance(raw, bytes):
        raw = os.fsdecode(raw)
    if not isinstance(raw, str) or not raw:
        return None
    return expand_git_bash_path(raw)
def _norm_path_key(path) -> str | None:
    raw = _coerce_fs_path(path)
    if raw is None:
        return None
    try:
        return os.path.normcase(os.path.abspath(raw))
    except (TypeError, ValueError, OSError) as exc:
        log_swallowed(__name__, exc,
                      context=f"_norm_path_key:{type(exc).__name__}")
        return None
def _iter_paths(paths):
    if paths is None:
        return ()
    if isinstance(paths, (str, bytes, os.PathLike)):
        return (paths,)
    return paths
def _abs_dir(value) -> str:
    raw = _coerce_fs_path(value)
    if raw is None:
        return ""
    try:
        return os.path.abspath(raw)
    except (TypeError, ValueError, OSError) as exc:
        log_swallowed(__name__, exc,
                      context=f"_abs_dir:{type(exc).__name__}")
        return ""
def require_skill_root(value) -> str:
    raw = _coerce_fs_path(value)
    if raw is None or not raw.strip():
        raise ValueError(
            "技能根不能为空或非路径: "
            f"{value!r}。空串会解析成进程工作目录/会话 Temp，导致缓存与台账"
            "跨项目串写，请传入真实项目或技能根目录。")
    return normalize_skill_dir(raw)
def fs_key(path: str) -> str:
    key = _norm_path_key(path)
    if key is None:
        raise ValueError(f"路径键要求非空路径，实际: {path!r}")
    return key
def _optional_skill_root(value) -> str:
    try:
        return require_skill_root(value)
    except (TypeError, ValueError) as exc:
        logger.debug("[Cache] 技能根无效，按无共享层处理: %r (%s)",
                     value, type(exc).__name__)
        return ""
def _is_within_skill_root(root: str, filepath: str) -> bool:
    root_n = _abs_dir(root)
    target_n = _abs_dir(filepath)
    if not root_n or not target_n:
        return False
    root_n = os.path.normcase(root_n)
    target_n = os.path.normcase(target_n)
    try:
        return os.path.commonpath([root_n, target_n]) == root_n
    except (TypeError, ValueError, OSError) as exc:
        log_swallowed(__name__, exc,
                      context=f"_is_within_skill_root:{type(exc).__name__}")
        return False
_VERDICT_SHARE_NAME = "syntax_verdicts.json"
_VERDICT_RECORD = tuple[tuple[int, int], bool, str, str | None]
def _temp_share_path(skill_dir: str, share_name: str) -> str:
    return os.path.join(get_temp_base(require_skill_root(skill_dir)),
                        share_name)
def verdict_share_path(skill_dir: str) -> str:
    return _temp_share_path(skill_dir, _VERDICT_SHARE_NAME)
def _load_verdict_records(
        path: str, freshness=None) -> dict[str, _VERDICT_RECORD] | None:
    entries = _read_verdict_payload(path)
    if entries is None:
        return None
    try:
        fresh: dict[str, _VERDICT_RECORD] = {}
        for path_key, rec in entries.items():
            parsed = _fresh_verdict_record(
                path_key, rec, freshness=freshness)
            if parsed is not None:
                fresh[path_key] = parsed
        return fresh
    except Exception as e:  # noqa: BLE001
        logger.debug("[Cache] verdict 落盘加载失败(降级纯内存): %s", e)
        return None
def load_verdict_share(
        path: str) -> dict[str, tuple[tuple[int, int], bool, str]] | None:
    records = _load_verdict_records(path)
    if records is None:
        return None
    return {path_key: entry[:3] for path_key, entry in records.items()}
def _read_json_object(path: str, label: str) -> dict | None:
    try:
        if not os.path.isfile(path):
            return None
        with open(path, "r", encoding="utf-8-sig") as f:
            payload = json.load(f)
    except Exception as e:  # noqa: BLE001
        logger.debug("[Cache] %s 快照读取失败(降级): %s", label, e)
        return None
    return payload if isinstance(payload, dict) else None
def _read_verdict_payload(path: str) -> dict | None:
    payload = _read_json_object(path, "verdict")
    if payload is None or payload.get("version") != 1:
        return None
    entries = payload.get("verdicts")
    return entries if isinstance(entries, dict) else None
def _coerce_verdict_err(value) -> str:
    return "" if value is None else str(value)
def _coerce_verdict_bool(value) -> bool | None:
    if isinstance(value, bool):
        return value
    if type(value) is int and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        token = value.strip().lower()
        if token in {"true", "1"}:
            return True
        if token in {"false", "0"}:
            return False
    return None
def _parse_verdict_record(rec) -> _VERDICT_RECORD | None:
    try:
        mtime_ns = int(rec["mtime_ns"])
        size = int(rec["size"])
        ok = _coerce_verdict_bool(rec["ok"])
        if ok is None:
            raise ValueError("verdict.ok 必须是明确的布尔值")
        err = _coerce_verdict_err(rec["err"])
        digest = rec.get("source_digest")
        if digest is not None and (not isinstance(digest, str) or not digest):
            raise ValueError("verdict.source_digest 必须是非空字符串")
    except (KeyError, TypeError, ValueError) as e:
        logger.debug("格式解析失败（跳过条目）: %s", e)
        return None
    return (mtime_ns, size), ok, err, digest
def _verdict_record_fresh(
        path_key: str, fingerprint: tuple[int, int],
        digest: str | None = None) -> bool:
    try:
        if digest is not None:
            source, current_fp = read_source_with_fingerprint(path_key)
            return (source is not None and current_fp == fingerprint
                    and source_digest(source) == digest)
        st = os.stat(path_key)
    except (OSError, ValueError) as e:
        logger.debug("文件状态探测失败（跳过）: %s: %s", path_key, e)
        return False
    return (st.st_mtime_ns, st.st_size) == fingerprint
def _fresh_verdict_record(
        path_key: str, rec, freshness=None) -> _VERDICT_RECORD | None:
    try:
        parsed = _parse_verdict_record(rec)
        if parsed is None:
            return None
        check_fresh = freshness or _verdict_record_fresh
        return (parsed if check_fresh(
            path_key, parsed[0], parsed[3]) else None)
    except Exception as e:  # noqa: BLE001
        logger.debug("记录级校验失败（跳过条目）: %s: %s", path_key, e)
        return None
def _file_signature(path: str) -> tuple[int, int, str] | None:
    try:
        st = os.stat(path)
        with open(path, "rb") as snapshot_file:
            digest = hashlib.sha256(snapshot_file.read()).hexdigest()
    except OSError as e:
        logger.debug("共享快照状态探测失败(按缺失处理): %s: %s", path, e)
        return None
    return (st.st_mtime_ns, st.st_size, digest)
def _atomic_write_json(path: str, payload: dict) -> bool:
    try:
        dir_path = os.path.dirname(path)
        if dir_path:
            os.makedirs(dir_path, exist_ok=True)
        atomic_write_text(
            path,
            json.dumps(payload, ensure_ascii=False, default=str),
            tag="shared_cache")
        return True
    except Exception as e:  # noqa: BLE001
        logger.debug("[Cache] 共享槽落盘失败(降级): %s", e)
        return False
def _verdict_payload_entry(value) -> dict | None:
    try:
        if not isinstance(value, (tuple, list)) or len(value) not in (3, 4):
            return None
        fingerprint, ok, err = value[:3]
        digest = value[3] if len(value) == 4 else None
        if not isinstance(fingerprint, (tuple, list)) or len(fingerprint) != 2:
            return None
        ok = _coerce_verdict_bool(ok)
        if ok is None:
            return None
        if digest is not None and (not isinstance(digest, str) or not digest):
            return None
        entry = {"mtime_ns": fingerprint[0], "size": fingerprint[1],
                 "ok": ok, "err": _coerce_verdict_err(err)}
        if digest is not None:
            entry["source_digest"] = digest
        return entry
    except (TypeError, ValueError, IndexError, KeyError) as e:
        logger.debug("[Cache] verdict 条目形态非法(跳过): %s", e)
        return None
def persist_verdict_share(path: str, verdicts: dict) -> int | None:
    if not isinstance(verdicts, dict):
        logger.debug("[Cache] verdict 快照载体非映射(降级): %s",
                     type(verdicts).__name__)
        return None
    entries: dict[str, dict] = {}
    for path_key, record in verdicts.items():
        entry = _verdict_payload_entry(record)
        if entry is not None:
            entries[str(path_key)] = entry
    if verdicts and not entries:
        logger.debug("[Cache] verdict 快照无合法条目，拒绝覆盖落盘")
        return None
    payload = {"version": 1, "verdicts": entries}
    if not _atomic_write_json(path, payload):
        return None
    return len(entries)
_CALLGRAPH_SHARE_NAME = "_callgraph_share.json"
def _rule_source_digest(h) -> None:
    base_dir = os.path.dirname(os.path.abspath(__file__))
    try:
        rule_modules = sorted(
            name for name in os.listdir(base_dir)
            if name.startswith("diag_callgraph_") and name.endswith(".py"))
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'_rule_source_digest:listdir:'
                              f'{type(_e).__name__}')
        h.update(b"builder-src-unavailable")
        return
    for mod in rule_modules:
        try:
            with open(os.path.join(base_dir, mod), "rb") as bf:
                h.update(bf.read())
        except Exception as _e:  # noqa: BLE001
            log_swallowed(__name__, _e,
                          context=f'_rule_source_digest:read:'
                                  f'{type(_e).__name__}')
            h.update(b"builder-src-unavailable")
        h.update(b"\x00")
def _tree_source_digest(h, sd: str) -> None:
    def _on_walk_error(exc: OSError) -> None:
        log_swallowed(__name__, exc,
                      context=f"_tree_source_digest:walk:"
                              f"{type(exc).__name__}")
        h.update(b"walk-unavailable\x00")
        h.update(str(exc).encode("utf-8", "replace"))
        h.update(b"\x00")
    for root, dirs, files in os.walk(sd, onerror=_on_walk_error):
        prune_ignore_dirs(dirs, sd)
        dirs.sort()
        for fn in sorted(files):
            if not is_py_source_file(fn):
                continue
            p = os.path.join(root, fn)
            h.update(os.path.relpath(p, sd).encode("utf-8"))
            h.update(b"\x00")
            try:
                with open(p, "rb") as source_file:
                    h.update(source_file.read())
            except OSError as exc:
                log_swallowed(__name__, exc,
                              context=f"_tree_source_digest:read:"
                                      f"{type(exc).__name__}")
                h.update(b"source-unavailable")
            h.update(b"\x00")
def callgraph_share_fingerprint(skill_dir: str) -> str:
    h = hashlib.sha256()
    _rule_source_digest(h)
    _tree_source_digest(h, require_skill_root(skill_dir))
    return h.hexdigest()
def callgraph_share_path(skill_dir: str) -> str:
    return _temp_share_path(skill_dir, _CALLGRAPH_SHARE_NAME)
def _share_function_count(data: dict) -> int | None:
    try:
        count = int(data.get("functions", 0) or 0)
    except (TypeError, ValueError, OverflowError) as e:
        logger.debug("[Cache] 调用图共享层 functions 字段损坏(降级重建): %s", e)
        return None
    if count < 0:
        logger.debug("[Cache] 调用图共享层 functions 为负数(%d)，拒绝复用",
                     count)
        return None
    return count
def _share_payload_matches(data: object, skill_dir: str) -> bool:
    return (isinstance(data, dict)
            and data.get("fingerprint") == callgraph_share_fingerprint(skill_dir)
            and isinstance(data.get("graph"), dict))
def load_call_graph_share(skill_dir: str) -> tuple[dict, int] | None:
    root = _optional_skill_root(skill_dir)
    if not root:
        return None
    data = _read_json_object(callgraph_share_path(root), "调用图")
    if data is None or not _share_payload_matches(data, root):
        return None
    func_count = _share_function_count(data)
    if func_count is None:
        return None
    return data["graph"], func_count
def persist_call_graph_share(skill_dir: str, graph: dict,
                             func_count: int, *,
                             expected_fingerprint: str | None = None) -> None:
    root = _optional_skill_root(skill_dir)
    if not root:
        logger.warning("[Cache] 调用图共享层技能根无效(降级不落盘): %r",
                       skill_dir)
        return
    skill_dir = root
    if not isinstance(graph, dict):
        logger.debug("[Cache] 调用图共享层 graph 非映射(拒绝落盘): %s",
                     type(graph).__name__)
        return
    try:
        function_count = int(func_count)
        if function_count < 0:
            logger.debug("[Cache] 调用图共享层 functions 为负数(%d)，拒绝落盘",
                         function_count)
            return
        fingerprint = callgraph_share_fingerprint(skill_dir)
        if (expected_fingerprint is not None
                and fingerprint != expected_fingerprint):
            logger.info(
                "[Cache] 调用图构建期间源码或规则已变化，拒绝共享旧代际产物: %s",
                skill_dir)
            return
        payload = {
            "fingerprint": fingerprint,
            "graph": graph,
            "functions": function_count,
            "saved_at": time.strftime("%Y%m%d%H%M%S"),
        }
        path = callgraph_share_path(skill_dir)
    except Exception:
        logger.debug("[Cache] 调用图磁盘共享层写入失败（不影响本轮）", exc_info=True)
        return
    _atomic_write_json(path, payload)
_T5_BASELINE_DIRNAME = "_baseline"
T5_BASELINE_FILENAME = "t5_regression_metrics.json"
def t5_baseline_path(skill_dir: str) -> str:
    return _domain_t5_baseline_path(require_skill_root(skill_dir))
_T5_READ_ERRORS = (OSError, ValueError, EOFError, zlib.error, RecursionError)
class _T5BaselinePersistenceError(RuntimeError):
    pass
def _read_t5_snapshot(path: str) -> dict:
    with open(path, "rb") as f:
        is_gzip = f.read(2) == b"\x1f\x8b"
    if is_gzip:
        with gzip.open(path, "rt", encoding="utf-8-sig") as f:
            data = json.load(f)
    else:
        with open(path, encoding="utf-8-sig") as f:
            data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError("T5 回归基线根节点必须是对象")
    return data
def load_t5_baseline(skill_dir: str, *, _strict: bool = False) -> dict:
    path = t5_baseline_path(skill_dir)
    if not os.path.isfile(path):
        logger.debug("T5 回归基线尚未生成（首轮正常态，按无基线处理）: %s", path)
        return {}
    try:
        return _read_t5_snapshot(path)
    except _T5_READ_ERRORS as e:
        log_swallowed(__name__, e,
                      context=f'load_t5_baseline:{type(e).__name__}')
        if _strict:
            raise _T5BaselinePersistenceError(
                f"T5 回归基线不可读: {path}: {e}") from e
        return {}
def _t5_tmp_path(path: str) -> str:
    return f"{path}.tmp.{os.getpid()}.{threading.get_ident()}"
def _write_gzip_snapshot(path: str, snapshot: dict, tmp: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with gzip.open(tmp, "wt", encoding="utf-8", compresslevel=6) as f:
        json.dump(snapshot, f, ensure_ascii=False, separators=(",", ":"),
                  default=str)
    replace_with_retry(tmp, path)
def _discard_t5_tmp(tmp: str) -> None:
    if safe_delete(tmp):
        return
    try:
        os.remove(tmp)  # jwsgj:suppress file_deletion — 审计认可：safe_delete 不可用（非 Windows/回收站失败）时的原生回退，非防护环境不被拦截
    except OSError as rm_exc:
        logger.debug("T5 基线孤儿 tmp 清理失败（残留待人工回收）: %s: %s",
                     tmp, rm_exc)
def save_t5_baseline(
        skill_dir: str, snapshot: dict, *, _strict: bool = False) -> None:
    if not isinstance(snapshot, dict):
        logger.warning("T5 回归基线快照非映射(拒绝落盘): %s",
                       type(snapshot).__name__)
        if _strict:
            raise _T5BaselinePersistenceError("T5 回归基线快照非映射，拒绝落盘")
        return
    path = t5_baseline_path(skill_dir)
    if os.path.lexists(path):
        try:
            _read_t5_snapshot(path)
        except _T5_READ_ERRORS as exc:
            logger.warning(
                "T5 既有基线不可读或结构损坏，拒绝用本轮快照覆盖（请先恢复或"
                "显式处理旧基线）: %s", exc)
            if _strict:
                raise _T5BaselinePersistenceError(
                    f"T5 回归基线保存失败，既有基线不可读: {path}: {exc}"
                ) from exc
            return
    tmp = _t5_tmp_path(path)
    try:
        _write_gzip_snapshot(path, snapshot, tmp)
    except (OSError, TypeError, ValueError, RecursionError, zlib.error) as exc:
        logger.warning("T5 回归基线保存失败（降级，基线未更新可下轮重试）: %s",
                       exc)
        _discard_t5_tmp(tmp)
        if _strict:
            raise _T5BaselinePersistenceError(
                f"T5 回归基线保存失败: {path}: {exc}") from exc
_SOURCE_KEY_PREFIX = "source::"
_AST_KEY_PREFIX = "ast::"
_SOURCE_MISS = object()
def _path_of_key(key: str) -> str:
    for pfx in (_SOURCE_KEY_PREFIX, _AST_KEY_PREFIX):
        if key.startswith(pfx):
            return key[len(pfx):]
    return key
def _source_key(filepath: str) -> str:
    return _SOURCE_KEY_PREFIX + filepath
def _ast_key(filepath: str) -> str:
    return _AST_KEY_PREFIX + filepath
class _DigestIndex:
    def __init__(self) -> None:
        self.by_digest: dict[str, OrderedDict[str, None]] = {}
        self.by_path: dict[str, str] = {}
    def _drop_digest_path(self, digest: str, filepath: str) -> None:
        paths = self.by_digest.get(digest)
        if paths is None:
            return
        paths.pop(filepath, None)
        if not paths:
            self.by_digest.pop(digest, None)
    def register(self, digest: str, filepath: str) -> None:
        old_digest = self.by_path.get(filepath)
        if old_digest is not None and old_digest != digest:
            self._drop_digest_path(old_digest, filepath)
        paths = self.by_digest.setdefault(digest, OrderedDict())
        paths[filepath] = None
        paths.move_to_end(filepath)
        self.by_path[filepath] = digest
    def drop_path(self, filepath: str) -> None:
        old_digest = self.by_path.pop(filepath, None)
        if old_digest is not None:
            self._drop_digest_path(old_digest, filepath)
    def paths_of(self, digest: str) -> tuple[str, ...]:
        return tuple(self.by_digest.get(digest, ()))
    def clear(self) -> None:
        self.by_digest.clear()
        self.by_path.clear()
class _FingerprintWindow:
    def __init__(self, lock: threading.RLock) -> None:
        self._lock = lock
        self.meta: dict[str, tuple[int, int]] = {}
        self._scan_prev: dict[str, tuple[int, int]] = {}
        self._frozen: bool = False
        self._depth: int = 0
    def registered(self, filepath: str) -> tuple[int, int] | None:
        return self.meta.get(filepath)
    def mark(self, filepath: str, fingerprint: tuple[int, int]) -> None:
        self.meta[filepath] = fingerprint
    def prev_of(self, filepath: str) -> tuple[int, int] | None:
        return self._scan_prev.get(filepath)
    def is_changed(self, filepath: str) -> bool:
        if self._frozen and filepath in self.meta:
            return False
        meta = self.meta.get(filepath)
        if meta is None:
            return True
        try:
            st = os.stat(filepath)
        except OSError as _e:
            log_swallowed(__name__, _e,
                          context=f'_FingerprintWindow.is_changed:'
                                  f'{type(_e).__name__}')
            return True
        return (st.st_mtime_ns, st.st_size) != meta
    def freeze(self) -> int:
        with self._lock:
            self._depth += 1
            self._frozen = True
            return len(self.meta)
    def unfreeze(self) -> None:
        with self._lock:
            if self._depth > 0:
                self._depth -= 1
            if self._depth == 0:
                self._frozen = False
    @property
    def frozen(self) -> bool:
        return self._frozen
    def begin_scan(self) -> None:
        self._scan_prev = dict(self.meta)
    def clear(self) -> None:
        self.meta.clear()
        self._scan_prev.clear()
        self._frozen = False
        self._depth = 0
class _CapAdaptation:
    CAP_MARGINS: tuple[tuple[str, int], ...] = (
        ("MAX_SOURCE_CACHE", 64), ("MAX_AST_CACHE", 64),
        ("MAX_SOURCE_HARD_CAP", 128), ("MAX_AST_HARD_CAP", 128),
    )
    def __init__(self) -> None:
        self._caps_adapted: dict[str, int] = {}
    def raised_caps(self, current: dict[str, int],
                    n_files: int) -> dict[str, int]:
        raised: dict[str, int] = {}
        for name, margin in self.CAP_MARGINS:
            value = current[name]
            if not self._should_adapt(name, value):
                continue
            new_value = max(n_files + margin, value)
            if new_value != value:
                raised[name] = new_value
                self._caps_adapted[name] = new_value
        return raised
    def _should_adapt(self, name: str, value: int) -> bool:
        last = self._caps_adapted.get(name)
        if last is None:
            return value == getattr(SourceAstStore, name)
        return value == last
def _default_pin_scope(skill_dir: str) -> Callable[[str], bool]:
    return lambda path: not is_diagnosis_out_of_scope(
        path, root_dir=skill_dir)
class _ResidencyPolicy:
    MAX_PIN_CACHE = 4096
    MAX_PINNED_PATHS = 8192
    def __init__(self, pin_scope: Callable[[str], bool]) -> None:
        self._pin_scope = pin_scope
        self._pin_cache: OrderedDict[str, bool] = OrderedDict()
        self._pinned_paths: OrderedDict[str, None] = OrderedDict()
    def pin_paths(self, paths) -> None:
        for path in _iter_paths(paths):
            _pinned = _norm_path_key(path)
            if _pinned is None:
                continue
            self._pinned_paths[_pinned] = None
            self._pinned_paths.move_to_end(_pinned)
        while len(self._pinned_paths) > self.MAX_PINNED_PATHS:
            self._pinned_paths.popitem(last=False)
    def is_pinned(self, filepath: str) -> bool:
        _key = _norm_path_key(filepath)
        if _key is not None and _key in self._pinned_paths:
            return True
        probe = _key if _key is not None else filepath
        cached = self._pin_cache.get(probe)
        if cached is not None:
            self._pin_cache.move_to_end(probe)
            return cached
        try:
            result = bool(self._pin_scope(probe))
        except Exception:
            logger.warning("[Cache] pin_scope 判定异常，按不豁免处理",
                           exc_info=True)
            result = False
        if len(self._pin_cache) >= self.MAX_PIN_CACHE:
            self._pin_cache.popitem(last=False)
        self._pin_cache[probe] = result
        return result
    def evict_for_insert(self, mapping: OrderedDict, soft_cap: int,
                         hard_cap: int) -> str | None:
        soft_cap = min(soft_cap, hard_cap)
        if len(mapping) < soft_cap:
            return None
        victim = self._first_evictable_key(mapping)
        if victim is not None:
            del mapping[victim]
            return victim
        return self._pop_hard_cap_victim(mapping, hard_cap)
    def _first_evictable_key(self, mapping: OrderedDict):
        return next((k for k in mapping
                     if not self.is_pinned(_path_of_key(k))), None)
    @staticmethod
    def _pop_hard_cap_victim(mapping: OrderedDict, hard_cap: int):
        if not mapping or len(mapping) < hard_cap:
            return None
        victim, _ = mapping.popitem(last=False)
        return victim
    def clear(self) -> None:
        self._pin_cache.clear()
        self._pinned_paths.clear()
class SourceAstStore:
    MAX_SOURCE_CACHE = 320
    MAX_AST_CACHE = 300
    MAX_SOURCE_HARD_CAP = 600
    MAX_AST_HARD_CAP = 350
    def __init__(self, skill_dir: str, lock: threading.RLock,
                 pin_scope: Callable[[str], bool] | None = None):
        self.skill_dir = require_skill_root(skill_dir)
        self._lock = lock
        self._source_map: OrderedDict[str, str | None] = OrderedDict()
        self._ast_map: OrderedDict[str, ast.AST | None] = OrderedDict()
        self._fingerprints = _FingerprintWindow(lock)
        self._digest = _DigestIndex()
        self._policy = _ResidencyPolicy(
            pin_scope or _default_pin_scope(self.skill_dir))
        self._caps = _CapAdaptation()
        self._func_nodes_index: weakref.WeakKeyDictionary | None = None
        self._stats: dict[str, int] = {
            "source_hits": 0, "source_misses": 0,
            "ast_hits": 0, "ast_misses": 0,
            "ast_parse_count": 0,
            "evictions": 0,
        }
    def pinned_paths(self, paths) -> list:
        with self._lock:
            return [path for path in _iter_paths(paths)
                    if self._policy.is_pinned(self._normalize_path(path))]
    def in_scope(self, filepath: str) -> bool:
        if not os.path.isabs(filepath):
            filepath = os.path.normpath(os.path.join(self.skill_dir, filepath))
        return _is_within_skill_root(self.skill_dir, filepath)
    def pin_paths(self, paths) -> None:
        normalized: list[str] = []
        for path in _iter_paths(paths):
            try:
                normalized.append(self._normalize_path(
                    os.fsdecode(os.fspath(path))))
            except TypeError as exc:
                log_swallowed(__name__, exc,
                              context=f"SourceAstStore.pin_paths:"
                                      f"{type(exc).__name__}")
        with self._lock:
            self._policy.pin_paths(normalized)
    def count_py_files(self) -> int:
        n = 0
        for _root, dirs, filenames in os.walk(self.skill_dir):
            prune_ignore_dirs(dirs, self.skill_dir)
            n += sum(1 for f in filenames if is_py_source_file(f))
        return n
    def adapt_caps(self, n_files: int) -> None:
        caps = {name: getattr(self, name) for name, _m in self._caps.CAP_MARGINS}
        for name, value in self._caps.raised_caps(caps, n_files).items():
            setattr(self, name, value)
    def _evict_for_insert(self, mapping: OrderedDict, soft_cap: int,
                          hard_cap: int) -> None:
        victim = self._policy.evict_for_insert(mapping, soft_cap, hard_cap)
        if victim is None:
            return
        victim_path = _path_of_key(victim)
        source_only = (mapping is self._source_map
                       and _ast_key(victim_path) not in self._ast_map)
        ast_only = (mapping is self._ast_map
                    and _source_key(victim_path) not in self._source_map)
        if source_only or ast_only:
            self._digest.drop_path(victim_path)
        self._stats["evictions"] += 1
    def _normalize_path(self, filepath: str) -> str:
        raw = _coerce_fs_path(filepath)
        if raw is None:
            return ""
        normalized = os.path.normpath(raw)
        if not os.path.isabs(normalized):
            normalized = os.path.normpath(os.path.join(self.skill_dir, normalized))
        return os.path.normcase(normalized)
    def _drop_resident(self, filepath: str) -> None:
        self._source_map.pop(_source_key(filepath), None)
        self._ast_map.pop(_ast_key(filepath), None)
        self._digest.drop_path(filepath)
    def _source_cache_hit(self, filepath: str, key: str):
        if key not in self._source_map:
            return _SOURCE_MISS
        if self.meta_changed(filepath):
            self._drop_resident(filepath)
            return _SOURCE_MISS
        self._source_map.move_to_end(key)
        return self._source_map[key]
    def get_source(self, filepath: str) -> str | None:
        filepath = self._normalize_path(filepath)
        if not filepath:
            return None
        if not self.in_scope(filepath):
            return self._read_outside_source(filepath)
        key = _source_key(filepath)
        with self._lock:
            cached = self._source_cache_hit(filepath, key)
            if cached is not _SOURCE_MISS and self.frozen:
                self._stats["source_hits"] += 1
                return cached
            src, fp_new = read_source_with_fingerprint(filepath)
            if src is None:
                logger.warning("[Cache] 读取失败 %s", filepath)
                self._drop_resident(filepath)
                self._stats["source_misses"] += 1
                return None
            if (cached is not _SOURCE_MISS
                    and source_digest(src) == self._digest.by_path.get(filepath)):
                self._stats["source_hits"] += 1
                return cached
            self._expire_stale_ast(filepath, fp_new)
            self._commit_source(filepath, src, fp_new)
            self._stats["source_misses"] += 1
            return src
    @staticmethod
    def _read_outside_source(filepath: str) -> str | None:
        src, _fp = read_source_with_fingerprint(filepath)
        if src is None:
            logger.warning("[Cache] 读取失败 %s", filepath)
        return src
    def _commit_source(self, filepath: str, src: str,
                       fp_new: tuple[int, int]) -> None:
        filepath = self._normalize_path(filepath)
        if not self.in_scope(filepath):
            return
        digest = source_digest(src)
        old_digest = self._digest.by_path.get(filepath)
        if old_digest is not None and old_digest != digest:
            self._ast_map.pop(_ast_key(filepath), None)
        self._fingerprints.mark(filepath, fp_new)
        self._digest.register(digest, filepath)
        key = _source_key(filepath)
        if key not in self._source_map:
            self._evict_for_insert(self._source_map, self.MAX_SOURCE_CACHE,
                                   self.MAX_SOURCE_HARD_CAP)
        self._source_map[key] = src
        self._source_map.move_to_end(key)
    def _expire_stale_ast(self, filepath: str, fp_new: tuple[int, int]) -> None:
        old_fp = self._fingerprints.registered(filepath)
        if old_fp is not None and old_fp != fp_new:
            self._ast_map.pop(_ast_key(filepath), None)
    @staticmethod
    def _parse_source_text(src: str, filepath: str) -> ast.AST | None:
        try:
            return ast.parse(src, filename=filepath)
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[Cache] 不可解析源码跳过 %s: %s: %s",
                           filepath, type(e).__name__, e)
        return None
    def _parse_outside_ast(self, filepath: str) -> ast.AST | None:
        src = self._read_outside_source(filepath)
        if src is None:
            return None
        return self._parse_source_text(src, filepath)
    def get_ast(self, filepath: str, *, check_meta: bool = True) -> ast.AST | None:
        filepath = self._normalize_path(filepath)
        if not filepath:
            return None
        if not self.in_scope(filepath):
            return self._parse_outside_ast(filepath)
        with self._lock:
            return self._get_ast_locked(filepath, check_meta=check_meta)
    def _get_ast_locked(
        self, filepath: str, *, check_meta: bool, src: str | None = None,
    ) -> ast.AST | None:
        key = _ast_key(filepath)
        if check_meta and src is None:
            src = self.get_source(filepath)
        if key in self._ast_map:
            if check_meta and self.meta_changed(filepath):
                del self._ast_map[key]
            else:
                self._ast_map.move_to_end(key)
                self._stats["ast_hits"] += 1
                return self._ast_map[key]
        self._stats["ast_misses"] += 1
        if src is None and not check_meta:
            src = self.get_source(filepath)
        if src is None:
            return None
        tree = self._parse_source_text(src, filepath)
        if tree is None:
            self._store_ast(key, None)
            return None
        self._stats["ast_parse_count"] += 1
        self._store_ast(key, tree)
        return tree
    def _store_ast(self, key: str, tree: ast.AST | None) -> None:
        if key not in self._ast_map:
            self._evict_for_insert(self._ast_map, self.MAX_AST_CACHE,
                                   self.MAX_AST_HARD_CAP)
        self._ast_map[key] = tree
        self._ast_map.move_to_end(key)
    def get_source_and_ast(self, filepath: str) -> tuple[str | None, ast.AST | None]:
        filepath = self._normalize_path(filepath)
        if not filepath:
            return None, None
        with self._lock:
            src = self.get_source(filepath)
            if src is None:
                return None, None
            if not self.in_scope(filepath):
                return src, self._parse_source_text(src, filepath)
            return src, self._get_ast_locked(
                filepath, check_meta=False, src=src)
    def get_ast_by_digest(self, digest: str) -> ast.AST | None:
        with self._lock:
            for filepath in self._digest.paths_of(digest):
                if self.meta_changed(filepath):
                    continue
                tree = self._ast_map.get(_ast_key(filepath))
                if tree is not None:
                    return tree
            return None
    def registered_fingerprint(self, filepath: str) -> tuple[int, int] | None:
        fp = self._normalize_path(filepath)
        return self._fingerprints.registered(fp)
    def get_function_nodes(self, tree: ast.AST) -> list | None:
        idx = self._func_nodes_index
        if idx is None:
            return None
        with self._lock:
            return idx.get(tree)
    def set_function_nodes(self, tree: ast.AST, nodes: list) -> None:
        with self._lock:
            if self._func_nodes_index is None:
                try:
                    self._func_nodes_index = weakref.WeakKeyDictionary()
                except Exception as _e:  # noqa: BLE001 — 受限解释器下索引创建失败降级关闭
                    log_swallowed(
                        __name__, _e,
                        context=f'SourceAstStore.set_function_nodes:'
                                f'{type(_e).__name__}')
                    return
            self._func_nodes_index[tree] = nodes
    def freeze_fingerprints(self) -> int:
        return self._fingerprints.freeze()
    def unfreeze_fingerprints(self) -> None:
        self._fingerprints.unfreeze()
    @property
    def frozen(self) -> bool:
        return self._fingerprints.frozen
    def meta_changed(self, filepath: str) -> bool:
        return self._fingerprints.is_changed(self._normalize_path(filepath))
    def resident_ast(self, filepath: str) -> ast.AST | None:
        key = _ast_key(self._normalize_path(filepath))
        with self._lock:
            return self._ast_map.get(key)
    def get_cache_stats(self) -> dict[str, int]:
        with self._lock:
            return dict(self._stats)
    def begin_scan(self) -> None:
        with self._lock:
            self._fingerprints.begin_scan()
    def ingest_scanned_file(self, fp: str, src: str,
                            fp_new: tuple[int, int]) -> None:
        fp = self._normalize_path(fp)
        with self._lock:
            previous = self._fingerprints.registered(fp)
            scan_previous = self._fingerprints.prev_of(fp)
            if (previous not in (None, fp_new)
                    or scan_previous not in (None, fp_new)):
                self._ast_map.pop(_ast_key(fp), None)
                self._digest.drop_path(fp)
            self._commit_source(fp, src, fp_new)
    def residency_keys(self, paths) -> tuple[frozenset[str], frozenset[str]]:
        normalized = [self._normalize_path(p) for p in _iter_paths(paths)]
        return (frozenset(_source_key(p) for p in normalized),
                frozenset(_ast_key(p) for p in normalized))
    def residency_sizes(self) -> tuple[int, int]:
        with self._lock:
            return len(self._source_map), len(self._ast_map)
    def residency_misses(self, src_keys, ast_keys) -> tuple[int, int]:
        with self._lock:
            # AST None 是语法错误的负缓存，键存在即表示该文件已完成处理。
            return (
                sum(1 for k in src_keys if self._source_map.get(k) is None),
                sum(1 for k in ast_keys if k not in self._ast_map),
            )
    def missing_sources(self, paths) -> list[str]:
        with self._lock:
            return [p for p in _iter_paths(paths)
                    if self._source_map.get(
                        _source_key(self._normalize_path(p))) is None]
    def missing_asts(self, paths) -> list[str]:
        with self._lock:
            return [p for p in _iter_paths(paths)
                    if _ast_key(self._normalize_path(p)) not in self._ast_map]
    def clear(self) -> None:
        with self._lock:
            self._source_map.clear()
            self._ast_map.clear()
            self._fingerprints.clear()
            self._digest.clear()
            self._policy.clear()
            self._func_nodes_index = None
class SyntaxVerdictCache:
    def __init__(self, skill_dir: str, store: SourceAstStore,
                 lock: threading.RLock) -> None:
        self._skill_dir = require_skill_root(skill_dir)
        self._store = store
        self._lock = lock
        self._entries: dict[str, _VERDICT_RECORD] = {}
        self._disk_path: str | None = None
        self._disk_loaded: bool = False
        self._disk_sig: tuple[int, int, str] | None = None
        self._dirty: bool = False
        self._dirty_keys: set[str] = set()
    def _record_fresh(
        self, path_key: str, fingerprint: tuple[int, int],
        digest: str | None = None,
    ) -> bool:
        if not self._store.frozen:
            return _verdict_record_fresh(path_key, fingerprint, digest)
        filepath = self._store._normalize_path(path_key)
        if fingerprint != self._store.registered_fingerprint(filepath):
            return False
        if digest is None:
            return True
        with self._store._lock:
            resident_digest = self._store._digest.by_path.get(filepath)
        return digest == resident_digest
    def get(self, filepath: str) -> tuple[bool, str] | None:
        filepath = self._store._normalize_path(filepath)
        entry = self._hit(filepath)
        if entry is None:
            return None
        if self._store.frozen:
            if not self._record_fresh(filepath, entry[0], entry[3]):
                return None
            return (entry[1], entry[2])
        fp, ok, err, digest = entry
        try:
            st = os.stat(filepath)
        except OSError as _e:
            log_swallowed(__name__, _e,
                          context=f'SyntaxVerdictCache.get:'
                                  f'{type(_e).__name__}')
            return None
        current_fp = (st.st_mtime_ns, st.st_size)
        if current_fp != fp:
            self._load_from_disk()
            with self._lock:
                entry = self._entries.get(filepath)
            if entry is None:
                return None
            fp, ok, err, digest = entry
            if current_fp != fp:
                return None
        if digest is not None and not _verdict_record_fresh(
                filepath, fp, digest):
            return None
        return (ok, err)
    def _hit(self, filepath: str) -> tuple | None:
        self._load_from_disk()
        with self._lock:
            return self._entries.get(filepath)
    def set(self, filepath: str, *, ok: bool, err: str) -> None:
        normalized_ok = _coerce_verdict_bool(ok)
        if normalized_ok is None:
            logger.debug("[Cache] verdict.ok 非明确布尔值，拒绝写入: %r", ok)
            return
        ok = normalized_ok
        err = _coerce_verdict_err(err)
        filepath = self._store._normalize_path(filepath)
        fp = (self._store.registered_fingerprint(filepath)
              if self._store.frozen else None)
        try:
            if fp is None:
                source, fp = read_source_with_fingerprint(filepath)
            else:
                source = self._store.get_source(filepath)
        except (OSError, ValueError) as _e:
            log_swallowed(__name__, _e,
                          context=f'SyntaxVerdictCache.set:'
                                  f'{type(_e).__name__}')
            return
        if source is None or fp is None:
            logger.debug("[Cache] verdict 源码读取失败，拒绝写入: %s", filepath)
            return
        digest = source_digest(source)
        with self._lock:
            self._entries[filepath] = (fp, ok, err, digest)
            self._dirty = True
            self._dirty_keys.add(filepath)
    def _disk_file(self) -> str:
        if self._disk_path is None:
            self._disk_path = verdict_share_path(self._skill_dir)
        return self._disk_path
    def _merge_fresh_entries(self, fresh: dict) -> None:
        normalized = {
            self._store._normalize_path(fp_key): entry
            for fp_key, entry in fresh.items()
        }
        changed = 0
        with self._lock:
            for fp_key in list(self._entries):
                if fp_key not in normalized and fp_key not in self._dirty_keys:
                    entry = self._entries[fp_key]
                    if (self._store.frozen and self._record_fresh(
                            fp_key, entry[0], entry[3])):
                        continue
                    del self._entries[fp_key]
                    changed += 1
            for fp_key, entry in normalized.items():
                if fp_key in self._dirty_keys:
                    continue
                if self._entries.get(fp_key) != entry:
                    changed += 1
                self._entries[fp_key] = entry
        if changed:
            logger.info("[Cache] verdict 落盘共享同步变更 %d 条", changed)
    def _read_disk_snapshot(self, path: str) -> dict | None:
        fresh = _load_verdict_records(path, freshness=self._record_fresh)
        if fresh is not None:
            return fresh
        try:
            os.stat(path)
        except FileNotFoundError:
            return {}
        except OSError as exc:
            logger.debug("[Cache] verdict 快照状态复核失败（保留内存）: %s: %s",
                         path, exc)
        return None
    def _load_from_disk(self) -> None:
        path = self._disk_file()
        sig = _file_signature(path)
        if self._disk_loaded and sig == self._disk_sig:
            return
        fresh = self._read_disk_snapshot(path)
        self._disk_sig = sig
        self._disk_loaded = True
        if fresh is not None:
            self._merge_fresh_entries(fresh)
    def flush(self) -> int:
        if not self._dirty:
            return 0
        path = self._disk_file()
        fd = None
        locked = False
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            fd = os.open(f"{path}.lock", os.O_RDWR | os.O_CREAT)
            ProcessLock.lock_region(fd, blocking=True)
            locked = True
            fresh = self._read_disk_snapshot(path)
            if fresh is None:
                logger.debug(
                    "[Cache] verdict 快照读取失败，取消本次落盘以避免覆盖"
                    "其他进程的共享记录")
                return 0
            self._merge_fresh_entries(fresh)
            with self._lock:
                stale = [(fp_key, entry) for fp_key, entry in self._entries.items()
                         if not self._record_fresh(
                             fp_key, entry[0], entry[3])]
                for fp_key, entry in stale:
                    if self._entries.get(fp_key) == entry:
                        del self._entries[fp_key]
                        self._dirty_keys.discard(fp_key)
                snapshot = dict(self._entries)
            written = persist_verdict_share(path, snapshot)
            sig_after = _file_signature(path)
        except OSError as e:
            log_swallowed(__name__, e,
                          context=f'SyntaxVerdictCache.flush:'
                                  f'{type(e).__name__}')
            return 0
        finally:
            if locked:
                ProcessLock.unlock_region(fd)
            if fd is not None:
                os.close(fd)
        if written is None:
            return 0
        self._disk_sig = sig_after
        with self._lock:
            if self._entries == snapshot:
                self._dirty = False
                self._dirty_keys.clear()
        return written
    def clear(self) -> None:
        with self._lock:
            self._entries.clear()
            self._disk_loaded = False
            self._dirty = False
            self._dirty_keys.clear()
class WarmupResidency:
    def __init__(self, lock: threading.RLock) -> None:
        self._lock = lock
        self._warmed: bool = False
        self._counts: tuple[int, int, int] | None = None
        self._keys: tuple[frozenset, frozenset] | None = None
    @property
    def is_warmed(self) -> bool:
        with self._lock:
            return self._warmed
    @property
    def keys(self) -> tuple[frozenset, frozenset] | None:
        with self._lock:
            return self._keys
    def mark(self, files: list, store: SourceAstStore) -> None:
        files = list(_iter_paths(files))
        with self._lock:
            src_n, ast_n = store.residency_sizes()
            self._counts = (len(files), src_n, ast_n)
            self._keys = store.residency_keys(files)
            store.pin_paths(files)
            self._warmed = True
    def reset(self) -> None:
        with self._lock:
            self._warmed = False
            self._counts = None
            self._keys = None
    def is_intact(self, store: SourceAstStore) -> bool:
        with self._lock:
            if not self._warmed:
                return False
            if self._keys is not None:
                return store.residency_misses(*self._keys) == (0, 0)
            if self._counts is None:
                return True
            src_n, ast_n = store.residency_sizes()
            return src_n >= self._counts[1] and ast_n >= self._counts[2]
    def ensure(self, store: SourceAstStore) -> None:
        with self._lock:
            if not self._warmed:
                raise CacheNotWarmedError(
                    "SharedCache 未完成全量预热（源码+AST）：预热是所有诊断方法与"
                    "管线步骤的强制前置条件，未预热不执行后续行为。请先调用 "
                    "get_warmed_cache(skill_dir) 或 create_cache(skill_dir) 完成预热后重试。"
                )
            if not self.is_intact(store):
                self._raise_integrity_error(store)
    def _raise_integrity_error(self, store: SourceAstStore) -> None:
        keys = self._keys
        counts = self._counts
        if keys is not None:
            src_keys, ast_keys = keys
            src_miss, ast_miss = store.residency_misses(src_keys, ast_keys)
            snap = (f"置位时文件数 {counts[0]}") if counts is not None else ""
            raise CacheNotWarmedError(
                "SharedCache 预热产物已不完整：置位快照键缺失"
                f"（source 缺 {src_miss}/{len(src_keys)}, "
                f"ast 缺 {ast_miss}/{len(ast_keys)}"
                + (f"，{snap}" if snap else "") + "）"
                + _PREWARM_INCOMPLETE_HINT
            )
        if counts is None:
            raise CacheNotWarmedError(
                "SharedCache 预热状态已失效（并发释放），"
                "请重新预热（get_warmed_cache）后重试。"
            )
        src_n, ast_n = store.residency_sizes()
        raise CacheNotWarmedError(
            "SharedCache 预热产物已不完整：缓存驻留低于置位快照"
            f"（source {src_n}/{counts[1]}, "
            f"ast {ast_n}/{counts[2]}，置位时文件数 {counts[0]}）"
            + _PREWARM_INCOMPLETE_HINT
        )
class PyFileInventory:
    STATE_ABSENT = "absent"
    STATE_BUILDING = "building"
    STATE_READY = "ready"
    def __init__(self, skill_dir: str, store: SourceAstStore,
                 cond: threading.Condition) -> None:
        self._skill_dir = require_skill_root(skill_dir)
        self._store = store
        self._cond = cond
        self._state = self.STATE_ABSENT
        self._files: list[str] | None = None
        self._count = 0
        self._lines = 0
    def ensure_ready(self, label: str) -> bool:
        try:
            self.ensure()
            return True
        except Exception as e:  # noqa: BLE001
            logger.warning("%s: %s", label, e)
            return False
    @property
    def paths(self) -> list[str]:
        if not self.ensure_ready("py_files"):
            return []
        return list(self._files or [])
    @property
    def count(self) -> int:
        return self._count if self.ensure_ready("file_count") else 0
    @property
    def lines(self) -> int:
        return self._lines if self.ensure_ready("total_lines") else 0
    @property
    def raw_paths(self) -> list[str]:
        return list(self._files or [])
    def snapshot(self) -> tuple[list[str], int, int]:
        return list(self._files or []), self._count, self._lines
    def ensure(self) -> None:
        with self._cond:
            if self._state == self.STATE_READY:
                return
            while self._state == self.STATE_BUILDING:
                self._cond.wait()
            if self._state == self.STATE_READY:
                return
            self._state = self.STATE_BUILDING
            try:
                self.scan()
                self._state = self.STATE_READY
            except Exception:
                self._state = self.STATE_ABSENT
                raise
            finally:
                self._cond.notify_all()
    def scan(self) -> None:
        self._files = []
        self._lines = 0
        self._store.begin_scan()
        def _fail_on_walk_error(exc: OSError) -> None:
            raise exc
        for root, dirs, filenames in os.walk(
                self._skill_dir, onerror=_fail_on_walk_error):
            prune_ignore_dirs(dirs, self._skill_dir)
            dirs.sort()
            for f in sorted(filenames):
                if not is_py_source_file(f):
                    continue
                fp = os.path.join(root, f)
                self._files.append(fp)
                src, fp_new = read_source_with_fingerprint(fp)
                if fp_new is None:
                    logger.warning("shared_cache: py file scan failed: %s", fp)
                    continue
                self._lines += count_lines(src)
                self._store.ingest_scanned_file(fp, src, fp_new)
        self._count = len(self._files)
    def reset(self) -> None:
        with self._cond:
            self._state = self.STATE_ABSENT
            self._files = None
            self._count = 0
            self._lines = 0
def _env_int(name: str, default: int) -> int:
    raw = os.environ.get(name)
    if raw is None:
        return default
    try:
        return int(raw.strip())
    except ValueError:
        logger.debug("环境变量 %s 非整数（%r），归一默认值 %d", name, raw, default)
        return default
_AST_CACHE_DIR_NAME = "ast_cache"
_STALE_SIBLING_MAX_AGE = 24 * 3600
_SIBLING_PRUNE_MIN_INTERVAL = 3600
_SIBLING_PRUNE_MARKER_NAME = ".sibling_cache_prune.marker"
_SIBLING_PRUNE_ARTIFACTS = (
    (_AST_CACHE_DIR_NAME, True),
    (".filecache.pkl", False),
)
_SIBLING_PRUNE_BUDGET = _env_int("JWSGJ_SIBLING_PRUNE_BUDGET", 48)
def _prune_age_allowed(value) -> bool:
    try:
        allowed = bool(value >= 0 and math.isfinite(value))
    except (TypeError, ValueError, OverflowError):
        allowed = False
    if not allowed:
        logger.warning("兄弟会话回收年龄非法（拒绝执行）: %r", value)
    return allowed
class AstBlobStore:
    def __init__(self, skill_dir: str) -> None:
        self.skill_dir = require_skill_root(skill_dir)
        self._dir_cache: str | None = None
        self._prune_lock = threading.RLock()
        self._prune_cycle_origins: dict[str, int] = {}
    def dir_path(self) -> str:
        if self._dir_cache is None:
            self._dir_cache = os.path.join(
                get_temp_base(self.skill_dir), _AST_CACHE_DIR_NAME)
        return self._dir_cache
    def _session_root(self, base_dir: str | None = None) -> str | None:
        return resolve_session_root_from_artifact_path(
            base_dir or self.dir_path())
    def _ordered_siblings(self, session: str,
                          budget: int) -> tuple[list[str], int]:
        siblings = iter_sibling_session_roots(session)
        total = len(siblings)
        if budget <= 0:
            return [], total
        if total <= budget:
            return siblings, total
        def _mtime_key(path: str) -> float:
            try:
                return os.path.getmtime(path)
            except Exception as _e:  # noqa: BLE001 -- 降级：不阻断主链
                logger.debug("兄弟会话 mtime 探测失败，按最旧语义: %s: %s",
                             path, _e)
                return 0.0
        siblings = sorted(siblings, key=_mtime_key)
        cycle = int(time.time() // _SIBLING_PRUNE_MIN_INTERVAL)
        with self._prune_lock:
            origin = self._prune_cycle_origins.setdefault(session, cycle)
            start = ((cycle - origin) * budget) % total
            rotated = siblings[start:] + siblings[:start]
            return rotated[:budget], total
    def prune_sibling_stale(
            self, max_age_seconds: int = _STALE_SIBLING_MAX_AGE,
            base_dir: str | None = None,
            budget: int = _SIBLING_PRUNE_BUDGET) -> int:
        if not _prune_age_allowed(max_age_seconds):
            return 0
        try:
            session = self._session_root(base_dir)
            if not session:
                return 0
            cutoff = time.time() - max_age_seconds
            siblings, total = self._ordered_siblings(session, budget)
            if total > len(siblings):
                logger.debug("兄弟会话回收按预算截断: 扫 %d/%d（剩余下周期轮转）",
                             len(siblings), total)
            removed = sum(self._prune_one_sibling(sibling, cutoff)
                          for sibling in siblings)
            if removed:
                logger.info("[Cache] 兄弟会话陈旧缓存回收: %d 项（阈值 %ds）",
                            removed, max_age_seconds)
            return removed
        except Exception as e:  # noqa: BLE001
            logger.debug("兄弟会话陈旧缓存回收异常（静默降级）: %s: %s",
                         type(e).__name__, e)
            return 0
    def _prune_one_sibling(self, sibling: str, cutoff: float) -> int:
        temp_dir = os.path.join(sibling, RUNTIME_DIR_NAME)
        try:
            with os.scandir(temp_dir) as scan_it:
                entries = list(scan_it)
        except FileNotFoundError:
            logger.debug("兄弟会话 Temp 目录不存在（跳过）: %s", temp_dir)
            return 0
        except OSError as e:
            logger.debug("兄弟会话 Temp 枚举失败（跳过）: %s: %s", temp_dir, e)
            return 0
        removed = self._prune_bucket_artifacts(
            temp_dir, {e.name: e for e in entries}, cutoff)
        for entry in entries:
            try:
                if not entry.is_dir() or entry.is_symlink():
                    continue
            except OSError as exc:
                logger.debug("兄弟会话目录项探测失败（跳过）: %s: %s",
                             entry.path, exc)
                continue
            removed += self._prune_bucket_artifacts(entry.path, {}, cutoff)
        return removed
    def _prune_bucket_artifacts(self, bucket: str,
                                direct: dict[str, os.DirEntry],
                                cutoff: float) -> int:
        return sum(
            self._try_prune_artifact(
                bucket, art_name, is_dir, direct.get(art_name), cutoff)
            for art_name, is_dir in _SIBLING_PRUNE_ARTIFACTS
        )
    @staticmethod
    def _try_prune_artifact(bucket: str, art_name: str, is_dir: bool,
                            entry: os.DirEntry | None, cutoff: float) -> bool:
        art = os.path.join(bucket, art_name)
        try:
            mtime = (entry.stat().st_mtime
                     if entry is not None else os.path.getmtime(art))
        except OSError as e:
            if not isinstance(e, FileNotFoundError):
                logger.debug("兄弟会话陈旧缓存探测失败（跳过）: %s: %s", art, e)
            return False
        if mtime >= cutoff:
            return False
        return two_level_rmtree(art) if is_dir else two_level_unlink(art)
    def _sibling_prune_marker_path(self) -> str:
        return os.path.join(get_temp_base(self.skill_dir),
                            _SIBLING_PRUNE_MARKER_NAME)
    def _container_prune_marker_path(self, base_dir: str | None = None) -> str | None:
        try:
            session = self._session_root(base_dir)
            if not session:
                return None
            return os.path.join(session, RUNTIME_DIR_NAME,
                                _SIBLING_PRUNE_MARKER_NAME)
        except Exception as e:  # noqa: BLE001
            logger.debug("容器级节流标记路径解析失败（降级纯桶级）: %s", e)
            return None
    @staticmethod
    def _read_marker_ts(path: str | None) -> float | None:
        if not path:
            return None
        try:
            with open(path, encoding="utf-8") as f:
                return float(f.read().strip())
        except FileNotFoundError:
            logger.debug("节流标记缺失或已回收（常态，按无节流执行回收）: %s", path)
            return None
        except (OSError, ValueError) as _e:
            log_swallowed(__name__, _e,
                          context=f'AstBlobStore._read_marker_ts:'
                                  f'{type(_e).__name__}')
            return None
    def _sibling_prune_touch_marker(self, base_dir: str | None = None) -> None:
        ts = str(time.time())
        for path in self._marker_paths(base_dir):
            if not path:
                continue
            try:
                parent = os.path.dirname(path)
                if parent:
                    os.makedirs(parent, exist_ok=True)
                with open(path, "w", encoding="utf-8") as f:
                    f.write(ts)
            except OSError as e:
                logger.debug("节流标记写入失败（该通道降级无节流）: %s: %s", path, e)
    def _marker_paths(self, base_dir: str | None = None) -> tuple[str, str | None]:
        return (self._sibling_prune_marker_path(),
                self._container_prune_marker_path(base_dir))
    def _prune_due(self, base_dir: str | None,
                   min_interval_seconds: int) -> bool:
        valid = [ts for ts in map(self._read_marker_ts,
                                  self._marker_paths(base_dir))
                 if ts is not None]
        now = time.time()
        if valid and 0 <= now - max(valid) < min_interval_seconds:
            logger.debug("兄弟会话回收距上次 %.0fs（间隔 %ds），共享节流跳过",
                         now - max(valid), min_interval_seconds)
            return False
        return True
    def prune_sibling_stale_async(
            self, max_age_seconds: int = _STALE_SIBLING_MAX_AGE,
            base_dir: str | None = None,
            min_interval_seconds: int = _SIBLING_PRUNE_MIN_INTERVAL) -> None:
        if not _prune_age_allowed(max_age_seconds):
            return
        if not self._prune_due(base_dir, min_interval_seconds):
            return
        self._sibling_prune_touch_marker(base_dir=base_dir)
        def _bg_prune():
            try:
                self.prune_sibling_stale(max_age_seconds=max_age_seconds,
                                         base_dir=base_dir)
            except Exception as e:  # noqa: BLE001
                logger.debug("兄弟会话后台回收异常（静默降级）: %s: %s",
                             type(e).__name__, e)
        try:
            threading.Thread(target=_bg_prune, name="sibling-prune",
                             daemon=True).start()
        except Exception as e:  # noqa: BLE001
            logger.debug("后台回收线程派遣失败，降级同步执行: %s", e)
            self.prune_sibling_stale(max_age_seconds=max_age_seconds,
                                     base_dir=base_dir)
_PYCACHE_DIR_NAME = "__pycache__"
def _pycache_paths(dir_path: str) -> list[str]:
    cache_paths: list[str] = []
    for root, dirs, _files in os.walk(dir_path):
        cache_paths.extend(
            os.path.join(root, name) for name in dirs
            if name.lower() == _PYCACHE_DIR_NAME)
        dirs[:] = [name for name in dirs if not name.startswith(".")]
        prune_ignore_dirs(dirs, dir_path)
    return cache_paths
def clean_pycache_before_scan(dir_path: str) -> int:
    count = 0
    for cache_path in _pycache_paths(dir_path):
        if safe_delete(cache_path):
            count += 1
            logger.debug("已清除: %s", cache_path)
        else:
            logger.warning("清除失败(回收站删除未成功): %s", cache_path)
    return count
__all__ = [
    "T5_BASELINE_FILENAME",
    "AstBlobStore",
    "CacheNotWarmedError",
    "PyFileInventory",
    "SourceAstStore",
    "SyntaxVerdictCache",
    "WarmupResidency",
    "callgraph_share_fingerprint",
    "callgraph_share_path",
    "clean_pycache_before_scan",
    "fs_key",
    "load_call_graph_share",
    "load_t5_baseline",
    "load_verdict_share",
    "persist_call_graph_share",
    "persist_verdict_share",
    "require_skill_root",
    "save_t5_baseline",
    "t5_baseline_path",
    "verdict_share_path",
]

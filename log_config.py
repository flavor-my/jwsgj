# ruff: noqa: I001
from __future__ import annotations
import contextvars
import importlib.abc
import inspect
import json
import logging
import math
import os
import re
import sys
import tempfile
import threading
import time
import weakref
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from datetime import datetime
from functools import wraps
from itertools import islice
from logging.handlers import BaseRotatingHandler
from typing import Any, NamedTuple
_msvcrt = None
_fcntl = None
try:
    if sys.platform == "win32":
        import msvcrt as _msvcrt
    else:
        import fcntl as _fcntl
except ImportError:
    logging.getLogger(__name__).debug(
        "[log_config] 平台锁原语导入失败，跨进程写锁降级无锁直写")
__all__ = [
    'ACTIVE_FILES',
    'AUDIT_FILE',
    'CONSUMPTION_FILE',
    'DEFAULT_LEVEL',
    'LOG_DIR_ENV_VAR',
    'LOG_LOCK_SPIN_INTERVAL_S',
    'LOG_LOCK_TIMEOUT_S',
    'MAIN_LOG_FILE',
    'MAX_BYTES',
    'STATE_FILE_SKILL_HOTNESS',
    'TEST_CASE_EVENT',
    'TEST_RUNS_FILE',
    'TEST_RUNS_MAX_BYTES',
    'TRIGGER_EVENTS_FILE',
    'DuplicateMessageFilter',
    'HumanFormatter',
    'JsonFormatter',
    'Stopwatch',
    'TraceIdFilter',
    'TruncatingFileHandler',
    'append_jsonl_locked',
    'build_json_log_entry',
    'clear_trace_id',
    'collect_and_reset_degraded',
    'degraded_section',
    'emit_fix_logs',
    'finish_test_logging',
    'format_log_timestamp',
    'get_log_dir',
    'get_module_logger',
    'get_skill_root',
    'get_trace_id',
    'install_exception_logging',
    'install_module_load_tracing',
    'install_test_logging',
    'lock_region_nonblocking',
    'locked_artifact',
    'log_swallowed',
    'mark_section_degraded',
    'now_iso_seconds',
    'observation_gate',
    'parse_log_ts',
    'perf_scope',
    'perf_trace',
    'prune_jsonl_file',
    'record_test_outcome',
    'safe_stderr_write',
    'safe_write_audit',
    'sanitize_payload',
    'set_trace_id',
    'setup_logging',
    'timed_log',
    'trace_module_run',
    'unlock_region',
    'write_audit',
    'write_bug_intercept',
    'write_defense_feedback',
    'write_detector_liveness',
    'write_module_run',
]
_LOGGER = logging.getLogger(__name__)
def safe_stderr_write(msg: str) -> None:
    try:
        sys.stderr.write(msg if isinstance(msg, str) else str(msg))
    except Exception as _stderr_err:  # noqa: BLE001
        _LOGGER.debug("safe_stderr_write: stderr 不可用，本次留痕丢弃: %s", _stderr_err)
        return
LOG_LOCK_SPIN_INTERVAL_S = 0.002
LOG_LOCK_TIMEOUT_S = 2.0
_DEFAULT_DURATION_MS = 0.0
_REENTRANT_LOCK_STATE = threading.local()
_ARTIFACT_THREAD_LOCKS_GUARD = threading.Lock()
_ARTIFACT_THREAD_LOCKS: weakref.WeakValueDictionary[str, threading.RLock] = weakref.WeakValueDictionary()
def _region_lock_primitives_available() -> bool:
    return _msvcrt is not None if sys.platform == "win32" else _fcntl is not None
def lock_region_nonblocking(fd: int) -> bool:
    try:
        if not _region_lock_primitives_available():
            return False
        if sys.platform == "win32":
            _msvcrt.locking(fd, _msvcrt.LK_NBLCK, 1)
        else:
            _fcntl.flock(fd, _fcntl.LOCK_EX | _fcntl.LOCK_NB)
        return True
    except (OSError, ValueError, TypeError) as _lock_err:
        _LOGGER.debug("lock_region_nonblocking: 跨进程锁获取失败，降级无锁直写: %s", _lock_err)
        return False
def unlock_region(fd: int) -> None:
    try:
        if sys.platform == "win32":
            if _msvcrt is None:
                return
            _msvcrt.locking(fd, _msvcrt.LK_UNLCK, 1)
        else:
            if _fcntl is None:
                return
            _fcntl.flock(fd, _fcntl.LOCK_UN)
    except (OSError, ValueError, TypeError) as _unlock_err:
        _LOGGER.debug("unlock_region: 解锁失败（fd 失效，内核兜底回收）: %s", _unlock_err)
        return
def _acquire_region_lock_with_retry(fd: int) -> bool:
    if not _region_lock_primitives_available():
        _LOGGER.debug(
            "跨进程锁原语不可用（%s），本次写路径直接降级无锁直写",
            sys.platform)
        return False
    deadline = time.monotonic() + LOG_LOCK_TIMEOUT_S
    while True:
        if lock_region_nonblocking(fd):
            return True
        if time.monotonic() >= deadline:
            return False
        time.sleep(LOG_LOCK_SPIN_INTERVAL_S)
_SKILL_ROOT = os.path.dirname(os.path.realpath(__file__))
_PRODUCT_LOGGER_NAMESPACE = "jwsgj"
_SKILL_ROOT_REAL = os.path.normcase(os.path.realpath(_SKILL_ROOT))
def _skill_module_namespace(pathname: str) -> str | None:
    if not isinstance(pathname, str) or not pathname:
        return None
    try:
        real = os.path.normcase(os.path.realpath(pathname))
    except (OSError, ValueError):
        return None
    if not real.startswith(_SKILL_ROOT_REAL + os.sep):
        return None
    rel = os.path.relpath(os.path.realpath(pathname), _SKILL_ROOT)
    parts = [part for part in rel.replace("\\", "/").split("/")
             if part not in ("", ".")]
    if not parts or not parts[-1].endswith(".py"):
        return None
    parts[-1] = parts[-1][:-3]
    return ".".join(
        [_PRODUCT_LOGGER_NAMESPACE]
        + [re.sub(r"[^0-9A-Za-z_]", "_", part) for part in parts])
def _main_module_path() -> str:
    entry = sys.modules.get("__main__")
    path = getattr(entry, "__file__", "") if entry is not None else ""
    return path if isinstance(path, str) else ""
def _bare_logger_namespace(name: str, pathname: str = "") -> str | None:
    if not name or "." in name:
        return None
    if pathname and _skill_module_namespace(pathname) is None:
        return None
    for rel in (os.path.join("tests", name + ".py"), name + ".py"):
        candidate = os.path.join(_SKILL_ROOT, rel)
        if os.path.isfile(candidate):
            return _skill_module_namespace(candidate)
    return None
def get_skill_root() -> str:
    return _SKILL_ROOT
DEFAULT_LEVEL = logging.INFO
LOG_DIR_ENV_VAR = "JWSGJ_LOG_DIR"
MAX_BYTES = 20 * 1024 * 1024
MAIN_LOG_FILE = "jwsgj.log"
AUDIT_FILE = "audit_events.jsonl"
CONSUMPTION_FILE = "consumption_state.json"
STATE_FILE_SKILL_HOTNESS = "skill_hotness.jsonl"
TRIGGER_EVENTS_FILE = "trigger_events.jsonl"
TEST_RUNS_FILE = "test_runs.jsonl"
TEST_CASE_EVENT = "test_case_result"
TEST_RUNS_MAX_BYTES = 8 * 1024 * 1024
_LOG_ARTIFACT_NAMES = (
    MAIN_LOG_FILE, AUDIT_FILE, TRIGGER_EVENTS_FILE,
    STATE_FILE_SKILL_HOTNESS, TEST_RUNS_FILE,
    "development_journal.jsonl",
)
ACTIVE_FILES = frozenset(_LOG_ARTIFACT_NAMES) | frozenset(
    name + ".lock" for name in _LOG_ARTIFACT_NAMES)
_trace_id_var: contextvars.ContextVar[str | None] = contextvars.ContextVar("trace_id", default=None)
class TraceIdFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        tid = _trace_id_var.get()
        if tid is not None and getattr(record, "trace_id", None) is None:
            record.trace_id = tid
        return True
_SURROGATE_RE = re.compile('[\ud800-\udfff]')
_MAX_ESCAPE_DEPTH = 10
def _escape_surrogates(obj: Any, _depth: int = 0) -> Any:
    if isinstance(obj, str):
        if _SURROGATE_RE.search(obj):
            return obj.encode('utf-8', 'backslashreplace').decode('utf-8')
        return obj
    if _depth >= _MAX_ESCAPE_DEPTH:
        return obj
    if isinstance(obj, dict):
        return {_escape_surrogates(k, _depth + 1):
                _escape_surrogates(v, _depth + 1) for k, v in obj.items()}
    if isinstance(obj, (list, tuple, set, frozenset)):
        items = [_escape_surrogates(v, _depth + 1) for v in obj]
        return tuple(items) if isinstance(obj, tuple) else type(obj)(items)
    return obj
class _SurrogateSafeFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        record.msg = _escape_surrogates(record.msg)
        args = record.args
        if isinstance(args, tuple):
            record.args = tuple(_escape_surrogates(_arg) for _arg in args)
        elif isinstance(args, dict):
            record.args = {_escape_surrogates(_k): _escape_surrogates(_v)
                           for _k, _v in args.items()}
        payload = getattr(record, "payload", None)
        if payload is not None:
            record.payload = _escape_surrogates(payload)
        return True
class _NamespaceAttributionFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        name = record.name or ""
        if (name == _PRODUCT_LOGGER_NAMESPACE
                or name.startswith(_PRODUCT_LOGGER_NAMESPACE + ".")):
            return True
        pathname = getattr(record, "pathname", "")
        if name == "py.warnings":
            if _skill_module_namespace(pathname) is None:
                return False
            record.name = _PRODUCT_LOGGER_NAMESPACE + ".warnings"
            return True
        if name == "__main__":
            derived = (_skill_module_namespace(_main_module_path())
                       or _skill_module_namespace(pathname))
            if derived is None:
                return False
            record.name = derived
            return True
        derived = (_skill_module_namespace(pathname)
                   or _bare_logger_namespace(name, pathname))
        if derived is None:
            return False
        if derived.rsplit(".", 1)[-1] != name.rsplit(".", 1)[-1]:
            return False
        record.name = derived
        return True
class _SwallowedFloodFilter(logging.Filter):
    _BUDGET_PER_CONTEXT = 100
    _SUMMARY_EVERY = 200
    _MAX_KEYS = 256
    def __init__(self) -> None:
        super().__init__()
        self._counts: dict[str, int] = {}
        self._lock = threading.Lock()
    def filter(self, record: logging.LogRecord) -> bool:
        if getattr(record, "event", None) != "swallowed_exception":
            return True
        payload = getattr(record, "payload", None)
        ctx = payload.get("context") if isinstance(payload, dict) else ""
        key = f"{record.name}|{ctx or ''}"
        with self._lock:
            if key not in self._counts and len(self._counts) >= self._MAX_KEYS:
                self._counts.pop(next(iter(self._counts)), None)
            count = self._counts.get(key, 0) + 1
            self._counts[key] = count
        over = count - self._BUDGET_PER_CONTEXT
        if over <= 0:
            return True
        if over % self._SUMMARY_EVERY:
            return False
        record.msg = (
            f"[FLOOD] 同源 swallowed_exception 已抑制 {over} 条: "
            f"{ctx or record.name}")
        record.args = ()
        base = payload if isinstance(payload, dict) else {}
        record.payload = {**base, "swallowed": True,
                          "context": ctx or "", "suppressed": over}
        return True
class _TestNoiseFilter(logging.Filter):
    def __init__(self, product_log: bool = False) -> None:
        super().__init__()
        self._product_log = product_log
        self._pytest_process = _in_pytest_process()
    def filter(self, record: logging.LogRecord) -> bool:
        if not (self._product_log
                and (_test_session_active or self._pytest_process)):
            return True
        event = getattr(record, "event", "")
        if event == TEST_CASE_EVENT:
            return False
        if record.levelno >= logging.WARNING:
            return event != "swallowed_exception"
        return event in ("test_session_start", "test_session_end")
class DuplicateMessageFilter(logging.Filter):
    _THRESHOLD = 3
    _SUMMARY_INTERVAL = 50
    _MAX_KEYS = 1024
    def __init__(self):
        super().__init__()
        self._counts: dict[str, int] = {}
        self._suppressed: dict[str, int] = {}
        self._evicted = 0
        self._cnt_lock = threading.Lock()
    def _evict_oldest_locked(self) -> None:
        oldest = next(iter(self._counts))
        self._counts.pop(oldest, None)
        self._suppressed.pop(oldest, None)
        self._evicted += 1
    def _message_snapshot(self, record: logging.LogRecord) -> str:
        orig = getattr(record, "_dedup_orig", None)
        if orig is not None:
            return orig
        try:
            orig = record.getMessage()[:200]
        except Exception as _msg_err:  # noqa: BLE001
            _LOGGER.debug(
                "DuplicateMessageFilter: getMessage 撕裂，降级原始 msg 快照: %s",
                _msg_err)
            orig = _safe_text(record.msg)[:200]
        record._dedup_orig = orig
        return orig
    def _dedup_key(self, record: logging.LogRecord, snapshot: str) -> str:
        key = f'{record.name}|{record.levelno}|{snapshot}'
        evt = getattr(record, "event", None)
        if evt is not None:
            key = (f'{key}|{evt}|'
                   f'{_payload_signature(getattr(record, "payload", None))}')
        return key
    def _consume_locked(self, key: str) -> tuple[bool, int]:
        with self._cnt_lock:
            if key not in self._counts and len(self._counts) >= self._MAX_KEYS:
                self._evict_oldest_locked()
            count = self._counts.get(key, 0)
            if count < self._THRESHOLD:
                self._counts[key] = count + 1
                return True, 0
            suppressed = self._suppressed.get(key, 0) + 1
            self._suppressed[key] = suppressed
            return False, suppressed
    def filter(self, record: logging.LogRecord) -> bool:
        if record.levelno < logging.WARNING:
            return True
        snapshot = self._message_snapshot(record)
        allowed, suppressed = self._consume_locked(
            self._dedup_key(record, snapshot))
        if allowed:
            return True
        if suppressed % self._SUMMARY_INTERVAL != 0:
            return False
        record.msg = f'[DEDUP] 已抑制 {suppressed} 次重复消息: {snapshot[:150]}'
        record.args = ()
        return True
def _validated_retain_ratio(value: float) -> float:
    if (not isinstance(value, (int, float))
            or isinstance(value, bool)
            or not 0.0 <= float(value) <= 1.0):
        raise ValueError(
            f"retain_ratio must be a real number in [0, 1], got: {value!r}")
    return value
class TruncatingFileHandler(BaseRotatingHandler):
    def __init__(self, filename: str, maxBytes: int = 0, encoding: str | None = None,
                 delay: bool = False, retain_ratio: float = 0.5) -> None:
        self._retain_ratio = _validated_retain_ratio(retain_ratio)
        self._lock_fd: int | None = None
        self._in_emit = False
        super().__init__(filename, "a", encoding=encoding, delay=delay,
                         errors="backslashreplace")
        self.maxBytes = maxBytes
    def _acquire_cross_process_lock(self) -> bool:
        if self._lock_fd is None:
            try:
                self._lock_fd = os.open(self.baseFilename + ".lock",
                                        os.O_CREAT | os.O_RDWR)
            except (OSError, ValueError, TypeError) as _lkf_err:
                _LOGGER.debug("TruncatingFileHandler: 锁文件创建失败，退化无锁直写: %s", _lkf_err)
                return False
        return _acquire_region_lock_with_retry(self._lock_fd)
    def _release_cross_process_lock(self) -> None:
        if self._lock_fd is not None:
            unlock_region(self._lock_fd)
    def _write_locked(self, record: logging.LogRecord) -> None:
        if not self.stream or getattr(self.stream, "closed", False):
            self.stream = self._open()
        if self.shouldRollover(record):
            self.doRollover()
        if not self.stream or getattr(self.stream, "closed", False):
            self.stream = self._open()
        self.stream.write(self.format(record) + self.terminator)
        self.flush()
    def emit(self, record: logging.LogRecord) -> None:
        if self._in_emit:
            return
        self._in_emit = True
        try:
            try:
                locked = self._acquire_cross_process_lock()
                try:
                    self._write_locked(record)
                finally:
                    if locked:
                        self._release_cross_process_lock()
            except RecursionError:
                raise
            except Exception:  # noqa: BLE001
                self.handleError(record)
        finally:
            self._in_emit = False
    def close(self) -> None:
        if self._lock_fd is not None:
            try:
                os.close(self._lock_fd)
            except OSError as exc:
                safe_stderr_write(
                    f"[log_config] TruncatingFileHandler 锁 fd 关闭失败: {exc}\n"
                )
            self._lock_fd = None
        super().close()
    def shouldRollover(self, record: logging.LogRecord) -> bool:
        if self.maxBytes > 0:
            try:
                msg = self.format(record) + self.terminator
                encoding = (getattr(self.stream, "encoding", None)
                            or self.encoding or "utf-8")
                errors = (getattr(self.stream, "errors", None)
                          or self.errors or "strict")
                if os.linesep != "\n":
                    msg = msg.replace("\n", os.linesep)
                msg_bytes = len(msg.encode(encoding, errors=errors))
                self.stream.seek(0, 2)
                if self.stream.tell() + msg_bytes > self.maxBytes:
                    return True
            except (OSError, ValueError, AttributeError) as _stat_err:
                _LOGGER.debug("shouldRollover: 日志文件状态检查失败，跳过本轮轮转: %s", _stat_err)
                return False
        return False
    def doRollover(self) -> None:
        self._close_current_stream()
        self._rewrite_tail_bytes()
        if not self.delay:
            try:
                self.stream = self._open()
            except Exception as _reopen_err:  # noqa: BLE001
                _LOGGER.warning("TruncatingFileHandler: 轮转后日志文件重开失败，日志通道降级: %s", _reopen_err)
                self.stream = None
    def _close_current_stream(self) -> None:
        if not self.stream:
            return
        try:
            self.stream.flush()
        except Exception as _flush_err:  # noqa: BLE001
            safe_stderr_write(
                f"[log_config] TruncatingFileHandler.doRollover flush failed (non-critical): {_flush_err}\n")
        try:
            self.stream.close()
        except Exception as _close_err:  # noqa: BLE001
            safe_stderr_write(
                f"[log_config] TruncatingFileHandler.doRollover close failed (non-critical): {_close_err}\n")
        self.stream = None
    def _rewrite_tail_bytes(self) -> None:
        try:
            cur = os.path.getsize(self.baseFilename)
            enc = self.encoding or "utf-8"
            keep_bytes = int(cur * self._retain_ratio)
            if keep_bytes <= 0:
                with open(self.baseFilename, "w", encoding=enc):
                    pass
            else:
                with open(self.baseFilename, "rb") as f:
                    start = max(cur - keep_bytes, 0)
                    previous = b"\n"
                    if start:
                        f.seek(start - 1)
                        previous = f.read(1)
                    f.seek(start)
                    tail = f.read().decode(enc, errors="replace")
                if previous != b"\n":
                    nl = tail.find("\n")
                    tail = tail[nl + 1:] if nl != -1 else ""
                with open(self.baseFilename, "w", encoding=enc,
                          errors=self.errors or "backslashreplace",
                          newline="") as f:
                    f.write(tail)
        except Exception as _rollover_err:  # noqa: BLE001
            safe_stderr_write(
                f"[log_config] TruncatingFileHandler.doRollover failed (non-critical): {_rollover_err}\n")
def now_iso_seconds() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%S")
def parse_log_ts(raw: str) -> datetime | None:
    if not isinstance(raw, str):
        logging.getLogger(__name__).debug("parse_log_ts: ts 非字符串输入 %r，归一为 None", raw)
        return None
    try:
        normalized = raw[:-1] + "+00:00" if raw.endswith("Z") else raw
        dt = datetime.fromisoformat(normalized)
        if dt.tzinfo is not None:
            dt = dt.astimezone().replace(tzinfo=None)
    except (ValueError, TypeError, OSError, OverflowError) as _e:
        logging.getLogger(__name__).debug("parse_log_ts: ts 解析/归一失败 %r: %s", raw, _e)
        return None
    return dt
def format_log_timestamp(dt: datetime, *, sep: str = "T") -> str:
    return (f"{dt.strftime('%Y-%m-%d')}{sep}"
            f"{dt.strftime('%H:%M:%S')}.{dt.microsecond // 1000:03d}")
def build_json_log_entry(
    *,
    level: str,
    logger: str,
    message: str,
    dt: datetime | None = None,
    phase: str | None = None,
    method_id: str | None = None,
    event: str | None = None,
    payload: Any = None,
) -> dict[str, Any]:
    now = dt if dt is not None else datetime.now()
    entry: dict[str, Any] = {
        "ts": format_log_timestamp(now),
        "level": level,
        "logger": logger,
    }
    if phase is not None:
        entry["phase"] = phase
    if method_id is not None:
        entry["method_id"] = method_id
    if event is not None:
        entry["event"] = event
    entry["message"] = message
    if payload is not None:
        entry["payload"] = payload
    return entry
def _lock_file_under_temp(path: str) -> str:
    try:
        from jwsgj.runtime_paths import artifact_lock_path
        return artifact_lock_path(path)
    except (ImportError, RuntimeError, ValueError, OSError) as _exc:
        _LOGGER.debug("锁文件落点解析失败，降级产物同目录: %s: %s", path, _exc)
        return path + ".lock"
def _lock_reentrancy_key(lock_path: str) -> str:
    try:
        return os.path.normcase(os.path.realpath(os.path.abspath(lock_path)))
    except (OSError, ValueError):
        return os.path.normcase(os.path.abspath(lock_path))
def _reentrant_held() -> dict[str, list[int]]:
    held = getattr(_REENTRANT_LOCK_STATE, "held", None)
    if held is None:
        held = {}
        _REENTRANT_LOCK_STATE.held = held
    return held
def _artifact_thread_lock(key: str) -> threading.RLock:
    with _ARTIFACT_THREAD_LOCKS_GUARD:
        lock = _ARTIFACT_THREAD_LOCKS.get(key)
        if lock is None:
            lock = threading.RLock()
            _ARTIFACT_THREAD_LOCKS[key] = lock
        return lock
def _acquire_jsonl_lock(path: str) -> tuple[int | None, bool]:
    lock_path = _lock_file_under_temp(path)
    try:
        os.makedirs(os.path.dirname(os.path.abspath(lock_path)), exist_ok=True)
    except (OSError, ValueError, TypeError):
        pass
    try:
        lock_fd = os.open(lock_path, os.O_CREAT | os.O_RDWR)
    except (OSError, ValueError, TypeError) as _lk_err:
        _LOGGER.debug(
            "append_jsonl_locked: 锁文件不可用，退化无锁直写 %s: %s",
            path, _lk_err)
        return None, False
    try:
        return lock_fd, _acquire_region_lock_with_retry(lock_fd)
    except (OSError, ValueError, TypeError) as _lk_err:
        _LOGGER.debug(
            "append_jsonl_locked: 锁文件不可用，退化无锁直写 %s: %s",
            path, _lk_err)
        return lock_fd, False
def _release_jsonl_lock(lock_fd: int | None, locked: bool) -> None:
    if lock_fd is None:
        return
    if locked:
        unlock_region(lock_fd)
    try:
        os.close(lock_fd)
    except OSError as exc:
        _LOGGER.debug("产物目录锁 fd 关闭失败（内核兜底）: %s", exc)
@contextmanager
def locked_artifact(path: str) -> Iterator[bool]:
    try:
        path = os.fsdecode(os.fspath(path))
    except (OSError, TypeError, ValueError) as _path_err:
        _LOGGER.debug("locked_artifact: 路径不可用（类型 %s），降级无锁: %s",
                      type(path).__name__, _path_err)
        yield False
        return
    key = _lock_reentrancy_key(_lock_file_under_temp(path))
    held = _reentrant_held()
    entry = held.get(key)
    if entry is not None:
        entry[0] += 1
        try:
            yield bool(entry[1])
        finally:
            entry[0] -= 1
            if entry[0] <= 0:
                held.pop(key, None)
        return
    thread_lock = _artifact_thread_lock(key)
    with thread_lock:
        lock_fd, locked = _acquire_jsonl_lock(path)
        held[key] = [1, 1 if locked else 0]
        try:
            yield locked
        finally:
            held.pop(key, None)
            _release_jsonl_lock(lock_fd, locked)
def append_jsonl_locked(path: str, line: str) -> bool:
    try:
        path = os.fsdecode(os.fspath(path))
    except (OSError, TypeError, ValueError) as _path_err:
        _LOGGER.warning("append_jsonl_locked: 路径不可用（类型 %s），留痕未落盘: %s",
                        type(path).__name__, _path_err)
        return False
    try:
        if isinstance(line, (bytes, bytearray)):
            line = bytes(line).decode("utf-8", errors="replace")
        elif not isinstance(line, str):
            line = str(line)
    except Exception as _line_err:  # noqa: BLE001
        _LOGGER.warning("append_jsonl_locked: 行内容不可归一（类型 %s），留痕未落盘: %s",
                        type(line).__name__, _line_err)
        return False
    payload = line if line.endswith("\n") else line + "\n"
    try:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        with locked_artifact(path) as locked:
            if not locked:
                _LOGGER.warning(
                    "append_jsonl_locked: 锁不可用，留痕未落盘: %s", path)
                return False
            separator = ""
            try:
                with open(path, "rb") as existing:
                    existing.seek(0, os.SEEK_END)
                    if existing.tell() > 0:
                        existing.seek(-1, os.SEEK_END)
                        last_byte = existing.read(1)
                        if (last_byte not in (b"\n", b"\r")
                                and not payload.startswith(("\n", "\r"))):
                            separator = "\n"
            except FileNotFoundError:
                pass
            with open(path, "a", encoding="utf-8",
                      errors="backslashreplace", newline="") as fh:
                fh.write(separator + payload)
                fh.flush()
        return True
    except (OSError, ValueError, TypeError, UnicodeError) as _io_err:
        _LOGGER.warning("append_jsonl_locked: 追加 %s 失败（留痕未落盘）: %s",
                        path, _io_err)
        return False
def _finite_float(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    try:
        num = float(value)
    except (TypeError, ValueError, OverflowError):
        return None
    return num if math.isfinite(num) else None
def _coerce_duration_ms(value: Any, tag: str) -> float | None:
    num = _finite_float(value)
    if num is None:
        _LOGGER.debug("%s: duration_ms 非有限数值（%r），按原值降级展示",
                      tag, value)
        return None
    return num
def _coerce_count(value: Any, tag: str) -> int:
    if value is None:
        return 0
    if isinstance(value, bool):
        _LOGGER.debug("%s: 计数入参为 bool（%r），按 0 降级留痕", tag, value)
        return 0
    try:
        count = int(value)
        if (not isinstance(value, (str, bytes, bytearray))
                and value != count):
            raise ValueError("fractional count")
    except (TypeError, ValueError, OverflowError):
        _LOGGER.debug("%s: 计数入参非整数（%r），按 0 降级留痕", tag, value)
        return 0
    if count < 0:
        _LOGGER.debug("%s: 计数入参为负（%r），按 0 降级留痕", tag, value)
        return 0
    return count
class JsonFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        payload = getattr(record, "payload", None)
        entry = build_json_log_entry(
            level=record.levelname,
            logger=record.name,
            message=record.getMessage(),
            dt=datetime.fromtimestamp(record.created),
            phase=getattr(record, "phase", None),
            method_id=getattr(record, "method_id", None),
            event=getattr(record, "event", None),
            payload=(sanitize_payload(payload)
                     if payload is not None else None),
        )
        for key in ("trace_id", "audit_seq"):
            val = getattr(record, key, None)
            if val is not None:
                entry[key] = val
        duration_ms = getattr(record, "duration_ms", None)
        if duration_ms is not None:
            _dur = _coerce_duration_ms(duration_ms, "JsonFormatter")
            if _dur is not None:
                entry["duration_ms"] = _dur
            elif isinstance(duration_ms, float) and not math.isfinite(duration_ms):
                entry["duration_ms"] = str(duration_ms)
            else:
                entry["duration_ms"] = duration_ms
        if record.exc_info:
            entry["exc_info"] = self.formatException(record.exc_info)
        if record.stack_info:
            entry["stack_info"] = self.formatStack(record.stack_info)
        return json.dumps(entry, ensure_ascii=False, default=str)
class HumanFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        msg = record.getMessage()
        _dt = datetime.fromtimestamp(record.created)
        prefix = f"{format_log_timestamp(_dt, sep=' ')} [{record.levelname}]"
        logger_name = record.name
        ctx = []
        for key in ("phase", "method_id", "event"):
            val = getattr(record, key, None)
            if val is not None:
                ctx.append(f"{key}={val}")
        duration_ms = getattr(record, "duration_ms", None)
        if duration_ms is not None:
            _dur = _coerce_duration_ms(duration_ms, "HumanFormatter")
            shown = f"{_dur:.1f}" if _dur is not None else str(duration_ms)
            ctx.append(f"duration_ms={shown}")
        suffix = f" ({', '.join(ctx)})" if ctx else ""
        exc_text = ""
        if record.exc_info:
            exc_text = "\n" + self.formatException(record.exc_info)
        stack_text = ""
        if record.stack_info:
            stack_text = "\n" + self.formatStack(record.stack_info)
        return f"{prefix} {logger_name}{suffix} {msg}{exc_text}{stack_text}"
_SENSITIVE_KEYWORDS = frozenset({
    "password", "passwd", "pwd", "token", "api_key", "apikey",
    "secret", "credential", "credentials", "cookie", "session", "auth",
    "access_key", "secret_key", "private_key", "ssh_key",
    "bearer", "authorization", "oauth", "refresh_token",
    "client_secret", "aws_secret", "azure_key",
})
_SENSITIVE_KEY_COMPACT = frozenset(
    skw.replace("_", "") for skw in _SENSITIVE_KEYWORDS
)
_SENSITIVE_KEY_MAX_PARTS = max(
    len(skw.split("_")) for skw in _SENSITIVE_KEYWORDS
)
_KEY_CAMEL_BOUNDARY_RE = re.compile(
    r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
def _key_tokens(key: Any) -> list:
    normalized = _KEY_CAMEL_BOUNDARY_RE.sub("_", str(key))
    return [t for t in re.split(r"[^a-z0-9]+", normalized.lower()) if t]
def _is_sensitive_key(key: Any) -> bool:
    key_tokens = _key_tokens(key)
    for start in range(len(key_tokens)):
        joined = ""
        for end in range(start, min(len(key_tokens),
                                    start + _SENSITIVE_KEY_MAX_PARTS)):
            joined += key_tokens[end]
            if joined in _SENSITIVE_KEY_COMPACT:
                return True
            # 复数键（passwords/apiKeys/secrets/cookies）与单数同义，
            # 只做尾部 s 归一，避免漏脱敏整组凭据。
            if (len(joined) > 1 and joined.endswith("s")
                    and joined[:-1] in _SENSITIVE_KEY_COMPACT):
                return True
    return False
_SANITIZE_MAX_ITEMS = 200
_SANITIZE_MAX_TEXT_CHARS = 2000
_MAX_SANITIZE_DEPTH = 10
def sanitize_payload(obj: Any, _depth: int = 0) -> Any:
    if _depth >= _MAX_SANITIZE_DEPTH:
        return "<max_depth>"
    if isinstance(obj, dict):
        return _sanitize_dict(obj, _depth)
    if isinstance(obj, (list, tuple, set, frozenset)):
        return _sanitize_seq(obj, _depth)
    return _sanitize_scalar(obj)
def _safe_text(obj: Any) -> str:
    try:
        return _escape_surrogates(str(obj))
    except Exception as _e:  # noqa: BLE001
        safe_stderr_write(f"[log_config] sanitize_payload str() failed: {_e}\n")
        return "<unserializable>"
_PAYLOAD_SIGNATURE_PREVIEW = 300
def _payload_signature(payload: Any, *,
                       limit: int | None = _PAYLOAD_SIGNATURE_PREVIEW) -> str:
    try:
        text = json.dumps(payload, sort_keys=True, default=str,
                          ensure_ascii=False)
    except Exception as _sig_err:  # noqa: BLE001
        _LOGGER.debug("payload signature: 序列化撕裂，降级安全文本: %s", _sig_err)
        text = _safe_text(payload)
    return text if limit is None else text[:limit]
def _sanitize_scalar(obj: Any) -> Any:
    if isinstance(obj, str):
        obj = _escape_surrogates(obj)
        if len(obj) <= _SANITIZE_MAX_TEXT_CHARS:
            return obj
        return obj[:_SANITIZE_MAX_TEXT_CHARS] + "..."
    if isinstance(obj, float) and not math.isfinite(obj):
        return str(obj)
    if isinstance(obj, (int, float, bool)) or obj is None:
        return obj
    text = _safe_text(obj)
    if len(text) <= _SANITIZE_MAX_TEXT_CHARS:
        return text
    return text[:_SANITIZE_MAX_TEXT_CHARS] + "..."
def _sanitize_dict(obj: dict, _depth: int) -> dict:
    items = list(islice(obj.items(), _SANITIZE_MAX_ITEMS))
    if len(obj) > _SANITIZE_MAX_ITEMS:
        items.append(("...truncated",
                      f"{len(obj) - _SANITIZE_MAX_ITEMS} more keys"))
    result = {}
    for k, v in items:
        key = (_safe_text(k)
               if not isinstance(k, (str, int, float)) and k is not None else k)
        key = _escape_surrogates(key)
        if _is_sensitive_key(key):
            result[key] = "***REDACTED***"
        else:
            result[key] = sanitize_payload(v, _depth + 1)
    return result
def _sanitize_seq(obj: Any, _depth: int) -> list:
    items = list(islice(obj, _SANITIZE_MAX_ITEMS))
    result = [sanitize_payload(v, _depth + 1) for v in items]
    if len(obj) > _SANITIZE_MAX_ITEMS:
        result.append(
            f"...truncated ({len(obj) - _SANITIZE_MAX_ITEMS} more items)")
    return result
def set_trace_id(trace_id: str) -> None:
    if trace_id is None:
        _trace_id_var.set(None)
        return
    text = str(trace_id)
    _trace_id_var.set(text if text.strip() else None)
def clear_trace_id() -> None:
    _trace_id_var.set(None)
def get_trace_id() -> str | None:
    return _trace_id_var.get()
_LOAD_DONE_PREFIX = "[ModuleLoad] 文件运行纳入统一日志: 模块加载完成（%d 项导出"
_test_session_active = False
def _in_pytest_process() -> bool:
    return any(name == "pytest" or name.startswith("_pytest")
               for name in sys.modules)
_module_load_tracing_lock = threading.Lock()
_traced_modules: set[str] = set()
_direct_run_seen: set[str] = set()
def _is_traced_module(fullname: str) -> bool:
    if not fullname.startswith("jwsgj."):
        return False
    _rest = fullname[len("jwsgj."):]
    return not (_rest == "tests" or _rest.startswith("tests."))
def _module_export_count(module: object, name: str) -> int:
    try:
        return len(getattr(module, "__all__", None) or ())
    except Exception:  # noqa: BLE001
        _LOGGER.debug("模块属性面异常（%s），导出数降级 0", name)
        return 0
def _safe_trace_register(registry: set, name: str) -> None:
    try:
        registry.add(name)
    except Exception as _reg_exc:  # noqa: BLE001
        _LOGGER.debug("留痕登记失败（防御面）: %s (%s)", name, _reg_exc)
class _TracingLoader:
    __slots__ = ("_in_exec", "_inner")
    def __init__(self, inner_loader) -> None:
        self._inner = inner_loader
        self._in_exec = False
    def create_module(self, spec):
        create = getattr(self._inner, "create_module", None)
        return create(spec) if create is not None else None
    def exec_module(self, module) -> None:
        _name = getattr(module, "__name__", "<unknown>")
        _t0 = time.monotonic()
        self._in_exec = True
        try:
            self._inner.exec_module(module)
        except BaseException as _exc:
            _emit_load_failure(
                _name, f"模块加载失败: {_exc.__class__.__name__}",
                duration_ms=(time.monotonic() - _t0) * 1000.0)
            raise
        finally:
            self._in_exec = False
        _emit_module_load(_name, _module_export_count(module, _name),
                          (time.monotonic() - _t0) * 1000.0)
    def get_code(self, fullname):
        try:
            _code = self._inner.get_code(fullname)
        except BaseException as _exc:
            if not self._in_exec:
                _emit_load_failure(
                    fullname,
                    f"文件直跑取码失败: {_exc.__class__.__name__}"
                    "（python -m 直跑形态）")
            raise
        if self._in_exec or not _is_traced_module(fullname):
            return _code
        _record_direct_run(fullname)
        return _code
    def __getattr__(self, name):
        return getattr(object.__getattribute__(self, "_inner"), name)
def _emit_load_info(name: str, exports: int, detail: str,
                    duration_ms: float) -> None:
    logging.getLogger(name).info(
        _LOAD_DONE_PREFIX + ", " + detail + "）",
        exports,
        extra={"event": "module_load", "duration_ms": duration_ms},
    )
def _emit_module_load(name: str, exports: int, elapsed_ms: float) -> None:
    logger = logging.getLogger(name)
    if name in _traced_modules:
        logger.debug(
            "[ModuleLoad] 模块重复 exec（同进程非首次加载）",
            extra={"event": "module_load_repeat",
                   "duration_ms": elapsed_ms},
        )
        return
    _emit_load_info(name, exports, f"{elapsed_ms:.1f}ms", elapsed_ms)
    _safe_trace_register(_traced_modules, name)
def _emit_load_failure(name: str, message: str,
                      duration_ms: float = _DEFAULT_DURATION_MS) -> None:
    logging.getLogger(name).exception(
        message, extra={"event": "module_load_failure",
                        "duration_ms": duration_ms})
def _record_direct_run(fullname: str) -> None:
    payload = sanitize_payload({"entry": "__main__", "run_mode": "python -m",
                                "argc": max(0, len(sys.argv) - 1)})
    logger = logging.getLogger(fullname)
    if fullname in _direct_run_seen:
        logger.debug("[ModuleLoad] 文件直跑重复取码（同进程非首次）",
                     extra={"event": "module_run_repeat", "payload": payload})
        return
    logger.info(
        "module_run: %s.__main__ outcome=direct_run（python -m 直跑）",
        fullname,
        extra={"event": "module_run", "payload": payload},
    )
    _safe_trace_register(_direct_run_seen, fullname)
class _ModuleLoadTracer(importlib.abc.MetaPathFinder):
    _JWSGJ_MODULE_TRACER = True
    def find_spec(self, fullname, path=None, target=None):
        if not _is_traced_module(fullname):
            return None
        for finder in sys.meta_path:
            if (finder is self
                    or getattr(finder, "_JWSGJ_MODULE_TRACER", False)):
                continue
            spec = finder.find_spec(fullname, path, target)
            if spec is None:
                continue
            if getattr(spec, "loader", None) is not None:
                spec.loader = _TracingLoader(spec.loader)
            return spec
        return None
def _has_module_load_tracer() -> bool:
    return any(getattr(f, "_JWSGJ_MODULE_TRACER", False)
               for f in sys.meta_path)
def _backfill_loaded_module_traces() -> int:
    n = 0
    try:
        for _name in sorted(sys.modules):
            if (_name in _traced_modules
                    or not _is_traced_module(_name)):
                continue
            if _backfill_one_module(_name):
                n += 1
    except Exception as _e:  # noqa: BLE001
        safe_stderr_write(
            f"[log_config] module load backfill failed: {_e}\n")
    return n
def _backfill_one_module(name: str) -> bool:
    module = sys.modules.get(name)
    if module is None:
        return False
    _emit_load_info(name, _module_export_count(module, name), "补录", 0.0)
    _traced_modules.add(name)
    return True
def install_module_load_tracing() -> bool:
    with _module_load_tracing_lock:
        if _has_module_load_tracer():
            return False
        try:
            sys.meta_path.insert(0, _ModuleLoadTracer())
        except Exception as _e:  # noqa: BLE001
            safe_stderr_write(
                f"[log_config] module load tracing install failed: {_e}\n")
            return False
        _backfill_loaded_module_traces()
        return True
def _under_root(path_real: str, root: str) -> bool:
    try:
        root_real = os.path.normcase(os.path.realpath(root))
    except (OSError, ValueError):
        return False
    return path_real == root_real or path_real.startswith(root_real + os.sep)
def _under_system_temp(path_real: str) -> bool:
    try:
        tmp_real = os.path.normcase(os.path.realpath(tempfile.gettempdir()))
    except (OSError, ValueError) as _tmp_err:
        logging.getLogger(__name__).debug(
            "[log_config] 系统临时根归一失败（按非临时根判定）: %s", _tmp_err)
        return False
    return (path_real == tmp_real
            or path_real.startswith(tmp_real + os.sep))
def _validate_log_dir_destination(normalized: str) -> str:
    try:
        path_real = os.path.normcase(os.path.realpath(normalized))
    except (OSError, ValueError) as _path_err:
        raise RuntimeError(
            f"{LOG_DIR_ENV_VAR}={normalized!r} 不是可用路径: {_path_err}"
        ) from _path_err
    if _under_root(path_real, _SKILL_ROOT):
        return normalized
    if _under_system_temp(path_real):
        return normalized
    workspace = os.environ.get("WORKSPACE_DIR", "").strip()
    if workspace and _under_root(path_real, workspace):
        return normalized
    raise RuntimeError(
        f"{LOG_DIR_ENV_VAR}={normalized!r} 不在日志归口内"
        f"（归口：治理包根 {_SKILL_ROOT!r}，默认落点"
        f" {os.path.join(_SKILL_ROOT, 'log')!r}），"
        "日志覆盖只服务测试会话/临时探针，只能指向治理包根、系统临时根"
        "或当前会话工作空间（不设其他位置兜底）")
def _require_absolute_log_dir(raw: str, source: str) -> str:
    normalized = os.path.normpath(str(raw))
    if not os.path.isabs(normalized):
        raise ValueError(
            f"{source}={raw!r} 必须是绝对路径（日志落点）；"
            f"相对路径会被拼接到当前目录（cwd={os.getcwd()!r}），"
            "导致日志落出统一归口且跨进程不可复现")
    return normalized
def _resolve_log_dir_override() -> str | None:
    raw = os.environ.get(LOG_DIR_ENV_VAR, "").strip()
    if not raw:
        return None
    return _validate_log_dir_destination(
        _require_absolute_log_dir(raw, LOG_DIR_ENV_VAR))
def _normalize_optional_log_dir(log_dir: str | None) -> str | None:
    if log_dir is None or not str(log_dir).strip():
        return None
    return _require_absolute_log_dir(log_dir, "log_dir")
def _default_log_dir() -> str | None:
    override = _resolve_log_dir_override()
    if override is not None:
        return override
    return os.path.join(_SKILL_ROOT, "log")
_configured = False
_handlers: list[logging.Handler] = []
_log_dir: str | None = None
_setup_fingerprint: tuple[Any, ...] | None = None
_setup_lock = threading.Lock()
_MAIN_HANDLER_NAME = "jwsgj_main"
_CONSOLE_HANDLER_NAME = "jwsgj_console"
_JWSGJ_HANDLER_NAMES = {_MAIN_HANDLER_NAME, _CONSOLE_HANDLER_NAME}
class _LogSetupOptions(NamedTuple):
    log_dir: str | None
    level: int
    json: bool
    console: bool
    audit: bool
    perf: bool
    force: bool
def setup_logging(
    log_dir: str | None = None,
    level: int = DEFAULT_LEVEL,
    json: bool = True,
    console: bool = False,
    audit: bool = True,
    perf: bool = True,
    force: bool = False,
) -> str | None:
    log_dir = _normalize_optional_log_dir(log_dir)
    with _setup_lock:
        return _setup_logging_inner(
            _LogSetupOptions(log_dir=log_dir, level=level, json=json,
                             console=console, audit=audit, perf=perf,
                             force=force))
def _ensure_configured() -> None:
    if not _configured:
        setup_logging()
def _resolve_target_log_dir(log_dir: str | None) -> str | None:
    resolved = (_validate_log_dir_destination(log_dir)
                if log_dir else _default_log_dir())
    if resolved is None:
        return None
    try:
        os.makedirs(resolved, exist_ok=True)
    except (OSError, ValueError) as _e:
        _LOGGER.warning("setup_logging: makedirs(%s) failed: %s, disabling file logging", resolved, _e)
        return None
    return resolved
def _close_handler_quietly(handler: logging.Handler, tag: str) -> None:
    try:
        handler.close()
    except Exception as _e:  # noqa: BLE001
        safe_stderr_write(f"[log_config] {tag} handler close failed: {_e}\n")
def _detach_handlers(root: logging.Logger,
                     handlers: list[logging.Handler], tag: str) -> None:
    for h in handlers:
        try:
            root.removeHandler(h)
        except ValueError as _e:
            safe_stderr_write(f"[log_config] {tag} removeHandler failed: {_e}\n")
        _close_handler_quietly(h, tag)
def _teardown_tracked_handlers(root: logging.Logger, tag: str) -> None:
    _detach_handlers(root, list(_handlers), tag)
    _handlers.clear()
def _purge_stale_handlers(root: logging.Logger) -> None:
    _stale = [h for h in list(root.handlers)
              if h.name in _JWSGJ_HANDLER_NAMES]
    for h in _stale:
        try:
            root.removeHandler(h)
        except ValueError as _rm_err:
            safe_stderr_write(
                f"[log_config] stale removeHandler failed: {_rm_err}\n")
        _close_handler_quietly(h, "stale")
_MAIN_HANDLER_OPEN_ATTEMPTS = 5
_MAIN_HANDLER_OPEN_BACKOFF_S = 0.05
def _open_main_handler(log_path: str) -> TruncatingFileHandler:
    last_error: OSError | None = None
    for attempt in range(_MAIN_HANDLER_OPEN_ATTEMPTS):
        try:
            return TruncatingFileHandler(
                log_path, maxBytes=MAX_BYTES, encoding="utf-8")
        except OSError as _open_err:
            last_error = _open_err
            if attempt + 1 < _MAIN_HANDLER_OPEN_ATTEMPTS:
                time.sleep(_MAIN_HANDLER_OPEN_BACKOFF_S * (attempt + 1))
    if last_error is None:
        raise OSError(f"主日志处理器打开失败（无底层异常）: {log_path}")
    raise last_error
def _install_main_and_console_handlers(root: logging.Logger,
                                       log_dir: str | None, json: bool,
                                       console: bool) -> bool:
    file_handler_failed = False
    if log_dir is not None:
        try:
            mh = _open_main_handler(
                os.path.join(log_dir, MAIN_LOG_FILE),
            )
            mh.set_name(_MAIN_HANDLER_NAME)
            mh.setFormatter(JsonFormatter() if json else HumanFormatter())
            mh.addFilter(_TestNoiseFilter(
                product_log=(os.path.normcase(os.path.realpath(log_dir))
                             == os.path.normcase(
                                 os.path.realpath(
                                     os.path.join(_SKILL_ROOT, "log"))))))
            root.addHandler(mh)
            _handlers.append(mh)
        except (OSError, ValueError) as _e:
            safe_stderr_write(f"[log_config] main log handler creation failed: {_e}\n")
            file_handler_failed = True
    if console:
        ch = logging.StreamHandler()
        ch.set_name(_CONSOLE_HANDLER_NAME)
        ch.setFormatter(HumanFormatter())
        root.addHandler(ch)
        _handlers.append(ch)
    return file_handler_failed
_HANDLER_FILTER_TYPES = (
    _NamespaceAttributionFilter,
    _SwallowedFloodFilter,
    TraceIdFilter,
    _SurrogateSafeFilter,
    DuplicateMessageFilter,
)
def _attach_handler_filters() -> None:
    for handler in _handlers:
        for filter_type in _HANDLER_FILTER_TYPES:
            if not any(isinstance(f, filter_type) for f in handler.filters):
                handler.addFilter(filter_type())
def _install_runtime_hooks() -> None:
    for _install, _name in (
        (install_exception_logging, "install_exception_logging"),
        (install_module_load_tracing, "install_module_load_tracing"),
    ):
        try:
            _install()
        except Exception as _e:  # noqa: BLE001
            safe_stderr_write(f"[log_config] {_name} failed: {_e}\n")
def _resolved_log_dir_for_fingerprint(log_dir: str | None) -> str | None:
    return os.path.abspath(log_dir) if log_dir else _default_log_dir()
def _setup_fingerprint_of(log_dir: str | None,
                          opts: _LogSetupOptions) -> tuple[Any, ...]:
    return (
        os.path.abspath(log_dir) if log_dir else "",
        bool(opts.json),
        bool(opts.console),
        bool(opts.audit),
        bool(opts.perf),
    )
def _idempotent_fastpath_hit(force: bool,
                             fingerprint: tuple[Any, ...]) -> str | None:
    root = logging.getLogger()
    main_handler_ready = any(
        getattr(handler, "name", "") == _MAIN_HANDLER_NAME
        and handler in root.handlers
        for handler in _handlers
    )
    tracked_ready = all(handler in root.handlers for handler in _handlers)
    if (_configured and not force and _log_dir is not None
            and main_handler_ready and tracked_ready
            and fingerprint == _setup_fingerprint):
        return _log_dir
    return None
def _degraded_regime(force: bool) -> bool:
    return _configured and not force and _log_dir is None
def _setup_logging_inner(opts: _LogSetupOptions) -> str | None:
    global _configured, _log_dir, _setup_fingerprint
    log_dir = (opts.log_dir if opts.log_dir is not None
               else (_log_dir if _configured else None))
    force = opts.force
    fingerprint = _setup_fingerprint_of(
        _resolved_log_dir_for_fingerprint(log_dir), opts)
    fast_path_hit = _idempotent_fastpath_hit(force, fingerprint)
    if fast_path_hit is not None:
        logging.getLogger().setLevel(opts.level)
        _attach_handler_filters()
        return fast_path_hit
    log_dir = _resolve_target_log_dir(log_dir)
    degraded_regime = _degraded_regime(force)
    root = logging.getLogger()
    root.setLevel(opts.level)
    if not any(isinstance(f, _SurrogateSafeFilter) for f in root.filters):
        root.addFilter(_SurrogateSafeFilter())
    if force:
        _teardown_tracked_handlers(root, "rebuild")
    if degraded_regime and log_dir is not None:
        _teardown_tracked_handlers(root, "degraded-recovery")
    if _rebuild_handlers_if_needed(root, log_dir, opts.json, opts.console):
        _LOGGER.warning(
            "主日志文件处理器创建失败（%s；日志目录仍按 %s 记账）",
            "文件通道不可用，仅保留控制台" if opts.console
            else "文件通道与控制台均不可用，仅 lastResort 输出",
            log_dir)
    logging.getLogger("jwsgj.audit").propagate = bool(opts.audit)
    logging.getLogger("jwsgj.perf").propagate = bool(opts.perf)
    _attach_handler_filters()
    _configured = True
    _log_dir = log_dir
    _setup_fingerprint = fingerprint
    _install_runtime_hooks()
    return log_dir
def _handler_shape_matches(root: logging.Logger, use_json: bool,
                           console: bool, expect_main: bool) -> bool:
    tracked = [h for h in _handlers if h in root.handlers]
    main = next((h for h in tracked
                 if getattr(h, "name", "") == _MAIN_HANDLER_NAME), None)
    want_formatter = JsonFormatter if use_json else HumanFormatter
    if expect_main:
        if main is None or not isinstance(main.formatter, want_formatter):
            return False
    elif main is not None:
        return False
    console_handlers = [h for h in tracked
                        if getattr(h, "name", "") == _CONSOLE_HANDLER_NAME]
    if bool(console_handlers) != bool(console):
        return False
    return all(isinstance(h.formatter, HumanFormatter)
               for h in console_handlers)
def _rebuild_handlers_if_needed(root: logging.Logger,
                                 log_dir: str | None, use_json: bool,
                                 console: bool) -> bool:
    if _handlers:
        if not _configured:
            same_dir = True
        elif _log_dir is None or log_dir is None:
            same_dir = _log_dir is None and log_dir is None
        else:
            same_dir = (os.path.normcase(os.path.abspath(log_dir))
                        == os.path.normcase(os.path.abspath(_log_dir)))
        if same_dir and _handler_shape_matches(
                root, use_json, console, log_dir is not None):
            return False
        _teardown_tracked_handlers(root, "handler-rebuild")
    _purge_stale_handlers(root)
    return _install_main_and_console_handlers(root, log_dir, use_json, console)
def get_log_dir() -> str | None:
    _ensure_configured()
    return _log_dir
def _skill_root_module_stem(file_path: str) -> str | None:
    try:
        real_file = os.path.realpath(file_path)
        if (real_file.endswith(".py")
                and os.path.normcase(os.path.dirname(real_file))
                == os.path.normcase(os.path.realpath(_SKILL_ROOT))):
            stem = os.path.splitext(os.path.basename(real_file))[0]
            return f"jwsgj.{stem}"
    except Exception as _e:  # noqa: BLE001
        _LOGGER.debug("get_module_logger: __main__ 锚点反推失败，保持原语义: %s", _e)
    return None
def _main_module_candidates(module_file: str | None) -> list[str]:
    candidates: list[str] = [module_file] if module_file else []
    main_file = _main_module_path()
    if main_file:
        candidates.append(main_file)
    return candidates
def get_module_logger(name: str,
                       module_file: str | None = None) -> logging.Logger:
    if name != "__main__":
        return logging.getLogger(name)
    for cand in _main_module_candidates(module_file):
        stem = _skill_root_module_stem(cand)
        if stem is not None:
            return logging.getLogger(stem)
    return logging.getLogger(name)
_AUDIT_JSONL_MAX_BYTES = 16 * 1024 * 1024
_audit_jsonl_lock = threading.Lock()
_audit_dedup_cache: dict[str, float] = {}
_AUDIT_PROC_ID = f"{os.getpid()}-{int(time.time() * 1000)}"
_audit_seq_pid = os.getpid()
_audit_seq_lock = threading.Lock()
_audit_seq_counter = 0
_audit_dedup_lock = threading.Lock()
_AUDIT_DEDUP_WINDOW = 2.0
_AUDIT_DEDUP_CACHE_SOFT_LIMIT = 200
_AUDIT_DEDUP_CACHE_HARD_LIMIT = 1000
def _next_audit_seq() -> str:
    global _AUDIT_PROC_ID, _audit_seq_pid, _audit_seq_counter
    with _audit_seq_lock:
        pid = os.getpid()
        if pid != _audit_seq_pid:
            _audit_seq_pid = pid
            _AUDIT_PROC_ID = f"{pid}-{int(time.time() * 1000)}"
            _audit_seq_counter = 0
        _audit_seq_counter += 1
        return f"{_AUDIT_PROC_ID}-{_audit_seq_counter}"
def _tail_lines_within_budget(lines: list[str], keep_budget: int) -> list[str]:
    kept: list[str] = []
    size = 0
    for ln in reversed(lines):
        sz = len(ln.encode("utf-8", errors="replace"))
        if kept and size + sz > keep_budget:
            break
        if not kept and sz > keep_budget:
            continue
        kept.append(ln)
        size += sz
    kept.reverse()
    return kept
def _jsonl_needs_prune(path: str, max_bytes: int) -> bool:
    try:
        return os.path.getsize(path) > max_bytes
    except (OSError, ValueError, TypeError):
        _LOGGER.debug("prune_jsonl_file: 状态检查失败，跳过裁剪: %r", path)
        return False
def _read_jsonl_lines(path: str) -> list[str] | None:
    try:
        with open(path, encoding="utf-8-sig", errors="replace",
                  newline="") as f:
            lines = f.readlines()
    except (OSError, ValueError, TypeError):
        _LOGGER.debug("prune_jsonl_file: 读取失败，跳过裁剪: %r", path)
        return None
    return lines or None
def _rewrite_jsonl_atomically(path: str, kept: list[str]) -> None:
    tmp = f"{path}.prune_tmp.{os.getpid()}.{threading.get_ident()}"
    try:
        with open(tmp, "w", encoding="utf-8", newline="") as tf:
            tf.writelines(kept)
        os.replace(tmp, path)
    except OSError:
        _LOGGER.warning("prune_jsonl_file: 裁剪落盘失败（保留原文件）: %s", path)
        try:
            os.unlink(tmp)
        except OSError as _tmp_err:
            _LOGGER.debug("prune_jsonl_file: 裁剪临时文件清理失败: %s: %s",
                          tmp, _tmp_err)
def prune_jsonl_file(path: str, max_bytes: int) -> None:
    try:
        path = os.fsdecode(os.fspath(path))
    except (OSError, TypeError, ValueError) as _path_err:
        _LOGGER.debug("prune_jsonl_file: 路径不可用（类型 %s），跳过裁剪: %s",
                      type(path).__name__, _path_err)
        return
    max_bytes = _coerce_count(max_bytes, "prune_jsonl_file")
    if max_bytes <= 0:
        _LOGGER.debug("prune_jsonl_file: 预算非正（%r），跳过裁剪: %s",
                      max_bytes, path)
        return
    if not _jsonl_needs_prune(path, max_bytes):
        return
    with locked_artifact(path) as locked:
        if not locked:
            _LOGGER.debug("prune_jsonl_file: 锁不可用，跳过裁剪: %s", path)
            return
        if not _jsonl_needs_prune(path, max_bytes):
            return
        lines = _read_jsonl_lines(path)
        if lines is None:
            return
        kept = _tail_lines_within_budget(lines, max_bytes * 2 // 3)
        _rewrite_jsonl_atomically(path, kept)
def _prune_audit_jsonl(path: str) -> None:
    with _audit_jsonl_lock:
        prune_jsonl_file(path, _AUDIT_JSONL_MAX_BYTES)
def _evict_dedup_cache(now: float) -> None:
    if len(_audit_dedup_cache) > _AUDIT_DEDUP_CACHE_SOFT_LIMIT:
        expired = [k for k, t in _audit_dedup_cache.items()
                   if now - t > _AUDIT_DEDUP_WINDOW * 10]
        for k in expired:
            del _audit_dedup_cache[k]
        if len(_audit_dedup_cache) > _AUDIT_DEDUP_CACHE_HARD_LIMIT:
            oldest = sorted(_audit_dedup_cache,
                            key=_audit_dedup_cache.get)
            for k in oldest[:len(_audit_dedup_cache)
                           - _AUDIT_DEDUP_CACHE_HARD_LIMIT]:
                del _audit_dedup_cache[k]
def _audit_dedup_admit(sig: str, now: float) -> bool:
    with _audit_dedup_lock:
        _evict_dedup_cache(now)
        if sig in _audit_dedup_cache and now - _audit_dedup_cache[sig] < _AUDIT_DEDUP_WINDOW:
            return False
        _audit_dedup_cache[sig] = now
        return True
def _audit_dedup_rollback(sig: str, admitted_at: float) -> None:
    with _audit_dedup_lock:
        if _audit_dedup_cache.get(sig) == admitted_at:
            _audit_dedup_cache.pop(sig, None)
def write_audit(event: str, **payload: Any) -> None:
    try:
        _ensure_configured()
    except Exception as _cfg_err:  # noqa: BLE001
        _LOGGER.warning("write_audit: 日志配置不可用（%s），审计降级尝试落盘",
                        _cfg_err)
    audit_payload = sanitize_payload(payload)
    trace_id = get_trace_id()
    sig = (f"{os.getpid()}:{trace_id or ''}:{event}:"
           f"{_payload_signature(audit_payload, limit=None)}")
    admitted_at = time.monotonic()
    if not _audit_dedup_admit(sig, admitted_at):
        return
    audit_seq = _next_audit_seq()
    lg = logging.getLogger("jwsgj.audit")
    try:
        lg.info(
            "audit:%s",
            event,
            extra={
                "event": event,
                "payload": audit_payload,
                "audit_seq": audit_seq,
            },
        )
    except Exception:  # noqa: BLE001
        _LOGGER.debug("write_audit emit failed for %s", event)
    written = _append_audit_jsonl(
        event, audit_payload, audit_seq, trace_id)
    if not written:
        _audit_dedup_rollback(sig, admitted_at)
def _append_audit_jsonl(event: str, audit_payload: dict,
                          audit_seq: str, trace_id: str | None) -> bool:
    try:
        dt = datetime.now()
        entry = {
            "ts": format_log_timestamp(dt),
            "level": "INFO",
            "logger": "jwsgj.audit",
            "event": event,
            "payload": audit_payload,
            "audit_seq": audit_seq,
        }
        if trace_id:
            entry["trace_id"] = trace_id
        audit_path = os.path.join(get_log_dir(), AUDIT_FILE)
        line = json.dumps(entry, ensure_ascii=False, default=str)
        if not append_jsonl_locked(audit_path, line):
            _LOGGER.warning("write_audit jsonl append failed for %s", event)
            return False
    except Exception:
        _LOGGER.warning("write_audit jsonl append failed for %s", event, exc_info=True)
        return False
    try:
        _prune_audit_jsonl(audit_path)
    except Exception:
        _LOGGER.warning("write_audit jsonl prune failed for %s", event, exc_info=True)
    return True
def safe_write_audit(event: str, **payload: Any) -> None:
    try:
        write_audit(event, **payload)
    except Exception:
        _LOGGER.warning("write_audit failed for %s", event, exc_info=True)
def _emit_event(logger_name: str, event: str, message: str,
                *msg_args: Any, payload: dict[str, Any]) -> None:
    try:
        _ensure_configured()
        logging.getLogger(logger_name).warning(message, *msg_args, extra={
            "event": event,
            "payload": sanitize_payload(payload),
        })
    except Exception:  # noqa: BLE001
        _LOGGER.debug("_emit_event 留痕失败（不阻断调用方）: %s", event)
def perf_trace(phase: str, duration_ms: float, **ctx: Any) -> None:
    try:
        _ensure_configured()
        extra: dict[str, Any] = {
            "phase": phase,
            "payload": sanitize_payload(ctx),
            "event": "perf",
        }
        duration = _coerce_duration_ms(duration_ms, "perf_trace")
        if duration is not None:
            extra["duration_ms"] = duration
        logging.getLogger("jwsgj.perf").info(
            "perf:%s", phase, extra=extra)
    except Exception:  # noqa: BLE001
        _LOGGER.debug("perf_trace emit failed for %s", phase)
class Stopwatch:
    __slots__ = ("_started_at",)
    def __init__(self) -> None:
        self._started_at = time.monotonic()
    def elapsed_ms(self) -> float:
        return (time.monotonic() - self._started_at) * 1000.0
def timed_log(name: str | None = None) -> Callable:
    def deco(fn):
        if inspect.iscoroutinefunction(fn):
            @wraps(fn)
            async def async_wrapper(*args, **kwargs):
                start = time.perf_counter()
                try:
                    return await fn(*args, **kwargs)
                finally:
                    perf_trace(name or fn.__name__,
                               (time.perf_counter() - start) * 1000.0,
                               function=fn.__name__)
            return async_wrapper
        @wraps(fn)
        def wrapper(*args, **kwargs):
            start = time.perf_counter()
            try:
                return fn(*args, **kwargs)
            finally:
                perf_trace(name or fn.__name__,
                           (time.perf_counter() - start) * 1000.0,
                           function=fn.__name__)
        return wrapper
    return deco
class _PerfCtx:
    def __init__(self, phase: str) -> None:
        self.phase = phase
@contextmanager
def perf_scope(phase: str, **ctx: Any) -> Iterator[Any]:
    start = time.perf_counter()
    try:
        yield _PerfCtx(phase)
    finally:
        perf_trace(**{
            "function": "perf_scope",
            **ctx,
            "phase": phase,
            "duration_ms": (time.perf_counter() - start) * 1000.0,
        })
def _safe_exc_text(exc: BaseException) -> tuple[str, str]:
    exc_type = type(exc).__name__
    try:
        return exc_type, str(exc)
    except Exception:  # noqa: BLE001
        _LOGGER.debug("log_swallowed 异常不可字符串化，按类型留痕: %s", exc_type)
        return exc_type, "<exception str() failed>"
def log_swallowed(module: str, exc: BaseException, context: str = "") -> None:
    exc_type, exc_message = _safe_exc_text(exc)
    _emit_event(
        module, "swallowed_exception",
        "已捕获但未处理的异常: %s: %s%s",
        exc_type, exc_message, f" ({context})" if context else "",
        payload={
            "swallowed": True,
            "exc_type": exc_type,
            "exc_message": exc_message,
            "context": context,
        },
    )
def emit_fix_logs(logs: list[str], logger: logging.Logger, *,
                  prefix: str,
                  skip_prefixes: tuple[str, ...] = (),
                  warn_prefixes: tuple[str, ...] = ()) -> None:
    for entry in logs:
        if skip_prefixes and entry.startswith(skip_prefixes):
            continue
        if warn_prefixes and entry.startswith(warn_prefixes):
            logger.warning("%s: %s", prefix, entry)
            continue
        logger.info("%s: %s", prefix, entry)
def observation_gate(label: str) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    def decorate(func: Callable[..., Any]) -> Callable[..., Any]:
        def log_failure(exc: Exception) -> None:
            logging.getLogger(func.__module__ or __name__).warning(
                "[gate] %s error: %s", label, exc)
        if inspect.iscoroutinefunction(func):
            @wraps(func)
            async def async_wrapper(*args: Any, **kwargs: Any) -> Any:
                try:
                    return await func(*args, **kwargs)
                except Exception as exc:  # noqa: BLE001
                    log_failure(exc)
            return async_wrapper
        @wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            try:
                return func(*args, **kwargs)
            except Exception as exc:  # noqa: BLE001
                log_failure(exc)
        return wrapper
    return decorate
_SECTION_DEGRADED: contextvars.ContextVar[dict[str, int] | None] = (
    contextvars.ContextVar('section_degraded', default=None))
def mark_section_degraded(section: str) -> None:
    current = dict(_SECTION_DEGRADED.get() or {})
    current[section] = current.get(section, 0) + 1
    _SECTION_DEGRADED.set(current)
def collect_and_reset_degraded() -> dict[str, int]:
    snapshot = dict(_SECTION_DEGRADED.get() or {})
    _SECTION_DEGRADED.set({})
    return snapshot
@contextmanager
def degraded_section(label: str):
    try:
        yield
    except Exception:
        _LOGGER.warning('%s段执行异常，跳过', label, exc_info=True)
        mark_section_degraded(label)
def _coerce_event_items(value: Any) -> list:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set, frozenset)):
        return list(value)
    if isinstance(value, Iterator):
        return list(value)
    return [value]
def _coerce_event_mapping(value: Any, tag: str) -> dict:
    if not value:
        return {}
    try:
        return dict(value)
    except (TypeError, ValueError) as _map_err:
        _LOGGER.debug("%s: 载荷映射不可转换（%r），降级空表: %s",
                      tag, value, _map_err)
        return {}
def write_bug_intercept(check_id: str, severity: str, filepath: str = "",
                        line: int = 0, **payload: Any) -> None:
    _emit_event(
        "jwsgj.bug_intercept", "bug_intercept",
        "BUG 拦截: %s (%s)", check_id, severity,
        payload={
            **payload,
            "check_id": check_id,
            "severity": severity,
            "file": filepath,
            "line": _coerce_count(line, "write_bug_intercept"),
        },
    )
def write_detector_liveness(probed: int = 0, alive: int = 0,
                            dead_rules: list | None = None,
                            dead_ratio: float = 0.0,
                            penalty_eligible: bool = False,
                            **payload: Any) -> None:
    dead = _coerce_event_items(dead_rules)
    probed_count = _coerce_count(probed, "write_detector_liveness")
    ratio = _finite_float(dead_ratio)
    _emit_event(
        "jwsgj.detector_liveness", "detector_liveness",
        "检测器活性探针: %d/%d 失效", len(dead), probed_count,
        payload={
            **payload,
            "probed": probed_count,
            "alive": _coerce_count(alive, "write_detector_liveness"),
            "dead_rules": dead,
            "dead_ratio": ratio if ratio is not None else 0.0,
            "penalty_eligible": penalty_eligible,
        },
    )
def write_defense_feedback(
    contradiction_count: int = 0,
    fix_safety_count: int = 0,
    regression_status: str = "",
    recommendations: list | None = None,
    by_category: dict | None = None,
    **payload: Any,
) -> None:
    contradictions = _coerce_count(contradiction_count, "write_defense_feedback")
    status = str(regression_status or "")
    _emit_event(
        "jwsgj.defense_feedback", "defense_feedback",
        "防御反馈: 矛盾 %d, 回归=%s",
        contradictions, status or "n/a",
        payload={
            **payload,
            "contradiction_count": contradictions,
            "fix_safety_count": _coerce_count(
                fix_safety_count, "write_defense_feedback"),
            "regression_status": status,
            "recommendations": _coerce_event_items(recommendations),
            "by_category": _coerce_event_mapping(
                by_category, "write_defense_feedback"),
        },
    )
_DEFAULT_MODULE_RUN_OUTCOME = "ok"
def write_module_run(
        module: str, entry: str, outcome: str = _DEFAULT_MODULE_RUN_OUTCOME,
        duration_ms: float | None = None,
        **payload: Any) -> None:
    try:
        _ensure_configured()
        _extra: dict[str, Any] = {"event": "module_run",
                                  "payload": sanitize_payload(payload)}
        if duration_ms is not None:
            duration = _coerce_duration_ms(duration_ms, "write_module_run")
            if duration is not None:
                _extra["duration_ms"] = duration
        logging.getLogger(f"jwsgj.{module}").info(
            "module_run: %s.%s outcome=%s", module, entry, outcome,
            extra=_extra)
    except Exception:  # noqa: BLE001
        _LOGGER.debug("write_module_run emit failed for %s.%s", module, entry)
def trace_module_run(module: str, entry: str, started_at: float,
                     outcome: str = _DEFAULT_MODULE_RUN_OUTCOME,
                     **payload: Any) -> None:
    write_module_run(module, entry, outcome=outcome,
                     duration_ms=(time.monotonic() - started_at) * 1000.0,
                     **payload)
_TEST_LOGGER = logging.getLogger("jwsgj.test")
_SLOW_CASE_MS = 2000.0
_TEST_FLUSH_THRESHOLD = 200
_TEST_BUFFER_KEEP_MAX = _TEST_FLUSH_THRESHOLD * 2
_TEST_MESSAGE_LIMIT = 500
_TEST_NODEID_LIMIT = 400
_TEST_LEVEL_BY_OUTCOME = {
    "passed": logging.DEBUG,
    "skipped": logging.INFO,
    "xfailed": logging.INFO,
    "xpassed": logging.WARNING,
    "rerun": logging.WARNING,
    "failed": logging.ERROR,
    "error": logging.ERROR,
}
_TEST_OUTCOMES = frozenset(_TEST_LEVEL_BY_OUTCOME)
_TEST_LOG_DIR_DEGRADED = "log 目录不可解析，测试留痕降级为仅主日志"
_TEST_FLUSH_IMMEDIATELY = frozenset(
    name for name, level in _TEST_LEVEL_BY_OUTCOME.items()
    if level >= logging.WARNING)
_TEST_STATE_LOCK = threading.Lock()
_TEST_STATE: dict[str, Any] = {
    "installed": False,
    "run_id": "",
    "pid": 0,
    "started_at": 0.0,
    "buffer": [],
    "counts": {},
    "flushed": 0,
    "degraded": "",
}
def _test_session_event(event: str, primary: bool, message: str,
                        *args: Any, payload: dict[str, Any]) -> None:
    level = logging.INFO if primary else logging.DEBUG
    _TEST_LOGGER.log(level, message, *args, extra={
        "event": event,
        "payload": sanitize_payload(payload),
    })
def _test_runs_path() -> str:
    try:
        log_dir = get_log_dir()
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_test_runs_path:Exc')
        return ""
    if not log_dir:
        return ""
    return os.path.join(log_dir, TEST_RUNS_FILE)
_test_run_id_lock = threading.Lock()
_last_test_run_ns = 0
def _resolve_test_run_id() -> str:
    global _last_test_run_ns
    uid = os.environ.get("PYTEST_XDIST_TESTRUNUID", "")
    if uid:
        return f"xdist-{uid}"
    with _test_run_id_lock:
        run_ns = max(time.time_ns(), _last_test_run_ns + 1)
        _last_test_run_ns = run_ns
    return f"local-{run_ns}-{os.getpid()}"
def _is_xdist_worker() -> bool:
    return "PYTEST_XDIST_WORKER" in os.environ
def install_test_logging(*, force: bool = False) -> dict[str, Any]:
    global _test_session_active
    started = time.time()
    try:
        resolved = setup_logging(force=force)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='install_test_logging:setup_logging')
        resolved = None
    _test_session_active = True
    runs_path = _test_runs_path()
    with _TEST_STATE_LOCK:
        if _TEST_STATE["buffer"]:
            _flush_test_buffer_locked()
        pending_buffer = _TEST_STATE["buffer"]
        pending_degraded = (
            (_TEST_STATE["degraded"]
             or "test_runs.jsonl 旧会话缓冲仍未落盘")
            if pending_buffer else ""
        )
        _TEST_STATE.update({
            "installed": True,
            "run_id": _resolve_test_run_id(),
            "pid": os.getpid(),
            "started_at": started,
            "buffer": pending_buffer,
            "counts": {},
            "flushed": 0,
            "degraded": (pending_degraded
                         or ("" if runs_path else _TEST_LOG_DIR_DEGRADED)),
        })
        snapshot = dict(_TEST_STATE)
    worker = _is_xdist_worker()
    _test_session_event(
        "test_session_start", not worker,
        "test_session_start: run_id=%s pid=%d xdist_worker=%s",
        snapshot["run_id"], snapshot["pid"], worker,
        payload={
            "run_id": snapshot["run_id"],
            "pid": snapshot["pid"],
            "xdist_worker": worker,
            "log_dir": resolved or "",
            "runs_file": runs_path,
        },
    )
    if not worker:
        safe_write_audit(
            "test_session_start",
            run_id=snapshot["run_id"],
            pid=snapshot["pid"],
            xdist_worker=worker,
            runs_file=runs_path,
        )
    return {
        "installed": True,
        "log_dir": resolved or "",
        "runs_file": runs_path,
        "run_id": snapshot["run_id"],
        "degraded": snapshot["degraded"],
    }
def _normalized_test_outcome(outcome: str) -> str:
    text = str(outcome or "").strip().lower()
    return text if text in _TEST_OUTCOMES else "error"
def _truncate_text(text: str, limit: int) -> str:
    text = str(text or "").replace("\n", " ").strip()
    return text if len(text) <= limit else text[:limit] + "…"
def _test_case_entry(nodeid: str, outcome: str, when: str,
                     duration_ms: float, message: str,
                     slow: bool) -> dict[str, Any]:
    with _TEST_STATE_LOCK:
        run_id = _TEST_STATE["run_id"]
        if not run_id:
            run_id = _resolve_test_run_id()
            _TEST_STATE["run_id"] = run_id
        pid = os.getpid()
    level = logging.WARNING if slow else _TEST_LEVEL_BY_OUTCOME[outcome]
    return build_json_log_entry(
        level=logging.getLevelName(level),
        logger=_TEST_LOGGER.name,
        message=f"{TEST_CASE_EVENT}: {outcome} {nodeid}",
        dt=datetime.now(),
        event=TEST_CASE_EVENT,
        payload=sanitize_payload({
            "nodeid": nodeid,
            "outcome": outcome,
            "when": when,
            "duration_ms": round(duration_ms, 2),
            "slow": slow,
            "run_id": run_id,
            "pid": pid,
            "detail": message,
        }),
    )
def _flush_test_buffer_locked() -> int:
    buffered = _TEST_STATE["buffer"]
    if not buffered:
        return 0
    path = _test_runs_path()
    if not path:
        _TEST_STATE["degraded"] = _TEST_LOG_DIR_DEGRADED
        _trim_test_buffer(buffered)
        return 0
    payload = "\n".join(json.dumps(e, ensure_ascii=False, default=str)
                        for e in buffered) + "\n"
    try:
        written = append_jsonl_locked(path, payload)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_flush_test_buffer_locked:append')
        written = False
    if not written:
        _TEST_STATE["degraded"] = "test_runs.jsonl 追加失败（留痕未落盘）"
        _TEST_LOGGER.warning("test_case_result 留痕落盘失败: %s", path)
        _trim_test_buffer(buffered)
        return 0
    del buffered[:]
    _TEST_STATE["flushed"] += 1
    return 1
def _trim_test_buffer(buffered: list) -> None:
    overflow = len(buffered) - _TEST_BUFFER_KEEP_MAX
    if overflow > 0:
        del buffered[:overflow]
def _buffer_test_case_entry(entry: dict[str, Any], outcome: str,
                            slow: bool) -> None:
    with _TEST_STATE_LOCK:
        counts = _TEST_STATE["counts"]
        counts[outcome] = counts.get(outcome, 0) + 1
        _TEST_STATE["buffer"].append(entry)
        need_flush = (len(_TEST_STATE["buffer"]) >= _TEST_FLUSH_THRESHOLD
                      or outcome in _TEST_FLUSH_IMMEDIATELY
                      or slow)
        if need_flush:
            _flush_test_buffer_locked()
def record_test_outcome(nodeid: str, outcome: str, *, when: str = "call",
                        duration_ms: float = _DEFAULT_DURATION_MS,
                        message: str = "") -> bool:
    try:
        node_text = _truncate_text(nodeid, _TEST_NODEID_LIMIT)
        outcome_text = _normalized_test_outcome(outcome)
        when = str(when or "call")
        duration = _coerce_duration_ms(duration_ms, "record_test_outcome")
        if duration is None:
            log_swallowed(
                __name__,
                TypeError(f"duration_ms 非有限数值: {duration_ms!r}"),
                context='record_test_outcome:duration')
            duration = _DEFAULT_DURATION_MS
        duration = max(0.0, duration)
        slow = outcome_text in ("passed", "xpassed") and duration >= _SLOW_CASE_MS
        entry = _test_case_entry(node_text, outcome_text, when, duration,
                                 _truncate_text(message, _TEST_MESSAGE_LIMIT),
                                 slow)
        _TEST_LOGGER.log(
            logging.WARNING if slow else _TEST_LEVEL_BY_OUTCOME[outcome_text],
            "%s %s (%s, %.1fms)%s",
            TEST_CASE_EVENT, node_text, when, duration,
            f" [slow ≥{_SLOW_CASE_MS:.0f}ms]" if slow else "",
            extra={
                "event": TEST_CASE_EVENT,
                "duration_ms": duration,
                "payload": entry["payload"],
            },
        )
        _buffer_test_case_entry(entry, outcome_text, slow)
        return True
    except Exception as e:  # noqa: BLE001
        _TEST_LOGGER.warning("record_test_outcome 留痕失败（不阻断测试）: %s: %s",
                             type(e).__name__, e)
        return False
def finish_test_logging(exitstatus: int = 0) -> dict[str, Any]:
    global _test_session_active
    exitstatus = _coerce_count(exitstatus, "finish_test_logging")
    with _TEST_STATE_LOCK:
        _flush_test_buffer_locked()
        counts = dict(_TEST_STATE["counts"])
        elapsed = (max(0.0, round(time.time() - _TEST_STATE["started_at"], 2))
                   if _TEST_STATE["started_at"] else 0.0)
        run_id = _TEST_STATE["run_id"]
        degraded = _TEST_STATE["degraded"]
        pid = _TEST_STATE["pid"] or os.getpid()
        _TEST_STATE["installed"] = False
    _test_session_active = False
    path = _test_runs_path()
    if path:
        try:
            prune_jsonl_file(path, TEST_RUNS_MAX_BYTES)
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e, context='finish_test_logging:prune')
    total = sum(counts.values())
    cases = total - counts.get("rerun", 0)
    status = "degraded" if degraded else "ok"
    worker = _is_xdist_worker()
    _test_session_event(
        "test_session_end", not worker,
        "test_session_end: run_id=%s pid=%d cases=%d failed=%d error=%d "
        "skipped=%d rerun=%d exitstatus=%d elapsed=%.1fs",
        run_id, pid, cases, counts.get("failed", 0), counts.get("error", 0),
        counts.get("skipped", 0), counts.get("rerun", 0), exitstatus, elapsed,
        payload={
            "run_id": run_id,
            "pid": pid,
            "counts": counts,
            "cases": cases,
            "exitstatus": exitstatus,
            "elapsed_s": elapsed,
            "runs_file": path,
            "degraded": degraded,
        },
    )
    if not worker:
        safe_write_audit(
            "test_session_end",
            run_id=run_id,
            pid=pid,
            cases=cases,
            counts=counts,
            exitstatus=exitstatus,
            elapsed_s=elapsed,
            degraded=degraded,
        )
    return {
        "status": status,
        "run_id": run_id,
        "pid": pid,
        "cases": cases,
        "counts": counts,
        "exitstatus": exitstatus,
        "elapsed_s": elapsed,
        "runs_file": path,
        "degraded": degraded,
    }
_exception_logging_installed = False
_exception_logging_lock = threading.Lock()
_UNHANDLED_LOGGER_NAME = "jwsgj.unhandled"
def _record_unhandled(logger_obj: logging.Logger, message: str,
                      message_args: tuple, exc_info: tuple,
                      audit_payload: dict) -> None:
    try:
        logger_obj.error(message, *message_args, exc_info=exc_info,
                         extra={"event": "unhandled_exception"})
    except Exception as exc:  # noqa: BLE001
        safe_stderr_write(
            "[log_config] unhandled 主日志留痕失败 "
            f"({type(exc).__name__})，继续审计双写\n")
    try:
        safe_write_audit("unhandled_exception", **audit_payload)
    except Exception:
        _LOGGER.warning("unhandled 审计双写失败（主日志通道已留痕）", exc_info=True)
def _make_chained_sys_hook(unhandled: logging.Logger,
                           prev_hook: Any) -> Any:
    def _chained_sys_hook(exc_type, exc_value, exc_tb):
        try:
            exc_name, exc_message = _safe_exc_text(exc_value)
            _record_unhandled(
                unhandled,
                "未捕获异常(主线程): %s: %s",
                (exc_name, exc_message),
                (exc_type, exc_value, exc_tb),
                {
                    "scope": "main_thread",
                    "exc_type": exc_name,
                    "exc_message": exc_message[:500],
                },
            )
        except Exception:
            _LOGGER.warning(
                "sys.excepthook 日志钩子自身失败，透传原钩子", exc_info=True)
        prev_hook(exc_type, exc_value, exc_tb)
    return _chained_sys_hook
def _make_chained_threading_hook(unhandled: logging.Logger,
                                  prev_hook: Any) -> Any:
    def _chained_threading_hook(args):
        thread_name = (getattr(args.thread, "name", "<unknown>")
                       if args.thread else "<unknown>")
        try:
            exc_name, exc_message = _safe_exc_text(args.exc_value)
            _record_unhandled(
                unhandled,
                "未捕获异常(线程 %s): %s: %s",
                (thread_name, exc_name, exc_message),
                (args.exc_type, args.exc_value, args.exc_traceback),
                {
                    "scope": "worker_thread",
                    "thread": thread_name,
                    "exc_type": exc_name,
                    "exc_message": exc_message[:500],
                },
            )
        except Exception:
            _LOGGER.warning(
                "threading.excepthook 日志钩子自身失败，透传原钩子", exc_info=True)
        prev_hook(args)
    return _chained_threading_hook
def _install_exception_logging_inner() -> None:
    _unhandled = logging.getLogger(_UNHANDLED_LOGGER_NAME)
    logging.captureWarnings(True)
    sys.excepthook = _make_chained_sys_hook(_unhandled, sys.excepthook)
    threading.excepthook = _make_chained_threading_hook(
        _unhandled, threading.excepthook)
def install_exception_logging() -> None:
    global _exception_logging_installed
    with _exception_logging_lock:
        if _exception_logging_installed:
            return
        try:
            _install_exception_logging_inner()
            _exception_logging_installed = True
        except Exception as _e:  # noqa: BLE001
            safe_stderr_write(
                f"[log_config] exception hook install failed: {_e}\n")

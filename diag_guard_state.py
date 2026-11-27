from __future__ import annotations

import errno
import hashlib
import hmac
import json
import logging
import os
import re
import sys
import threading
import time as _time
from collections.abc import Callable
from datetime import datetime
from typing import Any, ClassVar, NamedTuple, Self

if sys.platform == "win32":
    import msvcrt as _msvcrt
    _fcntl = None
else:
    import fcntl as _fcntl
    _msvcrt = None
from jwsgj.diag_guard_io import (
    _DEFAULT_TEXT_ENCODING,
    _FINGERPRINT_ENCODING,
    _UTF8_SIG_ENCODING,
    SourceReadError,
    _danger_hits,
    _ensure_generated_py_import,
    _inside_any_span,
    _is_python_source,
    _literal_token_spans,
    _lock_file_name,
    _within_skill_root,
    atomic_replace_bytes,
    atomic_write_text,
    bytes_fingerprint,
    decode_source_strict,
    normalize_fs_key,
    safe_write_text,
    two_level_unlink,
    write_text_atomic,
)
from jwsgj.diag_types_defs import (
    ConcurrentExecutionError,
    ContractViolationError,
)
from jwsgj.log_config import log_swallowed, safe_write_audit
from jwsgj.runtime_paths import (
    PIPELINE_STATE_FILENAME,
    get_temp_base,
    json_artifact_path_candidates,
)
from jwsgj.runtime_scope import canonical_path

_log = logging.getLogger(__name__)
__all__ = [
    'READ_BEFORE_WRITE_GUARD',
    'JsonSerializableMixin',
    'ProcessLock',
    'ProvenanceError',
    'ProvenanceGuard',
    'ReadBeforeWriteGuard',
    'RepCheck',
    'RepReport',
    'SafeWriteGuard',
    'SecurityConstraintSet',
    'StateIntegrityGuard',
    'StateTamperError',
    'enforce_read_before_write',
    'ensure_plan_dir',
    'invalidate_module_pyc',
    'max_review_seq',
    'read_json_artifact',
    'read_queue_json',
    'read_review_queue_entries',
    'restore_file_bytes',
    'rollback_note',
    'serialize_json',
    'snapshot_file_bytes',
    'verify_provenance_logged',
    'write_json_artifact',
    'write_queue_json',
    'write_with_rollback',
]
_FORBIDDEN_WRITE_PREFIXES = [
    "C:\\Windows",
    "C:\\Program Files",
    "C:\\Program Files (x86)",
    "C:\\ProgramData",
    "/usr/bin",
    "/usr/sbin",
    "/usr/lib",
    "/bin",
    "/sbin",
    "/etc",
    "/boot",
    "/dev",
    "/proc",
    "/sys",
    "/System",
    "/Library",
]
_SENSITIVE_IDENTIFIER_RULES: tuple[tuple[str, int], ...] = (
    ("password", 3),
    ("api[_-]?key", 8),
    ("secret", 8),
    ("token", 8),
    ("private[_-]?key", 20),
    ("access[_-]?key", 8),
)
_SENSITIVE_ANNOTATION_RE = r"(?P<ann>\s*:\s*[\w\[\]., |'\"]+)?"
def _sensitive_literal_source(min_len: int) -> str:
    return (r'(?P<prefix>(?i:[rubf]{0,2}))'
            + r"(?P<quote>\"\"\"|'''|\"|')"
            + r'(?:\\[\s\S]|(?!(?P=quote))[\s\S]){'
            + str(min_len) + r',}(?P=quote)')
def _sensitive_assignment_source(identifier: str) -> str:
    return (r'(?<![A-Za-z0-9_])(?P<name>(?:[A-Za-z_][A-Za-z0-9_\-]*)?'
            + identifier + r')' + _SENSITIVE_ANNOTATION_RE + r'\s*=')
def _sensitive_rule_source(identifier: str, min_len: int) -> str:
    return (_sensitive_assignment_source(identifier)
            + r'\s*' + _sensitive_literal_source(min_len))
_SENSITIVE_RULE_SOURCES: tuple[str, ...] = tuple(
    _sensitive_rule_source(identifier, min_len)
    for identifier, min_len in _SENSITIVE_IDENTIFIER_RULES)
_SENSITIVE_REWRITE_RULES: tuple[re.Pattern[str], ...] = tuple(
    re.compile(source, re.IGNORECASE) for source in _SENSITIVE_RULE_SOURCES)
_SENSITIVE_ASSIGNMENT_RULES: tuple[re.Pattern[str], ...] = tuple(
    re.compile(_sensitive_assignment_source(identifier), re.IGNORECASE)
    for identifier, _min_len in _SENSITIVE_IDENTIFIER_RULES)
def _contains_sensitive_assignment(content: str) -> bool:
    return any(
        pattern.search(content) for pattern in _SENSITIVE_ASSIGNMENT_RULES)
_SENSITIVE_COMPILED_BY_SOURCE: dict[str, re.Pattern[str]] = dict(
    zip(_SENSITIVE_RULE_SOURCES, _SENSITIVE_REWRITE_RULES, strict=True))
def _sensitive_env_replacement(match: re.Match) -> str:
    var_name = match.group("name")
    env_name = var_name.upper().replace("-", "_")
    annotation = (match.group("ann") or "").rstrip()
    prefix = (match.group("prefix") or "").lower()
    bytes_suffix = ".encode()" if "b" in prefix else ""
    return (f'{var_name}{annotation} = os.environ.get("{env_name}", "")'
            f'{bytes_suffix}')
def _sub_outside_literals(pattern: re.Pattern[str], text: str,
                           spans: list[tuple[int, int]],
                           replacement: Callable[[re.Match], str]) -> tuple[str, int]:
    matches = [match for match in pattern.finditer(text)
               if not _inside_any_span(match.start(), spans)]
    if not matches:
        return text, 0
    parts: list[str] = []
    cursor = 0
    for match in matches:
        parts.append(text[cursor:match.start()])
        parts.append(replacement(match))
        cursor = match.end()
    parts.append(text[cursor:])
    return "".join(parts), len(matches)
def _rewrite_sensitive_values(content: str, filepath: str) -> tuple[str, list[str]]:
    result = content
    logs: list[str] = []
    python_source = _is_python_source(filepath)
    if (python_source and _contains_sensitive_assignment(result)
            and _literal_token_spans(result) is None):
        _log.warning(
            "[guard_io] 脱敏: 字面量边界不可判定，跳过自动脱敏: %s",
            filepath)
        logs.append(f"警告: 跳过脱敏(字面量边界不可判定): {filepath}")
        return result, logs
    for pattern in _SENSITIVE_REWRITE_RULES:
        if not pattern.search(result):
            continue
        spans = _literal_token_spans(result) if python_source else []
        if spans is None:
            _log.warning(
                "[guard_io] 脱敏: 字面量边界不可判定，跳过自动脱敏: %s",
                filepath)
            logs.append(f"警告: 跳过脱敏(字面量边界不可判定): {filepath}")
            break
        result, match_count = _sub_outside_literals(
            pattern, result, spans, _sensitive_env_replacement)
        if match_count:
            logs.append(
                f"已脱敏: {filepath} - {match_count}处硬编码凭据→环境变量引用")
    return result, logs
def _collect_danger_findings(content: str, filepath: str) -> list[str]:
    return [
        f"警告: {filepath} 包含危险函数 {func_name}"
        for func_name, hits in _danger_hits(content).items()
        if hits
    ]
class SecurityConstraintSet:
    SENSITIVE_REWRITE_RULES: ClassVar[tuple[str, ...]] = _SENSITIVE_RULE_SOURCES
    SENSITIVE_PATTERNS: ClassVar[list[str]] = [
        *SENSITIVE_REWRITE_RULES,
        _sensitive_rule_source(r"private[_-]?key", 3),
        _sensitive_rule_source(r"ssh[_-]?key", 3),
    ]
    @classmethod
    def enforce_no_secrets_in_source(cls, source_code: str, filepath: str = "") -> str:
        sanitized, logs = cls.auto_sanitize(source_code, filepath)
        if any("跳过脱敏(字面量边界不可判定)" in entry for entry in logs):
            raise ContractViolationError(
                f"安全约束违反(不可自动修复): 文件 {filepath} "
                "字面量边界不可判定，无法确认敏感凭证已清除"
            )
        spans = _literal_token_spans(sanitized) or []
        for pattern in cls.SENSITIVE_PATTERNS:
            if any(not _inside_any_span(match.start(), spans)
                   for match in re.finditer(pattern, sanitized, re.IGNORECASE)):
                raise ContractViolationError(
                    f"安全约束违反(不可自动修复): 文件 {filepath} 包含敏感凭证硬编码 "
                    f"(匹配模式: {pattern})"
                )
        return sanitized
    @classmethod
    def auto_sanitize(cls, source_code: str,
                      filepath: str = "") -> tuple[str, list[str]]:
        sanitized, logs = _rewrite_sensitive_values(source_code, filepath)
        sanitized, import_logs = _ensure_generated_py_import(
            sanitized, filepath, bool(logs))
        logs.extend(import_logs)
        if logs:
            _log.warning("安全约束自动脱敏: %s", "; ".join(logs))
        return sanitized, logs
class JsonSerializableMixin:
    def to_json(self, indent: int = 2) -> str:
        return serialize_json(self.to_dict(), indent=indent)
def read_json_artifact(path: str, *,
                       propagate_io: bool = False) -> tuple[object, str, str]:
    for candidate in json_artifact_path_candidates(path):
        try:
            with open(candidate, "r", encoding=_UTF8_SIG_ENCODING) as f:
                data = json.load(f)
            if (os.path.normcase(candidate)
                    != os.path.normcase(os.path.abspath(path))):
                _log.info("read_json_artifact: 新布局缺失，已只读回退旧布局: %s",
                          candidate)
            return data, "ok", ""
        except FileNotFoundError:
            continue
        except OSError as e:
            if propagate_io:
                raise
            log_swallowed(__name__, e, context='read_json_artifact:OSError')
            return None, "parse_error", str(e)
        except (ValueError, RecursionError, MemoryError) as e:
            log_swallowed(__name__, e, context='read_json_artifact:parse')
            return None, "parse_error", str(e)
    _log.debug("read_json_artifact: 文件不存在（按 missing 口径）: %s", path)
    return None, "missing", ""
def read_review_queue_entries(path: str) -> list | None:
    old, kind, err = read_json_artifact(path, propagate_io=True)
    if kind == "missing":
        return None
    if kind == "parse_error":
        _log.warning("cv_uncertain 队列内容损坏，按空队列重建: %s", err)
        return None
    if not isinstance(old, dict):
        _log.debug(
            "cv_uncertain 队列结构异常（顶层非对象，得到 %s），跳过合并",
            type(old).__name__,
        )
        return None
    old_entries = old.get("entries", [])
    if not isinstance(old_entries, list):
        _log.debug(
            "cv_uncertain 队列 entries 字段异常（非列表，得到 %s），跳过合并",
            type(old_entries).__name__,
        )
        return None
    return old_entries
def serialize_json(payload, *, indent: int | None = None) -> str:
    return json.dumps(payload, ensure_ascii=False, indent=indent, default=str)
def write_json_artifact(path: str, payload, *, indent: int | None = None) -> None:
    write_text_atomic(path, serialize_json(payload, indent=indent),
                      newline="\n")
def read_queue_json(path: str, default, *, for_update: bool = False):
    data, kind, error = read_json_artifact(
        path, propagate_io=for_update)
    if kind == "missing":
        return default
    if kind != "ok":
        if for_update:
            raise ValueError(f"队列读取失败，拒绝按默认值覆盖: {path}: {error}")
        _log.warning("[AIReview] 读取失败: %s: %s", path, error)
        return default
    expected = type(default) if isinstance(default, (dict, list)) else None
    if expected is not None and not isinstance(data, expected):
        if for_update:
            raise ValueError(
                f"队列顶层类型不符({type(data).__name__}，期望 "
                f"{expected.__name__})，拒绝按默认值覆盖: {path}")
        _log.warning(
            "[AIReview] JSON 顶层类型不符(%s，期望 %s)，按默认值处理: %s",
            type(data).__name__,
            expected.__name__,
            path,
        )
        return default
    return data
def write_queue_json(path: str, data, *, fsync: bool = False) -> None:
    del fsync
    write_json_artifact(path, data, indent=2)
def ensure_plan_dir(plan_file: str) -> None:
    try:
        os.makedirs(os.path.dirname(plan_file), exist_ok=True)
    except OSError as e:
        _log.debug("目录创建失败（继续后续流程）: %s", e)
def max_review_seq(items: list, prefix: str, id_key: str = "review_id") -> int:
    mx = 0
    for it in items:
        if not isinstance(it, dict):
            continue
        rid = it.get(id_key)
        if not isinstance(rid, str) or not rid.startswith(prefix + "-"):
            continue
        tail = rid[len(prefix) + 1 :]
        if not tail.isdecimal():
            _log.debug("[AIReview] 序号后缀非十进制（跳过水位计算）: %r", rid)
            continue
        try:
            seq = int(tail)
        except ValueError:
            _log.debug("[AIReview] 序号后缀超出整数转换上限（跳过水位计算）: %r",
                       rid[:120])
            continue
        mx = max(mx, seq)
    return mx
_WRITE_FAILURE_SPECS: tuple[tuple[type[BaseException], str, str, str], ...] = (
    (ContractViolationError, "底层安全拦截: {err}",
     "blocked_security", "ContractViolationError"),
    (UnicodeEncodeError, "写入失败(内容含目标编码无法表示的字符): {err}",
     "write_error", "UnicodeEncodeError"),
    (LookupError, "写入失败(非法编码名称): {err}",
     "write_error", "LookupError"),
    (ValueError, "写入前备份失败: {err}",
     "blocked_backup", "ValueError"),
    (OSError, "写入失败: {err}",
     "write_error", "OSError"),
)
class SafeWriteGuard:
    def __init__(self: SafeWriteGuard, skill_dir: str = "",
                 sanitize: bool = True,
                 strict: bool = False) -> None:
        self._skill_dir = os.path.abspath(skill_dir) if skill_dir else ""
        self.sanitize_payload = sanitize
        self._strict = strict
        self._write_log: list[dict] = []
    def _record(self: SafeWriteGuard, action: str, path: str, **extra: Any) -> None:
        entry = {"action": action, "path": path, **extra}
        self._write_log.append(entry)
        safe_write_audit("guard_write_action", **entry)
    def _resolve_write_path(self: SafeWriteGuard, filepath: str) -> str:
        if os.path.isabs(filepath) or not self._skill_dir:
            return os.path.abspath(filepath)
        return os.path.abspath(os.path.join(self._skill_dir, filepath))
    def validate_path_safety(self: SafeWriteGuard, filepath: str) -> tuple[bool, str]:
        if not isinstance(filepath, str):
            return False, f"路径类型非法: {type(filepath).__name__}"
        if not filepath.strip():
            return False, "路径为空"
        abs_path = self._resolve_write_path(filepath)
        resolved_path = os.path.realpath(abs_path)
        normalized = os.path.normpath(filepath)
        _hit = _match_forbidden_write_prefix(resolved_path, normalized)
        if _hit is not None:
            return False, _hit
        if _contains_parent_segment(filepath, normalized):
            return False, f"路径包含穿越: {filepath}"
        if self._skill_dir and not _within_skill_root(
                self._skill_dir, abs_path):
            return False, f"文件不在技能目录内: {abs_path}"
        return True, "路径安全"
    def sanitize_content(self: SafeWriteGuard, content: str, filepath: str = "") -> tuple[str, list[str]]:
        result, logs = _rewrite_sensitive_values(content, filepath)
        has_sensitive_rewrites = bool(logs)
        logs.extend(_collect_danger_findings(result, filepath))
        result, import_logs = _ensure_generated_py_import(
            result, filepath, has_sensitive_rewrites)
        logs.extend(import_logs)
        return result, logs
    def guard_write(self: SafeWriteGuard, path: str, content: str,
                    encoding: str = _DEFAULT_TEXT_ENCODING) -> dict:
        result: dict = {"ok": False, "path": path, "sanitized": False,
                        "sanitize_logs": [], "warnings": [], "blocked_reason": ""}
        safe, reason = self.validate_path_safety(path)
        if not safe:
            result["blocked_reason"] = reason
            self._record("blocked", path, reason=reason)
            return result
        write_path = self._resolve_write_path(path)
        sanitized, logs = self.sanitize_content(content, write_path)
        if self.sanitize_payload:
            final_content = sanitized
            if sanitized != content:
                result["sanitized"] = True
        else:
            final_content = content
            if sanitized != content:
                logs.append(
                    f"警告: sanitize=False，检测到硬编码凭据但未脱敏: {write_path}")
        self._split_sanitize_logs(logs, result)
        if any("跳过脱敏(字面量边界不可判定)" in warning
               for warning in result["warnings"]):
            result["blocked_reason"] = (
                "写盘阻断: 字面量边界不可判定，无法安全脱敏")
            self._record("blocked_sanitize", write_path,
                         warnings=result["warnings"])
            return result
        if self._strict and result["warnings"]:
            result["blocked_reason"] = "strict模式: 内容安全校验未通过"
            self._record("blocked_strict", write_path,
                         warnings=result["warnings"])
            return result
        self._attempt_write(write_path, final_content, encoding, result)
        return result
    def _split_sanitize_logs(self: SafeWriteGuard, logs: list[str], result: dict) -> None:
        for log_entry in logs:
            if log_entry.startswith("警告"):
                result["warnings"].append(log_entry)
            elif self.sanitize_payload:
                result["sanitize_logs"].append(log_entry)
    def _attempt_write(self: SafeWriteGuard, path: str, final_content: str,
                       encoding: str, result: dict) -> None:
        try:
            safe_write_text(path, final_content, encoding, strict=self._strict)
            result["ok"] = True
            self._record("written", path, sanitized=result["sanitized"])
        except (ContractViolationError, UnicodeEncodeError, LookupError,
                ValueError, OSError) as e:
            self._record_write_failure(path, e, result)
    def _record_write_failure(self: SafeWriteGuard, path: str, exc: BaseException,
                              result: dict) -> None:
        for exc_type, reason_fmt, action, label in _WRITE_FAILURE_SPECS:
            if isinstance(exc, exc_type):
                log_swallowed(
                    __name__, exc,
                    context=f'SafeWriteGuard.guard_write:{label}')
                result["blocked_reason"] = reason_fmt.format(err=exc)
                self._record(action, path, error=str(exc))
                return
        raise exc
def _contains_parent_segment(filepath: str, normalized: str) -> bool:
    return (".." in re.split(r"[\\/]", filepath)
            or ".." in normalized.split(os.sep))
def _matches_forbidden_prefix(candidate: str, unified_prefix: str) -> bool:
    if not candidate.startswith(unified_prefix):
        return False
    rest = candidate[len(unified_prefix):]
    return not rest or rest[0] == os.sep
def _strip_device_namespace(path: str) -> str:
    if path.startswith(("\\\\?\\", "\\\\.\\")):
        return path[4:]
    return path
def _match_forbidden_write_prefix(abs_path: str, normalized: str) -> str | None:
    for prefix in _FORBIDDEN_WRITE_PREFIXES:
        unified_prefix = prefix.replace("/", os.sep).upper()
        for candidate in (abs_path, normalized):
            cand = _strip_device_namespace(candidate).replace("/", os.sep).upper()
            if _matches_forbidden_prefix(cand, unified_prefix):
                return f"禁止向系统路径写入: {candidate} (匹配 {prefix})"
    return None
def snapshot_file_bytes(file_path: str) -> bytes:
    with open(file_path, "rb") as f:
        return f.read()
def invalidate_module_pyc(file_path: str) -> int:
    stem = os.path.splitext(os.path.basename(file_path))[0]
    cache_dir = os.path.join(
        os.path.dirname(os.path.abspath(file_path)), "__pycache__")
    removed = 0
    try:
        entries = os.listdir(cache_dir)
    except OSError as e:
        _log.debug("[GuardIO] pyc 缓存目录不可读，跳过 stale pyc 失效: %s: %s",
                   cache_dir, e)
        return 0
    for name in entries:
        if name.startswith(stem + ".") and name.endswith(".pyc"):
            cache_path = os.path.join(cache_dir, name)
            try:
                if not os.path.lexists(cache_path):
                    continue
                if not two_level_unlink(cache_path):
                    _log.debug(
                        "[GuardIO] stale pyc 两级删除失败（不阻断其余失效）: %s",
                        name)
                    continue
                removed += 1
            except OSError as e:
                _log.debug("[GuardIO] stale pyc 删除失败（不阻断其余失效）: %s: %s",
                           name, e)
                continue
    return removed
def restore_file_bytes(file_path: str, snapshot: bytes) -> None:
    atomic_replace_bytes(
        file_path, snapshot,
        prefix=f".{os.path.basename(file_path)}.restore_",
        label="回滚恢复临时产物")
    removed = invalidate_module_pyc(file_path)
    if removed:
        _log.info("[GuardIO] 回滚后已失效 stale pyc %d 个: %s",
                  removed, file_path)
_PREWRITE_SNAPSHOT_UNKNOWN = object()

def _failed_atomic_write_rollback_note(
    file_path: str, content: str, backup_path: str, log_tag: str,
    encoding: str,
    original_bytes: bytes | None | object = _PREWRITE_SNAPSHOT_UNKNOWN,
) -> str:
    try:
        attempted = content.encode(encoding)
        current = snapshot_file_bytes(file_path)
    except FileNotFoundError:
        _log.warning("%s 写盘失败后目标不存在，跳过回滚: %s", log_tag, file_path)
        return "（目标不存在，跳过回滚）"
    except (OSError, ValueError, TypeError, AttributeError,
            LookupError, UnicodeError) as exc:
        _log.warning("%s 无法确认失败写入的内容所有权，跳过回滚: %s: %s",
                     log_tag, file_path, exc)
        return "（无法确认本次写入是否提交，跳过回滚以保护目标现状）"
    if current != attempted:
        _log.warning("%s 目标未提交本次写入内容，跳过回滚以保护现有内容: %s",
                     log_tag, file_path)
        return "（目标未提交本次内容，跳过回滚以保护现有内容）"
    if (original_bytes is not _PREWRITE_SNAPSHOT_UNKNOWN
            and original_bytes == attempted):
        _log.warning("%s 写入前内容已与待写内容一致，保留目标现状: %s",
                     log_tag, file_path)
        return "（写入前内容已与待写内容一致，保留目标现状）"
    return rollback_note(file_path, backup_path, log_tag)
def write_with_rollback(file_path: str, content: str, backup_path: str,
                        tag: str, log_tag: str,
                        encoding: str = _DEFAULT_TEXT_ENCODING) -> str:
    try:
        original_bytes = snapshot_file_bytes(file_path)
    except FileNotFoundError:
        original_bytes = None
    except (OSError, ValueError, TypeError, AttributeError):
        original_bytes = _PREWRITE_SNAPSHOT_UNKNOWN
    try:
        atomic_write_text(
            file_path, content, tag=tag, newline="", encoding=encoding)
    except Exception as e:  # noqa: BLE001
        _log.debug("[file-write:%s] 写盘异常统一回滚: %s", tag, e,
                     exc_info=True)
        note = _failed_atomic_write_rollback_note(
            file_path, content, backup_path, log_tag, encoding,
            original_bytes=original_bytes)
        return f"写入失败{note}: {e}"
    return ""
def rollback_note(file_path: str, backup_path: str,
                   log_tag: str) -> str:
    if not backup_path:
        _log.error("%s 无备份可回滚: %s", log_tag, file_path)
        return "（无备份可回滚）"
    try:
        restore_file_bytes(file_path, snapshot_file_bytes(backup_path))
        _log.warning("%s 已回滚: %s", log_tag, file_path)
        return "，已回滚"
    except OSError as err:
        _log.error("%s 回滚失败，源文件可能已损坏: %s — %s",
                     log_tag, file_path, err, exc_info=True)
        return f"且回滚失败({err})"
_LOCK_CONTENTION_ERRNOS = frozenset({errno.EACCES, errno.EAGAIN})
class StateTamperError(Exception):
    pass
class ProvenanceError(Exception):
    pass
def _canonical_json(data: dict) -> str:
    return json.dumps(data, ensure_ascii=False, sort_keys=True, default=str)
def _const_time_eq(actual: Any, expected: Any) -> bool:
    if not (isinstance(actual, str) and isinstance(expected, str)):
        return False
    return hmac.compare_digest(
        actual.encode(_FINGERPRINT_ENCODING, errors="surrogatepass"),
        expected.encode(_FINGERPRINT_ENCODING, errors="surrogatepass"))
def _read_json_object(path: str) -> dict | None:
    if not os.path.isfile(path):
        return None
    payload, _status, _error = read_json_artifact(path)
    return payload if isinstance(payload, dict) else None
class ProcessLock:
    _DEFAULT_LOCK_OFFSET: ClassVar[int] = 0
    _WINDOWS_LOCK_OFFSET: ClassVar[int] = 1 << 30
    def __init__(self, skill_dir: str, stage: str):
        self.skill_dir = os.path.abspath(skill_dir)
        self.stage = stage
        self._lock_dir = os.path.join(get_temp_base(self.skill_dir), "_locks")
        self._lock_path = os.path.join(self._lock_dir, _lock_file_name(stage))
        self._acquired = False
        self._fd: int | None = None
    def acquire(self) -> None:
        os.makedirs(self._lock_dir, exist_ok=True)
        fd = os.open(self._lock_path, os.O_RDWR | os.O_CREAT)
        try:
            self.lock_region(fd, self._WINDOWS_LOCK_OFFSET)
        except OSError as e:
            holder_desc = self._holder_desc()
            os.close(fd)
            if e.errno not in _LOCK_CONTENTION_ERRNOS:
                raise
            raise ConcurrentExecutionError(
                f"阶段 '{self.stage}' 正在被其他执行体占用{holder_desc}，"
                f"禁止并发执行。请等待当前执行完成后再试。"
            ) from None
        try:
            self._write_holder_metadata(fd)
        except BaseException:
            try:
                self.unlock_region(fd, self._WINDOWS_LOCK_OFFSET)
            finally:
                os.close(fd)
            raise
        self._fd = fd
        self._acquired = True
        _log.debug("[PipelineGuard] 锁已获取(内核字节锁): %s (pid=%d)",
                   self.stage, os.getpid())
    def release(self) -> None:
        if not self._acquired:
            return
        fd, self._fd = self._fd, None
        if fd is None:
            raise RuntimeError("PipelineGuard 内部不变量破坏: _acquired 为真但 _fd 为空")
        self._acquired = False
        try:
            self.unlock_region(fd, self._WINDOWS_LOCK_OFFSET)
        except OSError as e:
            _log.warning("[PipelineGuard] 锁释放失败: %s: %s",
                         self._lock_path, e)
        finally:
            os.close(fd)
            _log.debug("[PipelineGuard] 锁已释放: %s (pid=%d)",
                       self.stage, os.getpid())
    _BLOCKING_POLL_INTERVAL: ClassVar[float] = 0.05
    _BLOCKING_HELD: ClassVar[threading.local] = threading.local()
    @classmethod
    def _held_blocking_regions(cls) -> dict[int, set[tuple[int, int, int]]]:
        held = getattr(cls._BLOCKING_HELD, "regions", None)
        if held is None:
            held = {}
            cls._BLOCKING_HELD.regions = held
        return held
    @classmethod
    def _region_identity(cls, fd: int, offset: int) -> tuple[int, int, int]:
        st = os.fstat(fd)
        region_offset = offset if sys.platform == "win32" else cls._DEFAULT_LOCK_OFFSET
        return (st.st_dev, st.st_ino, region_offset)
    @classmethod
    def _try_lock_region(cls, fd: int, offset: int) -> None:
        if sys.platform == "win32":
            os.lseek(fd, offset, os.SEEK_SET)
            _msvcrt.locking(fd, _msvcrt.LK_NBLCK, 1)
        else:
            _fcntl.flock(fd, _fcntl.LOCK_EX | _fcntl.LOCK_NB)
    @classmethod
    def lock_region(cls, fd: int, offset: int = _DEFAULT_LOCK_OFFSET, *,
                    blocking: bool = False) -> None:
        held = cls._held_blocking_regions()
        key = cls._region_identity(fd, offset)
        if not blocking:
            cls._try_lock_region(fd, offset)
            held.setdefault(fd, set()).add(key)
            return
        if any(key in keys for keys in held.values()):
            raise OSError(
                errno.EDEADLOCK,
                f"同一线程重复获取同一文件区间锁（offset={offset}），"
                "继续等待会自死锁")
        while True:
            try:
                cls._try_lock_region(fd, offset)
            except OSError as e:
                if e.errno not in _LOCK_CONTENTION_ERRNOS:
                    raise
                _time.sleep(cls._BLOCKING_POLL_INTERVAL)
                continue
            held.setdefault(fd, set()).add(key)
            return
    @classmethod
    def unlock_region(cls, fd: int, offset: int = _DEFAULT_LOCK_OFFSET) -> None:
        try:
            if sys.platform == "win32":
                os.lseek(fd, offset, os.SEEK_SET)
                _msvcrt.locking(fd, _msvcrt.LK_UNLCK, 1)
            else:
                _fcntl.flock(fd, _fcntl.LOCK_UN)
        finally:
            held = cls._held_blocking_regions()
            keys = held.get(fd)
            if keys is not None:
                try:
                    keys.discard(cls._region_identity(fd, offset))
                except OSError as _swallow_e:
                    log_swallowed(__name__, _swallow_e,
                                  context='ProcessLock.unlock_region:OSError')
                    keys.clear()
                if not keys:
                    held.pop(fd, None)
    def _write_holder_metadata(self, fd: int) -> None:
        data = self._build_lock_data()
        raw = json.dumps(data, ensure_ascii=False, indent=2,
                         default=str).encode(_FINGERPRINT_ENCODING)
        os.ftruncate(fd, 0)
        os.lseek(fd, 0, os.SEEK_SET)
        view = memoryview(raw)
        while view:
            n = os.write(fd, view)
            view = view[n:]
        os.fsync(fd)
    def _build_lock_data(self) -> dict:
        return {
            "pid": os.getpid(),
            "thread_ident": threading.get_ident(),
            "start_time": datetime.now().isoformat(timespec="milliseconds"),
            "stage": self.stage,
            "lock_time": _time.time(),
            "cmd_fingerprint": hashlib.sha256(
                " ".join(sys.argv).encode(_FINGERPRINT_ENCODING)
            ).hexdigest()[:16],
        }
    def _holder_desc(self) -> str:
        holder = _read_json_object(self._lock_path)
        if not holder:
            return ""
        return (f" (持有者 pid={holder.get('pid')!r},"
                f" stage={holder.get('stage')!r})")
    def __enter__(self) -> Self:
        self.acquire()
        return self
    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        self.release()
        return False
class StateIntegrityGuard:
    @staticmethod
    def _derive_key(skill_dir: str) -> bytes:
        return hashlib.sha256(
            canonical_path(skill_dir).encode(_FINGERPRINT_ENCODING)
        ).digest()
    @staticmethod
    def _compute_signature(data_without_sig: str, key: bytes) -> str:
        return hmac.new(key, data_without_sig.encode(_FINGERPRINT_ENCODING),
                        hashlib.sha256).hexdigest()
    @classmethod
    def save_signed(cls, skill_dir: str, filepath: str, data: dict) -> None:
        key = cls._derive_key(skill_dir)
        data_copy = {k: v for k, v in data.items()
                     if k not in ("_state_signature", "_signed_at")}
        data_str = _canonical_json(data_copy)
        signature = cls._compute_signature(data_str, key)
        data_copy["_state_signature"] = signature
        data_copy["_signed_at"] = datetime.now().isoformat(timespec="milliseconds")
        write_json_artifact(filepath, data_copy, indent=2)
    @classmethod
    def load_verified(cls, skill_dir: str, filepath: str) -> dict | None:
        if not os.path.isfile(filepath):
            return None
        data = _read_json_object(filepath)
        if data is None:
            raise StateTamperError(
                f"状态文件 {filepath} 无法解析为 JSON 对象，可能已损坏或被篡改。")
        stored_sig = data.pop("_state_signature", None)
        data.pop("_signed_at", None)
        if stored_sig is None:
            raise StateTamperError(
                f"状态文件 {filepath} 缺少签名，可能被篡改或为旧版本。"
                f"请删除该文件后重新执行。"
            )
        key = cls._derive_key(skill_dir)
        try:
            data_str = _canonical_json(data)
            expected_sig = cls._compute_signature(data_str, key)
        except (TypeError, ValueError, RecursionError, MemoryError) as exc:
            raise StateTamperError(
                f"状态文件 {filepath} 无法规范化签名内容，可能已损坏或被篡改: "
                f"{type(exc).__name__}: {exc}") from exc
        if not _const_time_eq(stored_sig, expected_sig):
            raise StateTamperError(
                f"状态文件 {filepath} 签名验证失败，内容可能被篡改。"
                f"预期签名: {expected_sig[:16]}...，实际签名: {stored_sig!r}。"
                f"请删除该文件后重新执行。"
            )
        return data
_PROVENANCE_GENERATOR = "shared_cache.py"
_LEGACY_PROVENANCE_GENERATORS = frozenset({"pipeline_steps.py"})
_TRUSTED_GENERATORS = frozenset({_PROVENANCE_GENERATOR}) | _LEGACY_PROVENANCE_GENERATORS
def _require_generator(prov: dict,
                      trusted_generators: frozenset[str] | None = None) -> None:
    trusted = (_TRUSTED_GENERATORS if trusted_generators is None
               else trusted_generators)
    generator = prov.get("generator", "")
    if not isinstance(generator, str) or generator not in trusted:
        raise ProvenanceError(
            f"报告来源标记的生成器不匹配: 预期 {sorted(trusted)}, "
            f"实际 '{generator}'。"
        )
def _require_expected_step(prov: dict, expected_step: str | None) -> None:
    if expected_step is None:
        return
    step_name = prov.get("step_name", "")
    if step_name != expected_step:
        raise ProvenanceError(
            f"报告步骤名称不匹配: 预期 '{expected_step}', "
            f"实际 '{step_name}'。"
        )
def _verdict(verified: bool, message: str = "", issue: str = "") -> dict:
    if issue:
        return {"verified": verified, "issues": [issue]}
    return {"verified": verified, "message": message}
def _report_provenance_marker(report_data) -> tuple[dict | None, dict | None]:
    if not isinstance(report_data, dict):
        return None, _verdict(
            False, issue="报告数据形态无效（非对象），无法校验来源标记")
    prov = report_data.get("_step_provenance")
    if prov is None:
        return None, _verdict(False, issue="报告缺少来源标记 (_step_provenance)")
    if not isinstance(prov, dict):
        return None, _verdict(
            False, issue="报告来源标记格式无效 (_step_provenance 非对象)")
    return prov, None
def _report_content_hash(report_data: dict) -> str:
    content = {_k: _v for _k, _v in report_data.items()
               if _k != "_step_provenance"}
    return hashlib.sha256(
        _canonical_json(content).encode(_FINGERPRINT_ENCODING)).hexdigest()[:16]
def _require_report_claims(
        prov: dict, report_data: dict, expected_step: str | None,
        trusted_generators: frozenset[str] | None = None) -> None:
    _require_generator(prov, trusted_generators)
    _require_expected_step(prov, expected_step)
    expected_hash = _report_content_hash(report_data)
    actual_hash = prov.get("content_hash", "")
    if not _const_time_eq(actual_hash, expected_hash):
        raise ProvenanceError(
            f"报告内容哈希不匹配: 预期 {expected_hash}, 实际 {actual_hash!r}。"
            f"报告内容可能被篡改。"
        )
class ProvenanceGuard:
    @staticmethod
    def stamp(step_name: str, report_data: dict,
              generator: str | None = None) -> dict:
        content_hash = _report_content_hash(report_data)
        report_data["_step_provenance"] = {
            "step_name": step_name,
            "timestamp": datetime.now().strftime("%Y%m%d%H%M%S%f")[:17],
            "pid": os.getpid(),
            "content_hash": content_hash,
            "generator": generator or _PROVENANCE_GENERATOR,
        }
        return report_data
    @staticmethod
    def verify(report_data: dict | None = None, expected_step: str | None = None,
               skill_dir: str | None = None, *,
               trusted_generators: frozenset[str] | None = None,
               state_filename: str | None = None) -> dict:
        if report_data is None:
            if skill_dir is None:
                return _verdict(
                    False,
                    issue=("来源验证缺少输入（既无报告数据也无技能目录），"
                           "无法确认来源，拒绝放行"))
            return ProvenanceGuard._verify_state_file(
                skill_dir, state_filename)
        return ProvenanceGuard._verify_report_provenance(
            report_data, expected_step, trusted_generators)
    @staticmethod
    def _verify_state_file(skill_dir: str | None,
                           state_filename: str | None = None) -> dict:
        if skill_dir is None:
            return _verdict(
                False,
                issue=("来源验证缺少技能目录，无法定位状态文件，拒绝放行"))
        try:
            state_path = os.path.join(
                get_temp_base(skill_dir),
                state_filename or PIPELINE_STATE_FILENAME)
            if not os.path.lexists(state_path):
                return _verdict(
                    False,
                    issue=("Pipeline state file is missing; provenance is "
                           f"unmeasured and cannot be verified: {state_path}"))
            if not os.path.isfile(state_path):
                return _verdict(
                    False,
                    issue=("Pipeline state path is not a regular file; "
                           f"provenance cannot be verified: {state_path}"))
            state_data = StateIntegrityGuard.load_verified(
                skill_dir, state_path)
        except StateTamperError as e:
            _log.warning("[ProvenanceGuard] State file tampered: %s", e)
            return _verdict(
                False, issue=f"State file integrity check failed: {e}")
        except Exception as e:  # noqa: BLE001
            _log.warning("[ProvenanceGuard] State file verification error: %s", e)
            return _verdict(False, issue=f"State file verification error: {e}")
        if state_data is None:
            _log.warning(
                "[ProvenanceGuard] State file not loadable as signed JSON: %s",
                state_path)
            return _verdict(
                False,
                issue="State file exists but is corrupt or not signed JSON: "
                      f"{state_path}")
        return _verdict(True, "Pipeline state file HMAC signature verified")
    @staticmethod
    def _verify_report_provenance(report_data: dict,
                                  expected_step: str | None,
                                  trusted_generators: frozenset[str] | None = None) -> dict:
        prov, _shape_issue = _report_provenance_marker(report_data)
        if _shape_issue is not None:
            return _shape_issue
        try:
            _require_report_claims(
                prov, report_data, expected_step, trusted_generators)
        except ProvenanceError as _claim_err:
            _log.warning("[ProvenanceGuard] 报告来源声明校验失败: %s", _claim_err)
            return _verdict(False, issue=str(_claim_err))
        except (TypeError, ValueError, RecursionError, MemoryError) as _claim_err:
            _log.warning("[ProvenanceGuard] 报告来源内容校验异常: %s", _claim_err)
            return _verdict(
                False,
                issue=("报告来源内容无法规范化或计算哈希 "
                       f"({type(_claim_err).__name__}): {_claim_err}"))
        return {**_verdict(True, "来源验证通过"),
                "step_name": prov.get("step_name", "")}
def verify_provenance_logged(
        step_label: str, sd: str, *, state_filename: str | None = None) -> None:
    prov_result = ProvenanceGuard.verify(
        skill_dir=sd, state_filename=state_filename)
    if not prov_result.get("verified", False):
        _log.warning("[%s] 来源验证未通过: %s", step_label,
                     prov_result.get("issues", []))
def _source_fingerprint_strict(path: str) -> str:
    raw = snapshot_file_bytes(path)
    decode_source_strict(raw)
    return bytes_fingerprint(raw)
class RepCheck(NamedTuple):
    passed: bool
    rule: str
    message: str
class RepReport(NamedTuple):
    all_passed: bool
    checks: list[RepCheck]
    blocked_by: list[str]
class ReadBeforeWriteGuard:
    def __init__(self) -> None:
        self._read_log: dict[str, dict] = {}
    def mark_read(self, filepath: Any) -> int:
        filepath_str = str(filepath)
        entry: dict[str, Any] = {"timestamp": _time.time()}
        try:
            if os.path.isfile(filepath_str):
                entry["content_hash"] = _source_fingerprint_strict(
                    filepath_str)
        except (OSError, SourceReadError):
            _log.warning("[REP] mark_read 读取文件失败(不记录内容哈希)",
                         exc_info=True)
            entry["content_hash"] = None
        self._read_log[normalize_fs_key(filepath_str)] = entry
        return len(self._read_log)
    def enforce_rep1(self, filepath: Any) -> RepCheck:
        filepath_str = str(filepath)
        if normalize_fs_key(filepath_str) not in self._read_log:
            return RepCheck(
                passed=False, rule="REP-1",
                message=(f"文件 {filepath_str} 未被读取就尝试修改，"
                         f"违反 read-before-write 原则"))
        return RepCheck(passed=True, rule="REP-1", message="REP-1 通过")
    def enforce_rep2(self, source: Any, target: Any) -> RepCheck:
        source_str = str(source)
        target_str = str(target)
        if normalize_fs_key(source_str) != normalize_fs_key(target_str):
            return RepCheck(
                passed=False, rule="REP-3",
                message=(f"读取路径 {source_str} 与写入路径 {target_str} "
                         f"不一致，可能路径欺骗"))
        read_entry = self._read_log.get(normalize_fs_key(source_str))
        if read_entry is None:
            return RepCheck(passed=True, rule="REP-2",
                            message="未读取记录，跳过REP-2")
        stored_hash = read_entry.get("content_hash")
        if stored_hash is None:
            return RepCheck(
                passed=False, rule="REP-2",
                message=f"文件 {source_str} 未建立可验证的读取基线，拒绝写入")
        try:
            if not os.path.isfile(source_str):
                return RepCheck(
                    passed=False, rule="REP-2",
                    message=f"文件 {source_str} 在读取后被删除")
            if _source_fingerprint_strict(source_str) != stored_hash:
                return RepCheck(
                    passed=False, rule="REP-2",
                    message=f"文件 {source_str} 自上次读取后被外部修改（哈希不匹配）")
        except (OSError, SourceReadError) as exc:
            _log.warning("[REP] REP-2 校验读取文件失败(失败关闭): %s",
                         source_str, exc_info=True)
            return RepCheck(
                passed=False, rule="REP-2",
                message=(f"文件 {source_str} 在写入前无法重新读取"
                         f"({type(exc).__name__})，无法验证外部修改，拒绝写入"))
        return RepCheck(passed=True, rule="REP-2/3", message="REP-2/3 通过")
    def enforce_all(self, source_path: Any, target_path: Any) -> RepReport:
        checks: list[RepCheck] = []
        blocked_by: list[str] = []
        rep1 = self.enforce_rep1(source_path)
        checks.append(rep1)
        if not rep1.passed:
            blocked_by.append("REP-1")
        rep2 = self.enforce_rep2(source_path, target_path)
        checks.append(rep2)
        if not rep2.passed:
            blocked_by.append(rep2.rule)
        return RepReport(all_passed=not blocked_by, checks=checks,
                         blocked_by=blocked_by)
READ_BEFORE_WRITE_GUARD = ReadBeforeWriteGuard()
def enforce_read_before_write(source_path: str,
                              target_path: str | None = None) -> dict:
    report = READ_BEFORE_WRITE_GUARD.enforce_all(
        source_path=source_path,
        target_path=source_path if target_path is None else target_path)
    return {
        "passed": report.all_passed,
        "checks": [
            {"rep": c.rule, "passed": c.passed, "reason": c.message}
            for c in report.checks
        ],
        "blocked_by": list(report.blocked_by),
    }

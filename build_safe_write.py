from __future__ import annotations

import io
import logging
import os
import re
import shutil
import stat
import time
import tokenize
from dataclasses import dataclass
from typing import Any, Callable, Iterator, Self  # noqa: UP035 — 保持既有导入面预算

from jwsgj.diag_guard_io import (
    SourceReadError,
    _within_any_root,
    atomic_replace_bytes,
    atomic_write_text,
    bytes_fingerprint,
    decode_source_strict,
    format_diff_preview,
    guarded_open,
    path_identity,
    read_source_text_strict,
    read_text_bom,
    resolve_within_root,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    restore_file_bytes,
    snapshot_file_bytes,
)
from jwsgj.diag_types_defs import (
    ContractViolationError,
    GuardResult,
    OperationContext,
    is_read_only_audit,
    issues_guard_result,
    normalize_operation_kind,
    target_path_str,
)
from jwsgj.diag_types_normalize import (
    format_compact_ts,
    normalize_files_list,
    normalize_target_path,
)
from jwsgj.diag_types_vocab import (
    MSG_EXCEPTION_BROAD_HANDLER,
    PARSE_DEGRADE_EXC,
    GuardLevel,
    OperationType,
)
from jwsgj.log_config import (
    log_swallowed,
    safe_write_audit,
    write_module_run,
)
from jwsgj.runtime_paths import (
    BACKUP_SUBDIR_NAME,
    get_backup_base,
    get_legacy_backup_roots,
    get_skill_backup_roots,
    get_temp_base,
    resolve_workspace_root,
)
from jwsgj.runtime_scope import (
    LEGACY_BACKUP_DIR_NAME,
    RUNTIME_DIR_NAME,
    is_backup_artifact_name,
    normalize_skill_dir,
    strip_stale_coding_declaration,
)
from jwsgj.testsuite_runner import (
    run_post_write_regression,
    run_targeted_regression,
)

logger = logging.getLogger(__name__)
__all__ = [
    'BACKUP_DANGEROUS_OPS',
    'BACKUP_RETENTION_DAYS',
    'MIGRATE_BUDGET_BYTES',
    'ROLLBACK_SCAN_MAX_DEPTH',
    'UNKNOWN_SKILL_BUCKET',
    'BackupManager',
    'FixSafetyNet',
    'commit_writes',
    'copy_backup',
    'copytree_ignore',
    'file_backup',
    'find_rollback_state_file',
    'get_backup_dir',
    'get_backup_root',
    'guard_backup',
    'guard_path_sanitize',
    'guard_post_verify',
    'guard_safe_delete',
    'guard_snapshot_diff',
    'is_dangerous_operation',
    'is_rollback_state_name',
    'is_syntax_valid',
    'normalize_post_write_regression',
    'preflight_write_snapshot',
    'prune_all_backup_roots',
    'prune_backups',
    'quick_safe_backup',
    'resolve_backup_surface',
    'resolve_rollback_store',
    'restore_bytes',
    'restore_written_original',
    'rollback_state_filename',
    'rollback_state_search_dirs',
    'run_targeted_regression_for',
    'run_with_swap',
    'unique_backup_path',
]
UNKNOWN_SKILL_BUCKET = "unknown_skill"
_FALLBACK_BACKUP_WARNED = False
BACKUP_RETENTION_DAYS = 7
_DEFAULT_SOURCE_ENCODING = "utf-8"
MIGRATE_BUDGET_BYTES = 200 * 1024 * 1024
_BACKUP_DIR_TIMESTAMP_RE = re.compile(
    r"(?:^|_)\d{8}_\d{6}(?:_\d+)?\Z")
_BACKUP_CONTAINER_NAMES = frozenset({"executor_commit", "_legacy_skill"})
_PRUNE_COUNTER_KEYS = (
    "scanned", "deleted_files", "deleted_dirs", "freed_bytes",
    "protected", "errors",
)
_ROLLBACK_STATE_PREFIX = "_rollback_"
_ROLLBACK_STATE_SUFFIX = ".json"
ROLLBACK_SCAN_MAX_DEPTH = 2
_migrated_legacy_backups = False
_BACKUP_EXEMPT_OPS = frozenset({OperationType.ADD_IMPORT})
BACKUP_DANGEROUS_OPS = frozenset(OperationType) - _BACKUP_EXEMPT_OPS
@dataclass(frozen=True)
class _PruneScope:
    stats: dict
    protected: set
    cutoff: float
    dry_run: bool
    retention_days: float
def copy_backup(path: str, backup_path: str, is_dir: bool) -> None:
    if is_dir:
        ignore = copytree_ignore
        if _within_any_root(backup_path, [path]):
            destination = path_identity(backup_path)
            def _ignore_nested_destination(src: str, names: list[str]) -> list[str]:
                ignored = set(copytree_ignore(src, names))
                ignored.update(
                    name for name in names
                    if path_identity(os.path.join(src, name)) == destination)
                return [name for name in names if name in ignored]
            ignore = _ignore_nested_destination
        shutil.copytree(path, backup_path, ignore=ignore,
                        ignore_dangling_symlinks=True)
    else:
        shutil.copy2(path, backup_path)
    try:
        os.utime(backup_path, None)
    except OSError as exc:
        logger.warning("[Rollback] 备份产物 mtime 归一失败，备份按失败处理: %s (%s)",
                       backup_path, exc)
        raise
def _state_abspath(path: str) -> str:
    return os.path.abspath(path) if path else ""
def _explicit_target_path(ctx: OperationContext) -> str:
    if getattr(ctx, "_target_path_inferred", False):
        return ""
    return target_path_str(ctx)
def is_dangerous_operation(raw: Any) -> bool:
    kind = normalize_operation_kind(raw)
    if not isinstance(kind, OperationType):
        logger.warning("[Safety] 未识别的 operation %r，按危险操作处理（fail-closed）",
                       raw)
        return True
    return kind in BACKUP_DANGEROUS_OPS
def _operation_of(ctx: OperationContext) -> OperationType | None:
    kind = normalize_operation_kind(getattr(ctx, "operation", None))
    return kind if isinstance(kind, OperationType) else None
def _is_unknown_operation(ctx: OperationContext) -> bool:
    return not isinstance(
        normalize_operation_kind(getattr(ctx, "operation", None)),
        OperationType)
def _relocate_destination(ctx: OperationContext) -> str:
    if _operation_of(ctx) not in (
            OperationType.RENAME, OperationType.MOVE):
        return ""
    return _state_abspath(normalize_target_path(ctx.metadata.get("new_path", "")))
def _backup_target_list(target_path: str, affected_files,
                        relocate_dest: str = "") -> list[str]:
    candidates: list[str] = [target_path] if target_path else []
    candidates.extend(normalize_files_list(affected_files))
    if relocate_dest:
        candidates.append(relocate_dest)
    normalized = [p for p in (_state_abspath(c) for c in candidates) if p]
    return _dedupe_paths(normalized)
def resolve_backup_surface(ctx: OperationContext) -> tuple[str, list[str]]:
    target_path = _state_abspath(_explicit_target_path(ctx))
    affected_files = _backup_target_list(
        target_path, ctx.affected_files, _relocate_destination(ctx))
    return target_path, affected_files
def _raise_walk_error(err: OSError) -> None:
    raise err
def _walk_within_depth(
        top: str) -> Iterator[tuple[str, list[str], list[str]]]:
    root_depth = os.path.abspath(top).rstrip(os.sep).count(os.sep)
    for root_dir, dirs, files in os.walk(top, onerror=_raise_walk_error):
        rel_depth = (os.path.abspath(root_dir).rstrip(os.sep).count(os.sep)
                     - root_depth)
        if rel_depth >= ROLLBACK_SCAN_MAX_DEPTH:
            dirs[:] = []
        yield root_dir, dirs, files
def _walk_limited(top: str, target_name: str) -> str:
    try:
        for root_dir, _dirs, files in _walk_within_depth(top):
            if target_name in files:
                return os.path.join(root_dir, target_name)
    except OSError as _e:
        logger.warning("[Rollback] 状态文件遍历失败（该根按未命中处理）: %s (%s)",
                       top, _e)
    return ''
def _find_in_backup_root(rb_name: str) -> str:
    try:
        new_root = get_backup_root()
    except (OSError, RuntimeError, ValueError) as _e:
        logger.warning("[Rollback] 备份根解析失败,跳过新根通道: %s", _e)
        return ''
    if new_root and os.path.isdir(new_root):
        return _walk_limited(new_root, rb_name)
    return ''
def _find_in_workspace_base(search_dir: str, rb_name: str) -> str:
    try:
        temp_base = get_temp_base(search_dir)
    except (OSError, RuntimeError, ValueError) as _e:
        logger.warning("[Rollback] 工作空间根解析失败,跳过工作空间通道: %s", _e)
        return ''
    if temp_base:
        for sub in ('backup', BACKUP_SUBDIR_NAME, LEGACY_BACKUP_DIR_NAME):
            base = os.path.join(temp_base, sub)
            if os.path.isdir(base):
                found = _walk_limited(base, rb_name)
                if found:
                    return found
    return ''
def _find_in_legacy_backup_roots(rb_name: str) -> str:
    for sys_temp in get_legacy_backup_roots():
        if not os.path.isdir(sys_temp):
            continue
        try:
            skill_subs = os.listdir(sys_temp)
        except OSError:
            logger.warning("[Rollback] 旧根列举失败,跳过: %s", sys_temp,
                           exc_info=True)
            continue
        for skill_sub in skill_subs:
            candidate = os.path.join(sys_temp, skill_sub, rb_name)
            if os.path.isfile(candidate):
                return candidate
        candidate = os.path.join(sys_temp, rb_name)
        if os.path.isfile(candidate):
            return candidate
    return ''
def rollback_state_search_dirs() -> list[str]:
    candidates = (
        os.environ.get('JWSGJ_SKILL_DIR', '').strip(),
        os.path.dirname(__file__),
    )
    dirs: list[str] = []
    seen: set[str] = set()
    for candidate in candidates:
        if not candidate:
            continue
        normalized = normalize_skill_dir(candidate)
        identity = path_identity(normalized)
        if identity in seen:
            continue
        seen.add(identity)
        dirs.append(normalized)
    return dirs
def find_rollback_state_file(rollback_id: str, search_dir: str) -> str:
    if not is_valid_rollback_id(rollback_id):
        logger.warning("[Rollback] 非法回滚 ID %r，拒绝定位状态文件", rollback_id)
        return ''
    rb_name = rollback_state_filename(rollback_id)
    return (_find_in_backup_root(rb_name)
            or _find_in_workspace_base(search_dir, rb_name)
            or _find_in_legacy_backup_roots(rb_name))
def _collect_movable_entries(legacy: str, cutoff: float) -> list[tuple[str, str]]:
    movable: list[tuple[str, str]] = []
    moved_bytes = 0
    for name in sorted(os.listdir(legacy)):
        src = os.path.join(legacy, name)
        remaining = MIGRATE_BUDGET_BYTES - moved_bytes
        try:
            if os.path.getmtime(src) < cutoff:
                continue
            size = _entry_size(src, limit=remaining)
        except OSError as _e:
            logger.debug("[BackupRoot] 旧根条目 stat 失败跳过迁移: %s (%s)", src, _e)
            continue
        if size > remaining:
            logger.warning(
                "[BackupRoot] 旧备份迁移超出单次预算(%dMB)，剩余条目不迁移"
                "（回滚仍可查旧根）: %s",
                MIGRATE_BUDGET_BYTES // 1048576, legacy)
            break
        moved_bytes += size
        movable.append((name, src))
    return movable
def _move_legacy_entries(new_root: str, legacy: str,
                         movable: list[tuple[str, str]], days: int) -> int:
    target_parent = os.path.join(new_root, "_legacy_skill")
    os.makedirs(target_parent, exist_ok=True)
    moved_count = 0
    for name, src in movable:
        dst = os.path.join(target_parent, name)
        if os.path.exists(dst):
            logger.debug("[BackupRoot] 旧根条目目标已存在,跳过迁移: %s", dst)
            continue
        shutil.move(src, dst)
        moved_count += 1
    if moved_count:
        logger.info("[BackupRoot] 旧备份已迁移(%d 项/%d 天以内): %s -> %s",
                    moved_count, days, legacy, target_parent)
    else:
        logger.debug("[BackupRoot] 旧根条目均已存在或跳过,未发生迁移: %s -> %s",
                     legacy, target_parent)
    return moved_count
def _migrate_one_legacy_root(new_root: str, legacy: str,
                             cutoff: float, days: int) -> None:
    try:
        if not os.path.isdir(legacy):
            return
        if os.path.abspath(legacy) == os.path.abspath(new_root):
            return
        movable = _collect_movable_entries(legacy, cutoff)
        if movable:
            _move_legacy_entries(new_root, legacy, movable, days)
    except (OSError, shutil.Error) as _e:
        logger.warning("[BackupRoot] 旧备份迁移失败（不影响新备份写入）: %s", _e)
def _migrate_legacy_backups(new_root: str,
                            legacy_dirs: list | None = None,
                            keep_days: int | None = None) -> None:
    days = BACKUP_RETENTION_DAYS if keep_days is None else keep_days
    cutoff = time.time() - days * 86400
    for legacy in (get_legacy_backup_roots() if legacy_dirs is None else legacy_dirs):
        _migrate_one_legacy_root(new_root, legacy, cutoff, days)
def _system_temp_root() -> str:
    for name in ("TMPDIR", "TEMP", "TMP"):
        value = os.environ.get(name, "").strip()
        if value and os.path.isdir(value):
            return os.path.normpath(value)
    return ""
def _warn_fallback(exc: BaseException) -> None:
    global _FALLBACK_BACKUP_WARNED
    if _FALLBACK_BACKUP_WARNED:
        return
    _FALLBACK_BACKUP_WARNED = True
    logger.warning(
        "[BackupRoot] 会话工作空间不可用，通用备份通道改用兜底根"
        "（可恢复但不参与工作空间回收面；同类提示只记一次）: %s", exc)
def _fallback_backup_root(skill_dir: str | None) -> str:
    anchor = skill_dir or os.getcwd()
    project_root = _find_project_root(anchor)
    if project_root and not _is_skill_root(project_root):
        return os.path.join(project_root, "Temp", BACKUP_SUBDIR_NAME)
    system_temp = _system_temp_root()
    if system_temp:
        digest = bytes_fingerprint(os.fsencode(project_root or anchor))[:12]
        return os.path.join(system_temp, LEGACY_BACKUP_DIR_NAME,
                            digest, BACKUP_SUBDIR_NAME)
    return os.path.join(project_root or os.path.abspath(os.curdir),
                        "Temp", BACKUP_SUBDIR_NAME)
def _fallback_backup_dir(target_path: str) -> str:
    project_root = _find_project_root(target_path)
    name = (os.path.basename(project_root.rstrip("/\\"))
            if project_root else UNKNOWN_SKILL_BUCKET)
    return os.path.join(_fallback_backup_root(target_path), name)
def get_backup_root(skill_dir: str | None = None) -> str:
    global _migrated_legacy_backups
    root = get_backup_base(skill_dir)
    if not _migrated_legacy_backups:
        _migrate_legacy_backups(root)
        _migrated_legacy_backups = True
    return root
_PROJECT_ROOT_FILE_MARKERS = (
    "pyproject.toml", "setup.py", "setup.cfg", "tox.ini",
    "requirements.txt", "Pipfile", "poetry.lock", "uv.lock",
    "manage.py",
)
_PROJECT_ROOT_DIR_MARKERS = (".git", ".hg", ".svn")
_SKILL_ROOT_MARKER = "SKILL.md"
def _search_upwards(target_path: str, is_root) -> str:
    current = (os.path.abspath(target_path) if os.path.isdir(target_path)
               else os.path.dirname(os.path.abspath(target_path)))
    while current:
        if is_root(current):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return ""
        current = parent
    return ""
def _is_skill_root(directory: str) -> bool:
    return os.path.isfile(os.path.join(directory, _SKILL_ROOT_MARKER))
def _is_project_root(directory: str) -> bool:
    if _is_skill_root(directory):
        return True
    if any(os.path.isfile(os.path.join(directory, marker))
           for marker in _PROJECT_ROOT_FILE_MARKERS):
        return True
    return any(os.path.isdir(os.path.join(directory, marker))
               for marker in _PROJECT_ROOT_DIR_MARKERS)
def _find_project_root(target_path: str) -> str:
    return _search_upwards(target_path, _is_project_root)
def _project_backup_bucket(project_root: str) -> str:
    project_name = os.path.basename(project_root.rstrip("/\\"))
    identity = path_identity(project_root).encode("utf-8", "surrogatepass")
    return f"{project_name}-{bytes_fingerprint(identity)[:8]}"
def get_backup_dir(target_path: str) -> str:
    project_root = _find_project_root(target_path)
    bucket = (_project_backup_bucket(project_root) if project_root
              else UNKNOWN_SKILL_BUCKET)
    try:
        root = get_backup_root()
    except (OSError, RuntimeError, ValueError) as exc:
        _warn_fallback(exc)
        root = _fallback_backup_root(target_path)
    return os.path.join(root, bucket)
def resolve_rollback_store(skill_dir: str,
                           backup_dir: str = "") -> tuple[str, str]:
    normalized = normalize_skill_dir(skill_dir)
    if backup_dir:
        resolved_backup = normalize_target_path(backup_dir)
        if resolved_backup and os.path.isabs(resolved_backup):
            return normalized, os.path.abspath(resolved_backup)
        logger.warning("[Rollback] backup_dir 形态非法或不是绝对路径 %r，"
                       "回退到默认存储根", backup_dir)
    try:
        root = get_backup_root(normalized)
    except (OSError, RuntimeError, ValueError) as e:  # jwsgj:silent-ok 兜底根降级已由 _warn_fallback 限量留痕
        _warn_fallback(e)
        root = _fallback_backup_root(normalized)
    return normalized, os.path.join(root, "_rollback")
_PRUNE_MIN_INTERVAL = 30.0
_prune_gate: dict[str, float] = {}
def _prune_due(backup_dir: str) -> bool:
    now = time.monotonic()
    try:
        key = os.path.normcase(os.path.abspath(backup_dir))
    except (OSError, ValueError):  # jwsgj:silent-ok abspath 失败时退回原路径，纯值回退
        key = backup_dir
    last = _prune_gate.get(key)
    if last is not None and now - last < _PRUNE_MIN_INTERVAL:
        return False
    if len(_prune_gate) > 512:
        _prune_gate.clear()
    _prune_gate[key] = now
    return True
def _prune_after_backup(backup_dir: str = "") -> None:
    try:
        target = backup_dir or get_backup_root()
    except (OSError, RuntimeError, ValueError) as exc:
        logger.debug("[BackupPrune] 备份根不可用，跳过保留期裁剪: %s", exc)
        return
    if not _prune_due(target):
        return
    try:
        prune_backups(target)
    except Exception:
        logger.warning("[BackupPrune] prune_backups failed", exc_info=True)
def unique_backup_path(backup_dir: str, base_name: str, ext: str = "") -> str:
    pattern = re.compile(
        rf"{re.escape(base_name)}(?:_(\d+))?{re.escape(ext)}\Z")
    try:
        names = os.listdir(backup_dir)
    except OSError:
        names = []
    latest = -1
    for name in names:
        match = pattern.fullmatch(name)
        if match is not None:
            latest = max(latest, int(match.group(1) or 0))
    suffix = latest + 1
    candidate = os.path.join(
        backup_dir,
        f"{base_name}{f'_{suffix}' if suffix else ''}{ext}")
    while os.path.exists(candidate):
        suffix += 1
        candidate = os.path.join(backup_dir, f"{base_name}_{suffix}{ext}")
    return candidate
def copytree_ignore(_src: str, names: list[str]) -> list[str]:
    ignored = {'__pycache__'}
    if not _src or _is_skill_root(_src):
        ignored.add(RUNTIME_DIR_NAME.lower())
    return [n for n in names if n.lower() in ignored]
def _backup_name_sort_key(name: str, prefix: str) -> tuple[str, int]:
    tail = name[len(prefix):]
    match = re.fullmatch(
        r"(\d{8}_\d{6}_\d{3})(?:_(\d+))?", tail)
    if match is None:
        return tail, -1
    return match.group(1), int(match.group(2) or 0)
class BackupManager:
    MAX_BACKUPS_PER_FILE = 5
    def __init__(self: Self, skill_dir: str) -> None:
        self.skill_dir = skill_dir
        try:
            self.backup_root = get_backup_root(skill_dir)
        except (OSError, RuntimeError, ValueError) as exc:  # jwsgj:silent-ok 兜底根降级已由 _warn_fallback 限量留痕
            _warn_fallback(exc)
            self.backup_root = _fallback_backup_root(skill_dir)
        self._backed_up: dict[str, None] = {}
        self._backed_up_ids: set[str] = set()
    def _backup_stem(self: Self, src: str) -> str:
        raw = os.fspath(src)
        try:
            identity = os.path.realpath(raw)
        except OSError as _e:
            log_swallowed(__name__, _e, context='BackupManager._backup_stem:OSError')
            identity = raw
        digest = bytes_fingerprint(
            identity.encode("utf-8", "surrogatepass"))[:8]
        return (f"{os.path.basename(os.path.dirname(raw))}_"
                f"{os.path.basename(raw)}.{digest}")
    def backup_file(self: Self, filepath: str) -> str:
        src = os.fspath(filepath)
        if not os.path.exists(src):
            raise ContractViolationError(
                f"备份失败: 文件不存在: {filepath}"
            )
        now = time.time()
        timestamp = time.strftime("%Y%m%d_%H%M%S", time.localtime(now))
        millis = str(int(now * 1000) % 1000).zfill(3)
        backup_path = unique_backup_path(
            self.backup_root,
            f"{self._backup_stem(src)}.bak_{timestamp}_{millis}")
        try:
            os.makedirs(self.backup_root, exist_ok=True)
            copy_backup(src, backup_path, False)
            self._backed_up[src] = None
            self._backed_up_ids.add(path_identity(src))
            logger.info("[Backup] 已备份 %s → %s",
                        os.path.basename(src), backup_path)
        except OSError as e:
            logger.debug("备份 IO 失败转 ContractViolationError 抛出: %s", e)
            raise ContractViolationError(
                f"备份失败: {filepath} → {backup_path}: {e}"
            ) from e
        self._prune_old_backups(src)
        write_module_run(
            "build_safe_write", "BackupManager.backup_file",
            file=os.path.basename(src), backup=os.path.basename(backup_path))
        return backup_path
    def _prune_old_backups(self: Self, src: str) -> None:
        try:
            if not os.path.exists(self.backup_root):
                return
            prefix = f"{self._backup_stem(src)}.bak_"
            olds = sorted(
                (name for name in os.listdir(self.backup_root)
                 if name.startswith(prefix)),
                key=lambda name: _backup_name_sort_key(name, prefix))
            keep = max(int(self.MAX_BACKUPS_PER_FILE), 0)
            for stale in olds[:max(len(olds) - keep, 0)]:
                if safe_delete(os.path.join(self.backup_root, stale)):
                    logger.debug("[Backup] 清理超量备份: %s", stale)
                else:
                    logger.warning("[Backup] 清理超量备份失败: %s", stale)
        except OSError as e:
            logger.warning("[Backup] 超量备份裁剪失败（不影响已创建备份）: %s", e)
    def is_backed_up(self: Self, filepath: str) -> bool:
        return path_identity(filepath) in self._backed_up_ids
    def ensure_backed_up(self: Self, filepath: str) -> None:
        if not self.is_backed_up(filepath):
            self.backup_file(filepath)
    @property
    def backed_up_files(self: Self) -> list[str]:
        return list(self._backed_up)
def _snapshot_name(target_path: str, timestamp: str, is_dir: bool) -> tuple[str, str]:
    if is_dir:
        return f"{os.path.basename(os.path.abspath(target_path))}_{timestamp}", ""
    return f"{os.path.basename(target_path)}.{timestamp}", ".bak"
def _create_snapshot(target_path: str, backup_dir: str,
                     timestamp: str, is_dir: bool) -> str | None:
    base_name, ext = _snapshot_name(target_path, timestamp, is_dir)
    backup_path = unique_backup_path(backup_dir, base_name, ext)
    try:
        copy_backup(target_path, backup_path, is_dir)
    except OSError as e:
        logger.warning("[FileBackup] 快照复制失败（is_dir=%s，返回 None 由外层降级）: %s (%s)",
                       is_dir, target_path, e)
        return None
    _prune_after_backup(os.path.dirname(backup_path))
    return backup_path
def file_backup(target_path: str) -> str | None:
    target_path = normalize_target_path(target_path)
    if not target_path:
        return None
    try:
        backup_dir = get_backup_dir(target_path)
    except (OSError, RuntimeError, ValueError) as e:  # jwsgj:silent-ok 兜底根降级已由 _warn_fallback 限量留痕
        _warn_fallback(e)
        backup_dir = _fallback_backup_dir(target_path)
    if not os.path.exists(target_path):
        return None
    try:
        os.makedirs(backup_dir, exist_ok=True)
    except OSError as e:
        logger.warning("[FileBackup] 备份目录创建失败（返回 None 由外层降级）: %s (%s)", target_path, e)
        return None
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    is_dir = os.path.isdir(target_path)
    if not is_dir and not os.path.isfile(target_path):
        return None
    return _create_snapshot(target_path, backup_dir, timestamp, is_dir)
def _walk_tree_size(path: str, limit: int | None) -> int:
    total = 0
    for _root, _dirs, _files in os.walk(path):
        for _name in _files:
            _fp = os.path.join(_root, _name)
            try:
                if not os.path.islink(_fp):
                    total += os.path.getsize(_fp)
            except OSError as _e:
                logger.debug("[BackupSize] walk 内文件体积获取失败跳过: %s (%s)", _fp, _e)
            if limit is not None and total > limit:
                return total
    return total
def _entry_size(path: str, limit: int | None = None) -> int:
    if not os.path.isdir(path):
        try:
            return os.path.getsize(path)
        except OSError as _e:
            logger.debug(
                "[BackupSize] 文件体积获取失败计 0（竞态口径）: %s (%s)",
                path, _e)
            return 0
    return _walk_tree_size(path, limit)
def _dedupe_paths(paths: list[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for p in paths:
        key = path_identity(p)
        if key not in seen:
            seen.add(key)
            result.append(p)
    return result
def _normalize_retention_days(raw: Any) -> float:
    if isinstance(raw, bool) or not isinstance(raw, (int, float)):
        reason = "类型非法"
    elif raw != raw:  # noqa: PLR0124 — IEEE 754 NaN 自不等判定
        reason = "为非有限值（nan 会令新鲜备份整体误删）"
    elif raw in (float("inf"), float("-inf")):
        reason = "超出浮点表示范围（无法参与保留期计算）"
    elif raw < 0:
        reason = "为负（分界将落在未来致新鲜备份整体误删）"
    else:
        try:
            return float(raw)
        except OverflowError as _overflow:
            log_swallowed(__name__, _overflow,
                          context='_normalize_retention_days:OverflowError')
            reason = "超出浮点表示范围（无法参与保留期计算）"
    logger.warning('retention_days %s %r，已回退默认保留期 %s 天',
                   reason, raw, BACKUP_RETENTION_DAYS)
    return float(BACKUP_RETENTION_DAYS)
def _prune_expired_file(entry: str, label: str, scope: _PruneScope) -> None:
    stats = scope.stats
    try:
        if os.path.getmtime(entry) >= scope.cutoff:
            return
        size = os.path.getsize(entry)
        if not scope.dry_run and not safe_delete(entry):
            stats["errors"] += 1
            return
        stats["freed_bytes"] += size
        stats["deleted_files"] += 1
    except OSError as _e:
        logger.debug("[BackupPrune] %s裁剪失败: %s (%s)", label, entry, _e)
        stats["errors"] += 1
def rollback_state_filename(rollback_id: str) -> str:
    return f"{_ROLLBACK_STATE_PREFIX}{rollback_id}{_ROLLBACK_STATE_SUFFIX}"
_ROLLBACK_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\Z")
def is_valid_rollback_id(rollback_id: Any) -> bool:
    if not isinstance(rollback_id, str) or not rollback_id:
        return False
    if ".." in rollback_id:
        return False
    return _ROLLBACK_ID_RE.match(rollback_id) is not None
def is_rollback_state_name(name: str) -> bool:
    return (name.startswith(_ROLLBACK_STATE_PREFIX)
            and name.endswith(_ROLLBACK_STATE_SUFFIX))
def _is_link_or_junction(path: str) -> bool:
    if os.path.islink(path):
        return True
    is_junction = getattr(os.path, "isjunction", None)
    if callable(is_junction) and is_junction(path):
        return True
    if os.name == "nt" and os.path.lexists(path):
        attributes = getattr(os.lstat(path), "st_file_attributes", 0)
        reparse_point = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0)
        return bool(attributes & reparse_point)
    return False
def _prune_entry(entry: str, name: str, depth: int,
                 scope: _PruneScope) -> None:
    try:
        if _is_link_or_junction(entry):
            scope.stats["protected"] += 1
            logger.debug("[BackupPrune] 跳过目录链接或符号链接: %s", entry)
            return
        is_dir = os.path.isdir(entry)
    except OSError as _e:
        logger.debug("[BackupPrune] isdir 失败: %s (%s)", entry, _e)
        scope.stats["errors"] += 1
        return
    if is_dir:
        _prune_child_dir(entry, depth, scope)
        return
    if is_rollback_state_name(name):
        _prune_expired_file(entry, "回滚状态文件", scope)
        return
    if not is_backup_artifact_name(name):
        return
    if scope.protected and _covers_protected(path_identity(entry),
                                            scope.protected):
        scope.stats["protected"] += 1
        return
    _prune_expired_file(entry, "备份文件", scope)
def _prune_dir(path: str, depth: int, scope: _PruneScope) -> None:
    try:
        names = sorted(os.listdir(path))
    except OSError as _e:
        logger.debug("[BackupPrune] listdir 失败: %s (%s)", path, _e)
        scope.stats["errors"] += 1
        return
    for name in names:
        scope.stats["scanned"] += 1
        _prune_entry(os.path.join(path, name), name, depth, scope)
def _remove_expired_dir(entry: str, scope: _PruneScope) -> None:
    entry_size = _entry_size(entry)
    if not scope.dry_run:
        safe_delete(entry)
        if os.path.isdir(entry):
            scope.stats["errors"] += 1
            return
    scope.stats["freed_bytes"] += entry_size
    scope.stats["deleted_dirs"] += 1
def _is_backup_dir_artifact(entry: str) -> bool:
    name = os.path.basename(entry)
    if name.lower().endswith(".dirbak"):
        return True
    if _BACKUP_DIR_TIMESTAMP_RE.search(name):
        return True
    parent_name = os.path.basename(os.path.dirname(entry)).lower()
    return parent_name in _BACKUP_CONTAINER_NAMES
def _prune_child_dir(entry: str, depth: int, scope: _PruneScope) -> None:
    is_snapshot = _is_backup_dir_artifact(entry)
    if _rollback_referenced_dir(entry, scope.protected, cutoff=scope.cutoff):
        scope.stats["protected"] += 1
    else:
        try:
            expired = os.path.getmtime(entry) < scope.cutoff
        except OSError as _e:
            logger.debug("[BackupPrune] 目录 mtime 获取失败: %s (%s)", entry, _e)
            scope.stats["errors"] += 1
            return
        if expired and is_snapshot:
            _remove_expired_dir(entry, scope)
            return
    if is_snapshot:
        return
    if depth + 1 < ROLLBACK_SCAN_MAX_DEPTH:
        _prune_dir(entry, depth + 1, scope)
def _empty_prune_stats(dry_run: bool) -> dict:
    stats = dict.fromkeys(_PRUNE_COUNTER_KEYS, 0)
    stats["dry_run"] = dry_run
    return stats
def _prune_and_report(backup_dir: str, scope: _PruneScope) -> dict:
    stats = scope.stats
    if _is_link_or_junction(backup_dir):
        stats["protected"] += 1
        logger.warning("[BackupPrune] 备份根是符号链接/目录联接，"
                       "为防止越根裁剪已跳过: %s", backup_dir)
    elif os.path.isdir(backup_dir):
        _prune_dir(backup_dir, 0, scope)
    if (stats["deleted_files"] or stats["deleted_dirs"]) and not scope.dry_run:
        logger.info("[BackupPrune] 清理过期备份(%s 天): %s",
                    scope.retention_days, stats)
    return stats
def prune_backups(backup_dir: str | None = None,
                  retention_days: float = BACKUP_RETENTION_DAYS,
                  dry_run: bool = False) -> dict:
    retention_days = _normalize_retention_days(retention_days)
    if backup_dir is None:
        backup_dir = get_backup_root()
    else:
        backup_dir = normalize_target_path(backup_dir)
    if not os.path.isdir(backup_dir):
        if backup_dir and os.path.exists(backup_dir):
            logger.warning("[BackupPrune] 裁剪目标不是目录，跳过: %s",
                           backup_dir)
        return _empty_prune_stats(dry_run)
    cutoff = time.time() - retention_days * 86400
    protected, protection_errors = _collect_protected_for_roots(
        [backup_dir], cutoff=cutoff)
    stats = _empty_prune_stats(dry_run)
    if protection_errors:
        stats["errors"] = protection_errors
        logger.warning(
            "[BackupPrune] 回滚保护扫描不完整(%d 个根失败)，"
            "已中止整个裁剪: %s", protection_errors, backup_dir)
        return stats
    scope = _PruneScope(
        stats=stats,
        protected=protected,
        cutoff=cutoff,
        dry_run=dry_run,
        retention_days=retention_days,
    )
    return _prune_and_report(backup_dir, scope)
def prune_all_backup_roots(retention_days: float = BACKUP_RETENTION_DAYS,
                           dry_run: bool = False) -> dict:
    retention_days = _normalize_retention_days(retention_days)
    try:
        primary_root = get_backup_root()
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[BackupPrune] 主备份根不可用，跳过该裁剪候选: %s", exc)
        primary_root = ""
    candidates = _dedupe_paths(
        ([primary_root] if primary_root else []) + get_skill_backup_roots()
        + get_legacy_backup_roots())
    cutoff = time.time() - retention_days * 86400
    protected, protection_errors = _collect_protected_for_roots(
        candidates, cutoff)
    roots: list[dict] = []
    total = _empty_prune_stats(dry_run)
    for cand in candidates:
        exists = os.path.isdir(cand)
        stats = None
        if exists:
            stats = _empty_prune_stats(dry_run)
            if not protection_errors:
                stats = _prune_and_report(cand, _PruneScope(
                    stats=stats, protected=protected,
                    cutoff=cutoff, dry_run=dry_run,
                    retention_days=retention_days))
        roots.append({"path": cand, "exists": exists, "stats": stats})
        if stats is None:
            continue
        for key in _PRUNE_COUNTER_KEYS:
            total[key] += stats[key]
    if protection_errors:
        total["errors"] = protection_errors
        logger.warning(
            "[BackupPrune] 回滚保护扫描不完整(%d 个根失败)，"
            "已中止全部备份根裁剪", protection_errors)
    return {"roots": roots, "total": total}
def _rollback_state_fresh(path: str, cutoff: float | None) -> bool:
    if cutoff is None:
        return True
    try:
        return os.path.getmtime(path) >= cutoff
    except OSError as _e:
        logger.debug("[Rollback] 状态文件 mtime 获取失败（按新鲜保护，防止误删回滚依据）: %s (%s)", path, _e)
        return True
def _protected_from_rollback_file(
        state_path: str, cutoff: float | None,
) -> tuple[set, bool]:
    if not _rollback_state_fresh(state_path, cutoff):
        return set(), True
    state, status, load_err = read_json_artifact(state_path)
    if status != "ok":
        logger.warning("[Rollback] 新鲜状态文件读取/解析失败，本次裁剪失败关闭: %s (%s)",
                       state_path, load_err or status)
        return set(), False
    if not isinstance(state, dict):
        logger.warning("[Rollback] 新鲜状态文件顶层不是对象，本次裁剪失败关闭: %s",
                       state_path)
        return set(), False
    backups_map = state.get("backups")
    if not isinstance(backups_map, dict):
        logger.warning("[Rollback] 新鲜状态文件缺少合法 backups 映射，"
                       "本次裁剪失败关闭: %s", state_path)
        return set(), False
    protected: set[str] = set()
    for bp in backups_map.values():
        if not isinstance(bp, str) or not bp.strip():
            logger.warning("[Rollback] 新鲜状态文件含非法备份路径 %r，"
                           "本次裁剪失败关闭", bp)
            return set(), False
        try:
            protected.add(path_identity(bp))
        except (OSError, *PARSE_DEGRADE_EXC) as _e:
            logger.warning("[Rollback] 备份路径 realpath 归一失败，"
                           "本次裁剪失败关闭: %r (%s)", bp, _e)
            return set(), False
    return protected, True
def _covers_protected(path: str, protected: set) -> bool:
    path_keys = {path, os.path.normcase(path)}
    for ref in protected:
        ref_keys = {ref, os.path.normcase(ref)}
        for key in path_keys:
            prefix = key.rstrip("/\\") + os.sep
            for ref_key in ref_keys:
                ref_prefix = ref_key.rstrip("/\\") + os.sep
                if (ref_key == key or ref_key.startswith(prefix)
                        or key.startswith(ref_prefix)):
                    return True
    return False
def _rollback_referenced_dir(entry: str, protected: set,
                             cutoff: float | None = None) -> bool:
    try:
        for name in os.listdir(entry):
            if (is_rollback_state_name(name)
                    and _rollback_state_fresh(os.path.join(entry, name), cutoff)):
                return True
    except OSError as _e:
        logger.debug("[Rollback] 目录列举失败（跳过状态文件检查，祖先保护判定继续）: %s (%s)", entry, _e)
    real = path_identity(entry)
    return _covers_protected(real, protected)
def _collect_protected_for_roots(
        roots: list[str], cutoff: float | None,
) -> tuple[set, int]:
    try:
        temp_base = get_temp_base()
    except (OSError, RuntimeError, ValueError) as _e:
        logger.warning("[Rollback] 工作空间根解析失败,跳过工作空间保护扫描通道: %s", _e)
        temp_base = ''
    scan_dirs: list[str] = []
    for root in roots:
        scan_dirs.extend([root, os.path.dirname(root)])
    if temp_base:
        scan_dirs.extend(os.path.join(temp_base, sub) for sub in (
            'backup', BACKUP_SUBDIR_NAME, LEGACY_BACKUP_DIR_NAME))
    scan_dirs.extend(get_legacy_backup_roots())
    protected: set[str] = set()
    scan_errors = 0
    for scan_dir in _dedupe_paths(scan_dirs):
        if os.path.isdir(scan_dir):
            found, errors = _protected_paths_from_dir(scan_dir, cutoff)
            protected |= found
            scan_errors += errors
    return protected, scan_errors
def _protected_paths_from_dir(
        scan_dir: str, cutoff: float | None,
) -> tuple[set, int]:
    protected: set[str] = set()
    try:
        for root_dir, _dirs, files in _walk_within_depth(scan_dir):
            for entry in files:
                if not is_rollback_state_name(entry):
                    continue
                found, valid = _protected_from_rollback_file(
                    os.path.join(root_dir, entry), cutoff)
                protected |= found
                if not valid:
                    return protected, 1
    except OSError as _e:
        logger.warning("[Rollback] 扫描目录 walk 失败，保护集不完整，本次裁剪失败关闭: %s (%s)",
                       scan_dir, _e, exc_info=True)
        return protected, 1
    return protected, 0
def _guard_backup_targets(ctx: OperationContext) -> list[tuple[str, bool]]:
    primary, backup_paths = resolve_backup_surface(ctx)
    targets: list[tuple[str, bool]] = [(primary, True)] if primary else []
    targets.extend((path, False) for path in backup_paths if path != primary)
    return targets
_BACKUP_CREATE_OPS = frozenset({
    OperationType.WRITE_FILE, OperationType.REFACTOR, OperationType.SPLIT,
    OperationType.MERGE,
})
def _run_backup_targets(ctx: OperationContext,
                        targets: list[tuple[str, bool]]) -> tuple[list[str], list[str]]:
    backup_paths: list[str] = []
    failures: list[str] = []
    for path, required in targets:
        exists = os.path.exists(path)
        if not exists and (not required
                           or _operation_of(ctx) in _BACKUP_CREATE_OPS):
            continue
        backup_path = file_backup(path)
        if backup_path:
            backup_paths.append(backup_path)
        else:
            failures.append(path)
    return backup_paths, failures
def guard_backup(ctx: OperationContext) -> GuardResult:
    if not is_dangerous_operation(ctx.operation):
        return GuardResult(guard_name="G1", passed=True, message="非危险操作,跳过备份")
    if is_read_only_audit(ctx):
        return GuardResult(guard_name="G1", passed=True,
                           message="只读审计,跳过备份（无写操作,无回滚需求）")
    auto_backup = ctx.metadata.get("auto_backup")
    if auto_backup is None:
        auto_backup = True
    if not auto_backup:
        return GuardResult(guard_name="G1", passed=True, level=GuardLevel.WARN,
                           message="auto_backup=False,跳过备份（风险自负）")
    if ctx.dry_run:
        return GuardResult(guard_name="G1", passed=True, message="dry_run 模式,跳过备份")
    targets = _guard_backup_targets(ctx)
    if not targets:
        return GuardResult(guard_name="G1", passed=True, level=GuardLevel.WARN,
                           message="无可备份目标（target_path 与 affected_files 均为空）")
    backup_paths, failures = _run_backup_targets(ctx, targets)
    if failures:
        shown = "; ".join(failures)
        return GuardResult(guard_name="G1", passed=False, level=GuardLevel.BLOCK,
                           message=(f"备份失败: {len(failures)} 个路径未产出备份"
                                    f"（{shown}）"),
                           fix_suggestion="手动创建备份后重试")
    if not backup_paths:
        return GuardResult(guard_name="G1", passed=True, level=GuardLevel.WARN,
                           message="无需备份（目标不存在，或为新建产物）")
    return GuardResult(guard_name="G1", passed=True,
                       message=f"备份成功: {'; '.join(backup_paths)}")
def quick_safe_backup(target_path: str, reason: str = "") -> str | None:
    backup_path = file_backup(target_path)
    if not isinstance(reason, str):
        logger.warning('reason 类型非法 %r，已归一空串', reason)
        reason = ''
    if backup_path and reason:
        logger.info("[QuickBackup] 备份完成: %s (原因: %s)",
                    backup_path, reason)
    return backup_path
def _log_net_trace(entry: str, outcome: str, t0: float,
                   **payload: Any) -> None:
    write_module_run(
        "build_safe_write", entry, outcome=outcome,
        duration_ms=(time.monotonic() - t0) * 1000.0, **payload)
_BACKUP_SUFFIX_LIMIT = 1000
def _backup_failed(filepath: str, started: float, message: str,
                   exc: BaseException | None = None) -> str:
    if exc is None:
        logger.warning("安全网: %s %s", message, filepath)
    else:
        logger.warning("安全网: %s %s: %s", message, filepath, exc)
    _log_net_trace("FixSafetyNet.create_backup", "failed", started,
                   file=filepath)
    return ""
def _open_backup_exclusive(
        backup_dir: str, filepath: str, source_encoding: str):
    _ms = time.time_ns() // 1_000_000
    ts = format_compact_ts(_ms)
    basename = os.path.basename(filepath)
    digest = bytes_fingerprint(os.fsencode(os.path.abspath(filepath)))[:8]
    for suffix in range(_BACKUP_SUFFIX_LIMIT):
        tail = f"_{suffix}" if suffix else ""
        backup_path = os.path.join(
            backup_dir, f"{basename}.bak_{ts}_{digest}{tail}")
        try:
            return open(backup_path, "x", encoding=source_encoding, newline=""), backup_path  # jwsgj:suppress B02 RB-03 RB-11 — 备份句柄所有权移交调用方，由调用方 with/close
        except FileExistsError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_open_backup_exclusive:FileExistsError')
            continue
    raise FileExistsError(
        f"备份路径序号耗尽({_BACKUP_SUFFIX_LIMIT}): {basename}.bak_{ts}_{digest}")
def _resolve_backup_source(filepath: str, source: str | None,
                           started: float) -> tuple[str | None, str | None]:
    if source is not None and not isinstance(source, str):
        _backup_failed(
            filepath, started,
            f"source 非 str 形态({type(source).__name__})，拒绝创建备份")
        return None, None
    try:
        with open(filepath, "rb") as f:
            original_bytes = f.read()
        disk_source, source_encoding = decode_source_strict(original_bytes)
    except (OSError, SourceReadError) as e:
        log_swallowed(__name__, e,
                      context=f'_resolve_backup_source:{type(e).__name__}')
        _backup_failed(filepath, started, "无法读取文件创建备份", e)
        return None, None
    return (disk_source if source is None else source), source_encoding
def _write_backup_artifact(backup_dir: str, filepath: str, source: str,
                           source_encoding: str, started: float) -> str:
    try:
        os.makedirs(backup_dir, exist_ok=True)
        backup_file, backup_path = _open_backup_exclusive(
            backup_dir, filepath, source_encoding)
    except (OSError, UnicodeError) as e:
        log_swallowed(__name__, e,
                      context=f'_write_backup_artifact:{type(e).__name__}')
        return _backup_failed(filepath, started, "创建备份失败", e)
    try:
        with backup_file:
            backup_file.write(source)
    except (OSError, UnicodeError) as e:
        log_swallowed(__name__, e,
                      context=f'_write_backup_artifact:{type(e).__name__}')
        _discard_partial_backup(backup_path)
        return _backup_failed(filepath, started, "创建备份失败", e)
    return backup_path
def _discard_partial_backup(backup_path: str) -> None:
    try:
        if os.path.exists(backup_path) and not safe_delete(backup_path):
            logger.warning("安全网: 半写备份产物回收站删除失败 %s", backup_path)
    except OSError:
        logger.warning("安全网: 半写备份产物回滚失败 %s",
                       backup_path, exc_info=True)
class FixSafetyNet:
    def __init__(self, skill_dir: str = "."):
        self.skill_dir = normalize_skill_dir(skill_dir)
        try:
            backup_root = get_backup_root(self.skill_dir)
        except (OSError, RuntimeError, ValueError) as exc:  # jwsgj:silent-ok 兜底根降级已由 _warn_fallback 限量留痕
            _warn_fallback(exc)
            backup_root = _fallback_backup_root(self.skill_dir)
        self.backup_dir = os.path.join(backup_root, "fix_backups")
        self._backups: dict[str, str] = {}
        self._encodings: dict[str, str] = {}
        self._status: dict[str, str] = {}
    def create_backup(self, filepath: str, source: str | None = None) -> str:
        filepath = os.path.abspath(filepath)
        _t0 = time.monotonic()
        source, source_encoding = _resolve_backup_source(
            filepath, source, _t0)
        if source is None or source_encoding is None:
            return ""
        backup_path = _write_backup_artifact(
            self.backup_dir, filepath, source, source_encoding, _t0)
        if not backup_path:
            return ""
        self._backups[filepath] = backup_path
        self._encodings[filepath] = source_encoding
        self._status[filepath] = "backed_up"
        logger.debug("安全网: 已创建备份 %s -> %s", filepath, backup_path)
        _log_net_trace("FixSafetyNet.create_backup", "ok", _t0,
                       file=filepath, backup=backup_path)
        return backup_path
    def restore_from_backup(self, filepath: str) -> bool:
        filepath = os.path.abspath(filepath)
        _t0 = time.monotonic()
        backup_path = self._backups.get(filepath)
        if (not backup_path or not os.path.isfile(backup_path)
                or filepath not in self._encodings):
            logger.warning("安全网: 备份或编码登记不存在 %s", filepath)
            _log_net_trace("FixSafetyNet.restore_from_backup", "failed", _t0,
                           file=filepath)
            return False
        source_encoding = self._encodings[filepath]
        try:
            with open(backup_path, encoding=source_encoding, newline="") as f:
                backup_source = f.read()
            with guarded_open(
                    filepath, "w", encoding=source_encoding, newline="",
                    strict=False) as f:
                f.write(backup_source)
            self._status[filepath] = "rolled_back"
            logger.info("安全网: 已从备份恢复 %s", filepath)
            safe_write_audit("fix_safety_rollback", file=filepath, backup=backup_path)
            _log_net_trace("FixSafetyNet.restore_from_backup", "ok", _t0,
                           file=filepath, backup=backup_path)
            return True
        except (OSError, UnicodeError):
            logger.exception("安全网: 恢复失败 %s", filepath)
            _log_net_trace("FixSafetyNet.restore_from_backup", "failed", _t0,
                           file=filepath, backup=backup_path)
            return False
    def mark_committed(self, filepath: str) -> None:
        filepath = os.path.abspath(filepath)
        self._status[filepath] = "committed"
    def mark_rolled_back(self, filepath: str) -> None:
        filepath = os.path.abspath(filepath)
        self._status[filepath] = "rolled_back"
    def mark_backed_up(self, filepath: str) -> None:
        filepath = os.path.abspath(filepath)
        self._status[filepath] = "backed_up"
    def rollback_all(self) -> dict[str, bool]:
        results = {}
        for filepath, status in list(self._status.items()):
            if status == "backed_up":
                try:
                    results[filepath] = self.restore_from_backup(filepath)
                except Exception:
                    results[filepath] = False
                    logger.exception("安全网: 单文件回滚异常 %s", filepath)
        if results:
            logger.info("安全网: 批量回滚 %d 个文件", len(results))
        return results
    def get_status(self) -> dict[str, dict[str, str]]:
        return {
            filepath: {
                "status": status,
                "backup_path": self._backups.get(filepath, ""),
            }
            for filepath, status in self._status.items()
        }
    def cleanup(self) -> int:
        cleaned = 0
        for filepath, status in list(self._status.items()):
            if status in ("committed", "rolled_back"):
                backup_path = self._backups.get(filepath)
                if backup_path and os.path.isfile(backup_path):
                    if safe_delete(backup_path):
                        cleaned += 1
                    else:
                        logger.warning("安全网: 备份清理失败(non-critical): %s", filepath)
                        continue
                self._backups.pop(filepath, None)
                self._encodings.pop(filepath, None)
                self._status.pop(filepath, None)
        logger.info("安全网: 已清理 %d 个备份", cleaned)
        return cleaned
def restore_bytes(
        filepath: str, content: str,
        source_encoding: str = _DEFAULT_SOURCE_ENCODING,
) -> tuple[bool, str]:
    raw_target = filepath
    filepath = normalize_target_path(filepath)
    if not filepath:
        return False, (f"回滚目标路径形态异常({type(raw_target).__name__})，"
                       f"应为非空路径")
    if not isinstance(content, str):
        return False, (f"回滚内容形态异常({type(content).__name__})，"
                       f"应为源码全文 str")
    if not isinstance(source_encoding, str) or not source_encoding:
        return False, (f"回滚编码形态异常({type(source_encoding).__name__})，"
                       f"应为非空编码名")
    try:
        with guarded_open(
                filepath, "w", encoding=source_encoding, newline="",
                strict=False) as f:
            f.write(content)
        return True, ""
    except (OSError, LookupError, ValueError) as e:
        log_swallowed(__name__, e,
                      context=f'restore_bytes:{type(e).__name__}')
        return False, str(e)
def _read_swap_backup(filepath: str) -> tuple[bytes | None, tuple[bool, str] | None]:
    try:
        with open(filepath, "rb") as f:
            backup = f.read()
        decode_source_strict(backup)
        return backup, None
    except (OSError, SourceReadError, TypeError, ValueError) as e:
        logger.warning("原地交换: 读取原始文件失败: %s", e, exc_info=True)
        return None, (False, f"无法读取原始文件: {e}")
def _write_swap_replacement(filepath: str, replacement: str,
                            ) -> tuple[bool, str] | None:
    try:
        if not isinstance(replacement, str):
            raise TypeError(
                f"replacement 须为 str，当前为 {type(replacement).__name__}")
        _encoding = tokenize.detect_encoding(io.BytesIO(
            replacement.encode(_DEFAULT_SOURCE_ENCODING)).readline)[0]
        payload = replacement.removeprefix("\ufeff").encode(_encoding)
        atomic_replace_bytes(
            filepath, payload,
            prefix=f".{os.path.basename(filepath)}.swap_",
            label="交换验证临时产物")
    except (OSError, UnicodeError, SourceReadError, TypeError, ValueError,
            SyntaxError, LookupError) as e:
        logger.warning("原地交换: 写入修复版失败: %s", e, exc_info=True)
        return False, f"写入修复版失败: {e}"
    return None
def _restore_swap_backup(filepath: str, backup: bytes) -> str | None:
    try:
        restore_file_bytes(filepath, backup)
    except Exception:
        logger.exception("CRITICAL: 原地交换恢复通道异常 %s", filepath)
        logger.error("CRITICAL: 原地交换恢复失败 %s", filepath)
        return f"CRITICAL: 原地交换恢复失败(文件残留修复版): {filepath}"
    return None
def _normalize_swap_result(raw_result: Any) -> tuple[bool, str]:
    if (isinstance(raw_result, tuple) and len(raw_result) == 2
            and isinstance(raw_result[0], bool)
            and isinstance(raw_result[1], str)):
        return raw_result
    logger.warning("原地交换: 测试函数返回形态异常: %r", raw_result)
    return False, f"测试函数返回形态异常: {raw_result!r}"
def _run_swap_action_safely(action: Callable[[str], tuple[bool, str]],
                            filepath: str) -> tuple[bool, str]:
    try:
        return _normalize_swap_result(action(filepath))
    except Exception as e:
        logger.warning("原地交换: 测试函数执行异常: %s", e, exc_info=True)
        return False, f"测试函数执行异常: {e}"
def run_with_swap(filepath: str, replacement: str,
                  action: Callable[[str], tuple[bool, str]],
                  ) -> tuple[bool, str]:
    backup, read_failure = _read_swap_backup(filepath)
    if read_failure is not None:
        return read_failure
    restore_error = None
    try:
        write_failure = _write_swap_replacement(filepath, replacement)
        result = (write_failure if write_failure is not None
                  else _run_swap_action_safely(action, filepath))
    finally:
        if backup is not None:
            restore_error = _restore_swap_backup(filepath, backup)
    if restore_error is not None:
        return False, restore_error
    return result
def restore_written_original(net: FixSafetyNet, filepath: str,
                              original_source: str) -> tuple[bool, str, str]:
    try:
        if net.restore_from_backup(filepath):
            return True, "backup", ""
    except Exception:
        logger.warning("safe_fix_file: 备份恢复通道异常 %s", filepath,
                       exc_info=True)
    source_encoding = getattr(net, "_encodings", {}).get(
        os.path.abspath(filepath), _DEFAULT_SOURCE_ENCODING)
    restored, error = restore_bytes(
        filepath, original_source, source_encoding)
    if restored:
        net.mark_rolled_back(filepath)
        return True, "memory", ""
    net.mark_backed_up(filepath)
    return False, "", error
def preflight_write_snapshot(file_path: str,
                              fixed_source: str) -> tuple[bytes, dict | None]:
    if not isinstance(fixed_source, str):
        return b"", {
            "status": "rejected",
            "reason": (f"修复后源码形态异常({type(fixed_source).__name__})，"
                       f"应为修复后源码全文 str"),
        }
    try:
        with open(file_path, "rb") as f:
            f.read(1)
    except OSError as e:
        log_swallowed(__name__, e,
                      context=('preflight_write_snapshot:probe:'
                               f'{type(e).__name__}'))
        return b"", {"status": "error", "reason": f"读取文件失败: {e}"}
    if os.path.splitext(file_path)[1].lower() == ".py":
        try:
            compile(fixed_source, file_path, "exec")
        except PARSE_DEGRADE_EXC as e:
            log_swallowed(
                __name__, e,
                context=f'preflight_write_snapshot:compile:{type(e).__name__}')
            return b"", {"status": "rejected",
                         "reason": f"修复后代码语法错误: {e}"}
    try:
        return snapshot_file_bytes(file_path), None
    except OSError as e:
        log_swallowed(__name__, e,
                      context=('preflight_write_snapshot:snapshot:'
                               f'{type(e).__name__}'))
        return b"", {"status": "failed", "reason": f"留底读取原内容失败: {e}"}
def is_syntax_valid(code: str) -> bool:
    try:
        compile(code, "<exec-commit>", "exec")
        return True
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc,
                      context=f'is_syntax_valid:{type(exc).__name__}')
        return False
def _backup_for_write(filepath: str, skill_dir: str) -> str | None:
    if not os.path.exists(filepath):
        return None
    backup_root = get_backup_root(skill_dir or None)
    dest_dir = os.path.join(
        backup_root, "executor_commit",
        time.strftime("%Y%m%d_%H%M%S"))
    os.makedirs(dest_dir, exist_ok=True)
    stem, ext = os.path.splitext(os.path.basename(filepath))
    while True:
        dest = unique_backup_path(dest_dir, stem, ext)
        try:
            with open(dest, "xb"):
                pass
        except FileExistsError:
            continue
        try:
            copy_backup(filepath, dest, False)
        except (OSError, shutil.Error):
            _discard_partial_backup(dest)
            raise
        break
    _prune_after_backup(backup_root)
    return dest
def _preferred_line_ending(filepath: str) -> str:
    try:
        with open(filepath, "rb") as fh:
            sample = fh.read(65536)
    except OSError:  # jwsgj:silent-ok 行尾采样不可读时按 LF 默认回退
        return "\n"
    crlf = sample.count(b"\r\n")
    lf_only = sample.count(b"\n") - crlf
    return "\r\n" if crlf > lf_only else "\n"
def _atomic_write(filepath: str, code: str,
                  attempted_writes: dict[str, bytes]) -> None:
    newline = _preferred_line_ending(filepath)
    normalized = code.replace("\r\n", "\n").replace("\r", "\n")
    attempted_writes[filepath] = normalized.replace(
        "\n", newline).encode(_DEFAULT_SOURCE_ENCODING)
    atomic_write_text(filepath, normalized, tag="commit", newline=newline,
                      encoding=_DEFAULT_SOURCE_ENCODING)
def _rollback(backups: list[tuple[str, str | None]],
              attempted_writes: dict[str, bytes]) -> list[str]:
    failed: list[str] = []
    for filepath, bak in backups:
        if not _rollback_entry(filepath, bak, attempted_writes[filepath]):
            failed.append(filepath)
    return failed
def _rollback_entry(filepath: str, bak: str | None,
                    expected: bytes) -> bool:
    try:
        payload = None
        if bak:
            if not os.path.exists(bak):
                logger.error(
                    "[CommitRollback] 回滚失败 %s: 备份 %s 已缺失，"
                    "文件保持写盘后状态", filepath, bak)
                return False
            with open(bak, "rb") as backup_file:
                payload = backup_file.read()
        current = None
        if os.path.exists(filepath):
            with open(filepath, "rb") as current_file:
                current = current_file.read()
        if bak:
            if current != expected:
                if current == payload:
                    return True
                logger.error(
                    "[CommitRollback] 回滚失败 %s: 当前内容不属于本事务候选，"
                    "拒绝覆盖并发或外部修改", filepath)
                return False
            restore_file_bytes(filepath, payload)
            return True
        if current is None:
            return True
        if current != expected:
            logger.error(
                "[CommitRollback] 回滚失败 %s: 新建文件内容已被外部修改，"
                "拒绝按本事务旧候选删除", filepath)
            return False
        if safe_delete(filepath):
            return True
        logger.error("[CommitRollback] 回滚失败 %s: 新建文件"
                   "删除失败（safe_delete 返 False）", filepath)
        return False
    except Exception:
        logger.exception("[CommitRollback] 回滚失败 %s", filepath)
        return False
def _writes_error(message: str) -> dict:
    return {"status": "error", "data": {}, "message": message}
def _normalize_writes(
        writes,
) -> tuple[list[tuple[str, str]] | None, dict | None]:
    if not isinstance(writes, (list, tuple)):
        return None, _writes_error(
            f"writes 须为 (filepath, code) 二元组序列，"
            f"得到 {type(writes).__name__}")
    normalized: list[tuple[str, str]] = []
    seen: dict[str, str] = {}
    for _w in writes:
        if not isinstance(_w, (list, tuple)) or len(_w) != 2:
            _len_note = (f"（长度 {len(_w)}）"
                          if isinstance(_w, (list, tuple)) else "")
            return None, _writes_error(
                "writes 每项须为 (filepath, code) 二元组，"
                f"得到 {type(_w).__name__}{_len_note}")
        raw_path, code = _w
        filepath = normalize_target_path(raw_path)
        if not filepath or not filepath.strip():
            if isinstance(raw_path, str) and not raw_path.strip():
                message = ("写入目标 filepath 不能为空或纯空白"
                           "（空路径会解析到进程 cwd，产物落到工作区之外）")
            else:
                message = ("写入目标 filepath 须为 str/PathLike 路径，"
                           f"得到 {type(raw_path).__name__}: {raw_path!r}")
            return None, _writes_error(message)
        if os.path.isdir(filepath):
            return None, _writes_error(f"写入目标不能是目录: {filepath}")
        key = path_identity(filepath)
        if key in seen:
            return None, _writes_error(
                "writes 含重复写入目标，事务无法确定回滚基线: "
                f"{seen[key]} / {filepath}")
        seen[key] = filepath
        normalized.append((filepath, code))
    return normalized, None
def _ensure_write_dirs(writes: list[tuple[str, str]],
                       created: list[str]) -> None:
    for filepath, _code in writes:
        parent = os.path.dirname(os.path.abspath(filepath))
        missing: list[str] = []
        cur = parent
        while cur and not os.path.isdir(cur):
            missing.append(cur)
            nxt = os.path.dirname(cur)
            if nxt == cur:
                break
            cur = nxt
        for path in reversed(missing):
            try:
                os.mkdir(path)
            except FileExistsError as _swallowed_exc:
                log_swallowed(
                    __name__, _swallowed_exc, context='_ensure_write_dirs:FileExistsError')
                continue
            created.append(path)
def _remove_created_dirs(created: list[str]) -> None:
    for path in reversed(created):
        if not os.path.isdir(path):
            continue
        try:
            os.rmdir(path)
            continue
        except OSError as exc:
            logger.debug("[ExecCommit] rmdir 被拒，尝试安全删除 %s: %s",
                         path, exc)
        try:
            if os.listdir(path):
                continue
            if not safe_delete(path):
                logger.debug("[ExecCommit] 回滚保留新建目录 %s: 安全删除失败",
                             path)
        except OSError as exc:
            logger.debug("[ExecCommit] 回滚保留新建目录 %s: %s", path, exc)
def commit_writes(writes: list[tuple[str, str]], skill_dir: str = "") -> dict:
    writes, _shape_err = _normalize_writes(writes)
    if _shape_err is not None:
        return _shape_err
    backups: list[tuple[str, str | None]] = []
    created_dirs: list[str] = []
    attempted_writes: dict[str, bytes] = {}
    try:
        _validate_write_payloads(writes)
        _ensure_write_dirs(writes, created_dirs)
        _backup_writes(writes, skill_dir, backups)
        _apply_writes(writes, attempted_writes)
        return {
            "status": "ok",
            "data": {"files_written": [fp for fp, _ in writes]},
            "message": f"已落盘 {len(writes)} 个文件（备份+写盘校验通过）",
        }
    except (OSError, ValueError, RuntimeError) as e:
        rollback_entries = [
            entry for entry in backups if entry[0] in attempted_writes]
        failed = _rollback(rollback_entries, attempted_writes)
        _remove_created_dirs(created_dirs)
        if failed:
            logger.exception(
                "[ExecCommit] 写盘失败，回滚不完整 %d/%d 个目标未恢复: %s",
                len(failed), len(rollback_entries), failed)
            return {
                "status": "error",
                "data": {"rollback_failed": failed},
                "message": (f"写盘失败，回滚不完整（{len(failed)} 个目标未恢复）: "
                            f"{e}"),
            }
        logger.warning("[ExecCommit] 写盘失败，已回滚 %d 个备份: %s",
                       len(rollback_entries), e)
        return {"status": "error", "data": {}, "message": f"写盘失败已回滚: {e}"}
def _validate_write_payloads(writes: list[tuple[str, str]]) -> None:
    for filepath, code in writes:
        if not isinstance(code, str):
            raise ValueError(  # noqa: TRY004 — 类型违约须收敛进事务捕获面 (OSError, ValueError, RuntimeError) 整体回滚，raise TypeError 会穿透捕获面破坏回滚契约
                f"写入产物须为 str 源码文本，得到 {type(code).__name__}: {filepath}")
def _backup_writes(writes: list[tuple[str, str]], skill_dir: str,
                   backups: list[tuple[str, str | None]]) -> None:
    for filepath, _code in writes:
        backups.append((filepath, _backup_for_write(filepath, skill_dir)))
def _apply_writes(writes: list[tuple[str, str]],
                  attempted_writes: dict[str, bytes]) -> None:
    for filepath, code in writes:
        normalized_code = code
        if os.path.splitext(filepath)[1].lower() == ".py":
            normalized_code = strip_stale_coding_declaration(code)
            if not is_syntax_valid(normalized_code):
                raise ValueError(f"写入产物语法校验失败: {filepath}")
        _atomic_write(filepath, normalized_code, attempted_writes)
_G21_MODIFY_OPS = frozenset({
    OperationType.MODIFY_CODE, OperationType.REFACTOR,
    OperationType.REMOVE_CODE, OperationType.ADD_IMPORT,
})
_G21_RELOCATE_OPS = (OperationType.RENAME, OperationType.MOVE)
_G21_SINGLE_FILE_MODIFY_OPS = frozenset({
    OperationType.MODIFY_CODE, OperationType.REMOVE_CODE,
    OperationType.ADD_IMPORT,
})
_WORKSPACE_ROOT_ENV_VAR = "_JWS_WORKSPACE_ROOT"
def _resolve_guard_workspace_root() -> str:
    override = os.environ.get(_WORKSPACE_ROOT_ENV_VAR, "").strip()
    if override:
        override_root = os.path.normpath(os.path.abspath(override))
        if not os.path.isdir(override_root):
            logger.warning("工作区根覆盖 %s 不是已存在目录，G16 按无工作区"
                           "保守拒绝写类操作", override_root)
            return ""
        return override_root
    try:
        _root = resolve_workspace_root() or ""
    except RuntimeError as _ws_err:
        logger.warning("会话工作空间不可用，G16 按无工作区保守拒绝写类操作: %s",
                       _ws_err)
        return ""
    return os.path.normpath(_root) if _root else ""
_WORKSPACE_ROOT = _resolve_guard_workspace_root()
def _guard_workspace_root() -> str:
    if _WORKSPACE_ROOT:
        return _WORKSPACE_ROOT
    return _resolve_guard_workspace_root()
def _is_within_workspace(target_path: str) -> bool:
    root = _guard_workspace_root()
    if not root:
        return False
    return _within_any_root(target_path, [root])
def _has_workspace_root_config(ctx: OperationContext) -> bool:
    meta = ctx.metadata if isinstance(ctx.metadata, dict) else {}
    for key in ("workspace_root", "workspace_roots", "allowed_roots"):
        raw = meta.get(key)
        if isinstance(raw, str):
            if raw.strip():
                return True
        elif isinstance(raw, (list, tuple, set, frozenset)):
            if raw:
                return True
        elif raw is not None:
            return True
    return False
def _ctx_workspace_roots(ctx: OperationContext) -> list[str]:
    meta = ctx.metadata if isinstance(ctx.metadata, dict) else {}
    roots: list[str] = []
    seen: set[str] = set()
    for key in ("workspace_root", "workspace_roots", "allowed_roots"):
        raw = meta.get(key)
        values = ([raw] if isinstance(raw, str) else
                  list(raw) if isinstance(raw, (list, tuple, set, frozenset))
                  else [])
        for item in values:
            if not isinstance(item, str) or not item.strip():
                continue
            root = os.path.normpath(os.path.abspath(item))
            root_key = os.path.normcase(os.path.realpath(root))
            if root_key in seen:
                continue
            seen.add(root_key)
            if os.path.isdir(root):
                roots.append(root)
            else:
                logger.warning("G16 忽略不存在的工作区根: %s", root)
    return roots
def _implicit_workspace_roots(target_path: str) -> list[str]:
    root = _find_project_root(target_path)
    return [root] if root else []
def _within_guard_scope(candidate: str, roots: list[str]) -> bool:
    if roots:
        return _within_any_root(candidate, roots)
    if _guard_workspace_root():
        return _is_within_workspace(candidate)
    implicit = _implicit_workspace_roots(candidate)
    return bool(implicit) and _within_any_root(candidate, implicit)
def _has_path_traversal(target_path: str) -> bool:
    parts = target_path.replace("\\", "/").split("/")
    return ".." in parts
def _iter_component_prefixes(path: str) -> Iterator[str]:
    parts = path.replace("\\", "/").split("/")
    current = ""
    seen_component = False
    for part in parts:
        if part:
            current = (f"{current}/{part}" if seen_component
                       else f"{current}{part}")
            seen_component = True
            yield current
        elif not seen_component:
            current += "/"
def _is_symlink(target_path: str) -> bool:
    for prefix in _iter_component_prefixes(target_path):
        try:
            if os.path.islink(prefix):
                return True
        except OSError:
            logger.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            continue
    return False
_G16_FULL_PATH_OPS = (OperationType.DELETE_FILE, OperationType.DELETE_DIR,
                      OperationType.MODIFY_CODE, OperationType.CLEANUP,
                      OperationType.RENAME, OperationType.WRITE_FILE,
                      OperationType.MERGE, OperationType.MOVE,
                      OperationType.ADD_IMPORT, OperationType.REMOVE_CODE)
_G16_PARTIAL_PATH_OPS = (OperationType.REFACTOR, OperationType.SPLIT)
def _path_violations(path: str, *, enforce_workspace: bool,
                     label: str,
                     workspace_roots: list[str] | None = None) -> list[str]:
    issues: list[str] = []
    roots = workspace_roots or []
    def _within(candidate: str) -> bool:
        return _within_guard_scope(candidate, roots)
    if _has_path_traversal(path):
        issues.append(f"{label} {path} 包含 .. 越权访问.操作被拒绝.")
    if _is_symlink(path):
        real_path = os.path.realpath(path)
        if not _within(real_path):
            issues.append(
                f"{label} {path} 符号链接指向工作区外路径 {real_path}.操作被拒绝.")
    if enforce_workspace and not _within(path):
        issues.append(f"{label} {path} 不在工作区 {_guard_root_label(roots)} "
                      f"内.操作被拒绝.")
    return issues
def _guard_root_label(roots: list[str]) -> str:
    return ", ".join(roots) if roots else (
        _guard_workspace_root() or "<未配置:按目标项目根归属校验>")
def _g16_check_scope(ctx: OperationContext) -> tuple[bool, str | None]:
    if is_read_only_audit(ctx):
        return False, "只读审计,跳过路径净化（无真实写操作）"
    operation = _operation_of(ctx)
    if _is_unknown_operation(ctx):
        logger.warning("[G16] 未识别的 operation %r，按全量路径校验"
                       "（fail-closed）", getattr(ctx, "operation", None))
        return True, None
    if operation not in _G16_FULL_PATH_OPS + _G16_PARTIAL_PATH_OPS:
        return False, "非文件操作,跳过路径净化"
    return True, None
def _g16_sanitize_rename_target(ctx: OperationContext,
                                issues: list[str],
                                roots: list[str]) -> None:
    if _operation_of(ctx) not in (OperationType.RENAME, OperationType.MOVE):
        return
    raw_new_path = ctx.metadata.get("new_path", "")
    if raw_new_path is None or raw_new_path == "":
        return
    new_path = normalize_target_path(raw_new_path)
    if not new_path:
        issues.append(
            f"重命名目标类型非法({type(raw_new_path).__name__})，"
            f"无法校验目标路径.操作被拒绝.")
        return
    issues.extend(_path_violations(
        new_path, enforce_workspace=True, label="重命名目标",
        workspace_roots=roots))
def _g16_sanitize_affected_files(ctx: OperationContext, full_checks: bool,
                                 issues: list[str],
                                 roots: list[str]) -> None:
    for fpath in normalize_files_list(ctx.affected_files):
        issues.extend(_path_violations(
            fpath, enforce_workspace=full_checks, label="受影响文件",
            workspace_roots=roots))
def guard_path_sanitize(ctx: OperationContext) -> GuardResult:
    full_checks, skip_message = _g16_check_scope(ctx)
    if skip_message is not None:
        return GuardResult(guard_name="G16", passed=True, message=skip_message)
    issues = []
    roots = _ctx_workspace_roots(ctx)
    if _has_workspace_root_config(ctx) and not roots:
        issues.append(
            "显式工作区根配置全部无效，无法确认操作边界.操作被拒绝.")
    target = _explicit_target_path(ctx)
    if target:
        issues.extend(_path_violations(
            target, enforce_workspace=full_checks, label="路径",
            workspace_roots=roots))
    _g16_sanitize_rename_target(ctx, issues, roots)
    _g16_sanitize_affected_files(ctx, full_checks, issues, roots)
    return issues_guard_result(
        "G16", "路径净化", "违规", issues,
        "确保所有操作路径在工作区 " + _guard_root_label(roots)
        + " 内,不使用符号链接或 .. 越权访问.",
        "路径净化检查通过")
def _normalize_text_for_compare(text: str) -> str:
    return text.lstrip('\ufeff').replace('\r\n', '\n').replace('\r', '\n')
def _modified_content_issues(target: str, before_code: Any,
                             expected: Any, after_code: str) -> list[str]:
    issues: list[str] = []
    normalized_after = _normalize_text_for_compare(after_code)
    if (isinstance(before_code, str)
            and normalized_after == _normalize_text_for_compare(before_code)):
        issues.append(
            f"文件 {os.path.basename(target)} 修改前后内容完全一致."
            f"操作可能未生效（Agent 幻觉——声称修改但实际未执行）."
        )
    if (isinstance(expected, str) and expected
            and _normalize_text_for_compare(expected) not in normalized_after):
        issues.append(
            f"修改后文件不包含预期内容."
            f"预期: `{expected[:80]}`"
        )
    return issues
def _verify_file_modified(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    before_code = ctx.metadata.get("before_code")
    target = _explicit_target_path(ctx)
    if not target:
        return issues
    if not os.path.exists(target):
        issues.append(f"修改后文件 {target} 不存在.操作可能失败或目标路径错误.")
        return issues
    if os.path.isdir(target):
        if _operation_of(ctx) in _G21_SINGLE_FILE_MODIFY_OPS:
            issues.append(
                f"修改目标 {target} 不是普通文件."
                f"单文件修改操作可能失败或目标类型错误."
            )
        return issues
    after_code = read_text_bom(target)
    if after_code is None:
        issues.append(f"无法读取修改后文件 {target}")
        return issues
    expected = ctx.metadata.get("expected_content", "")
    issues.extend(_modified_content_issues(target, before_code, expected,
                                           after_code))
    return issues
def _verify_file_deleted(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    target = _explicit_target_path(ctx)
    if not target:
        return issues
    if os.path.lexists(target):
        issues.append(
            f"删除操作后文件 {target} 仍然存在."
            f"操作可能未生效（Agent 幻觉——声称删除但实际未执行）."
        )
    return issues
def _verify_file_created(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    target = _explicit_target_path(ctx)
    if not target:
        return issues
    if not os.path.exists(target):
        issues.append(
            f"创建操作后文件 {target} 不存在."
            f"操作可能未生效."
        )
        return issues
    if not os.path.isfile(target):
        issues.append(
            f"创建目标 {target} 不是普通文件.操作可能未生效或目标类型错误."
        )
    return issues
_RELOCATE_OPS = (OperationType.RENAME, OperationType.MOVE)
def _verify_file_renamed(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    target = _explicit_target_path(ctx)
    if not target:
        issues.append(
            "重命名/移动操作缺少明确原路径,无法验证旧路径是否已移除."
        )
        return issues
    raw_new_path = ctx.metadata.get("new_path", "")
    new_path = (normalize_target_path(raw_new_path)
                if raw_new_path not in (None, "") else "")
    if not new_path:
        if raw_new_path not in (None, ""):
            issues.append(
                f"重命名目标的 metadata.new_path 形态非法"
                f"({type(raw_new_path).__name__}),无法验证重命名目标."
            )
        else:
            issues.append(
                "重命名操作缺少 metadata.new_path,无法验证重命名目标."
            )
        return issues
    if not os.path.lexists(new_path):
        issues.append(
            f"重命名后新路径 {new_path} 不存在."
            f"操作可能未生效（Agent 幻觉——声称重命名但实际未执行）."
        )
    if os.path.lexists(target):
        issues.append(
            f"重命名后旧路径 {target} 仍然存在."
            f"操作可能未生效（可能是复制而非重命名）."
        )
    return issues
def _verify_affected_files(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    operation = _operation_of(ctx)
    if operation in (OperationType.DELETE_FILE, OperationType.DELETE_DIR,
                     OperationType.CLEANUP):
        for fpath in normalize_files_list(ctx.affected_files):
            if os.path.lexists(fpath):
                issues.append(
                    f"受影响文件 {os.path.basename(fpath)} 在删除/清理后仍然存在."
                    f"删除可能未完全生效（Agent 幻觉——声称删除但实际未执行）."
                )
        return issues
    if operation in _G21_RELOCATE_OPS:
        return issues
    for fpath in normalize_files_list(ctx.affected_files):
        if not os.path.exists(fpath):
            issues.append(
                f"受影响文件 {os.path.basename(fpath)} 不存在."
                f"可能是路径错误或已被意外删除."
            )
    return issues
def guard_post_verify(ctx: OperationContext) -> GuardResult:
    if is_read_only_audit(ctx):
        return GuardResult(guard_name="G21", passed=True,
                           message="只读审计,跳过操作后校验（无写操作）")
    if ctx.dry_run:
        return GuardResult(guard_name="G21", passed=True,
                           message="dry_run 演练,跳过操作后校验（无真实写操作）")
    if _is_unknown_operation(ctx):
        return GuardResult(
            guard_name="G21", passed=False, level=GuardLevel.BLOCK,
            message="未识别的操作类型，无法确认操作结果（fail-closed）",
            details=[f"operation: {getattr(ctx, 'operation', None)!r}"],
            fix_suggestion="传入 OperationType 枚举或合法的操作值后重试",
        )
    if not _explicit_target_path(ctx) and not normalize_files_list(ctx.affected_files):
        return GuardResult(
            guard_name="G21", passed=False, level=GuardLevel.BLOCK,
            message="无可校验目标（target_path 与 affected_files 均为空），"
                    "无法确认操作结果",
            fix_suggestion="提供操作目标或受影响文件后重新执行操作后校验",
        )
    issues: list[str] = []
    operation = _operation_of(ctx)
    if operation in _G21_MODIFY_OPS | {OperationType.MERGE}:
        issues.extend(_verify_file_modified(ctx))
    elif operation in (OperationType.DELETE_FILE, OperationType.DELETE_DIR,
                       OperationType.CLEANUP):
        issues.extend(_verify_file_deleted(ctx))
    elif operation in _G21_RELOCATE_OPS:
        issues.extend(_verify_file_renamed(ctx))
    elif operation == OperationType.WRITE_FILE:
        issues.extend(_verify_file_created(ctx))
        write_target = _explicit_target_path(ctx)
        if write_target and os.path.exists(write_target):
            issues.extend(_verify_file_modified(ctx))
    issues.extend(_verify_affected_files(ctx))
    return issues_guard_result(
        "G21", "操作后校验", "不一致", issues,
        "检查操作是否真正执行.如果 Agent 声称执行但实际未执行,"
        "这是 Agent 幻觉,需要重新执行操作.",
        "操作后结果校验通过",  # nosec B106 — 中文校验结论文案非密码
        level=GuardLevel.BLOCK)
_snapshots: dict[str, str] = {}
_SNAPSHOT_MAX_FILES = 64
_G23_DIFF_HUGE_LINES = 500
_G23_DIFF_LARGE_LINES = 100
_G23_PURE_DELETE_LINES = 10
_G23_CONTENT_OPS = frozenset({
    OperationType.MODIFY_CODE, OperationType.REFACTOR,
    OperationType.MERGE, OperationType.CLEANUP,
    OperationType.WRITE_FILE, OperationType.SPLIT,
    OperationType.ADD_IMPORT, OperationType.REMOVE_CODE,
})
def _snapshot_key(filepath: str) -> str:
    return path_identity(filepath) if filepath else ""
def _read_diff_text(filepath: str) -> str:
    return read_source_text_strict(filepath).replace(
        "\r\n", "\n").replace("\r", "\n")
def _take_snapshot(filepath: str) -> str | None:
    try:
        content = _read_diff_text(filepath)
    except (OSError, UnicodeDecodeError, *PARSE_DEGRADE_EXC) as e:
        logger.warning("[G23] 快照读取失败 %s: %s", filepath, e)
        return None
    key = _snapshot_key(filepath)
    if key in _snapshots:
        _snapshots.pop(key)
    elif len(_snapshots) >= _SNAPSHOT_MAX_FILES:
        _snapshots.pop(next(iter(_snapshots)), None)
    _snapshots[key] = content
    return content
def _count_diff_changes(diff_text: str) -> dict[str, int]:
    added = 0
    removed = 0
    for line in diff_text.split('\n')[2:]:
        if line.startswith('+'):
            added += 1
        elif line.startswith('-'):
            removed += 1
    return {"added": added, "removed": removed, "total": added + removed}
def _has_explicit_code_pair(before_code: Any, after_code: Any) -> bool:
    return (isinstance(before_code, str) and isinstance(after_code, str)
            and bool(before_code or after_code))
def _resolve_diff_sides(target: str, before_code: Any,
                        after_code: Any) -> tuple[Any, Any, bool, bool]:
    if _has_explicit_code_pair(before_code, after_code):
        return before_code, after_code, True, True
    have_before = isinstance(before_code, str) and bool(before_code)
    have_after = isinstance(after_code, str) and bool(after_code)
    if not have_before:
        baseline = _snapshots.get(_snapshot_key(target))
        if baseline is not None:
            before_code, have_before = baseline, True
    if not have_after:
        after_code, have_after = _read_disk_side(target)
    return before_code, after_code, have_before, have_after
def _read_disk_side(target: str) -> tuple[str | None, bool]:
    if not os.path.isfile(target):
        return None, False
    try:
        return _read_diff_text(target), True
    except (OSError, UnicodeDecodeError, *PARSE_DEGRADE_EXC) as e:
        logger.warning("[G23] 回退快照对比读取失败 %s: %s", target, e)
        return None, False
def _snapshot_target_and_affected(target: str, affected_files) -> None:
    if os.path.isfile(target):
        _take_snapshot(target)
    for fpath in normalize_files_list(affected_files):
        if fpath != target and os.path.isfile(fpath):
            _take_snapshot(fpath)
def _build_diff_issues(changes: dict,
                       operation: OperationType | None = None) -> list:
    issues = []
    if changes["total"] > _G23_DIFF_HUGE_LINES:
        issues.append(
            f"变更量过大: {changes['total']} 行"
            f"（+{changes['added']}/-{changes['removed']}）."
            f"超过 {_G23_DIFF_HUGE_LINES} 行阈值,可能存在意外的大规模修改."
        )
    elif changes["total"] > _G23_DIFF_LARGE_LINES:
        issues.append(
            f"变更量较大: {changes['total']} 行"
            f"（+{changes['added']}/-{changes['removed']}）."
            f"请确认变更范围符合预期."
        )
    if (changes["removed"] > _G23_PURE_DELETE_LINES
            and changes["added"] == 0
            and operation is not OperationType.REMOVE_CODE):
        issues.append(
            f"仅删除 {changes['removed']} 行,无新增."
            f"可能是误删操作."
        )
    return issues
def _record_diff_telemetry(ctx: OperationContext, changes: dict,
                           diff_text: str) -> None:
    try:
        ctx.metadata["_diff_summary"] = changes
        ctx.metadata["_diff_preview"] = diff_text[:500]
    except TypeError as e:
        logger.debug("[G23] diff 遥测写入只读 metadata 失败（跳过）: %s", e)
def _affected_diff_comparisons(
        target: str, affected_files,
) -> tuple[list[tuple[str, str, str]], int]:
    comparisons: list[tuple[str, str, str]] = []
    incomplete = 0
    seen = {_snapshot_key(target)} if target else set()
    for fpath in normalize_files_list(affected_files):
        key = _snapshot_key(fpath)
        if key in seen:
            continue
        seen.add(key)
        before, after, have_before, have_after = _resolve_diff_sides(
            fpath, None, None)
        if have_before and have_after:
            comparisons.append((fpath, before, after))
        else:
            incomplete += 1
    return comparisons, incomplete
def guard_snapshot_diff(ctx: OperationContext) -> GuardResult:
    if (_operation_of(ctx) not in _G23_CONTENT_OPS
            and not _is_unknown_operation(ctx)):
        return GuardResult(guard_name="G23", passed=True,
                           message="非内容写入操作,跳过快照对比")
    issues = []
    target = _explicit_target_path(ctx)
    before_code, after_code, have_before, have_after = _resolve_diff_sides(
        target, ctx.metadata.get("before_code"), ctx.metadata.get("after_code"))
    affected_comparisons, affected_incomplete = _affected_diff_comparisons(
        target, ctx.affected_files)
    _snapshot_target_and_affected(target, ctx.affected_files)
    compared = have_before and have_after
    comparisons = ([(target, before_code, after_code)] if compared else [])
    comparisons.extend(affected_comparisons)
    if comparisons:
        totals = {"added": 0, "removed": 0, "total": 0}
        previews: list[str] = []
        multiple = len(comparisons) > 1
        for path, before, after in comparisons:
            diff_text = format_diff_preview(
                before.splitlines(), after.splitlines(),
                os.path.basename(path) or 'content')
            changes = _count_diff_changes(diff_text)
            for key in totals:
                totals[key] += changes[key]
            previews.append(diff_text)
            for issue in _build_diff_issues(changes, _operation_of(ctx)):
                issues.append(
                    f"{os.path.basename(path) or 'content'}: {issue}"
                    if multiple else issue)
        _record_diff_telemetry(ctx, totals, "\n".join(previews))
    if issues:
        return GuardResult(guard_name="G23", passed=False, level=GuardLevel.WARN,
                           message=f"快照对比发现 {len(issues)} 个异常", details=issues,
                           fix_suggestion="检查变更范围是否符合预期."
                                          "如果变更量超出预期,回滚并重新规划操作.")
    if comparisons:
        primary_incomplete = (
            not compared and bool(target) and not os.path.isdir(target))
        if affected_incomplete or primary_incomplete:
            return GuardResult(
                guard_name="G23", passed=True, level=GuardLevel.WARN,
                message=f"已完成 {len(comparisons)} 个文件的快照对比；"
                        "其余目标仅保存基线或当前不可读")
        return GuardResult(
            guard_name="G23", passed=True, message="快照对比通过")
    if not have_before and not have_after:
        return GuardResult(
            guard_name="G23", passed=True, level=GuardLevel.WARN,
            message="无可对比基线（before/after 与磁盘内容均不可用），"
                    "未做快照对比",
            fix_suggestion="提供 before_code/after_code，或先执行一次"
                           "前置快照后重试")
    if not have_before:
        saved = bool(target) and os.path.isfile(target)
        return GuardResult(
            guard_name="G23", passed=True,
            message=("已保存当前快照基线（无历史基线，未做对比）"
                     if saved else
                     "无历史基线（目标文件不存在，未做对比）"))
    return GuardResult(
        guard_name="G23", passed=True, level=GuardLevel.WARN,
        message="目标当前不可读（无 after 内容），未做快照对比",
        fix_suggestion="确认目标文件存在且可读后重试")
_G26_SAFE_PATTERNS = ("Temp", "zhenduan", "htm", ".bak", "stub",
                       "__pycache__", "_intermediate", ".tmp", "test_tmp",
                       "_cache", ".pytest_cache")
_G26_SOURCE_DELETE_EXEMPT_DIRS = ("Temp", "stub", "test_tmp")
def _g26_matches_any(target: str, patterns: tuple[str, ...]) -> bool:
    return any(_g26_match_path(target, pat) for pat in patterns)
def _g26_match_path(target: str, pattern: str) -> bool:
    _low_target = target.lower()
    _low_pattern = pattern.lower()
    _segs = _low_target.replace("\\", "/").split("/")
    if pattern.startswith("."):
        if os.path.basename(_low_target).endswith(_low_pattern):
            return True
        return any(seg == _low_pattern or seg.endswith(_low_pattern)
                   for seg in _segs)
    return any(seg == _low_pattern for seg in _segs)
def _g26_target_is_safe(target: str) -> bool:
    norm_target = os.path.normpath(target)
    is_safe = (_g26_matches_any(norm_target, _G26_SAFE_PATTERNS)
               or is_backup_artifact_name(norm_target))
    if (norm_target.lower().endswith(".py")
            and not _g26_matches_any(
                norm_target, _G26_SOURCE_DELETE_EXEMPT_DIRS)):
        return False
    return is_safe
def _g26_delete_targets(ctx: OperationContext) -> list[str]:
    targets: list[str] = []
    seen: set[str] = set()
    primary = _explicit_target_path(ctx)
    for target in ([primary] if primary else []) + list(
            normalize_files_list(ctx.affected_files)):
        key = path_identity(target)
        if key in seen:
            continue
        seen.add(key)
        targets.append(target)
    return targets
def guard_safe_delete(ctx: OperationContext) -> GuardResult:
    targets = _g26_delete_targets(ctx)
    if _is_unknown_operation(ctx):
        if not targets:
            return GuardResult(guard_name="G26", passed=True,
                               message="无目标路径,跳过")
        return GuardResult(
            guard_name="G26", passed=False, level=GuardLevel.BLOCK,
            message="未识别的操作类型，无法确认删除面（fail-closed）",
            details=[f"operation: {getattr(ctx, 'operation', None)!r}",
                     f"目标: {targets[0]}"],
            fix_suggestion="传入 OperationType 枚举或合法的操作值后重试")
    if _operation_of(ctx) not in (
            OperationType.DELETE_FILE, OperationType.DELETE_DIR,
            OperationType.CLEANUP):
        return GuardResult(guard_name="G26", passed=True,
                           message="非删除操作,跳过路径校验")
    if not targets:
        return GuardResult(guard_name="G26", passed=True,
                           message="无目标路径,跳过")
    for target in targets:
        if _g26_target_is_safe(target):
            continue
        return GuardResult(
            guard_name="G26", passed=False,
            level=GuardLevel.BLOCK,
            message=f"删除路径 '{os.path.basename(target)}' 不在安全目录内",
            details=[f"目标: {target}", f"安全模式: {', '.join(_G26_SAFE_PATTERNS)}"],
            fix_suggestion="仅删除 Temp/、.bak、stub、__pycache__ 等安全路径下的文件，"
                           "删除源码须走 guard_delete(G5) 的导入者校验流程"
        )
    if len(targets) == 1:
        message = f"删除路径 '{os.path.basename(targets[0])}' 在安全目录内"
    else:
        message = f"删除目标及受影响文件均在安全目录内（{len(targets)} 个路径）"
    return GuardResult(guard_name="G26", passed=True, message=message)
def normalize_post_write_regression(
    skill_dir: str, target: str, *, security_channel: bool
) -> dict:
    try:
        result = run_post_write_regression(skill_dir, target)
    except Exception as exc:  # noqa: BLE001 — 未获验证结论必须回滚
        if security_channel:
            logger.warning(
                "[AIManualFix] 安全通道定向回归异常(按未验证处理): %s", exc)
        else:
            logger.warning(
                "[FixSafety] 定向回归异常（按未验证处理，将回滚）: %s", exc)
        return {"status": "error", "summary": f"定向回归异常: {exc}"}
    if isinstance(result, dict):
        return result
    if security_channel:
        logger.warning(
            "[AIManualFix] 安全通道定向回归返回非法结果(%s，按未验证处理)",
            type(result).__name__)
        summary = f"定向回归返回非法结果: {type(result).__name__}"
    else:
        logger.warning("[FixSafety] 定向回归返回非 dict 类型: %r",
                       type(result))
        summary = f"定向回归返回非 dict: {type(result).__name__}"
    return {"status": "error", "summary": summary}
def run_targeted_regression_for(skill_dir: str, mod) -> dict:
    raw_target = getattr(mod, "target_file", "") if mod else ""
    if not raw_target:
        return {"status": "skipped", "summary": "非改码级修改，定向回归跳过"}
    target_file = normalize_target_path(raw_target)
    if not target_file:
        logger.warning("[FixSafety] target_file 形态非法(%s)，按未验证处理",
                       type(raw_target).__name__)
        return {"status": "error",
                "summary": "目标文件路径形态非法，无法执行定向回归"}
    full_path = resolve_within_root(skill_dir, target_file)
    if full_path is None:
        logger.warning("[FixSafety] target_file 越界，按未验证处理: %s",
                       target_file)
        return {"status": "error",
                "summary": "目标路径越界，无法执行定向回归"}
    if not os.path.isfile(full_path):
        return {"status": "skipped", "summary": "目标文件不存在，定向回归跳过"}
    try:
        result = run_targeted_regression(skill_dir, full_path)
    except Exception as e:
        logger.warning("[FixSafety] 定向回归执行异常: %s", e, exc_info=True)
        return {"status": "error", "summary": f"定向回归执行异常: {e}"}
    if isinstance(result, dict):
        return result
    logger.warning("[FixSafety] 定向回归返回非法结果(%s，按未验证处理)",
                   type(result).__name__)
    return {"status": "error",
            "summary": f"定向回归返回非法结果: {type(result).__name__}"}

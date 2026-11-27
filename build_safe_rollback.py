from __future__ import annotations

import copy
import hashlib
import itertools
import logging
import os
import re
import shutil
import tempfile
import time
from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any, TypedDict

from jwsgj.build_safe_write import (
    copy_backup,
    find_rollback_state_file,
    get_backup_dir,
    is_dangerous_operation,
    resolve_backup_surface,
    resolve_rollback_store,
    rollback_state_filename,
    rollback_state_search_dirs,
    run_targeted_regression_for,
)
from jwsgj.build_safe_write import (
    is_valid_rollback_id as _is_valid_rollback_id,
)
from jwsgj.diag_guard_io import (
    atomic_replace_bytes,
    backup_file_name,
    bytes_fingerprint,
    cleanup_backup_dir,
    path_identity,
    read_source_text_strict,
    resolve_within_root,
    run_verify_guarded,
    safe_delete,
    sequenced_backup_path,
    two_level_rmtree,
    verify_syntax,
    verify_write_degradation,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    restore_file_bytes,
    serialize_json,
    snapshot_file_bytes,
    write_json_artifact,
)
from jwsgj.diag_split_plan import detect_new_patch_style_fixes
from jwsgj.diag_types_defs import (
    GuardResult,
    OperationContext,
    is_read_only_audit,
    normalize_operation_kind,
    str_field,
)
from jwsgj.diag_types_vocab import (
    FMT_DATETIME,
    PARSE_DEGRADE_EXC,
    GuardLevel,
    OperationType,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import normalize_skill_dir

logger = logging.getLogger(__name__)
__all__ = [
    'GATE_FAILURE_PREFIXES',
    'FeedbackRollbackManager',
    'FileSnapshot',
    'RollbackHistoryEntry',
    'RollbackResult',
    'RollbackStatus',
    'VersionChain',
    'VersionMeta',
    'VersionNode',
    'apply_regression_gate',
    'current_content_hash',
    'execute_rollback',
    'get_rollback_audit',
    'guard_rollback',
    'history_path',
    'load_history_state',
    'persist_history_file',
    'read_file_input',
    'record_history_entry',
    'record_version_chain',
    'regression_undecided',
    'remove_persisted_history',
    'save_rollback_state',
    'take_pre_snapshot',
    'verify_applied_modification',
    'verify_file_hash',
]
_rollback_store: dict[str, dict] = {}
_ROLLBACK_STORE_MAX_ENTRIES = 256
_DEFAULT_MAX_BACKUPS = 50
_DEFAULT_MAX_HISTORY = 100
@dataclass(frozen=True)
class _StateBackupPlan:
    target_path: str
    affected_files: list[str]
    backup_dir: str | None
    ts: str
    rollback_id: str
@dataclass
class _RollbackRun:
    rollback_id: str
    state: dict
    loaded_file: str
    results: dict[str, bool] = field(default_factory=dict)
    failed_paths: set[str] = field(default_factory=set)
    restored_backups: list[tuple[str, str]] = field(default_factory=list)
def _backup_fingerprint(path: str) -> str:
    return bytes_fingerprint(
        os.path.abspath(path).encode("utf-8", "surrogatepass"))[:8]
def _discard_restored_backups(restored_backups: list[tuple[str, str]],
                              impact: str) -> None:
    for _orig, _bp in restored_backups:
        if not safe_delete(_bp):
            logger.warning("[Safety] 已恢复条目备份清理失败(%s): %s", impact, _bp)
def _backup_entry(state: dict, path: str, plan: _StateBackupPlan,
                  is_dir: bool) -> None:
    if plan.backup_dir is None:
        return
    suffix = ".dirbak" if is_dir else ".bak"
    try:
        fp = _backup_fingerprint(path)
        backup_name = (f"{os.path.basename(path)}.{fp}."
                       f"{plan.ts}_{plan.rollback_id}{suffix}")
        backup_path = os.path.join(plan.backup_dir, backup_name)
        copy_backup(path, backup_path, is_dir)
        state["backups"][path] = backup_path
    except (OSError, shutil.Error) as exc:
        logger.warning("[Rollback] 回滚备份%s失败(跳过该条目): %s (%s)",
                       "目录" if is_dir else "单文件", path, exc)
        state["backup_failures"].append(path)
def _make_rollback_id(target_path: str) -> str:
    return hashlib.md5(
        f"{target_path}:{time.time_ns()}:{os.urandom(4).hex()}".encode(
            "utf-8", "surrogatepass"),
        usedforsecurity=False
    ).hexdigest()[:12]
def _new_rollback_state(ctx: OperationContext, target_path: str) -> dict:
    operation_kind = normalize_operation_kind(ctx.operation)
    return {
        "target_path": target_path,
        "operation": (operation_kind.value
                      if isinstance(operation_kind, OperationType)
                      else str(operation_kind)),
        "backups": {},
        "degraded": False,
        "backup_failures": [],
        "absent_paths": [],
    }
def _ensure_backup_dir(target_path: str, state: dict) -> str | None:
    try:
        backup_dir = get_backup_dir(target_path)
        os.makedirs(backup_dir, exist_ok=True)
        return backup_dir
    except (OSError, RuntimeError, ValueError) as _e:
        logger.warning("[Rollback] 回滚备份目录解析/创建失败(降级仅内存): %s", _e)
        state["degraded"] = True
        return None
def save_rollback_state(ctx: OperationContext) -> str:
    target_path, affected_files = resolve_backup_surface(ctx)
    rollback_id = _make_rollback_id(target_path)
    state = _new_rollback_state(ctx, target_path)
    backup_dir = _ensure_backup_dir(target_path, state)
    ts = time.strftime('%Y%m%d_%H%M%S')
    _save_state_backup_entries(state, _StateBackupPlan(
        target_path=target_path, affected_files=affected_files,
        backup_dir=backup_dir, ts=ts, rollback_id=rollback_id))
    _persist_rollback_state(rollback_id, state, backup_dir)
    return rollback_id
def _backup_path_entry(state: dict, path: str,
                       plan: _StateBackupPlan) -> None:
    if os.path.isfile(path):
        _backup_entry(state, path, plan, is_dir=False)
    elif os.path.isdir(path):
        _backup_entry(state, path, plan, is_dir=True)
    elif path:
        absent = state.get("absent_paths")
        if isinstance(absent, list) and path not in absent:
            absent.append(path)
def _save_state_backup_entries(state: dict, plan: _StateBackupPlan) -> None:
    _backup_path_entry(state, plan.target_path, plan)
    for fpath in plan.affected_files:
        if fpath == plan.target_path:
            continue
        _backup_path_entry(state, fpath, plan)
def _evict_oldest_rollback() -> None:
    evicted = next(iter(_rollback_store), None)
    if evicted is not None:
        _rollback_store.pop(evicted, None)
        logger.debug("[Rollback] 内存回滚状态超容量,淘汰最旧条目(磁盘副本兜底): %s",
                     evicted)
def _persist_rollback_state(rollback_id: str, state: dict,
                            backup_dir: str | None) -> None:
    if (rollback_id not in _rollback_store
            and len(_rollback_store) >= _ROLLBACK_STORE_MAX_ENTRIES):
        _evict_oldest_rollback()
    _rollback_store[rollback_id] = state
    if backup_dir is not None:
        rollback_file = os.path.join(
            backup_dir, rollback_state_filename(rollback_id))
        if not _dump_state_file(rollback_file, state):
            logger.warning("[Rollback] 回滚状态磁盘持久化失败: %s", rollback_file)
def _poll_disk_state(rollback_id: str) -> tuple[dict | None, str]:
    for search_dir in rollback_state_search_dirs():
        rollback_file = find_rollback_state_file(rollback_id, search_dir)
        if not rollback_file:
            continue
        state, status, load_err = read_json_artifact(rollback_file)
        if status != "ok":
            logger.warning("[Rollback] 磁盘回滚状态加载失败(%s): %s",
                           status, load_err)
            continue
        logger.info("[Rollback] 从磁盘加载回滚状态: %s", rollback_id)
        return state, rollback_file
    return None, ''
def _load_rollback_state(rollback_id: str) -> tuple[dict | None, str]:
    state = _rollback_store.get(rollback_id)
    loaded_file = ''
    if state is None:
        state, loaded_file = _poll_disk_state(rollback_id)
        if state is None:
            logger.warning("[Rollback] 回滚状态不存在"
                           "（内存与磁盘均未找到）: %s", rollback_id)
            return None, ''
    if not isinstance(state, dict):
        logger.warning("[Rollback] 回滚状态格式非法(非对象): %s", rollback_id)
        return None, ''
    if not isinstance(state.get("backups"), dict):
        logger.warning("[Rollback] 回滚状态缺少合法 backups 映射: %s", rollback_id)
        return None, ''
    return state, loaded_file
def _is_py_source(path: str) -> bool:
    return isinstance(path, str) and path.lower().endswith(".py")
def _py_source_compile_failure(path: str) -> str:
    try:
        with open(path, 'rb') as f:
            compile(f.read(), '<string>', 'exec')
    except PARSE_DEGRADE_EXC + (OSError,) as e:
        log_swallowed(__name__, e, context="_py_source_compile_failure:PARSE_DEGRADE_EXC+")
        return f"{type(e).__name__}: {e}"
    return ""
def _verify_restored_py_syntax(original_path: str, backup_path: str) -> bool:
    failure = _py_source_compile_failure(original_path)
    if not failure:
        return True
    logger.warning(
        "回滚后语法验证失败 %s: %s（备份保留在 %s）",
        original_path, failure, backup_path,
    )
    return False
def _verify_backup_py_syntax(original_path: str, backup_path: str) -> bool:
    failure = _py_source_compile_failure(backup_path)
    if not failure:
        return True
    logger.warning(
        "回滚备份语法校验失败，跳过恢复并保留目标现状 %s: %s（备份保留在 %s）",
        original_path, failure, backup_path,
    )
    return False
def _cleanup_directory_restore_staging(staging_root: str) -> None:
    if not os.path.lexists(staging_root):
        return
    if not two_level_rmtree(staging_root):
        logger.warning(
            "[Rollback] 目录恢复暂存清理失败（保留供人工核验）: %s",
            staging_root)
def _restore_directory_backup(original_path: str, backup_path: str) -> bool:
    original_path = os.path.abspath(original_path)
    parent_dir = os.path.dirname(original_path)
    os.makedirs(parent_dir, exist_ok=True)
    staging_root = tempfile.mkdtemp(
        prefix=".jwsgj_rollback_", dir=parent_dir)
    staged_path = os.path.join(staging_root, "restored")
    previous_path = os.path.join(staging_root, "previous")
    original_moved = False
    preserve_staging = False
    try:
        shutil.copytree(backup_path, staged_path)
        if os.path.lexists(original_path):
            os.replace(original_path, previous_path)
            original_moved = True
        try:
            os.replace(staged_path, original_path)
        except OSError:
            if original_moved and not os.path.lexists(original_path):
                try:
                    os.replace(previous_path, original_path)
                    original_moved = False
                except OSError:
                    logger.exception(
                        "[Rollback] CRITICAL: 目录交换失败后现况恢复失败: %s",
                        previous_path)
            if original_moved:
                preserve_staging = True
                logger.error(
                    "[Rollback] CRITICAL: 目录交换失败，原目录保留在: %s",
                    previous_path)
            raise
        return True
    finally:
        if preserve_staging:
            logger.error(
                "[Rollback] 目录恢复暂存含唯一现况副本，禁止自动清理: %s",
                staging_root)
        else:
            _cleanup_directory_restore_staging(staging_root)
def _restore_backup_entry(original_path: str, backup_path: str) -> bool:
    try:
        parent_dir = os.path.dirname(original_path)
        if parent_dir:
            os.makedirs(parent_dir, exist_ok=True)
        if os.path.isdir(backup_path):
            _restore_directory_backup(original_path, backup_path)
        else:
            if (_is_py_source(original_path)
                    and not _verify_backup_py_syntax(original_path, backup_path)):
                return False
            restore_file_bytes(
                original_path, snapshot_file_bytes(backup_path))
            if (_is_py_source(original_path)
                    and not _verify_restored_py_syntax(original_path, backup_path)):
                return False
        return True
    except (OSError, shutil.Error) as e:
        logger.warning('[Rollback] 单文件恢复失败 %s: %s', original_path, e,
                       exc_info=True)
        return False
def _collect_unresolved_backup_failures(run: _RollbackRun) -> list[str]:
    return [m for m in _str_list_field(run.state, "backup_failures", run.rollback_id)
            if m not in run.results]
def _str_list_field(state: dict, key: str, rollback_id: str) -> list[str]:
    container = state.get(key) if isinstance(state, dict) else None
    if not isinstance(container, list):
        if container:
            logger.warning("[Rollback] 回滚状态 %s 非法容器形态(%s)，"
                           "按空清单处理: %s", key, type(container).__name__,
                           rollback_id)
        return []
    return [m for m in container if isinstance(m, str) and m]
def _record_absent_path_results(state: dict, run: _RollbackRun) -> None:
    unresolved = []
    for path in _str_list_field(state, "absent_paths", run.rollback_id):
        if os.path.lexists(path):
            run.results[path] = False
            run.failed_paths.add(path)
            unresolved.append(path)
        else:
            run.results[path] = True
    if unresolved:
        shown = ", ".join(unresolved[:3])
        logger.warning("[Rollback] %d 个保存时不存在的路径仍有新产物，"
                       "按安全策略不自动删除（回滚未完成，需人工核验）: %s%s",
                       len(unresolved), shown,
                       " ..." if len(unresolved) > 3 else "")
def _finalize_rollback(run: _RollbackRun) -> None:
    if run.results and all(run.results.values()):
        if _retire_rollback_state(run.rollback_id, run.state, run.loaded_file):
            _discard_restored_backups(run.restored_backups, "不影响回滚")
        return
    if run.failed_paths or run.restored_backups:
        _shrink_rollback_state(run.rollback_id, run.state, run.loaded_file,
                               run.failed_paths, run.restored_backups)
        return
    _retire_rollback_state(run.rollback_id, run.state, run.loaded_file)
def _rollback_path_identity(path: str, label: str) -> str:
    try:
        return path_identity(path)
    except (OSError, TypeError, ValueError) as exc:
        logger.warning("[Rollback] %s路径非法(%r): %s", label, path, exc)
        return ""
def _restore_target_identities(backups_map: dict) -> set[str]:
    identities: set[str] = set()
    for raw_path in backups_map:
        original_path = raw_path if isinstance(raw_path, str) else str(raw_path or "")
        if original_path:
            identity = _rollback_path_identity(original_path, "恢复目标")
            if identity:
                identities.add(identity)
    return identities
def _restore_item_order(item: tuple[Any, Any]) -> tuple[bool, int]:
    raw_path, raw_backup = item
    original_path = raw_path if isinstance(raw_path, str) else str(raw_path or "")
    is_directory = isinstance(raw_backup, str) and os.path.isdir(raw_backup)
    depth = os.path.abspath(original_path).count(os.sep) if original_path else 0
    return is_directory, -depth if is_directory else 0
def _restore_entries(backups_map: dict, run: _RollbackRun) -> None:
    target_identities = _restore_target_identities(backups_map)
    restore_items = sorted(backups_map.items(), key=_restore_item_order)
    for raw_path, raw_backup in restore_items:
        original_path = raw_path if isinstance(raw_path, str) else str(raw_path or "")
        if not original_path:
            logger.warning("[Rollback] 回滚条目键为空(%r)，跳过该条目", raw_path)
            run.results[""] = False
            run.failed_paths.add("")
            continue
        if not isinstance(raw_backup, str) or not raw_backup:
            logger.warning("[Rollback] 回滚条目备份路径非法(%r)，跳过该条目: %s",
                           raw_backup, original_path)
            run.results[original_path] = False
            run.failed_paths.add(original_path)
            continue
        backup_identity = _rollback_path_identity(raw_backup, "备份")
        if not backup_identity:
            run.results[original_path] = False
            run.failed_paths.add(original_path)
            continue
        if backup_identity in target_identities:
            logger.error(
                "[Rollback] 备份路径指向恢复目标，拒绝恢复及后续清理: %s -> %s",
                raw_backup, original_path)
            run.results[original_path] = False
            run.failed_paths.add(original_path)
            continue
        if _restore_backup_entry(original_path, raw_backup):
            run.results[original_path] = True
            run.restored_backups.append((original_path, raw_backup))
        else:
            run.results[original_path] = False
            run.failed_paths.add(original_path)
    ordered_results = {}
    for raw_path in backups_map:
        original_path = raw_path if isinstance(raw_path, str) else str(raw_path or "")
        ordered_results[original_path] = run.results[original_path]
    run.results = ordered_results
def execute_rollback(rollback_id: str) -> dict[str, bool]:
    raw_id = rollback_id
    rollback_id = _normalize_rollback_id(rollback_id)
    if not rollback_id:
        logger.warning("[Rollback] execute_rollback 收到非法 rollback_id(%r)，"
                       "本次无条目可回滚", raw_id)
        return {}
    state, loaded_file = _load_rollback_state(rollback_id)
    if state is None:
        return {}
    backups_map = state["backups"]
    run = _RollbackRun(rollback_id=rollback_id, state=state,
                       loaded_file=loaded_file)
    _restore_entries(backups_map, run)
    for miss in _collect_unresolved_backup_failures(run):
        run.results[miss] = False
        run.failed_paths.add(miss)
    _record_absent_path_results(state, run)
    if not backups_map:
        _log_empty_rollback_surface(state, rollback_id)
    _finalize_rollback(run)
    return run.results
def _log_empty_rollback_surface(state: dict, rollback_id: str) -> None:
    if state.get("degraded"):
        logger.warning("[Rollback] 回滚状态标记为降级（保存时备份目录不可用），"
                       "无可恢复备份内容: %s", rollback_id)
        return
    failures = _str_list_field(state, "backup_failures", rollback_id)
    if failures:
        shown = ", ".join(failures[:3])
        logger.warning("[Rollback] 回滚无可用备份内容：%d 个条目保存时备份失败"
                       "（回滚面不完整，需人工核验）: %s%s",
                       len(failures), shown, " ..." if len(failures) > 3 else "")
        return
    absent = _str_list_field(state, "absent_paths", rollback_id)
    if absent:
        return
    logger.warning("[Rollback] 回滚状态无任何备份条目（保存时无可用目标），"
                   "本次回滚为空操作: %s", rollback_id)
def _failed_backup_entries(backups: dict, failed_paths: set[str]) -> dict:
    remaining: dict = {}
    for k, v in backups.items():
        key = k if isinstance(k, str) else str(k or "")
        if key in failed_paths:
            remaining[key] = v
    return remaining
def _retire_rollback_state(rollback_id: str, state: dict,
                           loaded_file: str) -> bool:
    _rollback_store.pop(rollback_id, None)
    return _consume_rollback_state_file(rollback_id, state, loaded_file)
def _dedupe_candidates(paths: list[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for path in filter(None, paths):
        key = path_identity(path)
        if key not in seen:
            seen.add(key)
            result.append(path)
    return result
def _state_backup_dir(state: dict | None, label: str) -> str:
    target = state.get("target_path") if isinstance(state, dict) else None
    if not isinstance(target, str) or not target:
        return ""
    try:
        return get_backup_dir(target)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.debug("[Rollback] %s备份目录解析失败跳过: %r (%s)",
                     label, target, exc)
        return ""
def _state_file_candidates(rollback_id: str, state: dict,
                           loaded_file: str, label: str) -> list[str]:
    candidates: list[str] = []
    if loaded_file:
        candidates.append(loaded_file)
    backup_dir = _state_backup_dir(state, label)
    if backup_dir:
        candidates.append(os.path.join(
            backup_dir, rollback_state_filename(rollback_id)))
    return _dedupe_candidates(candidates)
def _dump_state_file(path: str, state: dict) -> bool:
    try:
        write_json_artifact(path, state, indent=2)
        return True
    except (OSError, ValueError, RecursionError) as _e:
        log_swallowed(__name__, _e, context='_dump_state_file:write_state')
        return False
def _write_state_file(state: dict, candidates: list[str], label: str) -> bool:
    for cand in candidates:
        if _dump_state_file(cand, state):
            return True
        logger.warning("[Rollback] %s回写失败: %s", label, cand)
    return False
def _shrink_rollback_state(rollback_id: str, state: dict,
                           loaded_file: str,
                           failed_paths: set[str],
                           restored_backups: list[tuple[str, str]]) -> bool:
    backups = state.get("backups") if isinstance(state, dict) else None
    if not isinstance(backups, dict):
        return False
    state["backups"] = _failed_backup_entries(backups, failed_paths)
    _rollback_store[rollback_id] = state
    if _write_state_file(state, _state_file_candidates(
            rollback_id, state, loaded_file, "收缩状态"), "收缩状态"):
        _discard_restored_backups(restored_backups, "不影响状态收缩")
        return True
    logger.warning("[Rollback] 收缩状态未能回写磁盘"
                   "（已恢复备份保留待重试，内存态保留收缩结果）")
    return False
_INSTALL_ROOT = os.path.dirname(os.path.abspath(__file__))
def _state_search_roots(state: dict | None = None,
                        loaded_file: str = '') -> list[str]:
    roots: list[str] = []
    if loaded_file:
        roots.append(os.path.dirname(loaded_file))
    backup_dir = _state_backup_dir(state, "搜索根")
    if backup_dir:
        roots.append(backup_dir)
    roots.extend(rollback_state_search_dirs())
    install_identity = path_identity(_INSTALL_ROOT)
    ordered: list[str] = []
    seen: set[str] = set()
    for root in roots:
        if not isinstance(root, str):
            continue
        identity = path_identity(root) if root else ""
        if identity == install_identity or identity in seen:
            continue
        if identity:
            seen.add(identity)
        ordered.append(root)
    return ordered
def _discover_state_file(rollback_id: str, roots: list[str]) -> str:
    search_roots = roots or [os.getcwd()]
    for root in search_roots:
        found = find_rollback_state_file(rollback_id, root)
        if found:
            return found
    return ''
def _consume_rollback_state_file(rollback_id: str, state: dict,
                                 loaded_file: str = '') -> bool:
    roots = _state_search_roots(state, loaded_file)
    candidates = _state_file_candidates(rollback_id, state, loaded_file, "回滚")
    discovered_file = _discover_state_file(rollback_id, roots)
    if discovered_file:
        candidates.append(discovered_file)
    pending = _dedupe_candidates(candidates)
    discovered = {path_identity(cand) for cand in pending}
    failed = False
    while pending:
        cand = pending.pop(0)
        if os.path.isfile(cand):
            if safe_delete(cand):
                logger.info("[Rollback] 回滚状态已消费,清理磁盘状态文件: %s", cand)
            else:
                failed = True
                logger.warning("[Rollback] 回滚状态文件清理失败: %s", cand)
        next_candidate = _discover_state_file(rollback_id, roots)
        if next_candidate:
            key = path_identity(next_candidate)
            if key not in discovered:
                discovered.add(key)
                pending.append(next_candidate)
    if failed or _rollback_state_on_disk(rollback_id, state):
        logger.warning("[Rollback] 回滚状态文件仍有残留，已恢复备份暂不清理: %s",
                       rollback_id)
        return False
    return True
def _normalize_rollback_id(raw: Any) -> str:
    if isinstance(raw, str):
        if not raw:
            return ''
        if _is_valid_rollback_id(raw):
            return raw
        logger.warning('[Rollback] rollback_id 含非标识符字符（拒绝路径形态）'
                       '%r，已按空串处理', raw)
        return ''
    if raw is not None:
        logger.warning('[Rollback] rollback_id 类型非法 %r，已按空串处理', raw)
    return ''
def _rollback_id_from(ctx: OperationContext) -> str:
    return _normalize_rollback_id(ctx.metadata.get("rollback_id", ""))
def _rollback_state_on_disk(rollback_id: str,
                            state: dict | None = None) -> bool:
    return bool(_discover_state_file(
        rollback_id, _state_search_roots(state)))
def _check_rollback_available(ctx: OperationContext) -> list[str]:
    rollback_id = _rollback_id_from(ctx)
    if not rollback_id or rollback_id in _rollback_store:
        return []
    if _rollback_state_on_disk(
            rollback_id, {"target_path": ctx.target_path}):
        return []
    return [f"回滚 ID {rollback_id} 不存在或已过期.无法执行回滚."]
def _check_rollback_needed(ctx: OperationContext) -> list[str]:
    if not ctx.metadata.get("operation_failed", False):
        return []
    rollback_id = _rollback_id_from(ctx)
    if rollback_id:
        return [f"操作标记为失败,建议执行回滚（ID: {rollback_id}）."]
    return ["操作标记为失败,但未保存回滚状态.无法自动回滚,需手动恢复."]
def _check_rollback_state_health(rollback_id: str) -> list[str]:
    issues: list[str] = []
    state = _rollback_store.get(rollback_id)
    if not isinstance(state, dict):
        return issues
    if state.get("degraded"):
        issues.append("回滚状态降级（保存时备份目录不可用），无备份内容可恢复，"
                      "本轮回滚不可用.")
    failures = _str_list_field(state, "backup_failures", rollback_id)
    if failures:
        shown = ", ".join(failures[:3])
        issues.append(f"回滚备份 {len(failures)} 个条目失败，可恢复面不完整: {shown}")
    return issues
def _rollback_surface_note(rollback_id: str) -> str:
    state = _rollback_store.get(rollback_id)
    if not isinstance(state, dict) or state.get("degraded"):
        return ""
    absent = _str_list_field(state, "absent_paths", rollback_id)
    if absent:
        return ("回滚状态已保存（存在保存时不存在的目标：无历史内容可恢复，"
                "新建产物不会被自动清除，回滚结果将标记未完成，需人工核验）")
    backups = state.get("backups")
    if isinstance(backups, dict) and backups:
        return ""
    return "回滚状态已保存（无备份条目：保存时无可用目标，回滚为空操作）"
def guard_rollback(ctx: OperationContext) -> GuardResult:
    if is_read_only_audit(ctx):
        return GuardResult(guard_name="G24", passed=True,
                           message="只读审计,跳过回滚快照（无写操作,无回滚需求）")
    issues: list[str] = []
    snapshot_saved = False
    if is_dangerous_operation(ctx.operation) and not ctx.dry_run:
        rollback_id = save_rollback_state(ctx)
        snapshot_saved = True
        try:
            ctx.metadata["rollback_id"] = rollback_id
        except TypeError as _e:
            logger.warning("[G24] rollback_id 写入只读 metadata 失败: %s", _e)
            issues.append(f"rollback_id={rollback_id} 写入操作元数据失败"
                          "（只读元数据容器），回滚 ID 未经 metadata 交接给调用方.")
        issues.extend(_check_rollback_state_health(rollback_id))
    issues.extend(_check_rollback_available(ctx))
    issues.extend(_check_rollback_needed(ctx))
    if issues:
        return GuardResult(guard_name="G24", passed=False, level=GuardLevel.WARN,
                           message=f"回滚检查发现 {len(issues)} 个问题", details=issues,
                           fix_suggestion="执行回滚恢复操作前先确认状态,"
                                          "或确认操作结果可接受.")
    if not snapshot_saved:
        reason = ("dry_run 模式,跳过快照保存（无写盘,无需回滚）"
                  if ctx.dry_run else
                  "非危险操作,跳过快照保存（无可回滚内容）")
        return GuardResult(guard_name="G24", passed=True, message=reason)
    note = _rollback_surface_note(_rollback_id_from(ctx))
    return GuardResult(guard_name="G24", passed=True,
                       message=note or "回滚状态已保存,可安全回滚")
class RollbackStatus(str, Enum):
    VERIFIED = "verified"
    ROLLED_BACK = "rolled_back"
    SKIPPED = "skipped"
    FAILED = "failed"
@dataclass(eq=False)
class FileSnapshot:
    filepath: str
    content_hash: str
    size: int
    mtime: float
    backup_path: str = ""
    modification_id: str = ""
    timestamp: float = 0.0
    original_exists: bool = True
    def __hash__(self) -> int:
        return hash(self.modification_id)
    def __eq__(self, other) -> bool:
        if isinstance(other, FileSnapshot):
            return self.modification_id == other.modification_id
        if isinstance(other, str):
            return self.modification_id == other
        return NotImplemented
@dataclass
class RollbackResult:
    status: RollbackStatus
    filepath: str
    modification_id: str
    reason: str = ""
    original_hash: str = ""
    current_hash: str = ""
    rolled_back: bool = False
    timestamp: float = 0.0
    verification_details: dict[str, Any] = field(default_factory=dict)
    rollback_attempted: bool = False
@dataclass
class RollbackHistoryEntry:
    modification_id: str
    filepath: str
    status: RollbackStatus
    reason: str
    timestamp: float
    details: dict[str, Any] = field(default_factory=dict)
    def to_dict(self) -> dict:
        return {
            "modification_id": self.modification_id,
            "filepath": self.filepath,
            "status": self.status.value if isinstance(self.status, RollbackStatus) else str(self.status),
            "reason": self.reason,
            "timestamp": self.timestamp,
            "details": self.details,
        }
def history_path(backup_dir: str) -> str:
    return os.path.join(backup_dir, "rollback_history.json")
def _serializable_details(details: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(details, dict):
        return {}
    try:
        serialize_json(details)
        return copy.deepcopy(details)
    except (OSError, ValueError, TypeError, RecursionError) as e:
        logger.warning(
            "[Rollback] 历史条目 details 不可序列化（降级为占位）: %s", e)
        return {
            "error": "<unserializable details, quarantined>",
            "quarantine_reason": str(e)[:200],
        }
def _parse_history_entry(e: Any) -> RollbackHistoryEntry | None:
    if not isinstance(e, dict):
        return None
    modification_id = e.get("modification_id", "")
    filepath = e.get("filepath", "")
    reason = e.get("reason", "")
    if not all(isinstance(value, str)
               for value in (modification_id, filepath, reason)):
        return None
    if not modification_id or not filepath:
        return None
    try:
        _raw_details = e.get("details")
        return RollbackHistoryEntry(
            modification_id=modification_id,
            filepath=filepath,
            status=RollbackStatus(e.get("status", "skipped")),
            reason=reason,
            timestamp=float(e.get("timestamp", 0.0)),
            details=_raw_details if isinstance(_raw_details, dict) else {},
        )
    except (ValueError, TypeError, OverflowError) as parse_err:
        logger.debug("[Rollback] 格式解析失败（跳过条目）: %s", parse_err)
        return None
def _rebuild_rolled_back_ids(
        history: list[RollbackHistoryEntry]) -> set[str]:
    rolled_back_ids: set[str] = set()
    for entry in history:
        if entry.status == RollbackStatus.ROLLED_BACK:
            rolled_back_ids.add(entry.modification_id)
        elif entry.status in (RollbackStatus.VERIFIED, RollbackStatus.FAILED):
            rolled_back_ids.discard(entry.modification_id)
    return rolled_back_ids
def _history_limit(max_history: Any) -> int:
    if isinstance(max_history, bool):
        return _DEFAULT_MAX_HISTORY
    if isinstance(max_history, float) and not max_history.is_integer():
        logger.warning("[Rollback] max_history 非整数值(%r)，回落默认 %d",
                       max_history, _DEFAULT_MAX_HISTORY)
        return _DEFAULT_MAX_HISTORY
    try:
        limit = int(max_history)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='_history_limit:convert')
        return _DEFAULT_MAX_HISTORY
    return max(limit, 0)
def _history_entries(raw: Any) -> list:
    entries = raw.get("entries") if isinstance(raw, dict) else raw
    if not isinstance(entries, list):
        raise TypeError("历史 entries 应为列表")
    return entries
def _parse_history_entries(
        entries: list, limit: int) -> list[RollbackHistoryEntry]:
    if limit <= 0:
        return []
    parsed = (_parse_history_entry(e) for e in entries)
    valid = [e for e in parsed if e is not None]
    if len(valid) != len(entries):
        raise ValueError(
            f"历史条目格式非法: {len(entries) - len(valid)} 条记录无法解析")
    return valid[-limit:]
def load_history_state(
    history_path: str,
    max_history: int,
    read_failures: list[str] | None = None,
) -> tuple[list[RollbackHistoryEntry], set[str]]:
    history: list[RollbackHistoryEntry] = []
    rolled_back_ids: set[str] = set()
    if not os.path.isfile(history_path):
        return history, rolled_back_ids
    try:
        raw, status, load_err = read_json_artifact(
            history_path, propagate_io=True)
    except OSError as e:
        log_swallowed(__name__, e, context='load_history_state:OSError')
        logger.warning(
            "[Rollback] 历史读取 IO 故障（保留既有文件，不覆盖）: %s", e)
        if read_failures is not None:
            read_failures.append(str(e))
        return history, rolled_back_ids
    if status != "ok":
        detail = load_err or status
        logger.warning(
            "[Rollback] 历史加载失败（保留既有文件，不覆盖）: %s", detail)
        if read_failures is not None:
            read_failures.append(str(detail))
        return history, rolled_back_ids
    limit = _history_limit(max_history)
    try:
        entries = _history_entries(raw)
        all_history = _parse_history_entries(entries, len(entries))
        rolled_back_ids = _rebuild_rolled_back_ids(all_history)
        history = all_history[-limit:] if limit > 0 else []
    except (ValueError, TypeError, RecursionError) as e:
        logger.warning(
            "[Rollback] 历史结构非法（保留既有文件，不覆盖）: %s", e)
        if read_failures is not None:
            read_failures.append(str(e))
    return history, rolled_back_ids
def persist_history_file(
    history_path: str,
    entries: list[RollbackHistoryEntry],
) -> None:
    try:
        payload = {
            "updated": time.strftime(FMT_DATETIME),
            "entries": [h.to_dict() for h in entries],
        }
        text = serialize_json(payload, indent=2)
        atomic_replace_bytes(
            history_path, text.encode("utf-8", errors="replace"),
            prefix=os.path.basename(history_path) + ".hist_",
            label="回滚历史")
    except (OSError, ValueError, TypeError, RecursionError) as e:
        logger.warning("[Rollback] 历史持久化失败: %s", e)
def remove_persisted_history(history_path: str) -> None:
    try:
        if os.path.isfile(history_path) and not safe_delete(history_path):
            logger.warning(
                "[Rollback] 历史清理失败: safe_delete 返回 False: %s",
                history_path)
    except OSError as e:
        logger.warning("[Rollback] 历史清理失败: %s", e)
def record_history_entry(
    modification_id: str,
    filepath: str,
    status: RollbackStatus,
    reason: str,
    timestamp: float,
    verification_details: dict[str, Any] | None,
) -> RollbackHistoryEntry:
    return RollbackHistoryEntry(
        modification_id=modification_id,
        filepath=filepath,
        status=status,
        reason=reason,
        timestamp=timestamp,
        details=_serializable_details(verification_details or {}),
    )
def _count_backup_artifacts(backup_dir: str) -> int:
    total = 0
    skipped = 0
    try:
        with os.scandir(backup_dir) as entries:
            for entry in entries:
                try:
                    if ((entry.is_file() and entry.name.endswith(".bak"))
                            or (entry.is_dir()
                                and entry.name.endswith(".dirbak"))):
                        total += 1
                except OSError as exc:
                    skipped += 1
                    logger.debug("[Rollback] 备份条目类型探测失败跳过: %s (%s)",
                                 entry.name, exc)
    except FileNotFoundError:
        return 0
    except OSError as _e:
        log_swallowed(__name__, _e, context='_count_backup_artifacts:OSError')
        logger.warning("[Rollback] 备份目录统计不可读（按 0 归档，需人工核验）：%s",
                       backup_dir)
        return 0
    if skipped:
        logger.warning("[Rollback] 备份统计跳过 %d 个不可探测条目：%s",
                       skipped, backup_dir)
    return total
def get_rollback_audit(skill_dir: str) -> dict:
    try:
        _normalized, backup_dir = resolve_rollback_store(skill_dir)
        history, rolled_back_ids = load_history_state(
            history_path(backup_dir), FeedbackRollbackManager.MAX_HISTORY)
        return {
            "stats": {
                "total_snapshots": _count_backup_artifacts(backup_dir),
                "total_rolled_back": len(rolled_back_ids),
                "total_history": len(history),
                "rolled_back_ids": sorted(rolled_back_ids),
            },
            "recent": [h.to_dict() for h in history[-20:]],
        }
    except Exception as e:
        logger.warning("[Rollback] get_rollback_audit: %s", e)
        return {"stats": {}, "recent": []}
def current_content_hash(filepath: str) -> tuple[str, OSError | None]:
    content, _stat, error = read_file_input(filepath)
    if error is not None:
        if isinstance(error, FileNotFoundError):
            return "", None
        log_swallowed(__name__, error, context='current_content_hash:OSError')
        return "", error
    return hashlib.sha256(content).hexdigest(), None
def _baseline_short_circuit_result(
    filepath: str,
    modification_id: str,
    snapshot: FileSnapshot,
    current_hash: str,
    hash_err: OSError | None,
) -> RollbackResult | None:
    if hash_err is not None:
        logger.error("[Rollback] 计算当前哈希失败 %s", filepath)
        return _attempted_rollback_result(
            filepath, modification_id,
            f"计算当前哈希失败: {hash_err}", snapshot, False,
            current_hash="", verification_details=None,
            rollback_attempted=False)
    if snapshot.original_exists and not snapshot.content_hash:
        return _attempted_rollback_result(
            filepath, modification_id,
            "快照缺少可靠的原始内容哈希，无法判定文件未变更", snapshot, False,
            current_hash="", verification_details=None,
            rollback_attempted=False)
    if current_hash == snapshot.content_hash:
        return _verified_result(
            filepath, modification_id, "文件未变更", snapshot,
            current_hash=current_hash, verification_details=None)
    return None
def _skipped_result(filepath: str, modification_id: str, reason: str) -> RollbackResult:
    return _rollback_result(
        RollbackStatus.SKIPPED, filepath, modification_id, reason, None)
def _rollback_result(
    status: RollbackStatus,
    filepath: str,
    modification_id: str,
    reason: str,
    snapshot: FileSnapshot | None,
    *,
    current_hash: str = "",
    verification_details: dict[str, Any] | None = None,
    rollback_attempted: bool = False,
) -> RollbackResult:
    return RollbackResult(
        status=status,
        filepath=filepath,
        modification_id=modification_id,
        reason=reason,
        original_hash=snapshot.content_hash if snapshot is not None else "",
        current_hash=current_hash,
        rolled_back=status is RollbackStatus.ROLLED_BACK,
        timestamp=time.time(),
        verification_details=verification_details or {},
        rollback_attempted=rollback_attempted,
    )
def _verified_result(
    filepath: str,
    modification_id: str,
    reason: str,
    snapshot: FileSnapshot,
    *,
    current_hash: str,
    verification_details: dict[str, Any] | None,
) -> RollbackResult:
    return _rollback_result(
        RollbackStatus.VERIFIED, filepath, modification_id, reason, snapshot,
        current_hash=current_hash, verification_details=verification_details)
def _attempted_rollback_result(
    filepath: str,
    modification_id: str,
    reason: str,
    snapshot: FileSnapshot,
    rolled_back: bool,
    *,
    current_hash: str,
    verification_details: dict[str, Any] | None,
    rollback_attempted: bool = True,
) -> RollbackResult:
    return _rollback_result(
        RollbackStatus.ROLLED_BACK if rolled_back else RollbackStatus.FAILED,
        filepath, modification_id, reason, snapshot,
        current_hash=current_hash, verification_details=verification_details,
        rollback_attempted=rollback_attempted)
def _lookup_snapshot(
    rolled_back_ids: set[str],
    snapshots: dict[str, FileSnapshot],
    filepath: str,
    modification_id: str,
) -> tuple[FileSnapshot | None, RollbackResult | None]:
    if modification_id in rolled_back_ids:
        return None, _skipped_result(filepath, modification_id, "该修改已被回滚")
    snapshot = snapshots.get(modification_id)
    if snapshot is None:
        return None, _skipped_result(filepath, modification_id, "无修改前快照")
    if os.path.normcase(snapshot.filepath) != os.path.normcase(filepath):
        return None, _skipped_result(
            filepath, modification_id, "快照与目标文件不匹配")
    return snapshot, None
def _restore_original_absence(snapshot: FileSnapshot) -> bool:
    if not os.path.lexists(snapshot.filepath):
        return True
    if not safe_delete(snapshot.filepath):
        logger.error("[Rollback] 恢复原始不存在状态失败: %s", snapshot.filepath)
        return False
    if os.path.lexists(snapshot.filepath):
        logger.error("[Rollback] 新文件回收后仍然存在: %s", snapshot.filepath)
        return False
    return True
def _rollback_ownership_valid(filepath: str, expected_hash: str) -> bool:
    actual_hash, error = current_content_hash(filepath)
    if error is not None:
        logger.error(
            "[Rollback] 回滚前候选所有权校验读取失败 %s: %s",
            filepath, error)
        return False
    if actual_hash != expected_hash:
        logger.error(
            "[Rollback] 回滚前目标内容已变化，拒绝覆盖并发更新: %s "
            "(candidate=%s..., current=%s...)",
            filepath, expected_hash[:8], actual_hash[:8])
        return False
    return True

def _restore_snapshot_file(
    snapshot: FileSnapshot,
    expected_current_hash: str | None = None,
) -> bool:
    if (expected_current_hash is not None
            and not _rollback_ownership_valid(
                snapshot.filepath, expected_current_hash)):
        return False
    if not snapshot.original_exists:
        return _restore_original_absence(snapshot)
    if not snapshot.content_hash:
        logger.error(
            "[Rollback] 快照缺少可靠的原始内容哈希，拒绝恢复: %s",
            snapshot.filepath)
        return False
    if not snapshot.backup_path or not os.path.isfile(snapshot.backup_path):
        logger.error("[Rollback] 备份文件不存在: %s", snapshot.backup_path)
        return False
    if not verify_file_hash(
            snapshot.backup_path, snapshot.content_hash, "备份",
            "内容与快照哈希失配，拒绝恢复"):
        return False
    try:
        parent_dir = os.path.dirname(snapshot.filepath)
        if parent_dir:
            os.makedirs(parent_dir, exist_ok=True)
        restore_file_bytes(
            snapshot.filepath, snapshot_file_bytes(snapshot.backup_path))
    except OSError:
        logger.exception("[Rollback] 回滚失败")
        return False
    return verify_file_hash(
        snapshot.filepath, snapshot.content_hash, "恢复",
        "内容与快照哈希失配")
def _empty_snapshot_data(
    filepath: str,
    modification_id: str,
    *,
    original_exists: bool,
) -> FileSnapshot:
    return FileSnapshot(
        filepath=filepath,
        content_hash="",
        size=0,
        mtime=0.0,
        modification_id=modification_id,
        timestamp=time.time(),
        original_exists=original_exists,
    )
def _resolve_backup_path(
    backup_dir: str,
    snapshots: dict[str, FileSnapshot],
    modification_id: str,
    filepath: str,
    backup_path: str,
) -> str:
    if not os.path.exists(backup_path):
        return backup_path
    _prev = snapshots.get(modification_id)
    _is_redo = (_prev is not None and _prev.backup_path
                and os.path.normcase(_prev.backup_path)
                == os.path.normcase(backup_path))
    if _is_redo:
        return backup_path
    return sequenced_backup_path(
        backup_dir, modification_id, filepath, backup_path)
def _active_backup_protect(
    snapshots: dict[str, FileSnapshot],
    rolled_back_ids: set[str],
) -> set[str]:
    return {snapshot.backup_path
            for snapshot_id, snapshot in snapshots.items()
            if snapshot.backup_path and snapshot_id not in rolled_back_ids}
def _capture_backup(
    backup_dir: str,
    snapshots: dict[str, FileSnapshot],
    modification_id: str,
    filepath: str,
    content: bytes,
) -> str:
    candidate = os.path.join(
        backup_dir, backup_file_name(modification_id, filepath))
    resolved = _resolve_backup_path(
        backup_dir, snapshots, modification_id, filepath, candidate)
    try:
        parent_dir = os.path.dirname(resolved)
        if parent_dir:
            os.makedirs(parent_dir, exist_ok=True)
        atomic_replace_bytes(
            resolved, content,
            prefix=f".{os.path.basename(resolved)}.tmp_",
            label="回滚快照备份临时产物")
    except OSError:
        logger.exception(
            "[Rollback] 备份创建失败(磁盘/权限)，快照降级为无备份")
        return ""
    return resolved
@dataclass(frozen=True, slots=True)
class _RollbackAttempt:
    success: bool
    reason: str
    current_hash: str = ""
    verification_details: dict[str, Any] | None = None
class FeedbackRollbackManager:
    MAX_BACKUPS = _DEFAULT_MAX_BACKUPS
    MAX_HISTORY = _DEFAULT_MAX_HISTORY
    def __init__(self, skill_dir: str, backup_dir: str = ""):
        self.skill_dir, self.backup_dir = resolve_rollback_store(
            skill_dir, backup_dir)
        os.makedirs(self.backup_dir, exist_ok=True)
        self._snapshots: dict[str, FileSnapshot] = {}
        self._history_read_failures: list[str] = []
        self._history_capacity = _history_limit(self.MAX_HISTORY)
        self._history, self._rolled_back_ids = load_history_state(
            history_path(self.backup_dir), self._history_capacity,
            self._history_read_failures)
    def _next_auto_id(self) -> str:
        return (f"mod_{int(time.time() * 1000)}_"
                f"{os.urandom(4).hex()}")
    def _register_snapshot(self, snapshot: FileSnapshot) -> FileSnapshot:
        self._snapshots[snapshot.modification_id] = snapshot
        self._rolled_back_ids.discard(snapshot.modification_id)
        return snapshot
    def _snapshot_read_failure(
        self,
        filepath: str,
        modification_id: str,
        read_err: Exception,
    ) -> FileSnapshot:
        if isinstance(read_err, FileNotFoundError):
            logger.warning("[Rollback] 文件不存在，创建空快照: %s", filepath)
            return self._register_snapshot(
                _empty_snapshot_data(
                    filepath, modification_id, original_exists=False))
        logger.error("[Rollback] 文件读取失败(权限/锁定)，创建空快照: %s", read_err)
        return self._register_snapshot(
            _empty_snapshot_data(
                filepath, modification_id, original_exists=True))
    def snapshot_before(
        self,
        filepath: str,
        modification_id: str = "",
    ) -> FileSnapshot:
        if not modification_id:
            modification_id = self._next_auto_id()
        filepath = os.path.abspath(filepath)
        content, stat, _read_err = read_file_input(filepath)
        if _read_err is not None:
            return self._snapshot_read_failure(
                filepath, modification_id, _read_err)
        content_hash = hashlib.sha256(content).hexdigest()
        backup_path = _capture_backup(
            self.backup_dir, self._snapshots, modification_id, filepath, content)
        snapshot = FileSnapshot(
            filepath=filepath,
            content_hash=content_hash,
            size=len(content),
            mtime=stat.st_mtime,
            backup_path=backup_path,
            modification_id=modification_id,
            timestamp=time.time(),
        )
        self._register_snapshot(snapshot)
        cleanup_backup_dir(
            self.backup_dir, self.MAX_BACKUPS,
            protect=_active_backup_protect(
                self._snapshots, self._rolled_back_ids))
        logger.debug("[Rollback] 快照已创建: %s (mod=%s, hash=%s...)",
                     filepath, modification_id, content_hash[:8])
        return snapshot
    def rekey_snapshot(self, snapshot: FileSnapshot, new_id: str) -> None:
        if snapshot is None or not new_id:
            return
        existing = self._snapshots.get(new_id)
        if existing is not None and existing is not snapshot:
            logger.warning(
                "[Rollback] rekey 目标 ID 已被其他快照占用（旧快照将被覆盖）: %s",
                new_id)
        old_id = snapshot.modification_id
        self._snapshots[new_id] = snapshot
        snapshot.modification_id = new_id
        if (old_id and old_id != new_id
                and self._snapshots.get(old_id) is snapshot):
            del self._snapshots[old_id]
        if old_id != new_id:
            if old_id in self._rolled_back_ids:
                self._rolled_back_ids.discard(old_id)
                self._rolled_back_ids.add(new_id)
            else:
                self._rolled_back_ids.discard(new_id)
    def get_snapshot(self, modification_id: str) -> FileSnapshot | None:
        return self._snapshots.get(modification_id)
    def _enter_entry(
        self,
        filepath: str,
        modification_id: Any,
    ) -> tuple[str, str, FileSnapshot | None, RollbackResult | None]:
        filepath = os.path.abspath(filepath)
        if isinstance(modification_id, FileSnapshot):
            modification_id = modification_id.modification_id
        if not modification_id:
            modification_id = self._next_auto_id()
        snapshot, skipped = _lookup_snapshot(
            self._rolled_back_ids, self._snapshots, filepath, modification_id)
        return filepath, modification_id, snapshot, skipped
    def verify_and_rollback(
        self,
        filepath: str,
        modification_id: str = "",
        verify_fn: Any | None = None,
    ) -> RollbackResult:
        filepath, modification_id, snapshot, skipped = self._enter_entry(
            filepath, modification_id)
        if skipped is not None:
            return skipped
        current_hash, _hash_err = current_content_hash(filepath)
        baseline_result = _baseline_short_circuit_result(
            filepath, modification_id, snapshot, current_hash, _hash_err)
        if baseline_result is not None:
            self._add_history(baseline_result)
            return baseline_result
        passed, details = run_verify_guarded(
            verify_fn, self._default_verify, filepath, snapshot)
        if passed:
            result = _verified_result(
                filepath, modification_id, "验证通过", snapshot,
                current_hash=current_hash, verification_details=details)
            self._add_history(result)
            return result
        return self._rollback_after_verify_failure(
            filepath, modification_id, snapshot, current_hash, details)
    def _finalize_rollback(
        self,
        filepath: str,
        modification_id: str,
        snapshot: FileSnapshot,
        attempt: _RollbackAttempt,
    ) -> RollbackResult:
        result = _attempted_rollback_result(
            filepath, modification_id, attempt.reason, snapshot,
            attempt.success, current_hash=attempt.current_hash,
            verification_details=attempt.verification_details)
        if attempt.success:
            self._rolled_back_ids.add(modification_id)
        self._add_history(result)
        return result
    def _rollback_after_verify_failure(
        self,
        filepath: str,
        modification_id: str,
        snapshot: FileSnapshot,
        current_hash: str,
        details: dict[str, Any],
    ) -> RollbackResult:
        rollback_success = _restore_snapshot_file(
            snapshot, expected_current_hash=current_hash)
        result = self._finalize_rollback(
            filepath, modification_id, snapshot,
            _RollbackAttempt(rollback_success,
                             f"验证失败: {details.get('error', '未知原因')}",
                             current_hash, details))
        logger.info("[Rollback] %s: %s (mod=%s)",
                    "已回滚" if rollback_success else "回滚失败",
                    filepath, modification_id)
        return result
    def _default_verify(
        self,
        filepath: str,
        snapshot: FileSnapshot,
    ) -> tuple[bool, dict]:
        return verify_write_degradation(filepath, snapshot, self.skill_dir)
    def rollback(
        self,
        filepath: str,
        modification_id: str = "",
        *,
        expected_current_hash: str | None = None,
    ) -> RollbackResult:
        filepath, modification_id, snapshot, skipped = self._enter_entry(
            filepath, modification_id)
        if skipped is not None:
            return skipped
        success = _restore_snapshot_file(
            snapshot, expected_current_hash=expected_current_hash)
        return self._finalize_rollback(
            filepath, modification_id, snapshot,
            _RollbackAttempt(success, "手动回滚" if success else "回滚失败"))
    def _add_history(self, result: RollbackResult) -> None:
        self._history.append(record_history_entry(
            result.modification_id,
            result.filepath,
            result.status,
            result.reason,
            result.timestamp,
            result.verification_details,
        ))
        limit = self._history_capacity
        if limit == 0:
            self._history.clear()
        elif len(self._history) > limit:
            self._history = self._history[-limit:]
        self._persist_history()
    def _persist_history(self) -> None:
        if self._history_read_failures:
            logger.warning(
                "[Rollback] 历史读取曾失败(%s)，本次不覆盖既有历史文件: %s",
                self._history_read_failures[0],
                history_path(self.backup_dir))
            return
        persist_history_file(history_path(self.backup_dir), self._history)
    def get_history(self) -> list[RollbackHistoryEntry]:
        return copy.deepcopy(self._history)
    def get_rolled_back_ids(self) -> set:
        return set(self._rolled_back_ids)
    def has_snapshot(self, modification_id: str) -> bool:
        return modification_id in self._snapshots
    def is_rolled_back(self, modification_id: str) -> bool:
        return modification_id in self._rolled_back_ids
    def get_stats(self) -> dict:
        return {
            "total_snapshots": len(self._snapshots),
            "total_rolled_back": len(self._rolled_back_ids),
            "total_history": len(self._history),
            "rolled_back_ids": sorted(self._rolled_back_ids),
        }
    def clear_history(self) -> None:
        persisted = history_path(self.backup_dir)
        remove_persisted_history(persisted)
        if os.path.isfile(persisted):
            logger.warning(
                "[Rollback] 历史清理未持久化，保留内存状态以便重试: %s",
                persisted)
            return
        self._history.clear()
        self._rolled_back_ids.clear()
        self._snapshots.clear()
@dataclass
class VersionNode:
    node_id: str
    filepath: str
    pre_hash: str = ""
    post_hash: str = ""
    modification_id: str = ""
    level: str = ""
    source_enhancement_id: str = ""
    timestamp: float = 0.0
    parent_id: str = ""
    backup_path: str = ""
    is_active: bool = True
    rollback_count: int = 0
    description: str = ""
    def to_dict(self) -> dict:
        return asdict(self)
class VersionMeta(TypedDict, total=False):
    modification_id: str
    level: str
    source_enhancement_id: str
    backup_path: str
    description: str
_VERSION_NODE_SEQ = itertools.count()
class VersionChain:
    MAX_NODES = 200
    def __init__(self, skill_dir: str):
        self.skill_dir = os.path.abspath(skill_dir)
        self._nodes: dict[str, VersionNode] = {}
        self._file_chains: dict[str, list[str]] = {}
    def _chain_nodes(self, chain: list[str]) -> list[VersionNode]:
        return [self._nodes[nid] for nid in chain if nid in self._nodes]
    def _next_node_id(self) -> str:
        return (f"VN-{int(time.time() * 1000)}-"
                f"{next(_VERSION_NODE_SEQ):04d}-{os.urandom(2).hex()}")
    def _append_to_chain(self, node: VersionNode) -> None:
        self._nodes[node.node_id] = node
        self._file_chains.setdefault(
            path_identity(node.filepath), []).append(node.node_id)
        if not node.parent_id:
            return
        parent = self._nodes.get(node.parent_id)
        if parent is not None:
            parent.is_active = False
    def _last_active_node(self, chain: list[str]) -> VersionNode | None:
        for nid in reversed(chain):
            node = self._nodes.get(nid)
            if node and node.is_active:
                return node
        return None
    def add_version(
        self,
        filepath: str,
        pre_hash: str,
        post_hash: str,
        meta: VersionMeta | None = None,
    ) -> VersionNode:
        if not isinstance(meta, dict):
            meta = {}
        modification_id = meta.get("modification_id", "")
        filepath = os.path.abspath(filepath)
        node_id = self._next_node_id()
        if not modification_id:
            modification_id = node_id
        _parent = self._last_active_node(
            self._file_chains.get(path_identity(filepath), []))
        node = VersionNode(
            node_id=node_id,
            filepath=filepath,
            pre_hash=pre_hash,
            post_hash=post_hash,
            modification_id=modification_id,
            level=meta.get("level", ""),
            source_enhancement_id=meta.get("source_enhancement_id", ""),
            timestamp=time.time(),
            parent_id=_parent.node_id if _parent is not None else "",
            backup_path=meta.get("backup_path", ""),
            description=meta.get("description", ""),
        )
        self._append_to_chain(node)
        self._prune_chain()
        logger.debug("[VersionChain] 版本节点已添加: %s (file=%s, parent=%s)",
                     node_id, os.path.basename(filepath), node.parent_id or "ROOT")
        return node
    def _prune_chain(self) -> None:
        overflow = len(self._nodes) - self.MAX_NODES
        if overflow <= 0:
            return
        for node_id in list(self._nodes):
            if overflow <= 0:
                break
            if self._evict_node(node_id):
                overflow -= 1
        if overflow > 0:
            logger.warning(
                "[VersionChain] 节点数超过上限 %d（当前 %d）：%d 个活跃节点"
                "不可淘汰，容量上限已失效", self.MAX_NODES,
                len(self._nodes), overflow)
        logger.debug("[VersionChain] 裁剪后节点数: %d", len(self._nodes))
    def _evict_node(self, node_id: str) -> bool:
        node = self._nodes.get(node_id)
        if node is None or node.is_active:
            return False
        for child in self._nodes.values():
            if child.parent_id == node_id:
                child.parent_id = node.parent_id
        self._unlink_from_chain(node)
        del self._nodes[node_id]
        return True
    def _unlink_from_chain(self, node: VersionNode) -> None:
        key = path_identity(node.filepath)
        chain = self._file_chains.get(key)
        if not chain or node.node_id not in chain:
            return
        chain.remove(node.node_id)
        if not chain:
            del self._file_chains[key]
    def _gate_backup_integrity(self, node: VersionNode, backup_path: str,
                               expected_hash: str) -> bool:
        if not expected_hash:
            logger.error(
                "[VersionChain] 节点缺少 post_hash，拒绝无完整性基线恢复: %s",
                node.node_id)
            return False
        backup_hash, hash_err = current_content_hash(backup_path)
        if hash_err is not None:
            logger.error("[VersionChain] 备份完整性校验读取失败: %s", hash_err)
            return False
        if not backup_hash.startswith(expected_hash):
            logger.error(
                "[VersionChain] 备份内容与 post_hash 失配，拒绝恢复: %s "
                "(expect=%s..., got=%s...)",
                backup_path, expected_hash[:8], backup_hash[:8])
            return False
        return True
    def _gate_readback_matches(self, backup_path: str, filepath: str) -> bool:
        try:
            with open(backup_path, "rb") as fb, open(filepath, "rb") as ft:
                if fb.read() != ft.read():
                    logger.error("[VersionChain] 恢复内容与备份失配: %s (file=%s)",
                                 backup_path, filepath)
                    return False
        except OSError:
            logger.exception("[VersionChain] 恢复读回校验读取失败")
            return False
        return True
    def _rollback_image(self, node: VersionNode) -> tuple[str, str] | None:
        chain = self._chain_nodes(
            self._file_chains.get(path_identity(node.filepath), []))
        index = next((i for i, candidate in enumerate(chain)
                      if candidate.node_id == node.node_id), None)
        if index is None or index + 1 >= len(chain):
            return None
        successor = chain[index + 1]
        if not node.post_hash or not successor.pre_hash:
            return None
        if not (successor.pre_hash.startswith(node.post_hash)
                or node.post_hash.startswith(successor.pre_hash)):
            logger.error(
                "[VersionChain] 版本链前后哈希断裂，拒绝恢复: %s -> %s",
                node.node_id, successor.node_id)
            return None
        if not successor.backup_path or not os.path.isfile(successor.backup_path):
            return None
        return successor.backup_path, node.post_hash
    def _resolve_rollback_target(self, node_id: str) -> VersionNode | None:
        node = self._nodes.get(node_id)
        if not node:
            logger.warning("[VersionChain] 版本节点不存在: %s", node_id)
            return None
        if node_id not in self._file_chains.get(
                path_identity(node.filepath), []):
            logger.warning("[VersionChain] 节点不在文件链中: %s", node_id)
            return None
        return node
    def _gate_active_version_ownership(self, filepath: str) -> bool:
        active = self.get_active_version(filepath)
        if active is None or not active.post_hash:
            logger.error(
                "[VersionChain] 缺少活动版本完整性基线，拒绝恢复: %s", filepath)
            return False
        actual_hash, hash_err = current_content_hash(filepath)
        if hash_err is not None:
            logger.error(
                "[VersionChain] 回滚前当前版本读取失败: %s", hash_err)
            return False
        if not actual_hash.startswith(active.post_hash):
            logger.error(
                "[VersionChain] 当前文件已偏离活动版本，拒绝覆盖外部更新: %s "
                "(active=%s..., current=%s...)",
                filepath, active.post_hash[:8], actual_hash[:8])
            return False
        return True
    def _restate_chain_activity(self, filepath: str, target: VersionNode) -> None:
        for nid in self._file_chains.get(path_identity(filepath), []):
            if nid == target.node_id:
                continue
            other = self._nodes.get(nid)
            if other and other.is_active:
                other.is_active = False
                other.rollback_count += 1
        target.is_active = True
        target.rollback_count += 1
    def rollback_to(self, node_id: str) -> bool:
        node = self._resolve_rollback_target(node_id)
        if node is None:
            return False
        filepath = node.filepath
        if not self._gate_active_version_ownership(filepath):
            return False
        image = self._rollback_image(node)
        if image is None:
            current_hash, hash_err = current_content_hash(filepath)
            if (hash_err is None and node.post_hash
                    and current_hash.startswith(node.post_hash)):
                self._restate_chain_activity(filepath, node)
                return True
            logger.warning(
                "[VersionChain] 目标版本缺少可用的修改后备份: %s", node_id)
            return False
        backup_path, expected_hash = image
        if not self._gate_backup_integrity(node, backup_path, expected_hash):
            return False
        try:
            restore_file_bytes(filepath, snapshot_file_bytes(backup_path))
        except OSError:
            logger.exception("[VersionChain] 文件恢复失败")
            return False
        if not self._gate_readback_matches(backup_path, filepath):
            return False
        self._restate_chain_activity(filepath, node)
        logger.info("[VersionChain] 回滚成功: %s → %s (file=%s)",
                    filepath, node_id, os.path.basename(filepath))
        return True
    def get_lineage(self, filepath: str) -> list[dict]:
        chain = self._file_chains.get(path_identity(filepath), [])
        return [node.to_dict() for node in self._chain_nodes(chain)]
    def get_active_version(self, filepath: str) -> VersionNode | None:
        chain = self._file_chains.get(path_identity(filepath), [])
        return self._last_active_node(chain)
    def get_rollback_candidates(self, filepath: str) -> list[dict]:
        candidates = []
        chain = self._file_chains.get(path_identity(filepath), [])
        for node in self._chain_nodes(chain):
            if not node.is_active and self._rollback_image(node) is not None:
                candidates.append(node.to_dict())
        return candidates
    def get_modification_genealogy(self) -> dict:
        genealogy = {}
        for chain in self._file_chains.values():
            nodes = self._chain_nodes(chain)
            if nodes:
                genealogy[nodes[0].filepath] = [node.to_dict() for node in nodes]
        return genealogy
    def get_stats(self) -> dict:
        total_nodes = len(self._nodes)
        active_nodes = sum(1 for n in self._nodes.values() if n.is_active)
        rolled_back_nodes = sum(1 for n in self._nodes.values() if n.rollback_count > 0)
        files_tracked = len(self._file_chains)
        level_counts: dict[str, int] = {}
        for node in self._nodes.values():
            level_counts[node.level] = level_counts.get(node.level, 0) + 1
        return {
            "total_version_nodes": total_nodes,
            "active_nodes": active_nodes,
            "rolled_back_nodes": rolled_back_nodes,
            "files_tracked": files_tracked,
            "level_distribution": level_counts,
        }
_GATE_LABEL_PATCH_FIX_BASE = "写盘门禁失败"
_GATE_LABEL_PATCH_FIX = f"{_GATE_LABEL_PATCH_FIX_BASE}（禁止补丁方式修复）"
_GATE_LABEL_SYNTAX = "语法验证失败"
_REG_LABEL = "定向回归失败"
GATE_FAILURE_PREFIXES: tuple[str, ...] = (
    _GATE_LABEL_SYNTAX, _GATE_LABEL_PATCH_FIX_BASE, _REG_LABEL)
def _file_hash16(path: str) -> str:
    if not path or not os.path.isfile(path):
        return ""
    digest, error = current_content_hash(path)
    if error is not None:
        raise error
    return digest[:16]
def record_version_chain(skill_dir: str, coordinator, mod) -> None:
    try:
        skill_dir = normalize_skill_dir(skill_dir)
        full_path = resolve_within_root(skill_dir, mod.target_file)
        if full_path is None:
            logger.warning(
                "[FixSafety] 版本链记录拒绝越界目标: %s", mod.target_file)
            return
        pre_hash = _file_hash16(mod.backup_path)
        post_hash = _file_hash16(full_path)
        coordinator.record_modification(
            filepath=full_path, pre_hash=pre_hash, post_hash=post_hash,
            meta={
                "modification_id": mod.modification_id,
                "level": mod.level,
                "source_enhancement_id": getattr(
                    mod, "source_enhancement_id", ""),
                "backup_path": mod.backup_path,
                "description": f"{mod.target_name}: {mod.action_type}",
            })
    except Exception as e:
        logger.warning("[FixSafety] 版本链记录失败: %s", e)
def take_pre_snapshot(skill_dir: str, rollback_mgr, entry: dict,
                      target_file: str, level: str):
    if not _gate_applies(rollback_mgr, target_file, level):
        return None
    skill_dir = normalize_skill_dir(skill_dir)
    full_path = resolve_within_root(skill_dir, target_file)
    if full_path is None:
        logger.warning("[FixSafety] 改码前快照拒绝越界目标: %s", target_file)
        return None
    if os.path.lexists(full_path) and not os.path.isfile(full_path):
        logger.warning(
            "[FixSafety] 改码前快照目标不是普通文件，降级为无快照: %s",
            full_path)
        return None
    snapshot_id = _snapshot_id_for(full_path, str_field(entry, "target"))
    try:
        snapshot = rollback_mgr.snapshot_before(
            full_path, modification_id=snapshot_id)
        if snapshot is None:
            return None
        if getattr(snapshot, "original_exists", True):
            backup_path = getattr(snapshot, "backup_path", "")
            if (not getattr(snapshot, "content_hash", "")
                    or not backup_path or not os.path.isfile(backup_path)):
                logger.error(
                    "[FixSafety] 原文件快照缺少可靠哈希或可用备份，"
                    "拒绝执行无法回滚的修改: %s", full_path)
                return None
        return snapshot
    except Exception as e:
        logger.warning("[FixSafety] 改码前快照创建异常，拒绝无基线修改: %s", e)
        return None
_SNAPSHOT_ID_MAX = 120
def _snapshot_id_for(full_path: str, target_label: str) -> str:
    identity = path_identity(full_path)
    digest = bytes_fingerprint(identity.encode("utf-8", "surrogatepass"))[:8]
    label = re.sub(r"[^\w.-]", "_", (target_label
                                     if isinstance(target_label, str)
                                     else "").strip())[:50]
    label = label or os.path.basename(full_path) or "target"
    return f"pre_{label}_{digest}"[:_SNAPSHOT_ID_MAX]
def _read_text(path: str) -> str | None:
    if not path:
        return None
    try:
        return read_source_text_strict(path)
    except PARSE_DEGRADE_EXC + (OSError,) as _e:
        log_swallowed(__name__, _e, context='_read_text:PARSE_DEGRADE_EXC+OSError')
        return None
def _snapshot_original_text(
        rollback_mgr, modification_id: str,
) -> tuple[str | None, bool]:
    if not rollback_mgr:
        return None, False
    try:
        snap = rollback_mgr.get_snapshot(modification_id)
    except Exception as _e:
        log_swallowed(__name__, _e, context='_snapshot_original_text:Exc')
        return None, True
    if snap is None:
        return None, False
    if getattr(snap, "original_exists", True) is False:
        return "", False
    backup_path = getattr(snap, "backup_path", "")
    original_source = _read_text(backup_path) if backup_path else None
    return original_source, original_source is None
def _write_gate_verify(rollback_mgr, modification_id: str):
    original_source, baseline_unavailable = _snapshot_original_text(
        rollback_mgr, modification_id)
    def _verify(filepath: str):
        if not verify_syntax(filepath, tag="[CodeFeedback]"):
            return False, {"error": "语法验证失败", "gate": "syntax"}
        if baseline_unavailable:
            return False, {
                "error": "修改前快照基线读取失败，禁止降级放行",
                "gate": "snapshot_baseline",
            }
        if original_source is None or not _is_py_source(filepath):
            return True, {"gate": "syntax"}
        current = _read_text(filepath)
        if current is None:
            logger.warning(
                "[CodeFeedback] 修改后源码读取失败，禁止跳过补丁差集校验: %s",
                filepath)
            return False, {
                "error": "修改后源码读取失败，禁止降级放行",
                "gate": "current_source_read",
            }
        hits = detect_new_patch_style_fixes(original_source, current)
        if hits:
            return False, {
                "error": ("禁止补丁方式修复：" + "；".join(hits)
                          + "——吞异常遮蔽/裸捕获属只治症状不除根因，"
                            "请定位根因后以根因消除方式重修"),
                "gate": "no_patch_fix",
                "patch_forms": list(hits),
            }
        return True, {"gate": "syntax"}
    return _verify
def _reject_applied_modification(mod, message: str) -> None:
    mod.applied = False
    mod.regression_passed = False
    mod.error_message = message
def verify_applied_modification(skill_dir: str, rollback_mgr, mod,
                                target_file: str, level: str,
                                snapshot) -> None:
    if not _gate_applies(rollback_mgr, target_file, level):
        return
    skill_dir = normalize_skill_dir(skill_dir)
    mod_id = mod.modification_id
    full_path = resolve_within_root(skill_dir, target_file)
    if full_path is None:
        logger.warning("[FixSafety] 写盘门禁拒绝越界目标: %s", target_file)
        _reject_applied_modification(
            mod, f"{_GATE_LABEL_PATCH_FIX_BASE}（目标越界）: {target_file}；"
                 "未执行根外回滚")
        return
    if snapshot:
        snap_id = getattr(snapshot, "modification_id", None)
        if snap_id and snap_id != mod_id:
            rollback_mgr.rekey_snapshot(snapshot, mod_id)
    else:
        passed, gate = _write_gate_verify(rollback_mgr, mod_id)(full_path)
        if passed:
            gate = {
                "error": "修改前快照缺失，写后基线校验不可判定，禁止降级放行",
                "gate": "snapshot_missing",
            }
        reason = gate.get("error") or "写后校验失败"
        _reject_applied_modification(
            mod, _gate_failure_message(
                gate, f"{reason}；无修改前快照，无法自动回滚",
                "not_attempted"))
        return
    rb = rollback_mgr.verify_and_rollback(
        full_path, modification_id=mod_id,
        verify_fn=_write_gate_verify(rollback_mgr, mod_id))
    gate = getattr(rb, "verification_details", None)
    gate = gate if isinstance(gate, dict) else {}
    if rb.status == RollbackStatus.VERIFIED:
        return
    logger.info("[FixSafety] 写盘门禁回滚: %s rolled_back=%s status=%s",
                mod_id, rb.rolled_back,
                getattr(rb.status, "value", rb.status))
    rollback_outcome = _rollback_outcome(rb)
    _reject_applied_modification(
        mod, _gate_failure_message(
            gate, rb.reason, rollback_outcome))
def _gate_applies(rollback_mgr, target_file: str, level: str) -> bool:
    return bool(rollback_mgr and target_file and level != "L4")
def _rollback_outcome(result: RollbackResult) -> str:
    if result.rolled_back:
        return "rolled_back"
    return ("rollback_failed" if getattr(result, "rollback_attempted", False)
            else "not_attempted")
_ROLLBACK_OUTCOME_TAILS: dict[str, str] = {
    "rolled_back": "，已通过RollbackManager回滚",
    "rollback_failed": "且回滚失败（文件可能损坏，人工介入）",
    "not_attempted": "（未执行回滚，需人工核验）",
}
def _gate_failure_message(gate: dict, reason: str,
                          rollback_outcome: str) -> str:
    gate_kind = gate.get("gate")
    if gate_kind == "no_patch_fix":
        label = _GATE_LABEL_PATCH_FIX
    elif gate_kind == "syntax":
        label = _GATE_LABEL_SYNTAX
    else:
        label = _GATE_LABEL_PATCH_FIX_BASE
    tail = _ROLLBACK_OUTCOME_TAILS.get(
        rollback_outcome, _ROLLBACK_OUTCOME_TAILS["not_attempted"])
    return f"{label}{tail}: {reason}"
def apply_regression_gate(skill_dir: str, rollback_mgr, mod) -> None:
    skill_dir = normalize_skill_dir(skill_dir)
    full_path = None
    candidate_hash = ""
    candidate_hash_err = None
    if rollback_mgr and mod.target_file:
        full_path = resolve_within_root(skill_dir, mod.target_file)
        if full_path is not None:
            candidate_hash, candidate_hash_err = current_content_hash(full_path)
    reg = run_targeted_regression_for(skill_dir, mod)
    summary = str_field(reg, "summary")
    status = reg.get("status", "unknown")
    logger.info("[FixSafety] 定向回归门禁: %s %s -> %s",
                mod.modification_id, mod.level, status)
    if status == "failed":
        rollback_outcome = "not_attempted"
        if rollback_mgr and mod.target_file:
            if full_path is None:
                logger.warning(
                    "[FixSafety] 回归回滚拒绝越界目标: %s", mod.target_file)
            elif candidate_hash_err is not None:
                logger.error(
                    "[FixSafety] 回归回滚候选基线读取失败，保留现状: %s",
                    candidate_hash_err)
            elif _rollback_ownership_valid(full_path, candidate_hash):
                rb = rollback_mgr.rollback(
                    full_path, modification_id=mod.modification_id,
                    expected_current_hash=candidate_hash)
                rollback_outcome = _rollback_outcome(rb)
        mod.applied = False
        mod.regression_passed = False
        mod.error_message = _regression_failure_message(
            rollback_outcome, summary)
    elif status == "error":
        mod.regression_passed = False
        mod.error_message = f"[定向回归未定论交AI决策] {summary[:150]}"
    elif status not in ("passed", "skipped"):
        mod.regression_passed = False
        mod.error_message = (
            f"[定向回归未定论交AI决策] 未知状态 {status!r}: {summary[:150]}")
def regression_undecided(mod) -> bool:
    return bool(mod.applied) and getattr(mod, "regression_passed", True) is False
_REGRESSION_ROLLBACK_TAILS: dict[str, str] = {
    "rolled_back": "，已回滚",
    "rollback_failed": "（回滚失败，文件可能损坏，人工介入）",
}
def _regression_failure_message(rollback_outcome: str, summary: str) -> str:
    tail = _REGRESSION_ROLLBACK_TAILS.get(
        rollback_outcome, "（未执行回滚，需人工核验）")
    return f"{_REG_LABEL}{tail}: {summary[:150]}"
def verify_file_hash(
    path: str,
    expected_hash: str,
    label: str,
    mismatch_note: str = "",
) -> bool:
    if not expected_hash:
        logger.error("[Rollback] %s完整性校验缺少预期哈希: %s", label, path)
        return False
    actual_hash, error = current_content_hash(path)
    if error is not None:
        logger.error("[Rollback] %s完整性校验读取失败: %s", label, error)
        return False
    if actual_hash != expected_hash:
        logger.error(
            "[Rollback] %s%s: %s (expect=%s..., got=%s...)",
            label, mismatch_note, path, expected_hash[:8], actual_hash[:8])
        return False
    return True
def read_file_input(filepath: str) -> tuple[bytes | None, Any | None, OSError | None]:
    try:
        with open(filepath, "rb") as f:
            content = f.read()
            stat = os.fstat(f.fileno())
        return content, stat, None
    except OSError as e:
        log_swallowed(__name__, e, context='read_file_input:OSError')
        return None, None, e

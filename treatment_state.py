from __future__ import annotations

import copy
import datetime
import difflib
import logging
import math
import os
import re
import time
from collections import Counter
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, ClassVar

from jwsgj.diag_guard_io import (
    SourceReadError,
    check_path_traversal,
    decode_source_strict,
)
from jwsgj.diag_guard_state import (
    READ_BEFORE_WRITE_GUARD,
    read_json_artifact,
    write_json_artifact,
    write_queue_json,
)
from jwsgj.diag_shared_ast_views import register_cache_release
from jwsgj.diag_types_defs import (
    norm_result_line,
    severity_rank_of_text,
)
from jwsgj.diag_types_defs import (
    str_field as _str_field,
)
from jwsgj.diag_types_normalize import (
    finding_file_key,
    finite_float_or_none,
    int_or,
    list_field,
    norm_rule_id,
    normalize_line_no,
    plan_index,
    severity_literal_from_rank,
    str_or,
)
from jwsgj.diag_types_vocab import (
    HUMAN_CONFIRM_RULE_ID,
    TX_FAILED_STATUSES,
    TX_FIXED_STATUSES,
)
from jwsgj.log_config import (
    locked_artifact,
    log_swallowed,
    safe_write_audit,
    write_module_run,
)
from jwsgj.runtime_paths import (
    fixer_experiences_path,
    get_temp_dir,
    human_confirmations_path,
    json_artifact_path,
    path_scoped_namespace,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
    normalize_text,
    resolve_skill_relative_path,
)
from jwsgj.shared_cache import get_warmed_cache

logger = logging.getLogger(__name__)
__all__ = [
    'AUTO_FIXED_STATUSES',
    'DEFAULT_COUNTED_STATUSES',
    'EXPERIENCE_FILE',
    'FAILED_STATUSES',
    'FALLBACK_RULE_ID',
    'MAX_EXPERIENCES_PER_RULE',
    'NO_INDEX',
    'SOFT_CLOSURE_BANNED_STATUSES',
    'TREATMENT_COUNT_KEYS',
    'TREATMENT_TERMINAL_STATUSES',
    'ExperienceStore',
    'FixRecord',
    'FixTarget',
    'FixerExperience',
    'HumanConfirmationEntry',
    'HumanConfirmationStore',
    'LearningHook',
    'adjust_treatment_counters',
    'apply_human_confirm_to_findings',
    'apply_human_confirmation',
    'apply_item_status',
    'canonical_locator_key',
    'check_treatment_zero_leftover',
    'clear_fix_plans_cache',
    'clear_treatment_state_cache',
    'confirmed_real_locators',
    'fp_item_identity',
    'get_treatment_state_path',
    'init_treatment_state',
    'item_index',
    'item_result',
    'item_result_reason',
    'item_status',
    'iter_unique_rule_observations',
    'load_fix_target',
    'load_treatment_fix_plans',
    'load_treatment_items',
    'load_treatment_state',
    'locate_treatment_item',
    'mark_fix_plan_status',
    'mark_item_fp_confirmed',
    'normalize_item_severity',
    'normalize_rule_key',
    'open_confirm_store',
    'parse_locator_rule_family',
    'query_fix_experience',
    'read_treatment_state_items',
    'record_fix_experience',
    'record_fix_result',
    'record_treatment_fix_plan',
    'reset_treatment_artifacts',
    'rule_id_of',
    'save_treatment_fix_plans',
    'save_treatment_state',
    'state_item_entry',
    'treatment_fix_plan_path',
    'treatment_items_integrity',
    'treatment_progress',
    'treatment_save_deferral',
    'update_treatment_item_state',
    'warm_shared_ast_cache',
]
logger.info("treatment_state 状态域（治疗状态/修复计划/人工确认/条目投影/误报身份）已加载: %d 项导出", len(__all__))
def _skill_dir_arg(skill_dir, arg: str = "skill_dir") -> str:
    if isinstance(skill_dir, os.PathLike):
        skill_dir = os.fspath(skill_dir)
    if not isinstance(skill_dir, str):
        raise TypeError(
            f"{arg} 必须为 str 或 os.PathLike，实际 "
            f"{type(skill_dir).__name__}: {skill_dir!r}")
    if not skill_dir.strip():
        raise ValueError(f"{arg} 为空，拒绝把治疗状态落到进程 cwd")
    return normalize_skill_dir(skill_dir)
def _cache_key_for_path(path: str) -> str:
    return os.path.normcase(os.path.normpath(path))
def _path_fingerprint(path: str) -> tuple[int, int] | None:
    try:
        stat = os.stat(path)
    except OSError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_path_fingerprint:OSError')
        return None
    return stat.st_mtime_ns, stat.st_size
def treatment_fix_plan_path(skill_dir: str) -> str:
    return json_artifact_path(_skill_dir_arg(skill_dir),
                              '_treatment_fix_plan.json')
_FIX_PLANS_CACHE: dict[str, list] = {}
_FIX_PLANS_CACHE_FINGERPRINTS: dict[str, tuple[int, int] | None] = {}
def _plan_index_matches(plan: object, index: int) -> bool:
    return isinstance(plan, dict) and plan_index(plan.get("index")) == index
def _find_plan_position(plans: list, index: int) -> int | None:
    for _pos, _plan in enumerate(plans):
        if _plan_index_matches(_plan, index):
            return _pos
    return None
def _evict_fix_plans_cache(key: str) -> None:
    _FIX_PLANS_CACHE.pop(key, None)
    _FIX_PLANS_CACHE_FINGERPRINTS.pop(key, None)
def clear_fix_plans_cache() -> int:
    _n = len(_FIX_PLANS_CACHE)
    _FIX_PLANS_CACHE.clear()
    _FIX_PLANS_CACHE_FINGERPRINTS.clear()
    return _n
_FIX_PLANS_CORRUPT_KINDS = frozenset({"parse_error", "non_list"})
def _read_fix_plans_shared(skill_dir: str) -> tuple[list, str]:
    """读取修复方案清单的只读视图（缓存命中不深拷贝）。

    调用方只允许读或写时复制（构造新列表/新 dict）；需要原地修改时走
    ``_read_fix_plans_checked`` 拿隔离副本。清单实测 358KB/71 项，逐次
    深拷贝是 O(N²) 重复劳动（70 次 1.4s），故读侧共享、写侧拷贝一次。
    """
    path = treatment_fix_plan_path(skill_dir)
    _key = _cache_key_for_path(path)
    _hit = _FIX_PLANS_CACHE.get(_key)
    if _hit is not None:
        _cached_fp = _FIX_PLANS_CACHE_FINGERPRINTS.get(_key)
        if _cached_fp is not None and _cached_fp == _path_fingerprint(path):
            return _hit, "ok"
        _evict_fix_plans_cache(_key)
    data, kind, _err = read_json_artifact(path, propagate_io=True)
    if kind == "parse_error":
        logger.warning('[TreatmentPlan] 修复方案清单读取失败，按空处理: %s (%s)',
                       path, _err)
        return [], "parse_error"
    if kind != "ok":
        return [], "missing"
    if not isinstance(data, list):
        logger.warning(
            "[TreatmentPlan] 修复方案清单顶层非列表(%s)，按损坏处理: %s",
            type(data).__name__, path)
        return [], "non_list"
    _FIX_PLANS_CACHE[_key] = copy.deepcopy(data)
    _FIX_PLANS_CACHE_FINGERPRINTS[_key] = _path_fingerprint(path)
    return list(data), "ok"
def _read_fix_plans_checked(skill_dir: str) -> tuple[list, str]:
    """返回隔离副本（公开契约）：调用方可安全原地修改。"""
    plans, kind = _read_fix_plans_shared(skill_dir)
    if kind != "ok":
        return plans, kind
    return copy.deepcopy(plans), kind
def load_treatment_fix_plans(skill_dir: str) -> list:
    plans, _kind = _read_fix_plans_checked(skill_dir)
    return plans
def save_treatment_fix_plans(skill_dir: str, plans: list) -> None:
    if isinstance(plans, tuple):
        plans = list(plans)
    if not isinstance(plans, list):
        raise TypeError(
            "修复方案清单必须是 list/tuple，实际 "
            f"{type(plans).__name__}；拒绝写入非清单载荷")
    plans = list(plans)
    path = treatment_fix_plan_path(skill_dir)
    _key = _cache_key_for_path(path)
    try:
        write_json_artifact(path, plans)
        _FIX_PLANS_CACHE[_key] = copy.deepcopy(plans)
        _FIX_PLANS_CACHE_FINGERPRINTS[_key] = _path_fingerprint(path)
    except (OSError, ValueError, TypeError, RecursionError):
        _evict_fix_plans_cache(_key)
        raise
def record_treatment_fix_plan(skill_dir: str, plan: dict) -> list:
    if not isinstance(plan, dict):
        raise TypeError(
            f"修复方案必须是 dict，实际 {type(plan).__name__}；"
            "拒绝把非映射载荷写入方案清单")
    plans, _kind = _read_fix_plans_shared(skill_dir)
    if _kind in _FIX_PLANS_CORRUPT_KINDS:
        raise ValueError(
            "修复方案清单损坏或顶层形态异常，拒绝用单条记录覆盖原始证据: "
            f"{treatment_fix_plan_path(skill_dir)}")
    _idx = plan_index(plan.get('index'))
    if _idx is not None:
        plans = [p for p in plans if not _plan_index_matches(p, _idx)]
    plans = [*plans, plan]
    save_treatment_fix_plans(skill_dir, plans)
    return plans
def mark_fix_plan_status(skill_dir: str, index: int, status: str,
                         extra: dict | None = None) -> bool:
    if extra is not None and not isinstance(extra, dict):
        raise TypeError(
            f"extra 必须是 dict 或 None，实际 {type(extra).__name__}")
    _idx = plan_index(index)
    if _idx is None:
        return False
    plans, _kind = _read_fix_plans_shared(skill_dir)
    if _kind in _FIX_PLANS_CORRUPT_KINDS:
        raise ValueError(
            "修复方案清单损坏或顶层形态异常，拒绝状态回写（保留原始证据）: "
            f"{treatment_fix_plan_path(skill_dir)}")
    _pos = _find_plan_position(plans, _idx)
    if _pos is None:
        return False
    updated = {**plans[_pos], **(extra or {})}
    updated.update({
        'index': plans[_pos]['index'],
        'status': status,
        'updated_at': time.strftime('%Y%m%d%H%M%S'),
    })
    plans = [*plans[:_pos], updated, *plans[_pos + 1:]]
    save_treatment_fix_plans(skill_dir, plans)
    return True
_TREATMENT_STATE_PATH = "_treatment_state.json"
_STATE_INTEGRITY_KEY = "_state_integrity"
_STATE_INTEGRITY_REASON_KEY = "_state_integrity_reason"
_STATE_INTEGRITY_TORN = "torn"
_CORRUPT_AUDIT_EVENT = "guard_treatment_state_corrupt"
_TREATMENT_STATE_CACHE: dict[str, dict] = {}
_TREATMENT_STATE_CACHE_FINGERPRINTS: dict[str, tuple[int, int] | None] = {}
TREATMENT_TERMINAL_STATUSES = frozenset({
    *TX_FIXED_STATUSES, "fp_confirmed",
})
SOFT_CLOSURE_BANNED_STATUSES = frozenset({"suggestion"})
AUTO_FIXED_STATUSES: tuple[str, ...] = TX_FIXED_STATUSES
DEFAULT_COUNTED_STATUSES: tuple[str, ...] = (
    *TX_FIXED_STATUSES, *TX_FAILED_STATUSES)
FAILED_STATUSES: tuple[str, ...] = TX_FAILED_STATUSES
_TREATMENT_COUNTER_KEYS = (
    "succeeded", "failed", "rolled_back", "skipped", "fp_confirmed",
    "pending_confirm", "suggestion", "no_fixer", "ai_fixed",
)
_COUNTER_KEY_ALIASES: dict[str, str | None] = {
    "pending": None, "planned": None, "fixed": "succeeded",
    "error": "failed",
}
_KNOWN_ITEM_STATUSES = frozenset({
    *_TREATMENT_COUNTER_KEYS, *_COUNTER_KEY_ALIASES, "error",
})
def _normalized_status_text(status: object) -> str:
    if not isinstance(status, str):
        return ""
    return status.strip().lower()
def _known_item_status(status: object) -> str:
    normalized = _normalized_status_text(status)
    return normalized if normalized in _KNOWN_ITEM_STATUSES else ""
def _empty_state(status: str = "no_plan") -> dict:
    state: dict = {"total": 0, "executed": 0}
    state.update(dict.fromkeys(_TREATMENT_COUNTER_KEYS, 0))
    state.update({"current_index": 0, "status": status,
                  "items": [], "item_details": []})
    return state
def _sync_state_cache(path: str, state: dict) -> None:
    if not isinstance(state, dict):
        _evict_state_cache(path)
        return
    key = _cache_key_for_path(path)
    _TREATMENT_STATE_CACHE[key] = copy.deepcopy(state)
    _TREATMENT_STATE_CACHE_FINGERPRINTS[key] = _path_fingerprint(path)
def _evict_state_cache(path: str) -> None:
    key = _cache_key_for_path(path)
    _TREATMENT_STATE_CACHE.pop(key, None)
    _TREATMENT_STATE_CACHE_FINGERPRINTS.pop(key, None)
@dataclass
class _SaveSlot:
    depth: int = 1
    dirty: dict | None = None
_TREATMENT_SAVE_SLOTS: dict[str, _SaveSlot] = {}
def _release_slot(key: str, slot: _SaveSlot, skill_dir: str,
                  exc: BaseException | None) -> None:
    slot.depth -= 1
    if slot.depth > 0:
        return
    if _TREATMENT_SAVE_SLOTS.get(key) is slot:
        _TREATMENT_SAVE_SLOTS.pop(key, None)
    if slot.dirty is not None:
        _flush_on_exit(skill_dir, slot.dirty, exc)
def _flush_on_exit(skill_dir: str, latest: dict,
                   exc: BaseException | None) -> None:
    path = get_treatment_state_path(skill_dir)
    try:
        _ensure_treatment_state_writable(latest)
        write_json_artifact(path, latest)
        _sync_state_cache(path, latest)
    except Exception:
        _evict_state_cache(path)
        if exc is None:
            raise
        logger.warning("[GuardIO] 批量治疗异常退出时状态刷盘失败"
                     "（不掩盖原始异常）", exc_info=True)
@contextmanager
def treatment_save_deferral(skill_dir: str) -> Iterator[None]:
    _key = _cache_key_for_path(get_treatment_state_path(skill_dir))
    _slot = _TREATMENT_SAVE_SLOTS.get(_key)
    if _slot is None:
        _slot = _TREATMENT_SAVE_SLOTS[_key] = _SaveSlot()
    else:
        _slot.depth += 1
    _exc: BaseException | None = None
    try:
        yield
    except BaseException as _be:
        _exc = _be
        raise
    finally:
        _release_slot(_key, _slot, skill_dir, _exc)
def clear_treatment_state_cache() -> int:
    n = len(_TREATMENT_STATE_CACHE)
    _TREATMENT_STATE_CACHE.clear()
    _TREATMENT_STATE_CACHE_FINGERPRINTS.clear()
    return n
def get_treatment_state_path(skill_dir: str) -> str:
    return os.path.join(get_temp_dir(_skill_dir_arg(skill_dir)),
                        _TREATMENT_STATE_PATH)
def _corrupt_fallback(path: str, kind: str, **details) -> dict:
    safe_write_audit(_CORRUPT_AUDIT_EVENT, path=path, kind=kind, **details)
    detail = details.get("error") or details.get("form") or "未提供细节"
    state = _empty_state("error")
    state[_STATE_INTEGRITY_KEY] = _STATE_INTEGRITY_TORN
    state[_STATE_INTEGRITY_REASON_KEY] = (
        f"治疗状态文件损坏（kind={kind}，detail={detail}），"
        "无法确认治疗项终态；需人工修复原始文件或重新初始化治疗状态")
    return state
def _corrupt_state_reason(state: object) -> str:
    if not isinstance(state, dict):
        return ""
    if (state.get(_STATE_INTEGRITY_KEY) != _STATE_INTEGRITY_TORN
            and state.get("status") != "error"):
        return ""
    reason = state.get(_STATE_INTEGRITY_REASON_KEY)
    return reason if isinstance(reason, str) and reason else (
        "治疗状态文件完整性异常，无法确认治疗项终态")
def _ensure_treatment_state_writable(state: dict) -> None:
    if not isinstance(state, dict):
        raise TypeError(
            f"治疗状态顶层形态异常({type(state).__name__})，"
            "拒绝写盘/覆盖状态文件")
    reason = _corrupt_state_reason(state)
    if reason:
        raise ValueError(f"{reason}；禁止用损坏回退状态覆盖原状态文件")
    integrity_ok, integrity_reason = treatment_items_integrity(state)
    if not integrity_ok:
        raise ValueError(f"{integrity_reason}；禁止覆盖治疗状态文件")
def _read_state_payload(path: str) -> tuple[dict, bool]:
    state, kind, _err = read_json_artifact(path, propagate_io=True)
    if kind == "missing":
        return _empty_state(), False
    if kind == "parse_error":
        logger.warning("加载治疗状态失败: %s", _err)
        return _corrupt_fallback(path, "parse_error", error=_err), False
    if not isinstance(state, dict):
        logger.warning("治疗状态文件内容非 dict 形态(%s)，按损坏回退默认: %s",
                     type(state).__name__, path)
        return _corrupt_fallback(path, "non_dict",
                                 form=type(state).__name__), False
    return state, True
def load_treatment_state(skill_dir: str) -> dict:
    path = get_treatment_state_path(skill_dir)
    _key = _cache_key_for_path(path)
    slot = _TREATMENT_SAVE_SLOTS.get(_key)
    if slot is not None and slot.dirty is not None:
        return slot.dirty
    _cached = _TREATMENT_STATE_CACHE.get(_key)
    if _cached is not None:
        if (_TREATMENT_STATE_CACHE_FINGERPRINTS.get(_key)
                == _path_fingerprint(path)):
            return copy.deepcopy(_cached)
        _evict_state_cache(path)
    state, cacheable = _read_state_payload(path)
    if cacheable:
        _sync_state_cache(path, state)
    return state
def _counter_key(status: object) -> str | None:
    s = _normalized_status_text(status)
    if not s:
        return None
    key = _COUNTER_KEY_ALIASES.get(s, s)
    return key if key in _TREATMENT_COUNTER_KEYS else None
def _net_counter_deltas(from_status: str, to_status: str,
                        n: int) -> dict[str, int]:
    net: dict[str, int] = {}
    for status, delta in ((from_status, -n), (to_status, n)):
        key = _counter_key(status)
        if key is not None:
            net[key] = net.get(key, 0) + delta
    return net
def _apply_counter_delta(state: dict, k: str, delta: int) -> None:
    state[k] = max(0, int_or(state.get(k, 0)) + delta)
def adjust_treatment_counters(state: dict, from_status: str, to_status: str, n: int=1) -> dict:
    if not isinstance(state, dict):
        logger.debug("治疗状态入参非 dict(重建空簿记): %r", type(state).__name__)
        state = {}
    n = max(0, int_or(n))
    for key, delta in _net_counter_deltas(from_status, to_status, n).items():
        _apply_counter_delta(state, key, delta)
    return state
def _state_items(state: dict) -> list:
    items = state.get("items")
    if not isinstance(items, list):
        items = state["items"] = []
    return items
def _target_item(items: list, index) -> dict | None:
    idx = plan_index(index)
    if idx is None or idx < 0:
        return None
    matched = None
    for item in items:
        if (isinstance(item, dict) and "index" in item
                and plan_index(item.get("index")) == idx):
            if matched is not None:
                return None
            matched = item
    if matched is not None:
        return matched
    if idx < len(items):
        legacy = items[idx]
        if isinstance(legacy, dict) and "index" not in legacy:
            return legacy
    return None
_AWAITING_EXECUTION_STATUSES = frozenset({"pending", "planned"})
def _executed_item_count(items: list) -> int:
    return sum(
        1 for item in items
        if isinstance(item, dict)
        and _known_item_status(item.get("status"))
        and _normalized_status_text(item.get("status"))
        not in _AWAITING_EXECUTION_STATUSES)
def _refresh_overall_status(state: dict, items: list) -> None:
    awaiting = any(
        not isinstance(item, dict)
        or not _known_item_status(item.get("status"))
        or _normalized_status_text(item.get("status"))
        in _AWAITING_EXECUTION_STATUSES
        for item in items)
    state["status"] = "in_progress" if awaiting else "completed"
def apply_item_status(state: dict, index, status: str,
                      result: dict | None = None) -> dict:
    if not isinstance(state, dict):
        logger.warning(
            "[TreatmentState] 状态非映射(%s)，拒绝条目状态迁移",
            type(state).__name__)
        return state
    normalized_status = _known_item_status(status)
    if not normalized_status:
        logger.warning("[TreatmentState] 非法条目状态，拒绝推进: index=%r, status=%r",
                       index, status)
        return state
    status = normalized_status
    items = _state_items(state)
    item = _target_item(items, index)
    if item is None:
        return state
    idx = plan_index(index)
    prev_status = item.get("status")
    item["status"] = status
    if result is not None:
        item["result"] = result
    state["current_index"] = max(
        int_or(state.get("current_index")), idx + 1)
    adjust_treatment_counters(state, prev_status, status)
    state["executed"] = _executed_item_count(items)
    if result is not None:
        details = state.get("item_details")
        if not isinstance(details, list):
            details = state["item_details"] = []
        details.append({"index": idx, "status": status, "detail": result})
    state["total"] = max(int_or(state.get("total")), len(items))
    _refresh_overall_status(state, items)
    return state
def update_treatment_item_state(skill_dir: str, index, status: str,
                                result: dict | None = None) -> dict:
    with treatment_save_deferral(skill_dir):
        state = load_treatment_state(skill_dir)
        state = apply_item_status(state, index, status, result)
        save_treatment_state(skill_dir, state)
    return state
def save_treatment_state(skill_dir: str, state: dict) -> None:
    _ensure_treatment_state_writable(state)
    path = get_treatment_state_path(skill_dir)
    _slot = _TREATMENT_SAVE_SLOTS.get(_cache_key_for_path(path))
    if _slot is None:
        try:
            write_json_artifact(path, state)
        except (OSError, TypeError, ValueError, RecursionError):
            _evict_state_cache(path)
            raise
        _sync_state_cache(path, state)
        return
    # 批量延迟写盘期间 slot.dirty 是权威状态，load_treatment_state 会优先读它，
    # 缓存快照必然过期；此处再深拷贝一份只增加 O(N) 开销（实测 72 项治疗
    # 共 2.7s）。真正落盘时由 _flush_on_exit 同步一次缓存。
    _slot.dirty = copy.deepcopy(state)
def _coerce_items(value, origin: str) -> list:
    if isinstance(value, (list, tuple)):
        return list(value)
    if value:
        logger.warning(
            "%s: items 形态非 list/tuple（%s），归一空清单",
            origin, type(value).__name__,
        )
    return []
def load_treatment_items(skill_dir: str) -> list:
    return _coerce_items(
        load_treatment_state(skill_dir).get("items"),
        "load_treatment_items")
def read_treatment_state_items(skill_dir: str) -> list:
    data, kind, err = read_json_artifact(
        get_treatment_state_path(skill_dir), propagate_io=True)
    if kind == "missing":
        return []
    if kind == "parse_error":
        logger.warning("读取治疗状态失败: %s", err)
        return []
    if isinstance(data, list):
        return list(data)
    if isinstance(data, dict):
        return list(_coerce_items(data.get("items"),
                                  "read_treatment_state_items"))
    return []
_DEFAULT_EXPIRES_DAYS = 90
_DEFAULT_TOLERANCE = 3
_DEFAULT_ITEM_SEVERITY = "P3"
_DEFAULT_MANUAL_FIX_DESCRIPTION = "AI 手动修复"
_FILE_LEVEL_SLOT = "FILE_LEVEL"
def canonical_locator_key(locator: object) -> str:
    if not isinstance(locator, str):
        return ""
    locator = locator.strip()
    if not locator:
        return ""
    parts = locator.rsplit(":", 2)
    if len(parts) != 3:
        return locator
    head, line_slot, family = parts
    head_key = finding_file_key(head)
    line_slot = line_slot.strip()
    family = family.strip()
    if not head_key or not family:
        return locator
    if line_slot == _FILE_LEVEL_SLOT:
        normalized_line = "0"
    elif line_slot.isdecimal() or (
            line_slot.startswith("-") and line_slot[1:].isdecimal()):
        normalized_line = str(int(line_slot))
    else:
        return locator
    return f"{head_key}:{normalized_line}:{family}"
def parse_locator_rule_family(locator: object) -> str:
    if not isinstance(locator, str) or not locator:
        return ""
    parts = canonical_locator_key(locator).rsplit(":", 2)
    if len(parts) != 3:
        return ""
    head, line_slot, family = parts
    if not finding_file_key(head):
        return ""
    line_slot = line_slot.strip()
    if not (line_slot.isdecimal() or (
            line_slot.startswith("-") and line_slot[1:].isdecimal())):
        return ""
    family = family.strip()
    return family if family and not family.isdecimal() else ""
@dataclass
class HumanConfirmationEntry:
    locator: str = ""
    verdict: str = ""
    rule_id: str = ""
    severity: str = ""
    reason: str = ""
    timestamp: str = ""
    session_id: str = ""
    expires_days: int = _DEFAULT_EXPIRES_DAYS
    project: str = ""
    def to_dict(self) -> dict:
        return {
            "locator": self.locator,
            "verdict": self.verdict,
            "rule_id": self.rule_id,
            "severity": self.severity,
            "reason": self.reason,
            "timestamp": self.timestamp,
            "session_id": self.session_id,
            "expires_days": self.expires_days,
            "project": self.project,
        }
    def is_expired(self) -> bool:
        try:
            if self.expires_days <= 0:
                return False
            if not isinstance(self.timestamp, str) or not self.timestamp:
                return True
            confirmed_at = datetime.datetime.fromisoformat(self.timestamp)
            if confirmed_at.tzinfo is not None:
                confirmed_at = confirmed_at.astimezone().replace(tzinfo=None)
            return (datetime.datetime.now() - confirmed_at
                    > datetime.timedelta(days=self.expires_days))
        except (ValueError, TypeError) as _e:
            log_swallowed(
                __name__, _e,
                context=(f'HumanConfirmationEntry.is_expired:'
                         f'{type(_e).__name__}'))
            return True
def _split_locator(locator: str) -> list[str]:
    parts = locator.rsplit(":", 2)
    if len(parts) < 3 or not parts[1].isdecimal():
        parts = locator.split(":")
    return parts
def _norm_tolerance(tolerance) -> int:
    if tolerance is None:
        return _DEFAULT_TOLERANCE
    if isinstance(tolerance, bool):
        logger.warning("[CV] 行容差为布尔值(%r)，按默认 %d 处理",
                       tolerance, _DEFAULT_TOLERANCE)
        return _DEFAULT_TOLERANCE
    if isinstance(tolerance, int):
        value = tolerance
    elif isinstance(tolerance, float):
        if not (math.isfinite(tolerance) and tolerance.is_integer()):
            logger.warning("[CV] 行容差非整数值(%r)，按默认 %d 处理",
                           tolerance, _DEFAULT_TOLERANCE)
            return _DEFAULT_TOLERANCE
        value = int(tolerance)
    elif isinstance(tolerance, str):
        try:
            value = int(tolerance.strip())
        except ValueError:
            logger.warning("[CV] 行容差非整数文本(%r)，按默认 %d 处理",
                           tolerance, _DEFAULT_TOLERANCE)
            return _DEFAULT_TOLERANCE
    else:
        logger.warning("[CV] 行容差形态非法(%s)，按默认 %d 处理",
                       type(tolerance).__name__, _DEFAULT_TOLERANCE)
        return _DEFAULT_TOLERANCE
    if value < 0:
        logger.warning("[CV] 行容差为负(%r)，按默认 %d 处理",
                       tolerance, _DEFAULT_TOLERANCE)
        return _DEFAULT_TOLERANCE
    return value
def _locator_line(parts: list[str]) -> int:
    if len(parts) > 1 and parts[1].isdecimal():
        return int(parts[1])
    return -1
def _norm_expires_days(value) -> int:
    if isinstance(value, bool):
        return _DEFAULT_EXPIRES_DAYS
    if isinstance(value, str):
        try:
            value = int(value.strip())
        except ValueError as _e:
            log_swallowed(__name__, _e, context='_norm_expires_days:ValueError')
            return _DEFAULT_EXPIRES_DAYS
    elif isinstance(value, float):
        if not (math.isfinite(value) and value.is_integer()):
            return _DEFAULT_EXPIRES_DAYS
        value = int(value)
    if isinstance(value, int) and value >= 0:
        return value
    return _DEFAULT_EXPIRES_DAYS
_CONFIRMATION_VERDICTS = frozenset({"confirmed", "false_positive", "deferred"})
def _normalized_verdict(value) -> str:
    return normalize_text(value).strip().lower()
def _rule_family_key(value) -> str:
    return normalize_text(value).strip().casefold()
def _build_entry(locator, verdict, *, rule_id="", severity="",
                 reason="", timestamp="", session_id="",
                 expires_days=None,
                 project="") -> HumanConfirmationEntry:
    if not isinstance(locator, str) or not isinstance(verdict, str):
        raise TypeError("locator/verdict 必须为字符串")
    return HumanConfirmationEntry(
        locator=canonical_locator_key(normalize_text(locator)),
        verdict=_normalized_verdict(verdict),
        rule_id=normalize_text(rule_id).strip(),
        severity=normalize_text(severity).strip(),
        reason=normalize_text(reason),
        timestamp=normalize_text(timestamp),
        session_id=normalize_text(session_id),
        expires_days=_norm_expires_days(expires_days),
        project=normalize_text(project).strip(),
    )
def _load_entry(entry_dict) -> HumanConfirmationEntry | None:
    if not isinstance(entry_dict, dict):
        return None
    try:
        entry = _build_entry(
            entry_dict["locator"], entry_dict["verdict"],
            rule_id=entry_dict.get("rule_id", ""),
            severity=entry_dict.get("severity", ""),
            reason=entry_dict.get("reason", ""),
            timestamp=entry_dict.get("timestamp", ""),
            session_id=entry_dict.get("session_id", ""),
            expires_days=entry_dict.get("expires_days"),
            project=entry_dict.get("project", ""),
        )
    except (KeyError, TypeError, ValueError) as _be:
        logger.warning("[CV] 确认记录单条损坏（%s），跳过该条", _be)
        return None
    if not entry.locator or not entry.verdict:
        logger.warning("[CV] 确认记录必填键为空（空 locator/verdict），跳过该条")
        return None
    if entry.verdict not in _CONFIRMATION_VERDICTS:
        logger.warning(
            "[CV] 确认记录裁决词未知(%r)，无法参与抑制/背书，跳过该条",
            entry.verdict)
        return None
    return entry if not entry.is_expired() else None
def _read_mapping_store(path: str, domain: str) -> dict:
    raw, kind, err = read_json_artifact(path, propagate_io=True)
    if kind == "missing":
        return {}
    if kind == "parse_error":
        logger.warning("[%s] 存储内容损坏，拒绝按空库重建: %s", domain, err)
        raise ValueError(f"{domain} 存储文件损坏({path}): {err}")
    if not isinstance(raw, dict):
        logger.warning(
            "[%s] 存储顶层非对象(%s)，拒绝按空库重建",
            domain, type(raw).__name__)
        raise ValueError(
            f"{domain} 存储顶层结构异常({type(raw).__name__}): {path}")
    return raw
class HumanConfirmationStore:
    """人工确认库。

    反哺进化账本跨目标共用同一份 ``_human_confirmations.json``，而 locator 是
    项目内相对定位（``scripts/x.py:10:rule``）。为避免 A 项目的确认在 B 项目
    同名相对路径上误抑制真问题，条目按项目作用域隔离：只有 ``project`` 等于
    当前项目作用域的条目参与匹配，其余条目原样保留回写。
    """
    def __init__(self, skill_dir: str):
        self.skill_dir = _skill_dir_arg(skill_dir)
        self._store_path = human_confirmations_path(self.skill_dir)
        self._project = path_scoped_namespace(self.skill_dir)
        self._confirmations: dict[str, HumanConfirmationEntry] = {}
        self._foreign_entries: list[HumanConfirmationEntry] = []
        self._load()
    def _load(self):
        raw = _read_mapping_store(self._store_path, "CV")
        _raw_entries = raw.get("entries", [])
        if not isinstance(_raw_entries, list):
            logger.warning(
                "[CV] 确认记录 entries 非列表(%s)，拒绝按空库重建",
                type(_raw_entries).__name__)
            raise ValueError("CV 确认记录 entries 非列表，拒绝按空库重建")
        for entry_dict in _raw_entries:
            entry = _load_entry(entry_dict)
            if entry is None:
                continue
            if entry.project == self._project:
                self._confirmations[entry.locator] = entry
            else:
                self._foreign_entries.append(entry)
    def _save(self) -> bool:
        try:
            with locked_artifact(self._store_path) as locked:
                if not locked:
                    logger.warning(
                        "[CV] 确认记录写锁不可用，拒绝无锁覆盖: %s",
                        self._store_path)
                    return False
                self._confirmations = {
                    locator: entry
                    for locator, entry in self._confirmations.items()
                    if not entry.is_expired()
                }
                self._write_merged_entries()
        except (OSError, TypeError, ValueError) as e:
            logger.warning("[CV] 确认记录写盘失败(不阻断): %s", e)
            return False
        return True
    def _write_merged_entries(self) -> None:
        """锁内重读磁盘再写：不覆盖其他进程/项目在本次 record 期间的写入。

        共享账本后两个治理会话可同时写同一文件；若直接全量覆盖内存快照，
        后写者会丢掉前者刚落的确认。项目作用域作为合并键，不同项目的同名
        locator 互不覆盖。
        """
        merged: dict[tuple[str, str], HumanConfirmationEntry] = {}
        raw = _read_mapping_store(self._store_path, "CV")
        raw_entries = raw.get("entries", [])
        if not isinstance(raw_entries, list):
            logger.warning(
                "[CV] 确认记录 entries 非列表(%s)，拒绝按空库重建",
                type(raw_entries).__name__)
            raise ValueError("CV 确认记录 entries 非列表，拒绝按空库重建")
        for entry_dict in raw_entries:
            entry = _load_entry(entry_dict)
            if entry is not None:
                merged[(entry.project, entry.locator)] = entry
        for entry in self._confirmations.values():
            merged[(entry.project, entry.locator)] = entry
        self._foreign_entries = [
            entry for entry in merged.values()
            if entry.project != self._project]
        write_queue_json(self._store_path, {
            "version": "1.0",
            "entries": [entry.to_dict() for entry in merged.values()],
        })
    def record(self, locator: str, verdict: str, **kw) -> bool:
        if not isinstance(locator, str) or not isinstance(verdict, str):
            logger.warning(
                "[CV] 确认记录必填键类型错误（locator=%s, verdict=%s），跳过落库",
                type(locator).__name__, type(verdict).__name__)
            return False
        locator = normalize_text(locator).strip()
        verdict = _normalized_verdict(verdict)
        if not locator or not verdict:
            logger.warning(
                "[CV] 确认记录必填键为空（locator=%r, verdict=%r），跳过落库",
                locator, verdict)
            return False
        if verdict not in _CONFIRMATION_VERDICTS:
            logger.warning(
                "[CV] 确认记录裁决词未知(%r)，不落库以免形成永不生效的"
                "静默证据", verdict)
            return False
        _t0 = time.monotonic()
        entry = _build_entry(
            locator, verdict,
            rule_id=kw.get("rule_id", ""),
            severity=kw.get("severity", ""),
            reason=kw.get("reason", ""),
            timestamp=datetime.datetime.now().isoformat(),
            session_id=kw.get("session_id", ""),
            expires_days=kw.get("expires_days"),
            project=self._project,
        )
        previous = self._confirmations.get(entry.locator)
        self._confirmations[entry.locator] = entry
        saved = self._save()
        if not saved:
            if previous is None:
                self._confirmations.pop(entry.locator, None)
            else:
                self._confirmations[entry.locator] = previous
        write_module_run(
            "treatment_state", "HumanConfirmationStore.record",
            outcome="ok" if saved else "failed",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            verdict=verdict, entries=len(self._confirmations))
        return saved
    def confirmed_locators(self) -> frozenset[str]:
        return frozenset(
            locator for locator, entry in self._confirmations.items()
            if entry.verdict == "confirmed" and not entry.is_expired())
    def lookup(self, locator: str) -> HumanConfirmationEntry | None:
        if not isinstance(locator, str):
            return None
        entry = self._confirmations.get(canonical_locator_key(locator))
        if entry is not None and entry.is_expired():
            return None
        return entry
    def _two_phase_match(self, items: list,
                         eligible_idx: list[int]) -> dict[int, tuple]:
        _matches: dict[int, tuple] = {}
        _exact_hits: set = set()
        _fuzzy_consumed: set = set()
        for i in eligible_idx:
            _item = items[i]
            _m = self.lookup(_item.get("locator", ""))
            if _m is not None and self._rule_family_guard(
                    _m, str(_item.get("rule_id", "") or ""), True):
                _matches[i] = (_m, True)
                _exact_hits.add(_m.locator)
        for i in eligible_idx:
            if i in _matches:
                continue
            _m = self.fuzzy_match(
                items[i].get("locator", ""),
                exclude=_exact_hits | _fuzzy_consumed,
                rule_id=str(items[i].get("rule_id", "") or ""))
            if _m is not None:
                _matches[i] = (_m, False)
                _fuzzy_consumed.add(_m.locator)
        return _matches
    @staticmethod
    def _rule_family_guard(match, item_rule_id: str, is_exact: bool) -> bool:
        _mrid = _rule_family_key(
            match.rule_id or parse_locator_rule_family(match.locator))
        _item_rid = _rule_family_key(item_rule_id)
        if _item_rid and _mrid and _item_rid != _mrid:
            return False
        return bool(_mrid) or bool(is_exact)
    @staticmethod
    def _stored_distance(stored_locator: str, file_part: str,
                         line_num: int) -> int | None:
        normalized = canonical_locator_key(stored_locator)
        file_key = finding_file_key(file_part)
        if not normalized.startswith(file_key + ":"):
            return None
        stored_parts = _split_locator(normalized)
        tail = stored_parts[1] if len(stored_parts) > 1 else ""
        if not tail.isdecimal():
            return None
        return abs(int(tail) - line_num)
    @staticmethod
    def _best_fuzzy_candidate(
            confirmations: dict, file_part: str, line_num: int,
            tolerance: int, excluded: frozenset,
            rule_id: str | None = None,
            rule_family: str = "") -> HumanConfirmationEntry | None:
        best_match = None
        best_distance = tolerance + 1
        for stored_locator, entry in confirmations.items():
            if stored_locator in excluded or entry.is_expired():
                continue
            if (not (rule_id or "").strip()
                    and _rule_family_key(
                        parse_locator_rule_family(stored_locator)) != rule_family):
                continue
            if (rule_id is not None
                    and not HumanConfirmationStore._rule_family_guard(
                        entry, rule_id, False)):
                continue
            dist = HumanConfirmationStore._stored_distance(
                stored_locator, file_part, line_num)
            if dist is None or dist > best_distance:
                continue
            if dist == best_distance:
                best_match = None
                continue
            best_distance = dist
            best_match = entry
        return best_match
    def fuzzy_match(
        self, locator: str, tolerance: int | None = None,
        exclude: set | None = None, rule_id: str | None = None,
    ) -> HumanConfirmationEntry | None:
        if not isinstance(locator, str) or not locator:
            return None
        tolerance = _norm_tolerance(tolerance)
        _excluded = (
            frozenset(canonical_locator_key(item)
                      for item in exclude)
            if isinstance(exclude, (set, frozenset, list, tuple))
            else frozenset())
        exact = self.lookup(locator)
        if (exact is not None and exact.locator not in _excluded
                and (rule_id is None or self._rule_family_guard(
                    exact, rule_id, True))):
            return exact
        parts = _split_locator(locator)
        file_part = finding_file_key(parts[0])
        line_num = _locator_line(parts)
        if line_num < 0 or not file_part:
            return None
        return self._best_fuzzy_candidate(
            self._confirmations, file_part, line_num, tolerance, _excluded,
            rule_id, _rule_family_key(parse_locator_rule_family(locator)))
    @staticmethod
    def _xv_match_eligible(xvf) -> bool:
        if not isinstance(xvf, dict) or not HumanConfirmationStore._xv_apply_eligible(xvf):
            return False
        locator = xvf.get("locator", "")
        return isinstance(locator, str) and bool(locator)
    def _iter_verdict_matches(self, items: list,
                              eligible) -> Iterator[tuple[int, object]]:
        _eligible_idx = [i for i, item in enumerate(items) if eligible(item)]
        _matches = self._two_phase_match(items, _eligible_idx)
        for i, matched in _matches.items():
            match = self._guarded_match(items[i], matched)
            if match is not None:
                yield i, match
    @staticmethod
    def _finding_apply_eligible(finding) -> bool:
        if not isinstance(finding, dict):
            return False
        if finding.get("conclusion", "") not in (
                "investigated", "review", "suppressed"):
            return False
        locator = finding.get("locator", "")
        return isinstance(locator, str) and bool(locator)
    @staticmethod
    def _xv_apply_eligible(xvf: dict) -> bool:
        conclusion = xvf.get("conclusion", "")
        _count = xvf.get("_independent_source_count")
        if isinstance(_count, int) and not isinstance(_count, bool):
            _single_confirmed = conclusion == "confirmed" and _count == 1
        else:
            _srcs = xvf.get("sources")
            if isinstance(_srcs, list):
                _nsrc = len(_srcs)
            else:
                try:
                    _nsrc = int(xvf.get("_source_count", 0) or 0)
                except (TypeError, ValueError) as _e:
                    log_swallowed(
                        __name__, _e,
                        context=('HumanConfirmationStore._xv_apply_eligible:'
                                 f'{type(_e).__name__}'))
                    _nsrc = 0
            _single_confirmed = conclusion == "confirmed" and _nsrc == 1
        return (
            conclusion
            in ("investigated", "review", "uncertain", "contradictory",
                "suppressed")
            or _single_confirmed
        )
    @staticmethod
    def _stamp_match_meta(target: dict, match: HumanConfirmationEntry) -> None:
        target["_human_confirmed"] = True
        target["_human_verdict"] = match.verdict
        target["_human_reason"] = match.reason
        target["_human_timestamp"] = match.timestamp
    @staticmethod
    def _apply_verdict(target: dict,
                       match: HumanConfirmationEntry) -> tuple[str, bool]:
        current = (target.get("conclusion", ""),
                   target.get("conclusion_v2", ""))
        if match.verdict == "confirmed":
            HumanConfirmationStore._stamp_match_meta(target, match)
            target["conclusion"] = "confirmed"
            target["conclusion_v2"] = "confirmed"
            return "confirmed", current != ("confirmed", "confirmed")
        if match.verdict == "false_positive":
            HumanConfirmationStore._stamp_match_meta(target, match)
            target["conclusion"] = "suppressed"
            target["conclusion_v2"] = "suppressed"
            return "false_positive", current != ("suppressed", "suppressed")
        return "", False
    @staticmethod
    def _guarded_match(item: dict, matched) -> HumanConfirmationEntry | None:
        if matched is None:
            return None
        match, is_exact = matched
        item_rule_id = str(item.get("rule_id", "") or "")
        if not HumanConfirmationStore._rule_family_guard(
                match, item_rule_id, is_exact):
            return None
        return match
    def _apply_matches(self, items: list[dict], eligible,
                       copy_items: bool) -> tuple[int, int]:
        applied_confirmed = 0
        applied_suppressed = 0
        for i, match in self._iter_verdict_matches(items, eligible):
            target = dict(items[i]) if copy_items else items[i]
            kind, changed = self._apply_verdict(target, match)
            if copy_items:
                items[i] = target
            if not changed:
                continue
            if kind == "confirmed":
                applied_confirmed += 1
            elif kind == "false_positive":
                applied_suppressed += 1
        return applied_confirmed, applied_suppressed
    def apply_to_xv_results(self, xv_findings: list[dict]) -> tuple[int, int]:
        _t0 = time.monotonic()
        applied_confirmed, applied_suppressed = self._apply_matches(
            xv_findings, self._xv_match_eligible, copy_items=False)
        write_module_run(
            "treatment_state",
            "HumanConfirmationStore.apply_to_xv_results",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            findings=len(xv_findings), confirmed=applied_confirmed,
            suppressed=applied_suppressed)
        return applied_confirmed, applied_suppressed
    def apply_to_findings(self, findings: list[dict]) -> tuple[list[dict], int, int]:
        enriched = list(findings)
        _t0 = time.monotonic()
        applied_confirmed, applied_suppressed = self._apply_matches(
            enriched, self._finding_apply_eligible, copy_items=True)
        write_module_run(
            "treatment_state",
            "HumanConfirmationStore.apply_to_findings",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            findings=len(findings), confirmed=applied_confirmed,
            suppressed=applied_suppressed)
        return enriched, applied_confirmed, applied_suppressed
    def stats(self) -> dict:
        active = [e for e in self._confirmations.values()
                  if not e.is_expired()]
        counts = Counter(e.verdict for e in active)
        return {
            "total": len(active),
            "confirmed": counts.get("confirmed", 0),
            "false_positive": counts.get("false_positive", 0),
            "deferred": counts.get("deferred", 0),
        }
def open_confirm_store(skill_dir: str):
    try:
        if not skill_dir:
            return None
        return HumanConfirmationStore(_skill_dir_arg(skill_dir))
    except Exception as e:
        logger.debug(
            "[ChannelLoop2] 确认库不可用，裁决背书/止血查询降级跳过: %s", e)
        return None
_CONFIRMED_LOCATOR_CACHE: dict[
    str, tuple[tuple[int, int] | None, tuple[HumanConfirmationEntry, ...]]
] = {}
def confirmed_real_locators(skill_dir: str) -> frozenset[str]:
    if not skill_dir:
        return frozenset()
    _sd = _skill_dir_arg(skill_dir)
    path = human_confirmations_path(_sd)
    key = f"{_cache_key_for_path(path)}|{path_scoped_namespace(_sd)}"
    fingerprint = _path_fingerprint(path)
    cached = _CONFIRMED_LOCATOR_CACHE.get(key)
    if cached is not None and cached[0] == fingerprint:
        return frozenset(
            entry.locator for entry in cached[1] if not entry.is_expired())
    store = open_confirm_store(_sd)
    if store is None:
        return frozenset()
    locators = store.confirmed_locators()
    entries = tuple(store._confirmations[locator] for locator in locators)
    _CONFIRMED_LOCATOR_CACHE[key] = (fingerprint, entries)
    return locators
def _flatten_xv_findings(xv_findings):
    flat_findings = []
    origins = []
    for top_idx, xvf in enumerate(xv_findings):
        inner = xvf.get("findings") if isinstance(xvf, dict) else None
        if isinstance(inner, list) and inner:
            for inner_idx, f in enumerate(inner):
                flat_findings.append(f)
                origins.append((inner, inner_idx))
        else:
            flat_findings.append(xvf)
            origins.append((xv_findings, top_idx))
    return flat_findings, origins
def _writeback_flattened(origins, enriched) -> None:
    if not isinstance(enriched, list) or len(enriched) != len(origins):
        return
    for (container, idx), new_f in zip(origins, enriched, strict=True):
        if isinstance(container, list) and 0 <= idx < len(container):
            container[idx] = new_f
def apply_human_confirm_to_findings(rules_applied, xv_findings, human_store):
    human_applied_confirmed = 0
    human_applied_suppressed = 0
    if human_store is not None:
        try:
            flat_findings, origins = _flatten_xv_findings(xv_findings)
            _apply_xv = getattr(human_store, "apply_to_xv_results", None)
            if callable(_apply_xv):
                human_applied_confirmed, human_applied_suppressed = (
                    _apply_xv(flat_findings)
                )
            else:
                _enriched, human_applied_confirmed, human_applied_suppressed = (
                    human_store.apply_to_findings(flat_findings)
                )
                _writeback_flattened(origins, _enriched)
        except Exception as _e:
            logger.warning("[CV] 人工确认存储应用失败: %s", _e)
    _mark_human_confirm_rule_stats(
        rules_applied, human_applied_confirmed, human_applied_suppressed)
    return human_applied_confirmed, human_applied_suppressed
def _mark_human_confirm_rule_stats(
        rules_applied, confirmed: int, suppressed: int) -> None:
    if not (confirmed or suppressed):
        return
    if not isinstance(rules_applied, dict):
        logger.warning("[CV] rules_applied 非映射(%s)，跳过人工确认规则统计回填",
                       type(rules_applied).__name__)
        return
    if HUMAN_CONFIRM_RULE_ID not in rules_applied:
        return
    rule_stats = rules_applied[HUMAN_CONFIRM_RULE_ID]
    if not isinstance(rule_stats, dict):
        logger.warning("[CV] 人工确认规则统计形态异常(%s)，跳过回填",
                       type(rule_stats).__name__)
        return
    rule_stats["triggered"] = True
    rule_stats["confirmed"] = confirmed
    rule_stats["suppressed"] = suppressed
def apply_human_confirmation(validator, xv_findings) -> tuple[Any, int, int]:
    _store = open_confirm_store(getattr(validator, "skill_dir", None) or "")
    _confirmed, _suppressed = apply_human_confirm_to_findings(
        validator.rules_applied, xv_findings, _store)
    return _store, _confirmed, _suppressed
register_cache_release(
    "treatment_state_cache", clear_treatment_state_cache, "治疗状态缓存", order=200)
register_cache_release(
    "fix_plans_cache", clear_fix_plans_cache, "修复方案清单缓存", order=210)
NO_INDEX = -1
def item_result(item: dict) -> dict:
    if not isinstance(item, dict):
        return {}
    result = item.get("result")
    return result if isinstance(result, dict) else {}
def item_result_reason(item: dict, result: dict) -> str:
    _item = item if isinstance(item, dict) else {}
    _result = result if isinstance(result, dict) else {}
    return _str_field(_result, "reason") or _str_field(_item, "message") or ""
def item_status(item: dict) -> str:
    if not isinstance(item, dict):
        return "pending"
    return _normalized_status_text(item.get("status")) or "pending"
def item_index(item: dict, fallback: int = NO_INDEX) -> int:
    if not isinstance(item, dict):
        return fallback
    if "index" not in item:
        return fallback
    idx = plan_index(item.get("index"))
    return -1 if idx is None else idx
def treatment_items_integrity(state: dict) -> tuple[bool, str]:
    if not isinstance(state, dict):
        return False, (
            f"治疗状态顶层形态异常({type(state).__name__})，"
            "无法枚举治疗项，需人工修复或重新初始化")
    corrupt_reason = _corrupt_state_reason(state)
    if corrupt_reason:
        return False, corrupt_reason
    raw_total = state.get("total", 0)
    declared_total = plan_index(raw_total)
    if declared_total is None or declared_total < 0:
        return False, (
            f"治疗状态 total 非法({raw_total!r})，无法确认声明治疗项数；"
            "需人工修复状态文件")
    if "items" not in state:
        if declared_total > 0:
            return False, (
                f"治疗状态声明 total={declared_total}，但缺少 items 清单；"
                "无法确认条目是否丢失，需人工修复状态文件")
        return True, ""
    raw = state.get("items")
    if isinstance(raw, list):
        if "total" in state and declared_total != len(raw):
            return False, (
                f"治疗状态声明 total={declared_total}，但 items 实际为 "
                f"{len(raw)} 条；清单可能缺失或截断，需人工修复状态文件")
        index_positions = {}
        for position, item in enumerate(raw):
            if not isinstance(item, dict) or "index" not in item:
                continue
            index = plan_index(item.get("index"))
            if index is None or index < 0:
                continue
            if index in index_positions:
                return False, (
                    f"治疗状态 items 存在重复 index={index}（列表位置 "
                    f"{index_positions[index]} 与 {position}），无法唯一定位治疗项；"
                    "需人工修复状态文件")
            index_positions[index] = position
        return True, ""
    return False, (f"治疗状态 items 形态异常({type(raw).__name__})，"
                   f"无法枚举治疗项，需人工修复状态文件")
_LEFTOVER_ACTIONS = {
    "pending": "未执行治疗，需重新执行治疗步骤",
    "pending_confirm": "需人工/AI确认并修复",
    "no_fixer": "缺少修复器，需开发修复器或AI手动修复",
    "failed": "修复尝试失败，需AI手动修复",
    "error": "修复尝试失败，需AI手动修复",
    "rolled_back": "修复被回滚，需AI手动修复",
    "skipped": "被跳过，需重新处理",
    "planned": "已生成修复方案，待AI审核执行验证",
    "suggestion": "建议态不是终态（软销项被禁止），需实际修复或确认误报",
    "invalid_entry": "状态条目损坏（非 dict），需人工修复治疗状态文件",
}
TREATMENT_COUNT_KEYS = (
    "total", "executed", *_TREATMENT_COUNTER_KEYS, "current_index")
def _treatment_container_fields(state: dict) -> dict:
    _raw_status = state.get("status")
    if not isinstance(_raw_status, str) or not _raw_status:
        _raw_status = "no_plan"
    _raw_items = state.get("items")
    _raw_details = state.get("item_details")
    _raw_cov = state.get("fix_coverage")
    return {
        "status": _raw_status,
        "items": _raw_items if isinstance(_raw_items, list) else [],
        "item_details": _raw_details if isinstance(_raw_details, list) else [],
        "fix_coverage": _raw_cov if isinstance(_raw_cov, dict) else {},
    }
def _normalized_treatment_counts(state: dict) -> dict[str, int]:
    return {key: max(0, int_or(state.get(key, 0)))
            for key in TREATMENT_COUNT_KEYS}
def _next_actionable_item(items: list):
    for item in items:
        if (isinstance(item, dict)
                and item_status(item) in _AWAITING_EXECUTION_STATUSES):
            return item
    return None
def treatment_progress(state: dict) -> dict:
    if not isinstance(state, dict):
        state = {}
    result = _normalized_treatment_counts(state)
    result.update(_treatment_container_fields(state))
    result["next_item"] = _next_actionable_item(result["items"])
    return result
def check_treatment_zero_leftover(skill_dir: str) -> dict:
    state = load_treatment_state(skill_dir)
    integrity_ok, integrity_reason = treatment_items_integrity(state)
    if not integrity_ok:
        logger.warning("[ZeroLeftover] 治疗项容器撕裂(失败关闭，禁止按空-items 放行): %s",
                       integrity_reason)
    items = list_field(state, "items")
    total = len(items)
    leftover, leftover_by_status, leftover_by_rule, actions = \
        _scan_leftover_items(items)
    if not integrity_ok:
        actions.add(integrity_reason)
    terminal_count = total - len(leftover)
    passed = integrity_ok and not leftover
    if not passed:
        logger.warning(
            "[ZeroLeftover] 门禁未通过: %d/%d 项未到达终态, 按状态=%s, 按规则=%s",
            len(leftover), total, leftover_by_status, leftover_by_rule,
        )
        for item in leftover[:10]:
            logger.warning(
                "[ZeroLeftover] 未处理项 #%d %s %s:%d %s",
                item["index"], item["rule_id"],
                os.path.basename(item["file_path"]),
                item["line"], item["message"][:80],
            )
    else:
        logger.info("[ZeroLeftover] 门禁通过: %d/%d 项均已达终态", terminal_count, total)
    return {
        "passed": passed,
        "total": total,
        "terminal_count": terminal_count,
        "leftover_count": len(leftover),
        "leftover_by_status": leftover_by_status,
        "leftover_by_rule": leftover_by_rule,
        "leftover_items": leftover[:20],
        "actions_required": sorted(actions),
        "state_integrity": "ok" if integrity_ok else "torn",
        "state_integrity_reason": integrity_reason,
    }
def _scan_leftover_items(items: list) -> tuple[list, dict, dict, set]:
    leftover = []
    leftover_by_status = {}
    leftover_by_rule = {}
    actions = set()
    for pos, item in enumerate(items):
        entry = _leftover_entry(item, pos)
        if entry is None:
            continue
        status = entry["status"]
        leftover.append(entry)
        leftover_by_status[status] = leftover_by_status.get(status, 0) + 1
        rule = entry["rule_id"] or "unknown"
        leftover_by_rule[rule] = leftover_by_rule.get(rule, 0) + 1
        actions.add(_LEFTOVER_ACTIONS.get(status, "未知状态，需人工检查"))
    return leftover, leftover_by_status, leftover_by_rule, actions
def _leftover_entry(item, fallback_index: int = NO_INDEX) -> dict | None:
    if not isinstance(item, dict):
        return {
            "index": fallback_index,
            "rule_id": "invalid_entry",
            "status": "invalid_entry",
            "severity": "",
            "file_path": "",
            "line": 0,
            "message": (f"治疗状态条目非 dict（{type(item).__name__}），"
                        f"需人工修复状态文件"),
        }
    status = item_status(item)
    if status in TREATMENT_TERMINAL_STATUSES:
        return None
    return {
        "index": item_index(item, fallback_index),
        "rule_id": _str_field(item, "rule_id"),
        "status": status,
        "severity": _str_field(item, "severity"),
        "file_path": _str_field(item, "file_path"),
        "line": norm_result_line(item),
        "message": item_result_reason(item, item_result(item)),
    }
def normalize_item_severity(value) -> str:
    _token, rank = severity_rank_of_text(value)
    if rank is None:
        return _DEFAULT_ITEM_SEVERITY
    return severity_literal_from_rank(rank)
def fp_item_identity(it: dict) -> str:
    if not isinstance(it, dict):
        logger.warning("[TreatmentState] FP 身份入参非映射(%s)，按无身份处理",
                       type(it).__name__)
        return ""
    locator = canonical_locator_key(it.get("locator"))
    if locator:
        return locator
    line = normalize_line_no(it.get("line"))
    if not line:
        line = normalize_line_no(it.get("line_number"))
    return "{}|{}|{}".format(
        norm_rule_id(it.get("rule_id")),
        finding_file_key(it.get("file_path") or it.get("file") or ""),
        line,
    )
def iter_unique_rule_observations(items: list) -> Iterator[tuple[str, dict]]:
    seen: set[tuple[str, str]] = set()
    for item in items:
        if not isinstance(item, dict):
            continue
        rid = norm_rule_id(item.get("rule_id"))
        key = (rid, fp_item_identity(item))
        if key in seen:
            continue
        seen.add(key)
        yield rid, item
def mark_item_fp_confirmed(state: dict, item: dict, fp_reason: str,
                           strategy: str = "", position: int = NO_INDEX,
                           extra: dict | None = None) -> bool:
    if not isinstance(item, dict):
        logger.warning("[BatchFP] 治疗项非映射(%s)，拒绝脏条目簿记",
                       type(item).__name__)
        return False
    index = plan_index(item.get("index"))
    if index is None:
        index = position
    items = state.get("items") if isinstance(state, dict) else None
    if not isinstance(items, list) or _target_item(items, index) is not item:
        logger.warning("[BatchFP] 治疗项索引身份冲突，跳过脏条目簿记: index=%r",
                       index)
        return False
    if plan_index(item.get("index")) is None:
        item["index"] = index
    existing = item.get("result")
    result = dict(existing) if isinstance(existing, dict) else {}
    if isinstance(extra, dict):
        result.update(extra)
    result["ai_fix_reason"] = fp_reason
    if strategy:
        result["batch_marked"] = True
        result["detection_strategy"] = strategy
    apply_item_status(state, item["index"], "fp_confirmed", result)
    return True
def locate_treatment_item(
        items: list, index: int) -> tuple[dict | None, tuple[str, str] | None]:
    if not isinstance(items, list):
        reason = (f"治疗项容器形态异常({type(items).__name__})，"
                  "无法枚举治疗项")
        return None, (reason, reason)
    idx = plan_index(index)
    if idx is not None and idx >= 0:
        item = _target_item(items, idx)
        if item is not None:
            return item, None
    if idx is not None and 0 <= idx < len(items):
        current = items[idx]
        if not isinstance(current, dict):
            reason = (f"治疗项形态异常({type(current).__name__})，"
                      f"无法安全读取 index={index}")
            return None, (reason, reason)
        return None, (
            "治疗项索引与状态列表位置错位且无法按index字段定位",
            f"治疗项 index={index} 与状态列表位置错位，无法安全定位目标项")
    reason = f"无效索引 {index}"
    return None, (reason, reason)
def state_item_entry(index: int, item: dict) -> dict:
    _dirty = not isinstance(item, dict)
    if _dirty:
        logger.warning("[TreatmentState] 治疗项非映射(%s)，按损坏条目登记: "
                       "index=%s", type(item).__name__, index)
        item = {}
    entry = {
        "index": index,
        "locator": item.get("locator", ""),
        "rule_id": item.get("rule_id", ""),
        "strategy": item.get("strategy", "manual_confirm"),
        "severity": item.get("severity", _DEFAULT_ITEM_SEVERITY),
        "fixer_type": item.get("fixer_type", ""),
        "auto_safe": item.get("auto_safe") is True,
        "file_path": item.get("file_path", ""),
        "line": item.get("line", 0),
        "message": item.get("sample_message", "") or item.get("message", ""),
        "code_snippet": item.get("code_snippet", ""),
        "sources": item.get("sources", []),
        "rule_applied": item.get("rule_applied", ""),
        "evidence_strength": item.get("evidence_strength", 0.0),
        "adjusted_confidence": item.get("adjusted_confidence", 0.0),
        "evidence_type": item.get("evidence_type", ""),
        "conclusion": item.get("conclusion", ""),
        "domain": item.get("domain", ""),
        "raw_finding": (item.get("raw_finding", {})
                        if isinstance(item.get("raw_finding"), dict) else {}),
        "finding_id": item.get("finding_id", ""),
        "notes": item.get("notes", ""),
        "status": "pending",
        "result": None,
    }
    if _dirty:
        entry["status"] = "error"
        entry["result"] = {
            "reason": "治疗项损坏（非映射），需人工修复治疗方案后重跑",
        }
    return entry
def _plan_items(plan_or_items) -> list:
    if isinstance(plan_or_items, dict):
        items = plan_or_items.get("items")
        if not isinstance(items, list) or not items:
            fallback = plan_or_items.get("treatment_items")
            if isinstance(fallback, list):
                return list(fallback)
        return list(items) if isinstance(items, list) else []
    return _coerce_items(plan_or_items, "init_treatment_state")
def init_treatment_state(skill_dir: str, plan_or_items,
                          fix_coverage: dict | None = None) -> dict:
    skill_dir = _skill_dir_arg(skill_dir)
    items = _plan_items(plan_or_items)
    total = len(items)
    state = _empty_state("pending" if total else "no_plan")
    state.update({
        "skill_dir": skill_dir,
        "total": total,
        "fix_coverage": fix_coverage if isinstance(fix_coverage, dict) else {},
        "items": [state_item_entry(i, item)
                  for i, item in enumerate(items)],
    })
    save_treatment_state(skill_dir, state)
    logger.info("[TreatmentState] 初始化治疗状态: %d 项", total)
    return state
def reset_treatment_artifacts(skill_dir: str, plan_or_items,
                               fix_coverage: dict | None = None) -> dict:
    save_treatment_fix_plans(skill_dir, [])
    return init_treatment_state(skill_dir, plan_or_items, fix_coverage)
MAX_EXPERIENCES_PER_RULE = 50
DEFAULT_FILE_PATTERN = "*.py"
DEFAULT_FIX_CONTEXT_LABEL = "修复已生效"
EXPERIENCE_FILE = "_fixer_experiences.json"
FALLBACK_RULE_ID = "AI-FIX"
_SNIPPET_MAX_LINES = 10
_SNIPPET_MAX_CHARS = 500
_DEFAULT_SIMILARITY_THRESHOLD = 0.3
_MIN_BRIDGE_SNIPPET_LEN = 8
_MAX_REASONABLE_COUNT = 2 ** 53
_EXPERIENCE_DEFAULT_SUCCESS = 1
_EXPERIENCE_DEFAULT_FAILURE = 0
def normalize_rule_key(rule_id) -> str:
    if not isinstance(rule_id, str):
        return FALLBACK_RULE_ID
    return rule_id.strip() or FALLBACK_RULE_ID
def _clamp_count(n: int, default: int) -> int:
    if n < 0:
        return 0
    return n if n <= _MAX_REASONABLE_COUNT else default
def _coerce_count(value, default: int) -> int:
    if isinstance(value, bool):
        return default
    if isinstance(value, int):
        return _clamp_count(value, default)
    if isinstance(value, float):
        if math.isfinite(value):
            return _clamp_count(int(value), default)
        return default
    if isinstance(value, str):
        try:
            n = int(value.strip())
        except ValueError as _e:
            log_swallowed(__name__, _e, context='_coerce_count:ValueError')
            return default
        return _clamp_count(n, default)
    return default
def _coerce_threshold(
        value, default: float = _DEFAULT_SIMILARITY_THRESHOLD) -> float:
    if isinstance(value, bool):
        return 1.0 if value else 0.0
    if isinstance(value, str):
        try:
            value = float(value.strip())
        except ValueError as _e:
            log_swallowed(__name__, _e, context='_coerce_threshold:ValueError')
            return default
    number = finite_float_or_none(value)
    return default if number is None else min(1.0, max(0.0, number))
def _first_divergence(left: str, right: str) -> int:
    return next((i for i, (ca, cb) in enumerate(zip(left, right, strict=False))
                 if ca != cb), min(len(left), len(right)))
class _SnippetWindow:
    __slots__ = ("bounds", "max_chars", "max_lines", "new_lines", "old_lines")
    def __init__(self, old_lines: list[str], new_lines: list[str],
                 ops: list, max_lines: int, max_chars: int):
        self.old_lines = old_lines
        self.new_lines = new_lines
        self.bounds = self._bounds(ops)
        self.max_lines = max_lines
        self.max_chars = max_chars
    @staticmethod
    def _bounds(ops: list) -> tuple[int, int, int, int]:
        return (min(op[1] for op in ops), max(op[2] for op in ops),
                min(op[3] for op in ops), max(op[4] for op in ops))
    def _window_start(self, start: int, span: int) -> int:
        if span >= self.max_lines:
            return start
        return max(0, start - (self.max_lines - span))
    def _shift(self, lines: list[str], start: int,
               end: int) -> tuple[str, int]:
        s = self._window_start(start, end - start)
        return "\n".join(lines[s:s + self.max_lines]), s
    def select(self) -> tuple[str, str, int, int]:
        start_old, end_old, start_new, end_new = self.bounds
        span = max(end_old - start_old, end_new - start_new)
        s = self._window_start(start_old, span)
        old_snip = "\n".join(self.old_lines[s:s + self.max_lines])
        new_snip = "\n".join(self.new_lines[s:s + self.max_lines])
        if old_snip != new_snip:
            return old_snip, new_snip, s, s
        old_snip, s_old = self._shift(self.old_lines, start_old, end_old)
        new_snip, s_new = self._shift(self.new_lines, start_new, end_new)
        if old_snip != new_snip:
            return old_snip, new_snip, s_old, s_new
        old_core = self.old_lines[start_old:end_old]
        new_core = self.new_lines[start_new:end_new]
        old_snip = "\n".join(
            (old_core + self.old_lines[end_old:end_old + self.max_lines])
            [:self.max_lines])
        new_snip = "\n".join(
            (new_core + self.new_lines[end_new:end_new + self.max_lines])
            [:self.max_lines])
        return old_snip, new_snip, start_old, start_new
    def clip(self, old_snip: str, new_snip: str,
             s_old: int, s_new: int) -> tuple[str, str]:
        start_old, _, start_new, _ = self.bounds
        max_chars = self.max_chars
        old_snip, s_old = self._advance_to_diff(
            self.old_lines, s_old, start_old, old_snip)
        new_snip, s_new = self._advance_to_diff(
            self.new_lines, s_new, start_new, new_snip)
        if old_snip[:max_chars] != new_snip[:max_chars]:
            return old_snip[:max_chars], new_snip[:max_chars]
        diverge = _first_divergence(old_snip, new_snip)
        return (old_snip[diverge:diverge + max_chars],
                new_snip[diverge:diverge + max_chars])
    def _advance_to_diff(self, lines: list[str], s: int, diff_start: int,
                         snippet: str) -> tuple[str, int]:
        if diff_start > s and len("\n".join(
                lines[s:diff_start])) >= self.max_chars:
            s = diff_start
            snippet = "\n".join(lines[s:s + self.max_lines])
        return snippet, s
    def core_anchor(self) -> tuple[str, str]:
        start_old, end_old, start_new, end_new = self.bounds
        old_full = "\n".join(self.old_lines[start_old:end_old])
        new_full = "\n".join(self.new_lines[start_new:end_new])
        diverge = _first_divergence(old_full, new_full)
        return (old_full[diverge:diverge + self.max_chars],
                new_full[diverge:diverge + self.max_chars])
class FixerExperience:
    __slots__ = (
        "description",
        "failure_count",
        "file_pattern",
        "fixer_source",
        "new_snippet",
        "old_snippet",
        "rule_id",
        "success_count",
        "timestamp",
    )
    def __init__(self, rule_id: str, fixer_source: str = "",
                 file_pattern: str = DEFAULT_FILE_PATTERN, old_snippet: str = "",
                 new_snippet: str = "", description: str = "",
                 timestamp: str = "",
                 success_count: int = _EXPERIENCE_DEFAULT_SUCCESS,
                 failure_count: int = _EXPERIENCE_DEFAULT_FAILURE):
        self.rule_id = rule_id
        self.fixer_source = str_or(fixer_source)
        self.file_pattern = str_or(file_pattern, DEFAULT_FILE_PATTERN)
        self.old_snippet = str_or(old_snippet)
        self.new_snippet = str_or(new_snippet)
        self.description = str_or(description)
        self.timestamp = str_or(timestamp) or datetime.datetime.now().isoformat()
        self.success_count = _coerce_count(
            success_count, _EXPERIENCE_DEFAULT_SUCCESS)
        self.failure_count = _coerce_count(
            failure_count, _EXPERIENCE_DEFAULT_FAILURE)
    def to_dict(self) -> dict:
        return {k: getattr(self, k) for k in self.__slots__}
    @classmethod
    def from_dict(cls, d: dict) -> FixerExperience:
        fields = d if isinstance(d, dict) else {}
        return cls(rule_id=normalize_rule_key(fields.get("rule_id")),
                   **{k: fields[k] for k in cls.__slots__
                      if k != "rule_id" and k in fields})
    def confidence(self) -> float:
        total = self.success_count + self.failure_count
        return self.success_count / total if total else 0.0
    def similarity(self, old_code: str) -> float:
        old_code = str_or(old_code)
        if not self.old_snippet or not old_code:
            return 0.0
        tokens_a = set(re.findall(r"\w+", self.old_snippet))
        tokens_b = set(re.findall(r"\w+", old_code))
        if not tokens_a or not tokens_b:
            return 0.0
        return len(tokens_a & tokens_b) / len(tokens_a | tokens_b)
class ExperienceStore:
    def __init__(self, skill_dir: str):
        self.skill_dir = Path(_skill_dir_arg(skill_dir))
        self.file_path = Path(fixer_experiences_path(str(self.skill_dir)))
        self._cache: dict[str, list[dict]] | None = None
    _TEXT_FIELD_DEFAULTS: ClassVar[dict[str, str]] = {
        "fixer_source": "", "file_pattern": DEFAULT_FILE_PATTERN,
        "old_snippet": "",
        "new_snippet": "", "description": "", "timestamp": "",
    }
    @staticmethod
    def _normalize_entry(e: dict) -> dict:
        e["success_count"] = _coerce_count(
            e.get("success_count"), _EXPERIENCE_DEFAULT_SUCCESS)
        e["failure_count"] = _coerce_count(
            e.get("failure_count"), _EXPERIENCE_DEFAULT_FAILURE)
        for field_name, default in ExperienceStore._TEXT_FIELD_DEFAULTS.items():
            e[field_name] = str_or(e.get(field_name), default)
        return e
    @staticmethod
    def _normalize_loaded(raw: dict) -> dict[str, list[dict]]:
        loaded: dict[str, list[dict]] = {}
        for k, v in raw.items():
            if not isinstance(v, list):
                continue
            key = normalize_rule_key(k)
            for e in v:
                if not isinstance(e, dict):
                    continue
                entry = ExperienceStore._normalize_entry(e)
                entry["rule_id"] = key
                loaded.setdefault(key, []).append(entry)
        return loaded
    def _load(self) -> dict[str, list[dict]]:
        if self._cache is not None:
            return self._cache
        try:
            raw = _read_mapping_store(str(self.file_path), "FixerLearning")
        except OSError as e:
            logger.warning("[FixerLearning] 经验文件读取失败（保留原文件）: %s", e)
            raise
        self._cache = self._normalize_loaded(raw)
        return self._cache
    def _save(self) -> bool:
        if self._cache is None:
            return False
        try:
            write_json_artifact(str(self.file_path), self._cache, indent=2)
            logger.info("[FixerLearning] 经验保存: %d 个规则, %d 条经验",
                        len(self._cache),
                        sum(len(v) for v in self._cache.values()))
        except (OSError, ValueError, TypeError, RecursionError) as e:
            logger.warning("[FixerLearning] 经验文件保存失败: %s", e)
            return False
        return True
    def add(self, experience: FixerExperience) -> bool:
        data = self._load()
        rule_id = normalize_rule_key(experience.rule_id)
        entry = experience.to_dict()
        entry["rule_id"] = rule_id
        if not entry["old_snippet"] and not entry["new_snippet"]:
            logger.debug("[FixerLearning] 拒绝空模式经验（无判别力）: %s",
                        rule_id)
            return False
        had_rule = rule_id in data
        bucket = data.setdefault(rule_id, [])
        previous_bucket = copy.deepcopy(bucket)
        merged = self._merge_duplicate(bucket, entry)
        if merged is not None:
            saved = self._save()
            if saved:
                logger.debug("[FixerLearning] 经验更新: %s (success=%d)",
                             rule_id, merged.success_count)
        else:
            bucket.append(entry)
            self._trim_bucket(bucket)
            saved = self._save()
            if saved:
                logger.info("[FixerLearning] 新经验添加: %s (%s)",
                            rule_id, experience.description[:50])
        if not saved:
            if had_rule:
                data[rule_id] = previous_bucket
            else:
                data.pop(rule_id, None)
        return saved
    def _merge_duplicate(
            self, bucket: list, entry: dict) -> FixerExperience | None:
        for existing in bucket:
            exp = FixerExperience.from_dict(existing)
            if (exp.old_snippet != entry["old_snippet"]
                    or exp.new_snippet != entry["new_snippet"]):
                continue
            exp.success_count = min(
                _MAX_REASONABLE_COUNT,
                exp.success_count + entry["success_count"])
            exp.failure_count = min(
                _MAX_REASONABLE_COUNT,
                exp.failure_count + entry["failure_count"])
            exp.timestamp = entry["timestamp"]
            existing.update(exp.to_dict())
            return exp
        return None
    @staticmethod
    def _trim_bucket(bucket: list) -> None:
        if len(bucket) <= MAX_EXPERIENCES_PER_RULE:
            return
        bucket.sort(
            key=lambda x: (FixerExperience.from_dict(x).confidence(),
                           x.get("success_count", 0)),
            reverse=True)
        del bucket[MAX_EXPERIENCES_PER_RULE:]
    def record_failure(self, rule_id: str, old_snippet: str,
                       new_snippet: str | None = None) -> None:
        data = self._load()
        rule_id = normalize_rule_key(rule_id)
        old_snippet = str_or(old_snippet)
        if rule_id not in data:
            return
        if new_snippet is not None:
            new_snippet = str_or(new_snippet)
            self._bump_failure(
                data[rule_id],
                lambda e: (e.get("old_snippet") == old_snippet
                           and e.get("new_snippet") == new_snippet))
            return
        if not old_snippet:
            return
        self._bump_failure(
            data[rule_id], lambda e: e.get("old_snippet") == old_snippet)
    def _bump_failure(self, entries: list, match) -> None:
        for existing in entries:
            if match(existing):
                existing["failure_count"] = existing.get("failure_count", 0) + 1
                self._save()
                return
    def get_by_rule(self, rule_id: str) -> list[FixerExperience]:
        data = self._load()
        key = normalize_rule_key(rule_id)
        return [FixerExperience.from_dict(d) for d in data.get(key, [])]
    def get_similar(self, rule_id: str, old_code: str,
                    threshold: float | None = None
                    ) -> list[FixerExperience]:
        threshold = _coerce_threshold(threshold)
        experiences = self.get_by_rule(rule_id)
        scored = [(exp, exp.similarity(old_code)) for exp in experiences]
        scored = [(exp, score) for exp, score in scored if score >= threshold]
        scored.sort(key=lambda x: x[1], reverse=True)
        return [exp for exp, _ in scored]
    def get_stats(self) -> dict:
        data = self._load()
        high_confidence = sum(
            1 for v in data.values() for e in v
            if FixerExperience.from_dict(e).confidence() >= 0.8
        )
        return {
            "total_experiences": sum(len(v) for v in data.values()),
            "total_rules": len(data),
            "high_confidence": high_confidence,
            "file_path": str(self.file_path),
        }
    def clear(self) -> None:
        self._cache = {}
        self._save()
class LearningHook:
    def __init__(self, skill_dir: str):
        self.store = ExperienceStore(skill_dir)
    def on_fix_success(self, rule_id: str, fixer_source: str,
                       old_code: str, new_code: str,
                       description: str, filepath: str = "") -> bool:
        old_code = str_or(old_code)
        new_code = str_or(new_code)
        if not old_code or not new_code:
            return False
        old_snippet, new_snippet = self._extract_diff_snippet(old_code, new_code)
        if old_snippet == new_snippet:
            return False
        filepath = str_or(filepath)
        file_pattern = (f"*{Path(filepath).suffix or '.py'}"
                        if filepath else DEFAULT_FILE_PATTERN)
        experience = FixerExperience(
            rule_id=rule_id,
            fixer_source=fixer_source,
            file_pattern=file_pattern,
            old_snippet=old_snippet,
            new_snippet=new_snippet,
            description=str_or(description)[:200],
        )
        return self.store.add(experience)
    def on_fix_failure(self, rule_id: str, old_code: str, new_code: str = "") -> None:
        old_code = str_or(old_code)
        new_code = str_or(new_code)
        if not old_code:
            return
        if new_code:
            old_snippet, new_snippet = self._extract_diff_snippet(old_code, new_code)
            if old_snippet == new_snippet:
                return
            self.store.record_failure(rule_id, old_snippet, new_snippet)
        else:
            head_snippet = self._extract_snippet(old_code)
            old_snippet = self._locate_recorded_snippet(
                rule_id, head_snippet, old_code)
            self.store.record_failure(rule_id, old_snippet)
    def _extract_snippet(self, code: str, max_lines: int = _SNIPPET_MAX_LINES,
                         max_chars: int = _SNIPPET_MAX_CHARS) -> str:
        code = str_or(code)
        if not code:
            return ""
        snippet = "\n".join(code.split("\n")[:max_lines])
        return snippet[:max_chars]
    def _locate_recorded_snippet(self, rule_id: str, head_snippet: str,
                                 old_code: str) -> str:
        best = ""
        for exp in self.store.get_by_rule(rule_id):
            stored = exp.old_snippet
            if (len(stored) >= _MIN_BRIDGE_SNIPPET_LEN
                    and stored in old_code
                    and len(stored) > len(best)):
                best = stored
        return best or head_snippet
    @staticmethod
    def _extract_diff_snippet(old_code: str, new_code: str,
                              max_lines: int = _SNIPPET_MAX_LINES,
                              max_chars: int = _SNIPPET_MAX_CHARS
                              ) -> tuple[str, str]:
        old_code = str_or(old_code)
        new_code = str_or(new_code)
        if not old_code or not new_code:
            return "", ""
        old_lines = old_code.split("\n")
        new_lines = new_code.split("\n")
        sm = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
        ops = [op for op in sm.get_opcodes() if op[0] != "equal"]
        if not ops:
            return "", ""
        window = _SnippetWindow(old_lines, new_lines, ops,
                                max_lines, max_chars)
        old_snip, new_snip, s_old, s_new = window.select()
        if len(old_snip) > max_chars or len(new_snip) > max_chars:
            old_snip, new_snip = window.clip(old_snip, new_snip, s_old, s_new)
        if old_snip == new_snip:
            old_snip, new_snip = window.core_anchor()
        return old_snip, new_snip
def query_fix_experience(skill_dir: str, rule_id: str, code_snippet: str = "",
                         threshold: float | None = None
                         ) -> list[dict]:
    store = ExperienceStore(skill_dir)
    code_snippet = str_or(code_snippet)
    if code_snippet:
        experiences = store.get_similar(rule_id, code_snippet, threshold)
    else:
        experiences = store.get_by_rule(rule_id)
    return [{**exp.to_dict(), "confidence": round(exp.confidence(), 4)}
            for exp in experiences]
@dataclass
class FixTarget:
    state: dict | None
    item: dict | None
    file_path: str
    original_source: str
    original_bytes: bytes
    source_encoding: str
    index: int
    description: str
    error: str = ""
@dataclass
class FixRecord:
    skill_dir: str
    index: int
    item: dict
    file_path: str
    description: str
    status: str
    targeted_regression: dict
    backup_path: str
    side_effects: list
    original_source: str
    fixed_source: str
    success: bool
    plan_payload: dict
    context_label: str = DEFAULT_FIX_CONTEXT_LABEL
    write_artifact: bool = False
    extras: dict = field(default_factory=dict)
def _manual_fix_description(description) -> str:
    return str_or(description) or _DEFAULT_MANUAL_FIX_DESCRIPTION
def _fix_target_error(index, reason: str, audit_reason: str = "",
                      description: str = "") -> FixTarget:
    safe_write_audit("ai_fix_error", index=index, reason=audit_reason or reason)
    return FixTarget(None, None, "", "", b"", "utf-8", -1, description, reason)
def warm_shared_ast_cache(skill_dir: str) -> None:
    get_warmed_cache(_skill_dir_arg(skill_dir))
def load_fix_target(skill_dir: str, index: int,
                    description: str = "") -> FixTarget:
    skill_dir = _skill_dir_arg(skill_dir)
    warm_shared_ast_cache(skill_dir)
    if not isinstance(description, str):
        description = "" if description is None else str(description)
    idx = plan_index(index)
    if idx is None or idx < 0:
        return _fix_target_error(index, f"无效索引 {index!r}",
                                 description=description)
    state = load_treatment_state(skill_dir)
    if not isinstance(state, dict):
        return _fix_target_error(
            index,
            f"治疗状态文件形态异常({type(state).__name__})，无法定位治疗项",
            description=description)
    corrupt_reason = _corrupt_state_reason(state)
    if corrupt_reason:
        return _fix_target_error(index, corrupt_reason,
                                 description=description)
    _items = state.get("items")
    if not isinstance(_items, list):
        return _fix_target_error(
            index,
            f"治疗状态 items 形态异常({type(_items).__name__})，无法定位治疗项",
            description=description)
    item, _loc_error = locate_treatment_item(_items, idx)
    if item is None:
        _audit_reason, _return_reason = _loc_error
        return _fix_target_error(
            index, _return_reason, _audit_reason, description=description)
    file_path = item.get("file_path", "")
    if not isinstance(file_path, str):
        return _fix_target_error(
            index,
            f"治疗项 file_path 形态异常"
            f"({type(file_path).__name__})，无法定位目标文件",
            description=description)
    file_path = resolve_skill_relative_path(file_path, skill_dir)
    if file_path and not os.path.isabs(file_path):
        return _fix_target_error(
            index,
            f"目标路径无法按技能根解析，禁止按进程 cwd 定位写盘目标: "
            f"{file_path}", description=description)
    path_safe, path_reason = check_path_traversal(skill_dir, file_path)
    if not path_safe:
        return _fix_target_error(
            index, f"AI 修复目标越出技能根，拒绝读取与写盘: {path_reason}",
            description=description)
    if not os.path.isfile(file_path):
        return _fix_target_error(
            index, f"文件不存在: {file_path}", description=description)
    try:
        with open(file_path, "rb") as f:
            original_bytes = f.read()
        original_source, source_encoding = decode_source_strict(original_bytes)
    except (OSError, SourceReadError) as e:
        logger.debug("[AIManualFix] 目标文件读取失败(返回error): %s", e)
        return _fix_target_error(
            index, f"读取文件失败: {e}", description=description)
    READ_BEFORE_WRITE_GUARD.mark_read(file_path)
    return FixTarget(state, item, file_path, original_source, original_bytes,
                     source_encoding, idx, description)
def rule_id_of(item: dict) -> str:
    if not isinstance(item, dict):
        return FALLBACK_RULE_ID
    return _str_field(item, "rule_id") or FALLBACK_RULE_ID
def _build_item_result(record: FixRecord, fix_result_path: str = "") -> dict:
    result = (dict(record.extras) if isinstance(record.extras, dict) else {})
    result.update({
        "locator": _str_field(record.item, "locator"),
        "rule_id": _str_field(record.item, "rule_id"),
        "file_path": record.file_path,
        "line": norm_result_line(record.item),
        "status": record.status,
        "description": _manual_fix_description(record.description),
        "targeted_regression": record.targeted_regression,
        "backup": record.backup_path,
        "side_effects": record.side_effects,
    })
    if fix_result_path:
        result["fix_result_path"] = fix_result_path
    return result
def _persist_transition(skill_dir: str, state: dict, index: int, status: str,
                        result: dict, *,
                        context_label: str = DEFAULT_FIX_CONTEXT_LABEL,
                        ) -> tuple[str, bool]:
    normalized_status = _known_item_status(status)
    items = state.get("items") if isinstance(state, dict) else None
    target = _target_item(items, index) if isinstance(items, list) else None
    if not normalized_status or target is None:
        warning = (f"治疗状态迁移失败({context_label}): "
                   f"index={index!r}, status={status!r}，目标或状态无效")
        logger.warning("[AIManualFix] %s", warning)
        return warning, False
    transition_applied = False
    try:
        apply_item_status(state, index, status, result)
        if (target.get("status") != normalized_status
                or target.get("result") is not result):
            warning = (f"治疗状态迁移未生效({context_label}): "
                       f"index={index!r}, status={status!r}")
            logger.warning("[AIManualFix] %s", warning)
            return warning, False
        transition_applied = True
        save_treatment_state(skill_dir, state)
    except Exception as _ss_err:
        warning = f"治疗状态落盘失败({context_label}): {_ss_err}"
        logger.warning("[AIManualFix] %s", warning, exc_info=True)
        return warning, transition_applied
    return "", True
def _sync_plan_status_best_effort(skill_dir: str, index: int, status: str,
                                  payload: dict) -> None:
    try:
        mark_fix_plan_status(skill_dir, index, status, payload)
    except Exception:
        logger.warning(
            "[AIManualFix] 修复方案清单状态回写失败（不影响修复结果）: status=%s",
            status, exc_info=True)
def record_fix_experience(skill_dir: str, item: dict, original_source: str,
                          fixed_source: str, description: str, *,
                          success: bool, file_path: str = "") -> None:
    try:
        hook = LearningHook(skill_dir)
        _rule_id = rule_id_of(item)
        if success:
            hook.on_fix_success(
                rule_id=_rule_id,
                fixer_source="ai_manual_fix",
                old_code=original_source,
                new_code=fixed_source,
                description=_manual_fix_description(description),
                filepath=file_path,
            )
        else:
            hook.on_fix_failure(_rule_id, original_source, fixed_source or "")
    except Exception as e:
        logger.warning("[AIManualFix] 修复经验记录失败(不影响主流程): %s", e)
def _write_fix_result_artifact(record: FixRecord) -> str:
    try:
        artifact = {
            "rule_id": rule_id_of(record.item),
            "file_path": record.file_path,
            "original_source": record.original_source,
            "fixed_source": record.fixed_source,
            "fixer_source": "ai_manual_fix",
            "description": _manual_fix_description(record.description)[:200],
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "index": record.index,
        }
        _temp_dir = get_temp_dir(_skill_dir_arg(record.skill_dir))
        name = f"ai_fix_{record.index}_{time.time_ns()}.fix_result.json"
        path = os.path.join(_temp_dir, name)
        write_json_artifact(path, artifact, indent=2)
        return path
    except Exception as e:
        logger.warning("[AIManualFix] 修复产物打点失败(不影响主流程): %s", e)
        return ""
def record_fix_result(skill_dir: str, state: dict,
                      record: FixRecord) -> tuple[dict, str, str]:
    fix_result_path = (_write_fix_result_artifact(record)
                       if record.write_artifact else "")
    item_result = _build_item_result(record, fix_result_path)
    warning, transition_applied = _persist_transition(
        skill_dir, state, record.index, record.status, item_result,
        context_label=record.context_label)
    if not transition_applied:
        return item_result, warning, fix_result_path
    _sync_plan_status_best_effort(
        skill_dir, record.index, record.status, record.plan_payload)
    record_fix_experience(
        skill_dir, record.item, record.original_source, record.fixed_source,
        record.description, success=record.success, file_path=record.file_path)
    return item_result, warning, fix_result_path

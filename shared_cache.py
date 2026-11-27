from __future__ import annotations

import ast
import errno
import functools
import gc
import io
import json
import logging
import os
import stat
import threading
import time
import tracemalloc
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_shared_ast_views import (
    clear_lexical_scope_memo,
    clear_shared_walk,
    memoized_module_walk_scope,
    registered_cache_releases,
    release_tree_nodes_index,
)
from jwsgj.diag_shared_source_core import (
    SOURCE_READ_PARSE_ERRORS,
    aligned_source_lines,
    begin_snapshot_lines_window,
    clear_shared_parse_cache,
    clear_source_parse_cache,
    end_snapshot_lines_window,
    read_source,
    read_source_with_fingerprint,
    set_shared_snapshot_reader,
    shared_cache_bridge_scope,
    source_digest,
)
from jwsgj.diag_types_defs import ConcurrentExecutionError
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    canonical_json_artifact_dir,
    normalize_project_root,
)
from jwsgj.runtime_scope import (
    collect_gate_scan_files,
    collect_py_files_default,
    is_scan_scope_path,
    iter_scan_py_files,
    normalize_skill_dir,
)
from jwsgj.shared_cache_store import (
    AstBlobStore,
    CacheNotWarmedError,
    PyFileInventory,
    SourceAstStore,
    SyntaxVerdictCache,
    WarmupResidency,
    clean_pycache_before_scan,
    fs_key,
    load_call_graph_share,
    require_skill_root,
)

logger = logging.getLogger(__name__)
_UNSCOPED_SKILL_DIR = ""
_WARMED_CACHES: dict[str, SharedCache] = {}
_WARMED_CACHES_LOCK = threading.RLock()
_PERMANENT_GENERATION_LOCK = threading.Lock()
_PERMANENT_GENERATION_DEPTH = 0
def permanent_generation_adopt() -> bool:
    global _PERMANENT_GENERATION_DEPTH
    freeze = getattr(gc, "freeze", None)
    if freeze is None:
        logger.debug(
            "[Cache] 运行时无 gc.freeze（非 CPython GC），永久代冻结降级跳过")
        return False
    with _PERMANENT_GENERATION_LOCK:
        freeze()
        _PERMANENT_GENERATION_DEPTH += 1
    return True
def permanent_generation_release() -> bool:
    global _PERMANENT_GENERATION_DEPTH
    unfreeze = getattr(gc, "unfreeze", None)
    if unfreeze is None:
        logger.debug(
            "[Cache] 运行时无 gc.unfreeze，永久代解冻降级跳过")
        return False
    with _PERMANENT_GENERATION_LOCK:
        if _PERMANENT_GENERATION_DEPTH == 0:
            logger.debug("[Cache] 永久代释放无配对 adopt，跳过")
            return False
        if _PERMANENT_GENERATION_DEPTH == 1:
            unfreeze()
        _PERMANENT_GENERATION_DEPTH -= 1
    return True
class PipelineSlotStore:
    STATE_READY = "ready"
    CALL_GRAPH_HEALTHY = "healthy"
    CALL_GRAPH_DEGRADED = "degraded"
    CALL_GRAPH_MISSING = "missing"
    _CALL_GRAPH_HEALTH_VALUES = frozenset({
        CALL_GRAPH_HEALTHY, CALL_GRAPH_DEGRADED, CALL_GRAPH_MISSING})
    def __init__(self) -> None:
        self._mem_cache: dict[str, object] = {}
        self._states: dict[str, str] = {}
    def slot_get(self, name: str, who: str = "[Slot] slot_get"):
        try:
            return self._mem_cache.get(name)
        except Exception as e:  # noqa: BLE001
            logger.warning("%s: %s", who, e)
            return None
    def slot_set(self, name: str, value) -> None:
        self._mem_cache[name] = value
        self._states[name] = self.STATE_READY
    def _slot_drop(self, name: str) -> None:
        self._mem_cache.pop(name, None)
        self._states.pop(name, None)
    def _slot_has(self, name: str, who: str) -> bool:
        try:
            return self._states.get(name) == self.STATE_READY
        except Exception as e:  # noqa: BLE001
            logger.warning("%s: %s", who, e)
            return False
    def get_call_graph(self):
        return self.slot_get("call_graph", "get_call_graph")
    def set_call_graph(self, graph) -> None:
        self.slot_set("call_graph", graph)
    def has_call_graph(self) -> bool:
        return self._slot_has("call_graph", "has_call_graph")
    def get_blindspot_report(self):
        return self.slot_get("blindspot_report", "get_blindspot_report")
    def set_blindspot_report(self, report) -> None:
        self.slot_set("blindspot_report", report)
    def set_call_graph_summary(self, summary: dict) -> None:
        self.slot_set("call_graph_summary", summary)
    def get_call_graph_summary(self):
        return self.slot_get("call_graph_summary", "get_call_graph_summary")
    def has_call_graph_summary(self) -> bool:
        return self._slot_has("call_graph_summary", "has_call_graph_summary")
    @classmethod
    def _norm_call_graph_health(cls, value) -> str:
        if isinstance(value, str) and value in cls._CALL_GRAPH_HEALTH_VALUES:
            return value
        return cls.CALL_GRAPH_MISSING
    def set_call_graph_health(self, health: str, detail: str = "") -> None:
        self._states["call_graph_health"] = self._norm_call_graph_health(health)
        if detail:
            self._states["call_graph_health_detail"] = detail
        else:
            self._states.pop("call_graph_health_detail", None)
    def get_call_graph_health(self) -> str:
        try:
            return self._norm_call_graph_health(
                self._states.get(
                    "call_graph_health", self.CALL_GRAPH_MISSING))
        except Exception as e:  # noqa: BLE001
            logger.warning("get_call_graph_health: %s", e)
            return self.CALL_GRAPH_MISSING
    def load_call_graph_share(self, skill_dir: str):
        shared = load_call_graph_share(skill_dir)
        if shared is None:
            self._slot_drop("call_graph")
            self._slot_drop("call_graph_summary")
            self.set_call_graph_health(self.CALL_GRAPH_MISSING)
            return None
        summary, func_count = shared
        self.set_call_graph_summary(summary)
        self.set_call_graph_health(
            self.CALL_GRAPH_HEALTHY if func_count > 0
            else self.CALL_GRAPH_DEGRADED,
            "函数数为 0（空图）" if func_count <= 0 else "",
        )
        return summary
    def get_exception_result(self):
        return self.slot_get("exception_result", "get_exception_result")
    def set_exception_result(self, result) -> None:
        self.slot_set("exception_result", result)
    def has_exception_result(self) -> bool:
        return self._slot_has("exception_result", "has_exception_result")
    def clear(self) -> None:
        self._mem_cache.clear()
        self._states.clear()
_MEM_BUS_LOCK = threading.Lock()
_MEM_BUS: dict = {}
def _mem_bus_key(skill_dir: str) -> str:
    try:
        return normalize_skill_dir(skill_dir) if skill_dir else ""
    except Exception as _swallow_e:  # noqa: BLE001 — 归一失败原样键隔离（软失败域）
        log_swallowed(__name__, _swallow_e,
                      context=f'_mem_bus_key:{type(_swallow_e).__name__}')
        return skill_dir
def _mem_bus_slot(slot: str, skill_dir: str) -> tuple[str, str]:
    return _mem_bus_key(skill_dir), str(slot)
def mem_bus_put(slot: str, payload: Any, skill_dir: str = _UNSCOPED_SKILL_DIR) -> None:
    with _MEM_BUS_LOCK:
        _MEM_BUS[_mem_bus_slot(slot, skill_dir)] = payload
def mem_bus_take(slot: str, skill_dir: str = _UNSCOPED_SKILL_DIR) -> Any:
    with _MEM_BUS_LOCK:
        return _MEM_BUS.pop(_mem_bus_slot(slot, skill_dir), None)
def mem_bus_peek(slot: str, skill_dir: str = _UNSCOPED_SKILL_DIR) -> Any:
    with _MEM_BUS_LOCK:
        return _MEM_BUS.get(_mem_bus_slot(slot, skill_dir))
_HANDOFF_DISK_STATE = {"enabled": True}
def set_handoff_persistence(enabled: bool) -> bool:
    with _MEM_BUS_LOCK:
        prev = bool(_HANDOFF_DISK_STATE["enabled"])
        _HANDOFF_DISK_STATE["enabled"] = bool(enabled)
    return prev
def handoff_persistence_enabled() -> bool:
    with _MEM_BUS_LOCK:
        return bool(_HANDOFF_DISK_STATE["enabled"])
def mem_bus_clear(skill_dir: str = _UNSCOPED_SKILL_DIR, *, all_skills: bool = False) -> int:
    with _MEM_BUS_LOCK:
        if all_skills:
            _cleared = len(_MEM_BUS)
            _MEM_BUS.clear()
            return _cleared
        _sd = _mem_bus_key(skill_dir)
        keys_to_remove = [k for k in _MEM_BUS if k[0] == _sd]
        for k in keys_to_remove:
            del _MEM_BUS[k]
        return len(keys_to_remove)
def release_shared_registries() -> None:
    _clear_registry("release_tree_nodes_index", release_tree_nodes_index)
    _clear_registry("clear_shared_walk", clear_shared_walk)
    _clear_registry("clear_lexical_scope_memo", clear_lexical_scope_memo)
    _clear_registry("clear_shared_parse_cache", clear_shared_parse_cache)
    n_sp = _clear_registry(
        "clear_source_parse_cache", clear_source_parse_cache)
    if n_sp:
        logger.info("[Cache] release 连带清空 sha1 桥接解析缓存 %d 条", n_sp)
    n_identity = _clear_dict_store(
        "代码身份文件缓存", _FILE_CACHE, _FILE_CACHE_LOCK)
    n_owner = _clear_dict_store(
        "代码身份缓存归属", _SHARED_CACHE_FOR_FILE,
        _SHARED_CACHE_FOR_FILE_LOCK)
    if n_identity or n_owner:
        logger.info(
            "[Cache] release 连带清空代码身份缓存 %d 条（归属 %d 条）",
            n_identity, n_owner)
def _clear_registry(label: str, clear: Callable[[], object]) -> object:
    try:
        return clear()
    except Exception as e:  # pragma: no cover  # noqa: BLE001
        logger.debug("[Cache] %s 失败(降级): %s", label, e)
        return None
def _clear_dict_store(label: str, store: dict, lock) -> int:
    try:
        with lock:
            count = len(store)
            store.clear()
        return count
    except Exception as e:  # noqa: BLE001 — 释放软失败不阻断主链
        logger.debug("[Cache] %s 清空失败(降级): %s", label, e)
        return 0
class SharedCache:
    def __init__(self, skill_dir: str, output_dir: str | None = None,
                 pin_scope: Callable[[str], bool] | None = None):
        self.skill_dir = require_skill_root(skill_dir)
        self.output_dir = canonical_json_artifact_dir(
            self.skill_dir, output_dir)
        self._lock = threading.RLock()
        self._cond = threading.Condition(self._lock)
        self.slots = PipelineSlotStore()
        self.store = SourceAstStore(self.skill_dir, self._lock, pin_scope)
        self._blob_store = AstBlobStore(self.skill_dir)
        self._files = PyFileInventory(self.skill_dir, self.store, self._cond)
        self._verdicts = SyntaxVerdictCache(self.skill_dir, self.store,
                                             self._lock)
        self._residency = WarmupResidency(self._lock)
        self._gate_files: list[str] | None = None
        self._gate_scan_errors: tuple[BaseException, ...] = ()
        self._permanent_generation_adopted = False
        self._lifecycle_epoch = 0
        self._releasing = False
    def get_source(self, filepath: str) -> str | None:
        return self.store.get_source(filepath)
    def get_ast(self, filepath: str) -> ast.AST | None:
        return self.store.get_ast(filepath)
    def get_source_and_ast(self, filepath: str) -> tuple[str | None, ast.AST | None]:
        return self.store.get_source_and_ast(filepath)
    def get_ast_by_digest(self, digest: str) -> ast.AST | None:
        return self.store.get_ast_by_digest(digest)
    def freeze_fingerprints(self) -> int:
        return self.store.freeze_fingerprints()
    def unfreeze_fingerprints(self) -> None:
        return self.store.unfreeze_fingerprints()
    def get_function_nodes(self, tree: ast.AST) -> list | None:
        return self.store.get_function_nodes(tree)
    def set_function_nodes(self, tree: ast.AST, nodes: list) -> None:
        self.store.set_function_nodes(tree, nodes)
    @property
    def py_files(self) -> list[str]:
        return self._files.paths
    def gate_scan_files(self, errors: list | None = None) -> list[str]:
        with self._lock:
            if self._gate_files is None:
                scan_errors: list[BaseException] = []
                self._gate_files = collect_gate_scan_files(
                    self.skill_dir, scan_errors)
                self._gate_scan_errors = tuple(scan_errors)
            if errors is not None:
                errors.extend(self._gate_scan_errors)
            return list(self._gate_files)
    @property
    def file_count(self) -> int:
        return self._files.count
    @property
    def total_lines(self) -> int:
        return self._files.lines
    def warmup(self, *, verbose: bool = True) -> SharedCache:
        with self._lock:
            self._lifecycle_epoch += 1
            self._residency.reset()
            self._gate_files = None
            self._gate_scan_errors = ()
            gc_was = gc.isenabled()
            if gc_was:
                gc.disable()
            frozen_before = self.store.frozen
            try:
                if not frozen_before:
                    self.freeze_fingerprints()
                result = self._warmup_core(verbose=verbose)
            finally:
                if not frozen_before:
                    self.unfreeze_fingerprints()
                if gc_was:
                    gc.enable()
            if result.is_warmed():
                self._releasing = False
                if not self._permanent_generation_adopted:
                    self._permanent_generation_adopted = permanent_generation_adopt()
            return result
    def _warmup_core(self, *, verbose: bool) -> SharedCache:
        if verbose:
            logger.info("[Cache] 开始预热缓存...")
        self.store.adapt_caps(self.store.count_py_files())
        self._files.reset()
        self._files.ensure()
        files, file_count, total_lines = self._files.snapshot()
        self.store.adapt_caps(len(files))
        pinned = _preload_entries(self, files)
        if verbose:
            src_hit = len(pinned) - len(self.store.missing_sources(pinned))
            ast_hit = len(pinned) - len(self.store.missing_asts(pinned))
            src_n, ast_n = self.store.residency_sizes()
            logger.info(
                "[Cache] 预热完成：%d 文件, %d 行；诊断范围内 %d 个全部驻留"
                "（source %d/%d, ast %d/%d），总驻留 source=%d ast=%d",
                file_count, total_lines, len(pinned),
                src_hit, len(pinned), ast_hit, len(pinned),
                src_n, ast_n)
        _finalize_warmed(self, files)
        self._blob_store.prune_sibling_stale_async()
        return self
    def is_warmed(self) -> bool:
        return self._residency.is_warmed
    def ensure_warmed(self) -> SharedCache:
        self._residency.ensure(self.store)
        return self
    def is_residency_intact(self) -> bool:
        return self._residency.is_intact(self.store)
    def get_syntax_verdict(self, filepath: str) -> tuple[bool, str] | None:
        return self._verdicts.get(filepath)
    def set_syntax_verdict(self, filepath: str, *, ok: bool,
                           err: str) -> None:
        self._verdicts.set(filepath, ok=ok, err=err)
    def flush_syntax_verdicts(self) -> int:
        return self._verdicts.flush()
    def release(self) -> None:
        with _WARMED_CACHES_LOCK:
            self._releasing = True
            _invalidate_file_owner_entries([self])
        try:
            self.flush_syntax_verdicts()
        except Exception as e:  # pragma: no cover  # noqa: BLE001
            logger.debug("[Cache] release 前 verdict 落盘失败(降级): %s", e)
        with self._lock:
            self._releasing = True
            self.store.clear()
            self.slots.clear()
            self._verdicts.clear()
            self._files.reset()
            self._residency.reset()
            self._gate_files = None
            self._gate_scan_errors = ()
            generation_adopted = self._permanent_generation_adopted
            self._permanent_generation_adopted = False
            lifecycle_epoch = self._lifecycle_epoch
        release_shared_registries()
        _unregister_instance(self, lifecycle_epoch)
        if generation_adopted:
            permanent_generation_release()
        gc.collect()
def _preload_entries(cache: SharedCache, files: list) -> list:
    pinned = cache.store.pinned_paths(files)
    for p in files:
        cache.get_ast(p)
    return pinned
def _finalize_warmed(cache: SharedCache, files: list) -> None:
    src_missing = cache.store.missing_sources(files)
    ast_missing = cache.store.missing_asts(files)
    if src_missing or ast_missing:
        logger.warning(
            "[Cache] 全量预热对账未通过：source 缺失 %d/%d, ast 缺失 "
            "%d/%d —— 不置位预热标记（fail-fast，ensure_warmed 将拒绝）；"
            "source 缺失样例: %s；ast 缺失样例: %s",
            len(src_missing), len(files),
            len(ast_missing), len(files),
            ", ".join(src_missing[:5]) or "-",
            ", ".join(ast_missing[:5]) or "-")
        return
    cache._residency.mark(files, cache.store)
_MISSING = object()
class _CtxAstCacheView(dict):
    def __init__(self, cache: SharedCache) -> None:
        super().__init__()
        self._sc = cache
    def _resident_stale(self, filepath: str) -> bool:
        try:
            if self._sc.store.meta_changed(filepath):
                return True
            cur = self._sc.store.resident_ast(filepath)
            return cur is not dict.__getitem__(self, filepath)
        except (OSError, ValueError, TypeError, KeyError) as _e:
            log_swallowed(__name__, _e,
                          context=f'_CtxAstCacheView._resident_stale:'
                                  f'{type(_e).__name__}')
            return True
    def _refresh(self, filepath: str):
        try:
            tree = self._sc.get_ast(filepath)
        except (OSError, ValueError, TypeError) as _e:
            log_swallowed(__name__, _e,
                          context=f'_CtxAstCacheView._refresh:'
                                  f'{type(_e).__name__}')
            return None
        if tree is None:
            return None
        dict.__setitem__(self, filepath, tree)
        return tree
    def _resident_lookup(self, filepath: str):
        if not dict.__contains__(self, filepath):
            return _MISSING
        if not self._resident_stale(filepath):
            return dict.__getitem__(self, filepath)
        dict.__delitem__(self, filepath)
        return _MISSING
    def __contains__(self, filepath: object) -> bool:
        if not isinstance(filepath, str):
            return False
        if self._resident_lookup(filepath) is not _MISSING:
            return True
        return self._refresh(filepath) is not None
    def __getitem__(self, filepath: str):
        if not isinstance(filepath, str):
            return None
        resident = self._resident_lookup(filepath)
        return self._refresh(filepath) if resident is _MISSING else resident
    def get(self, filepath, default=None):
        if not isinstance(filepath, str):
            return default
        value = self[filepath]
        return default if value is None else value
class SharedCacheCtxView:
    def __init__(self, cache: SharedCache) -> None:
        self._cache = cache
        self._ast_cache = _CtxAstCacheView(cache)
    @property
    def py_files(self) -> list[str]:
        return self._cache.py_files
    @property
    def skill_dir(self) -> str:
        return self._cache.skill_dir
    def get_source(self, filepath: str) -> str | None:
        return self._cache.get_source(filepath)
    def get_ast(self, filepath: str):
        tree = self._cache.get_ast(filepath)
        if tree is not None:
            self._ast_cache[filepath] = tree
        return tree
def as_diag_ctx(cache: SharedCache) -> SharedCacheCtxView:  # jwsgj:suppress D51 — as_diag_ctx 返回只读视图对象，非纯透传
    if cache is None:
        raise TypeError(
            "as_diag_ctx 需要已预热/已创建的 SharedCache 实例，"
            "不得传入 None（调用方应先判断 cache 是否存在）")
    return SharedCacheCtxView(cache)
def cached_getter(ctx: Any, getter: str, fpath: str) -> Any:
    if ctx is None:
        return None
    try:
        return getattr(ctx, getter)(fpath)
    except Exception:
        logger.debug("[Cache] 缓存读取失败，回退直读: %s", fpath, exc_info=True)
        return None
class DiagnosticContext:
    def __init__(self, skill_dir: str):
        self.skill_dir: str = require_skill_root(skill_dir)
        self._py_files: list[str] = collect_py_files_default(self.skill_dir)
        self._source_cache: dict[str, str | None] = {}
        self._ast_cache: dict[str, ast.AST | None] = {}
        self._file_stats: dict[str, dict] = {}
        self._lock = threading.RLock()
    @property
    def py_files(self) -> list[str]:
        return self._py_files
    def _cached(self, cache: dict, key: str, loader) -> Any:
        if key not in cache:
            with self._lock:
                if key not in cache:
                    cache[key] = loader(key)
        return cache[key]
    def get_source(self, filepath: str) -> str | None:
        return self._cached(self._source_cache, filepath, self._load_source)
    def _load_source(self, filepath: str) -> str | None:
        source, _ = read_source_with_fingerprint(filepath)
        if source is None:
            logger.warning("[DiagUtils] source read failed: %s", filepath)
        return source
    def get_ast(self, filepath: str) -> ast.AST | None:
        return self._cached(self._ast_cache, filepath, self._load_ast)
    def _load_ast(self, filepath: str) -> ast.AST | None:
        src = self.get_source(filepath)
        if src is None:
            return None
        try:
            return ast.parse(src, filename=filepath)
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[DiagUtils] parse failed: %s: %s", filepath, e)
            return None
    def get_file_stats(self, filepath: str) -> dict:
        return self._cached(
            self._file_stats, filepath,
            lambda fp: self._measure_file_stats(self.get_source(fp)))
    @staticmethod
    def _measure_file_stats(src: str | None) -> dict:
        if src is None:
            return {"lines": 0, "comment_ratio": 0.0}
        lines = aligned_source_lines(src)
        total = len(lines)
        comment_lines = sum(
            1 for ln in lines if ln.lstrip().startswith(("#", '"""', "'''")))
        return {
            "lines": total,
            "comment_ratio": comment_lines / max(total, 1),
        }
def _cache_usable(cache: Any) -> bool:
    try:
        if getattr(cache, "_releasing", False):
            return False
    except Exception as e:  # noqa: BLE001
        logger.debug("[Cache] 释放状态探测失败，视为不可用: %s", e)
        return False
    return _intact_or_warmed(cache)
def peek_warmed_cache(skill_dir: str) -> SharedCache | None:
    with _WARMED_CACHES_LOCK:
        c = _WARMED_CACHES.get(fs_key(skill_dir))
    if c is not None and _cache_usable(c):
        return c
    return None
_INTACT_PROBES = ("is_residency_intact", "is_warmed")
def _probe_flag(obj: Any, name: str) -> bool | None:
    probe = getattr(obj, name, None)
    if probe is None:
        return None
    return bool(probe() if callable(probe) else probe)
def _intact_or_warmed(cache: Any) -> bool:
    try:
        for name in _INTACT_PROBES:
            flag = _probe_flag(cache, name)
            if flag is not None:
                return flag
        return False
    except Exception as e:
        logger.warning("[Cache] 驻留完整性探测失败，视为残缺: %s", e, exc_info=True)
        return False
def _store_warmed(skill_dir: str, cache: SharedCache) -> None:
    _WARMED_CACHES[fs_key(skill_dir)] = cache
    _clear_dict_store("代码身份归属缓存", _SHARED_CACHE_FOR_FILE,
                      _SHARED_CACHE_FOR_FILE_LOCK)
def _unregister_instance(cache: SharedCache, expected_epoch: int) -> None:
    skill_dir = getattr(cache, "skill_dir", "")
    if not isinstance(skill_dir, str) or not skill_dir:
        return
    with _WARMED_CACHES_LOCK:
        if cache._lifecycle_epoch != expected_epoch:
            return
        key = fs_key(skill_dir)
        if _WARMED_CACHES.get(key) is cache:
            del _WARMED_CACHES[key]
def register_warmed_cache(cache: SharedCache) -> SharedCache:
    ensure = getattr(cache, "ensure_warmed", None)
    if callable(ensure):
        ensure()
    skill_dir = getattr(cache, "skill_dir", None)
    if not isinstance(skill_dir, str) or not skill_dir:
        raise TypeError(
            "register_warmed_cache 要求缓存实例具备非空 skill_dir 字符串"
            f"（注册键标识），实际: {skill_dir!r}（实例类型 "
            f"{type(cache).__name__}）。替身对象须与 SharedCache 的 "
            "skill_dir 契约对齐方可注册。"
        )
    replaced = None
    with _WARMED_CACHES_LOCK:
        existing = _WARMED_CACHES.get(fs_key(skill_dir))
        if (existing is not None and existing is not cache
                and _cache_usable(existing)):
            logger.info(
                "[Cache] 技能根已有存活缓存实例，复用注册而不覆盖: %s",
                skill_dir)
            return existing
        if existing is not None and existing is not cache:
            replaced = existing
        _store_warmed(skill_dir, cache)
    if replaced is not None:
        _release_failed_instance(replaced, "残缺缓存替换")
    return cache
def discard_warmed_cache(skill_dir: str | None = None, *,
                         release: bool = True) -> int:
    with _PROCESS_CALL_LOCK:
        pooled = []
        if release:
            if skill_dir is None:
                pooled = list(_GLOBAL_CACHES.values())
                _GLOBAL_CACHES.clear()
                _GLOBAL_CACHE_ORDER.clear()
            else:
                key = fs_key(skill_dir)
                cached = _GLOBAL_CACHES.pop(key, None)
                if cached is not None:
                    pooled.append(cached)
                _GLOBAL_CACHE_ORDER[:] = [
                    k for k in _GLOBAL_CACHE_ORDER if k != key]
        with _WARMED_CACHES_LOCK:
            popped, n = _take_entries(skill_dir)
        if release:
            _release_instances([*popped, *pooled])
        return n
def _take_entries(skill_dir: str | None) -> tuple[list, int]:
    if skill_dir is not None:
        evicted = _WARMED_CACHES.pop(fs_key(skill_dir), None)
        popped = [] if evicted is None else [evicted]
    else:
        popped = list(_WARMED_CACHES.values())
        _WARMED_CACHES.clear()
    _invalidate_file_owner_entries(popped)
    return popped, len(popped)
def _invalidate_file_owner_entries(instances: list) -> None:
    discarded = {id(instance) for instance in instances}
    if not discarded:
        return
    with _SHARED_CACHE_FOR_FILE_LOCK:
        stale_keys = [key for key, cached in _SHARED_CACHE_FOR_FILE.items()
                      if id(cached) in discarded]
        for key in stale_keys:
            del _SHARED_CACHE_FOR_FILE[key]
def _release_instances(instances: list) -> int:
    released = 0
    seen: set[int] = set()
    for inst in instances:
        if id(inst) in seen:
            continue
        seen.add(id(inst))
        _release = getattr(inst, "release", None)
        if callable(_release):
            try:
                _release()
                released += 1
            except Exception as _re:  # noqa: BLE001 — 释放软失败不中断清理
                logger.warning(
                    "[Cache] 缓存实例 release 失败(条目已摘除): %s", _re)
    return released
def find_warmed_cache_for_file(filepath: str) -> SharedCache | None:
    if not isinstance(filepath, str) or not filepath:
        return None
    target = fs_key(filepath)
    with _WARMED_CACHES_LOCK:
        caches = list(_WARMED_CACHES.values())
    for cache in caches:
        if _scan_set_matches(cache, target):
            return cache
    return None
def _scan_set_matches(cache: Any, target: str) -> bool:
    try:
        if not _cache_usable(cache):
            return False
        files = cache.py_files
        if not isinstance(files, (list, tuple)):
            return False
        return any(fs_key(fp) == target for fp in files)
    except Exception as e:  # noqa: BLE001 — 替身实例检查面失败跳过（可选降级契约）
        logger.debug("find_warmed_cache_for_file: 实例检查失败，跳过: %s", e)
        return False
def _release_failed_instance(cache: Any, context: str) -> None:
    try:
        cache.release()
    except Exception:
        logger.warning("[Cache] %s后的实例释放失败", context, exc_info=True)
def _create_warmed_cache(skill_dir: str) -> SharedCache:
    cache = create_cache(skill_dir, warmup=True)
    try:
        cache.ensure_warmed()
    except BaseException:
        _release_failed_instance(cache, "预热核验失败")
        raise
    return cache
def get_warmed_cache(skill_dir: str) -> SharedCache:
    with _WARMED_CACHES_LOCK:
        existing = peek_warmed_cache(skill_dir)
        if existing is not None:
            return existing
        cache = _create_warmed_cache(skill_dir)
        registered = register_warmed_cache(cache)
        if registered is not cache:
            _release_failed_instance(cache, "并发登记冲突")
        return registered
def prepare_scan_input(target_path: str, clean_cache: bool = False) -> int | None:
    if not os.path.isdir(target_path):
        return None
    get_warmed_cache(target_path)
    if not clean_cache:
        return None
    return clean_pycache_before_scan(target_path)
def create_cache(skill_dir: str, warmup: bool = True) -> SharedCache:
    cache = SharedCache(skill_dir)
    if warmup:
        try:
            cache.warmup()
        except BaseException:
            _release_failed_instance(cache, "warmup 异常")
            raise
    return cache
def require_warmed(cache: Any, who: str = "诊断方法") -> Any:
    if cache is None:
        raise CacheNotWarmedError(
            f"{who} 要求 SharedCache 已全量预热（源码+AST），但未传入 cache。"
            "SharedCache 预热是所有诊断方法与管线步骤的强制前置条件，未预热"
            "不执行后续行为。请先调用 get_warmed_cache(skill_dir) 或 "
            "create_cache(skill_dir) 完成预热后重试。"
        )
    ensure = getattr(cache, "ensure_warmed", None)
    if not callable(ensure) and isinstance(cache, SharedCacheCtxView):
        ensure = getattr(cache._cache, "ensure_warmed", None)
    if not callable(ensure):
        raise CacheNotWarmedError(
            f"{who} 要求 SharedCache 已全量预热（源码+AST），但当前对象 "
            f"{type(cache).__name__} 未提供 ensure_warmed() 生命周期校验。"
        )
    ensure()
    return cache
def ensure_entry_warmed(skill_dir: str, cache: Any = None,
                        who: str = "诊断入口") -> Any:
    if cache is None:
        return get_warmed_cache(skill_dir)
    return require_warmed(cache, who)
@contextmanager
def fingerprint_freeze_window(cache: Any, tag: str):
    _froze = False
    try:
        if cache is not None and hasattr(cache, "freeze_fingerprints"):
            try:
                cache.freeze_fingerprints()
                _froze = True
            except Exception as e:  # noqa: BLE001
                logger.debug("[%s] 指纹冻结失败(降级逐次校验): %s", tag, e)
        yield
    finally:
        if _froze:
            try:
                cache.unfreeze_fingerprints()
            except Exception:
                logger.warning("[%s] 指纹解冻失败", tag, exc_info=True)
@contextmanager
def e1_snapshot_session(cache):
    try:
        begin_snapshot_lines_window(cache)
        with fingerprint_freeze_window(cache, "E1-snap"):
            yield
    finally:
        end_snapshot_lines_window()
_SNAPSHOT_UNSET = object()
@contextmanager
def diagnostic_read_scope(cache: Any, *, memoize_walk: bool = True,
                          bind_reader: bool = False,
                          reader: Any = None) -> Iterator[None]:
    _prev = _SNAPSHOT_UNSET
    if bind_reader:
        _prev = set_shared_snapshot_reader(reader)
    try:
        with shared_cache_bridge_scope(cache):
            if memoize_walk:
                with memoized_module_walk_scope():
                    yield
            else:
                yield
    finally:
        if _prev is not _SNAPSHOT_UNSET:
            set_shared_snapshot_reader(_prev)
_PROCESS_CALL_LOCK = threading.RLock()
def get_process_call_lock() -> threading.RLock:
    return _PROCESS_CALL_LOCK
_GLOBAL_CACHES: dict[str, SharedCache] = {}
_GLOBAL_CACHE_ORDER: list[str] = []
_GLOBAL_CACHE_MAX: int = 3
def _touch_lru(cache_key: str) -> None:
    if cache_key in _GLOBAL_CACHE_ORDER:
        _GLOBAL_CACHE_ORDER.remove(cache_key)
    _GLOBAL_CACHE_ORDER.append(cache_key)
def _retire_evicted_cache(evicted: Any, cache_key: str) -> None:
    _release = getattr(evicted, "release", None)
    if callable(_release):
        try:
            _release()
        except Exception as _re:  # noqa: BLE001
            logger.warning("[Cache] 淘汰实例 release 失败: %s", _re)
    with _WARMED_CACHES_LOCK:
        current = _WARMED_CACHES.get(fs_key(cache_key))
        if current is None or current is evicted:
            _take_entries(cache_key)
def _evict_until_capacity() -> None:
    while len(_GLOBAL_CACHES) >= _GLOBAL_CACHE_MAX:
        if _GLOBAL_CACHE_ORDER:
            evict_key = _GLOBAL_CACHE_ORDER.pop(0)
        else:
            evict_key = next(iter(_GLOBAL_CACHES), None)
            if evict_key is None:
                break
        evicted = _GLOBAL_CACHES.pop(evict_key, None)
        _GLOBAL_CACHE_ORDER[:] = [k for k in _GLOBAL_CACHE_ORDER
                                  if k in _GLOBAL_CACHES]
        if evicted is not None:
            _retire_evicted_cache(evicted, evict_key)
def _drop_pool_entry(cache_key: str) -> None:
    broken = _GLOBAL_CACHES.pop(cache_key, None)
    _GLOBAL_CACHE_ORDER[:] = [k for k in _GLOBAL_CACHE_ORDER if k != cache_key]
    if broken is not None:
        _retire_evicted_cache(broken, cache_key)
def _admit_to_pool(cache_key: str, cache: Any) -> None:
    _evict_until_capacity()
    _GLOBAL_CACHES[cache_key] = cache
    _touch_lru(cache_key)
def _build_pool_cache(cache_key: str, skill_dir) -> Any:
    created = _create_warmed_cache(skill_dir)
    try:
        registered = register_warmed_cache(created)
    except BaseException:
        _release_failed_instance(created, "缓存池登记失败")
        raise
    if registered is not created:
        _release_failed_instance(created, "缓存池并发登记冲突")
    _admit_to_pool(cache_key, registered)
    return registered
def get_or_create_cache(skill_dir: str) -> Any:
    cache_key = fs_key(skill_dir)
    with _PROCESS_CALL_LOCK:
        existing = peek_warmed_cache(cache_key)
        if existing is not None:
            pooled = _GLOBAL_CACHES.get(cache_key)
            if pooled is not None and pooled is not existing:
                _drop_pool_entry(cache_key)
            if cache_key not in _GLOBAL_CACHES:
                _admit_to_pool(cache_key, existing)
            else:
                _touch_lru(cache_key)
            return existing
        cached = _GLOBAL_CACHES.get(cache_key)
        if cached is not None:
            if _cache_usable(cached):
                registered = register_warmed_cache(cached)
                if registered is cached:
                    _touch_lru(cache_key)
                    return cached
                _drop_pool_entry(cache_key)
                _admit_to_pool(cache_key, registered)
                return registered
            _drop_pool_entry(cache_key)
        return _build_pool_cache(cache_key, skill_dir)
def _trace_mem() -> int | None:
    try:
        if tracemalloc.is_tracing():
            cur, _peak = tracemalloc.get_traced_memory()
            return int(cur)
    except Exception as _e:
        logger.debug("tracemalloc 内存统计失败，忽略: %s", _e, exc_info=True)
    return None
def _fmt_mem(n) -> str:
    if n is None:
        return "n/a"
    try:
        v = float(n)
        for unit in ("B", "KB", "MB", "GB"):
            if abs(v) < 1024:
                return f"{v:.1f}{unit}"
            v /= 1024
        return f"{v:.1f}TB"
    except Exception as e:  # noqa: BLE001
        logger.debug("体积格式化失败，降级占位符: %s", e)
        return "?"
def _mem_delta_text(before, after) -> str:
    if before is None or after is None:
        return ""
    freed = before - after
    if freed >= 0:
        return f"，内存回落 {_fmt_mem(freed)}"
    return f"，内存增长 {_fmt_mem(-freed)}"
def _release_pool_locked() -> int:
    instances = list(_GLOBAL_CACHES.values())
    _GLOBAL_CACHES.clear()
    _GLOBAL_CACHE_ORDER.clear()
    with _WARMED_CACHES_LOCK:
        warmed, _ = _take_entries(None)
    instances.extend(warmed)
    return _release_instances(instances)
def clear_global_caches(gc_collect: bool = True) -> int:
    _mem_before = _trace_mem()
    with _PROCESS_CALL_LOCK:
        released = _release_pool_locked()
    if gc_collect:
        gc.collect()
    _mem_after = _trace_mem()
    if released or _mem_before is not None:
        logger.info("[Cache] 已释放 %d 个共享缓存实例，缓存池已清空%s",
                    released, _mem_delta_text(_mem_before, _mem_after))
    return released
def release_project_caches(skill_dir: str) -> int:
    key = fs_key(skill_dir)
    with _PROCESS_CALL_LOCK:
        pooled = _GLOBAL_CACHES.pop(key, None)
        _GLOBAL_CACHE_ORDER[:] = [k for k in _GLOBAL_CACHE_ORDER if k != key]
        with _WARMED_CACHES_LOCK:
            warmed, _ = _take_entries(skill_dir)
    return _release_instances([pooled, *warmed])
def _apply_release_step(result: dict, key: str, release_fn: Callable,
                        label: str, kind: str) -> None:
    try:
        value = release_fn()
    except Exception:
        logger.warning("[Mem] %s释放失败", label, exc_info=True)
        return
    if kind != "count":
        result[key] = True
    elif isinstance(value, dict):
        result.update(value)
    else:
        result[key] = value
_RELEASE_DOMAIN_KEYS: tuple[str, ...] = (
    "registries", "shared_ast", "shared_parse", "source_parse", "guard_ast",
    "taint_scope_memos", "experience_atoms", "e1_scan_base_caches",
    "d_group_caches", "rule_match_caches", "rule_metadata_cache",
    "e1_diagnoser_caches", "sec_tree_nodes_index", "sec_tokenize_caches",
    "module_binding_index", "shared_walk_memo", "shared_tokenize_cache",
    "e_group_caches", "summary_cache", "defense_feedback",
    "treatment_state_cache", "fix_plans_cache",
)
def release_domain_caches(result: dict, skill_dir: str = _UNSCOPED_SKILL_DIR) -> None:
    _hooks = registered_cache_releases()
    _registered = {_hook.key for _hook in _hooks}
    _missing = [_key for _key in _RELEASE_DOMAIN_KEYS
                if _key not in _registered]
    if _missing:
        logger.debug(
            "[Mem] 可选缓存域未登记（模块未加载或钩子未注册），跳过: %s",
            _missing)
    if skill_dir:
        result["registries"] = False
        result["project_context"] = False
    for _hook in _hooks:
        if skill_dir and _hook.scope == "process":
            continue
        _release_fn = (functools.partial(_hook.release_fn, skill_dir)
                       if skill_dir and _hook.scope == "project"
                       else _hook.release_fn)
        _apply_release_step(result, _hook.key, _release_fn,
                            _hook.label, _hook.kind)
def _init_release_result(keep_shared_cache: bool,
                        skill_dir: str = _UNSCOPED_SKILL_DIR) -> dict:
    result = {"global_caches": 0, "registries": False,
              "shared_ast": False, "shared_parse": False,
              "taint_scope_memos": 0,
              "project_context": False,
              "experience_atoms": 0,
              "defense_feedback": 0, "treatment_state_cache": 0,
              "fix_plans_cache": 0}
    if keep_shared_cache:
        result["shared_cache_kept"] = True
    elif skill_dir:
        result["global_caches"] = release_project_caches(skill_dir)
    else:
        result["global_caches"] = clear_global_caches(gc_collect=False)
    return result
def _release_mem_bus(result: dict, skill_dir: str = _UNSCOPED_SKILL_DIR,
                     all_skills: bool = False) -> None:
    try:
        result["mem_bus_slots"] = mem_bus_clear(
            skill_dir=skill_dir, all_skills=all_skills)
    except Exception:
        logger.warning("[Mem] 管线内存交换区释放失败", exc_info=True)
def _collect_garbage(keep_shared_cache: bool) -> None:
    if keep_shared_cache:
        gc.collect(1)
    else:
        gc.collect()
def clear_all_process_memory(gc_collect: bool = True,
                             keep_shared_cache: bool = False,
                             skill_dir: str = _UNSCOPED_SKILL_DIR) -> dict:
    result = _init_release_result(keep_shared_cache, skill_dir)
    release_domain_caches(result, skill_dir)
    if not keep_shared_cache:
        _release_mem_bus(result, skill_dir, all_skills=not skill_dir)
    if gc_collect:
        _collect_garbage(keep_shared_cache)
    logger.info("[Mem] 诊断完成统一释放: %s", result)
    return result
class BatchDetector:
    _call_records: ClassVar[dict[str, int]] = {}
    _call_owners: ClassVar[dict[str, tuple[int, int]]] = {}
    _RECORD_LOCK: ClassVar[threading.Lock] = threading.Lock()
    @classmethod
    def _record_key(cls, step_name: str, skill_dir: str | None = None) -> str:
        if skill_dir is None:
            return step_name
        return json.dumps([fs_key(skill_dir), step_name], ensure_ascii=False)
    @classmethod
    def check_and_record(cls, step_name: str,
                         skill_dir: str | None = None) -> None:
        key = cls._record_key(step_name, skill_dir)
        with cls._RECORD_LOCK:
            count = cls._call_records.get(key, 0)
            if count > 0:
                logger.critical(
                    "[PipelineGuard] 批量执行违规: step='%s' (第%d次调用)，"
                    "独立运行模式要求每次bash调用仅执行一项，拒绝继续执行",
                    step_name, count + 1
                )
                raise ConcurrentExecutionError(
                    f"步骤 '{step_name}' 本进程已执行过（第{count + 1}次调用），"
                    "独立运行模式要求每次命令轮次仅执行一项；"
                    "批内多相位推进请使用 run_pipeline_batch 的内部通道"
                )
            cls._call_records[key] = count + 1
            cls._call_owners[key] = (os.getpid(), threading.get_ident())
        logger.debug("[PipelineGuard] 批量检测记录: %s (第%d次)", step_name, count + 1)
    @classmethod
    def _rollback_pending_record(cls, step_name: str,
                                 skill_dir: str | None = None) -> None:
        key = cls._record_key(step_name, skill_dir)
        caller = (os.getpid(), threading.get_ident())
        with cls._RECORD_LOCK:
            if (cls._call_records.get(key) == 1
                    and cls._call_owners.get(key) == caller):
                del cls._call_records[key]
                cls._call_owners.pop(key, None)
                logger.debug("[PipelineGuard] 前置失败回滚批量检测记录: %s", step_name)
def carry_failure_detail(out: dict, source: dict) -> None:
    if out.get("status") != "failed":
        return
    if source.get("error"):
        out["error"] = str(source["error"])[:500]
    if source.get("traceback"):
        out["traceback"] = str(source["traceback"])[:1000]
def validated_warmed_root(project_root) -> str:
    root = normalize_project_root(project_root)
    get_warmed_cache(root)
    return root
_FILE_CACHE: dict[tuple, tuple] = {}
_FILE_CACHE_MAX = 128
_FILE_CACHE_LOCK = threading.Lock()
_SHARED_CACHE_FOR_FILE: dict[str, object] = {}
_SHARED_CACHE_FOR_FILE_LOCK = threading.Lock()
_SHARED_CACHE_FOR_FILE_MAX = 512
_SHARED_CACHE_FOR_FILE_MISS = object()
def _shared_cache_for_file(filepath: str) -> object | None:
    if not isinstance(filepath, (str, os.PathLike)):
        return None
    try:
        path = os.fsdecode(os.fspath(filepath))
        key = fs_key(path)
    except (TypeError, ValueError) as _e:
        logger.debug("[Cache] 路径键归一化失败，跳过归属缓存: %r (%s)",
                     filepath, type(_e).__name__)
        return None
    hit = _memo_resident_cache(key)
    if hit is not _SHARED_CACHE_FOR_FILE_MISS:
        return hit
    cache = find_warmed_cache_for_file(path)
    _memo_resident_cache_put(key, cache)
    return cache
def _memo_resident_cache(key: str) -> object:
    with _SHARED_CACHE_FOR_FILE_LOCK:
        hit = _SHARED_CACHE_FOR_FILE.get(key, _SHARED_CACHE_FOR_FILE_MISS)
    if hit is _SHARED_CACHE_FOR_FILE_MISS or hit is None:
        return hit
    if _cache_usable(hit):
        return hit
    with _SHARED_CACHE_FOR_FILE_LOCK:
        _SHARED_CACHE_FOR_FILE.pop(key, None)
    return _SHARED_CACHE_FOR_FILE_MISS
def _memo_resident_cache_put(key: str, cache) -> None:
    with _SHARED_CACHE_FOR_FILE_LOCK:
        if (key not in _SHARED_CACHE_FOR_FILE
                and len(_SHARED_CACHE_FOR_FILE) >= _SHARED_CACHE_FOR_FILE_MAX):
            _SHARED_CACHE_FOR_FILE.pop(next(iter(_SHARED_CACHE_FOR_FILE)))
        _SHARED_CACHE_FOR_FILE[key] = cache
def _collect_func_spans(tree: ast.Module) -> list:
    spans = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        end_lineno = getattr(node, "end_lineno", None)
        def_lineno = getattr(node, "lineno", None)
        if end_lineno is None or def_lineno is None:
            continue
        start = def_lineno
        for decorator in getattr(node, "decorator_list", ()):
            dec_lineno = getattr(decorator, "lineno", None)
            if isinstance(dec_lineno, int) and 0 < dec_lineno < start:
                start = dec_lineno
        spans.append((start, end_lineno))
    return spans
def _func_spans_of(tree: ast.Module | None) -> list | None:
    return _collect_func_spans(tree) if tree is not None else None
def _load_via_shared_cache(filepath: str) -> tuple[list[str] | None, ast.Module | None, list | None] | None:
    cache = _shared_cache_for_file(filepath)
    if cache is None:
        return None
    paired_getter = getattr(cache, "get_source_and_ast", None)
    if callable(paired_getter):
        try:
            src, tree = paired_getter(filepath)
        except Exception as _cache_err:  # noqa: BLE001
            logger.debug(
                "load_code_hash_lines: 配对读取异常，降级磁盘通道: %s",
                _cache_err)
            return None
    else:
        try:
            src = cache.get_source(filepath)
        except Exception as _cache_err:  # noqa: BLE001
            logger.debug("load_code_hash_lines: get_source 异常，降级磁盘通道: %s", _cache_err)
            src = None
        if not isinstance(src, str):
            if src is not None:
                logger.warning(
                    "load_code_hash_lines: 缓存源码形态违约（按未命中处理）: %s: %s",
                    filepath, type(src).__name__)
            return None
        try:
            tree = cache.get_ast(filepath)
        except Exception as _ast_err:  # noqa: BLE001
            logger.debug("load_code_hash_lines: get_ast 异常，降级磁盘通道: %s", _ast_err)
            return None
    if not isinstance(src, str):
        if src is not None:
            logger.warning(
                "load_code_hash_lines: 缓存源码形态违约（按未命中处理）: %s: %s",
                filepath, type(src).__name__)
        return None
    lines = io.StringIO(src).readlines()
    if tree is not None and not isinstance(tree, ast.Module):
        logger.warning(
            "load_code_hash_lines: 缓存 AST 形态违约（按未命中处理）: %s: %s",
            filepath, type(tree).__name__)
        return None
    return (lines, tree, _func_spans_of(tree))
def _read_code_hash_source(filepath: str) -> str | None:
    try:
        source, _fingerprint = read_source_with_fingerprint(filepath)
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_read_code_hash_source:{type(_e).__name__}')
        return None
    if not isinstance(source, str):
        if source is not None:
            logger.warning(
                "_load_via_disk: 源码形态违约（按未命中处理）: %s: %s",
                filepath, type(source).__name__)
        return None
    return source
def _code_hash_entry_from_source(
        source: str, filepath: str,
) -> tuple[list[str], ast.Module | None, list | None]:
    lines = io.StringIO(source).readlines()
    try:
        tree = ast.parse(source, filename=filepath)
    except SOURCE_READ_PARSE_ERRORS:
        logger.debug("_load_via_disk: AST 解析失败，改走缩进推断回退", exc_info=True)
        tree = None
    return (lines, tree, _func_spans_of(tree))
def _load_via_disk(
        filepath: str, source: str | None = None,
) -> tuple[list[str] | None, ast.Module | None, list | None] | None:
    if source is None:
        source = _read_code_hash_source(filepath)
    if source is None:
        return None
    return _code_hash_entry_from_source(source, filepath)
def load_code_hash_lines(
        filepath: str) -> tuple[list[str] | None, ast.Module | None, list | None]:
    source = _read_code_hash_source(filepath)
    if source is None:
        return None, None, None
    key = _file_cache_key(filepath, source=source)
    if key is None:
        return None, None, None
    cached = _cache_get(key)
    if cached is not None:
        return cached
    entry = _load_via_shared_cache(filepath)
    shared_lines = entry[0] if entry is not None else None
    if shared_lines is None or "".join(shared_lines) != source:
        entry = _load_via_disk(filepath, source=source)
    if entry is None:
        return None, None, None
    _cache_put(key, entry)
    return entry
_CACHE_FAILURE_TYPES: tuple[type[Exception], ...] = (
    *SOURCE_READ_PARSE_ERRORS, KeyError, AttributeError)
def load_module_source(f: Path, cache: SharedCache | None
                       ) -> tuple[str, ast.Module] | None:
    if cache is not None:
        loaded = _load_cached_source(f, cache)
        if loaded is not None:
            return loaded
    src = read_source(f)
    if src is None:
        logger.debug("源码读取失败（跳过该文件）: %s", f)
        return None
    try:
        return src, ast.parse(src)
    except SOURCE_READ_PARSE_ERRORS as e:
        logger.debug("语法解析失败（跳过该文件）: %s", e)
        return None
def _load_cached_source(f: Path, cache: SharedCache
                        ) -> tuple[str, ast.Module] | None:
    paired_getter = getattr(cache, "get_source_and_ast", None)
    try:
        if callable(paired_getter):
            src, tree = paired_getter(str(f))
        else:
            src = cache.get_source(str(f))
            tree = cache.get_ast(str(f)) if src is not None else None
    except _CACHE_FAILURE_TYPES:
        logger.debug("缓存读取失败（回退磁盘）: %s", f, exc_info=True)
        return None
    if src is None or tree is None:
        return None
    if not isinstance(src, str) or not isinstance(tree, ast.Module):
        logger.warning(
            "缓存条目形态违约（回退磁盘）: %s: src=%s tree=%s",
            f, type(src).__name__, type(tree).__name__)
        return None
    return src, tree
_EXPECTED_NON_FILE_ERRNOS: frozenset[int] = frozenset({
    errno.ENOENT, errno.ENOTDIR, errno.EISDIR, errno.EINVAL})
def _is_expected_non_file_error(exc: BaseException) -> bool:
    return (isinstance(exc, (FileNotFoundError, NotADirectoryError,
                              IsADirectoryError))
            or (isinstance(exc, OSError) and exc.errno in _EXPECTED_NON_FILE_ERRNOS))
def _file_cache_key(
        filepath: str, *, source: str | None = None,
) -> tuple[str, str] | None:
    try:
        st = os.stat(filepath)
    except (OSError, ValueError, TypeError) as _e:
        if _is_expected_non_file_error(_e):
            logger.debug("[Cache] 非普通文件路径，跳过代码身份缓存: %s (%s)",
                         filepath, type(_e).__name__)
            return None
        log_swallowed(__name__, _e,
                      context=f'_file_cache_key:{type(_e).__name__}')
        return None
    if not stat.S_ISREG(st.st_mode):
        logger.debug("[Cache] 目录或特殊文件，跳过代码身份缓存: %s", filepath)
        return None
    if source is None:
        source = _read_code_hash_source(filepath)
    if source is None:
        return None
    return (os.path.abspath(filepath), source_digest(source))
def _cache_get(key: tuple[str, str]):
    with _FILE_CACHE_LOCK:
        if key in _FILE_CACHE:
            _FILE_CACHE[key] = _FILE_CACHE.pop(key)
            return _FILE_CACHE[key]
    return None
def _cache_put(key: tuple[str, str], entry: tuple) -> None:
    with _FILE_CACHE_LOCK:
        _FILE_CACHE[key] = entry
        if len(_FILE_CACHE) > _FILE_CACHE_MAX:
            _FILE_CACHE.pop(next(iter(_FILE_CACHE)))
__all__ = [
    "BatchDetector",
    "CacheNotWarmedError",
    "DiagnosticContext",
    "DimensionRun",
    "PipelineSlotStore",
    "SharedCache",
    "SharedCacheCtxView",
    "as_diag_ctx",
    "cached_getter",
    "carry_failure_detail",
    "clear_all_process_memory",
    "clear_global_caches",
    "coerce_dimension_issues",
    "collect_scan_py_files",
    "create_cache",
    "diagnostic_read_scope",
    "discard_warmed_cache",
    "e1_snapshot_session",
    "ensure_entry_warmed",
    "find_warmed_cache_for_file",
    "fingerprint_freeze_window",
    "gate_scan_files_cached",
    "get_or_create_cache",
    "get_process_call_lock",
    "get_warmed_cache",
    "handoff_persistence_enabled",
    "load_code_hash_lines",
    "load_module_source",
    "mem_bus_clear",
    "mem_bus_peek",
    "mem_bus_put",
    "mem_bus_take",
    "peek_warmed_cache",
    "permanent_generation_adopt",
    "permanent_generation_release",
    "prepare_scan_input",
    "register_warmed_cache",
    "release_domain_caches",
    "release_project_caches",
    "release_shared_registries",
    "require_warmed",
    "run_dimension_channels",
    "set_handoff_persistence",
    "validated_warmed_root",
]
def gate_scan_files_cached(cache: Any, skill_dir: str,
                           errors: list | None = None) -> list[str]:
    getter = getattr(cache, "gate_scan_files", None) if cache is not None else None
    if getter is not None:
        try:
            return getter(errors)
        except (OSError, TypeError, ValueError) as _swallow_e:
            log_swallowed(__name__, _swallow_e,
                          context=f'gate_scan_files_cached:'
                                  f'{type(_swallow_e).__name__}')
    return collect_gate_scan_files(skill_dir, errors)
def _cached_py_path(value: Any) -> str:
    path = os.fspath(value) if isinstance(value, os.PathLike) else value
    return path if isinstance(path, str) and path else ""
def _partition_cached_py_files(cached) -> tuple[list[str], int, int]:
    files: list[str] = []
    bad_path = 0
    bad_suffix = 0
    for value in cached:
        path = _cached_py_path(value)
        if not path:
            bad_path += 1
        elif not path.lower().endswith(".py"):
            bad_suffix += 1
        else:
            files.append(path)
    return files, bad_path, bad_suffix
def _cached_py_files_optional(cache) -> list | None:
    cached = getattr(cache, "py_files", None) if cache is not None else None
    if not isinstance(cached, (list, tuple)):
        return None
    files, bad_path, bad_suffix = _partition_cached_py_files(cached)
    if bad_path:
        logger.warning(
            "[UnifiedAstEngine] 缓存 py_files 含非路径元素 %d 个，已剔除",
            bad_path)
    if bad_suffix:
        logger.warning(
            "[UnifiedAstEngine] 缓存 py_files 含非 Python 路径元素 %d 个，已剔除",
            bad_suffix)
    if not files and not _cache_usable(cache):
        return None
    return files
def collect_scan_py_files(skill_dir: str, cache: Any = None) -> list[str]:
    files = _cached_py_files_optional(cache)
    if files is None:
        files = iter_scan_py_files(skill_dir)
    return sorted(f for f in files
                  if is_scan_scope_path(f, False, root_dir=skill_dir))
class DimensionRun(NamedTuple):
    results: dict[str, list]
    failed_dims: dict[str, str]
    timers: dict[str, float]
def coerce_dimension_issues(value) -> list | None:
    if isinstance(value, (list, tuple)):
        return list(value)
    return None
def _run_dimension_channel(name: str, factory, engine: Any,
                           results: dict, failed_dims: dict) -> float:
    _t_dim_start = time.perf_counter()
    try:
        issues = factory(engine)
        _shaped = coerce_dimension_issues(issues)
        if _shaped is None:
            _type_name = type(issues).__name__
            logger.warning(
                "[UnifiedAstEngine] %s 维度返回非 list/tuple 形态(%s)，按契约置空",
                name, _type_name)
            results[name] = []
            failed_dims[name] = f"non-container return: {_type_name}"
        else:
            results[name] = _shaped
    except Exception as e:  # noqa: BLE001 —— 单维度检测器异常按维度隔离降级，不阻断其余维度
        logger.warning("[UnifiedAstEngine] %s 维度异常: %s", name, e)
        results[name] = []
        failed_dims[name] = str(e)[:200]
    return round(time.perf_counter() - _t_dim_start, 1)
def run_dimension_channels(cache, dimension_factories, engine: Any) -> DimensionRun:
    if not hasattr(dimension_factories, "items"):
        raise TypeError(
            "dimension_factories 必须是「维度名 -> 工厂」映射，"
            f"得到 {type(dimension_factories).__name__}")
    _results: dict[str, list] = {}
    _failed_dims: dict[str, str] = {}
    _timers: dict[str, float] = {}
    with diagnostic_read_scope(cache):
        for name, factory in dimension_factories.items():
            _timers[name] = _run_dimension_channel(
                name, factory, engine, _results, _failed_dims)
    return DimensionRun(_results, _failed_dims, _timers)

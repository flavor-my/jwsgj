from __future__ import annotations

import ast
import copy
import hashlib
import io
import json
import logging
import os
import re
import tempfile
import threading
import time
import tokenize
import weakref
from collections import defaultdict, deque
from collections.abc import Iterator
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_guard_io import safe_delete
from jwsgj.diag_shared_ast_nodes import (
    collect_param_names,
    cyclomatic_complexity,
    definition_start_line,
    dotted_name,
    first_segment,
    import_binds_of,
    is_main_check,
    is_type_checking_guard,
    iter_class_scope_methods,
    iter_own_nodes,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    main_guard_branch,
    module_imports_test_framework,
    module_postpones_annotations,
    resolve_call_name,
    type_last_name,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_surface import (
    collect_module_exports_ordered,
    dunder_all_node_names,
)
from jwsgj.diag_shared_ast_views import shared_walk
from jwsgj.diag_shared_source_core import (
    count_lines,
    parse_cached,
    read_source,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed, write_module_run
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import get_temp_base
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    TEST_ARTIFACT_DIRS,
    TEST_DIR_CANDIDATES,
    collect_py_files_default,
    is_pruned_scan_dir,
    is_py_source_file,
    is_scan_py_name,
    is_test_dir_candidate,
    is_test_source_basename,
    scan_prune_dirs,
)

_log = logging.getLogger(__name__)
TRY_STAR_T = getattr(ast, 'TryStar', ast.Try)
MATCH_T = getattr(ast, 'Match', None)
MATCH_CASE_T = getattr(ast, 'match_case', None)
_TYPE_ALIAS_T = getattr(ast, 'TypeAlias', None)
_BODY_CONTAINER_TYPES = ((ast.ExceptHandler,)
                         + ((MATCH_CASE_T,) if MATCH_CASE_T is not None else ()))
__all__ = [
    'FUNCTION_SCOPE_CONTAINERS',
    'MATCH_CASE_T',
    'MATCH_T',
    'TRY_STAR_T',
    'FileCache',
    'FileEntry',
    'annotate_complexity_finding',
    'annotate_safety_finding',
    'build_import_graph_excluding_lazy',
    'build_mutation_test_mapping',
    'collect_func_scopes',
    'collect_function_behavior_metrics',
    'collect_module_assign_names',
    'collect_py_files',
    'collect_scope_binding_names',
    'collect_string_annotation_refs',
    'collect_typing_tc_bindings',
    'container_names_of_stmt',
    'entry_calls',
    'entry_class_method_ids',
    'entry_import_node_dotted',
    'entry_lines',
    'entry_module_dotted',
    'entry_nodes',
    'entry_rel_path',
    'entry_used_names',
    'file_content_digest',
    'find_function_boundary',
    'get_internal_modules',
    'import_binding_names',
    'import_node_dotted',
    'in_scope_py_file',
    'is_main_entry_guard',
    'is_transient_io_error',
    'iter_direct_scope_nodes',
    'iter_module_binding_nodes',
    'iter_module_level_stmts',
    'iter_module_stmts',
    'iter_own_scope_nodes',
    'iter_test_dirs',
    'iter_test_py_files',
    'main_guard_live_body',
    'module_entry_indexes',
    'module_has_toplevel_side_effect',
    'module_level_bound_names',
    'node_first_line',
    'nodes_where',
    'own_scope_loaded_names',
    'parse_python_file',
    'qualified_name',
    'record_module_import',
    'resolve_file_cache',
    'resolve_tests_dir',
    'reuse_or_build_import_graph',
    'scope_direct_bindings',
    'skill_has_nested_sources',
    'static_if_branch',
    'type_checking_static_body',
]
def type_checking_static_body(node, typing_refs, tc_binds):
    if not isinstance(node, ast.If):
        return None
    if is_type_checking_guard(node.test, typing_refs, tc_binds):
        return node.body
    if (isinstance(node.test, ast.UnaryOp)
            and isinstance(node.test.op, ast.Not)
            and is_type_checking_guard(
                node.test.operand, typing_refs, tc_binds)):
        return node.orelse
    return None
class FileEntry:
    __slots__ = (
        '_all_names',
        '_calls',
        '_classes',
        '_deferred_precompute',
        '_docstring',
        '_functions',
        '_has_all',
        '_has_future',
        '_has_version',
        '_imports',
        '_walk_nodes',
        '_where_cache',
        'is_init',
        'is_test',
        'line_ending',
        'lines',
        'mod_stem',
        'parse_error',
        'path',
        'rel_path',
        'source',
        'tree',
    )
    _SER_SLOTS = (
        ('functions', '_functions'),
        ('classes', '_classes'),
        ('imports', '_imports'),
        ('calls', '_calls'),
        ('has_future', '_has_future'),
        ('has_version', '_has_version'),
        ('has_all', '_has_all'),
        ('all_names', '_all_names'),
        ('docstring', '_docstring'),
    )
    _SER_PLAIN_KEYS = (
        'path', 'rel_path', 'source', 'tree', 'lines',
        'parse_error', 'mod_stem', 'is_test', 'is_init', 'line_ending',
    )
    _SER_KEYS = tuple(dict(_SER_SLOTS)) + _SER_PLAIN_KEYS
    _SLOT_BY_KEY: ClassVar[dict] = dict(_SER_SLOTS)
    _SER_TYPE_CONTRACT: ClassVar[tuple[tuple[str, tuple[type, ...]], ...]] = (
        ('tree', (ast.Module, type(None))),
        ('functions', (list,)),
        ('classes', (list,)),
        ('imports', (list,)),
        ('calls', (list,)),
        ('all_names', (list,)),
        ('source', (str,)),
        ('path', (str,)),
        ('rel_path', (str,)),
        ('mod_stem', (str,)),
        ('lines', (int,)),
        ('line_ending', (str,)),
        ('docstring', (str, type(None))),
        ('parse_error', (str, type(None))),
        ('is_test', (bool,)),
        ('is_init', (bool,)),
        ('has_future', (bool,)),
        ('has_version', (bool,)),
        ('has_all', (bool,)),
    )
    def __init__(self, path: str, skill_dir: str, ctx=None,
                 *, precompute: bool = True):
        self.path = path
        self.rel_path = os.path.relpath(path, skill_dir)
        self.parse_error: str | None = None
        self._deferred_precompute = False
        self._functions: list[dict] = []
        self._classes: list[dict] = []
        self._imports: list[dict] = []
        self._calls: list[dict] = []
        self._has_future: bool = False
        self._has_version: bool = False
        self._has_all: bool = False
        self._all_names: list[str] = []
        self._docstring: str | None = None
        self.line_ending: str = '\n'
        self._walk_nodes: list | None = None
        self._where_cache: dict | None = None
        basename = os.path.basename(path)
        self.mod_stem = os.path.splitext(basename)[0]
        self.is_init = basename == '__init__.py'
        self.is_test = self._in_test_dir()
        try:
            _ctx_src_failed = False
            self.source, _ctx_src_failed = self._read_source(path, ctx)
            if '\r\n' in self.source:
                self.line_ending = '\r\n'
            elif '\r' in self.source:
                self.line_ending = '\r'
            self.source = self.source.removeprefix('\ufeff')
            self.source = self.source.replace('\r\n', '\n').replace('\r', '\n')
            self.tree = self._parse_tree(path, ctx,
                                         ctx_src_failed=_ctx_src_failed)
            self.lines = count_lines(self.source)
            if precompute:
                self._pre_compute()
                self.is_test = self._classify_test(basename)
            else:
                self.is_test = self._classify_test(basename)
                self._deferred_precompute = True
        except (OSError, UnicodeDecodeError, SyntaxError, LookupError,
                *PARSE_DEGRADE_EXC) as e:
            _log.debug("suppressed entry build failure: %s", e)
            _degrade_entry(self, e)
    @staticmethod
    def _read_source(path: str, ctx) -> tuple[str, bool]:
        if ctx is not None:
            _src = ctx.get_source(path)
            if _src is None:
                return '', True
            return _src, False
        with open(path, 'rb') as _raw:
            _payload = _raw.read()
        _encoding, _ = tokenize.detect_encoding(io.BytesIO(_payload).readline)
        return _payload.decode(_encoding), False
    def _parse_tree(self, path: str, ctx, *, ctx_src_failed: bool):
        if ctx is not None:
            tree = ctx.get_ast(path)
            if tree is None:
                if ctx_src_failed:
                    raise OSError(f"no source available: {path}")
                return ast.parse(self.source, filename=path)
            if ctx_src_failed:
                raise OSError(f"source unavailable while ast cached: {path}")
            return tree
        return ast.parse(self.source, filename=path)
    def _ensure_precomputed(self) -> None:
        if not self._deferred_precompute:
            return
        self._deferred_precompute = False
        try:
            self._pre_compute()
            self.is_test = self._classify_test(os.path.basename(self.path))
        except (OSError, UnicodeDecodeError, SyntaxError, LookupError,
                *PARSE_DEGRADE_EXC) as e:
            _log.debug("suppressed deferred precompute failure: %s", e)
            _degrade_entry(self, e)
    @property
    def functions(self) -> list[dict]:
        self._ensure_precomputed()
        return self._functions
    @property
    def classes(self) -> list[dict]:
        self._ensure_precomputed()
        return self._classes
    @property
    def imports(self) -> list[dict]:
        self._ensure_precomputed()
        return self._imports
    @property
    def calls(self) -> list[dict]:
        self._ensure_precomputed()
        return self._calls
    @property
    def has_future(self) -> bool:
        self._ensure_precomputed()
        return self._has_future
    @property
    def has_version(self) -> bool:
        self._ensure_precomputed()
        return self._has_version
    @property
    def has_all(self) -> bool:
        self._ensure_precomputed()
        return self._has_all
    @property
    def all_names(self) -> list[str]:
        self._ensure_precomputed()
        return self._all_names
    @property
    def docstring(self) -> str | None:
        self._ensure_precomputed()
        return self._docstring
    def _classify_test(self, basename: str) -> bool:
        if self._in_test_dir():
            return True
        if not is_test_source_basename(basename):
            return False
        if self.tree is None:
            return False
        if module_imports_test_framework(self.tree):
            return True
        return self._defines_test_prefixed()
    def _in_test_dir(self) -> bool:
        parts = self.rel_path.replace('\\', '/').split('/')[:-1]
        return any(is_test_dir_candidate(part) for part in parts)
    def _defines_test_prefixed(self) -> bool:
        if self.tree is None:
            return False
        return any(
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name.startswith('test_')
            for node in iter_direct_scope_nodes(
                self.tree, include_class_body=True))
    def walk_nodes(self) -> tuple:
        """返回全部 AST 节点的**不可变**共享视图。

        结果按树身份缓存并被多个检测器复用。返回 ``tuple`` 而非 ``list``
        是刻意防护：任何检测器若尝试 ``.sort()`` / ``.append()`` /
        ``.remove()``，会在调用点直接抛 ``AttributeError``，而不是静默
        污染后续所有检测器看到的节点集合。这类污染不报错、只让其他规则
        漏报，属于最难定位的一类精准性事故。
        """
        if self.tree is None:
            return ()
        if self._walk_nodes is None:
            self._walk_nodes = tuple(shared_walk(self.tree))
        return self._walk_nodes
    def nodes_where(self, types: tuple[type, ...]) -> tuple:
        """按类型筛选节点，结果同 ``walk_nodes`` 一样是不可变共享视图。"""
        types = tuple(types)
        _cache = self._where_cache
        if _cache is None:
            _cache = self._where_cache = {}
        got = _cache.get(types)
        if got is None:
            got = (tuple(n for n in self.walk_nodes() if isinstance(n, types))
                   if self.tree is not None else ())
            _cache[types] = got
        return got
    def _pre_compute(self) -> None:
        if self.tree is None:
            return
        _idx = _build_entry_indexes(self.tree, self.walk_nodes())
        self._docstring = _idx.docstring
        self._functions = _idx.functions
        self._classes = _idx.classes
        self._imports = _idx.imports
        self._calls = _idx.calls
        self._all_names = _idx.all_names
        self._has_future = _idx.has_future
        self._has_version = _idx.has_version
        self._has_all = _idx.has_all
def is_transient_io_error(parse_error) -> bool:
    return isinstance(parse_error, str) and parse_error.startswith("IO:")
def file_content_digest(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, 'rb') as source_file:
        for chunk in iter(lambda: source_file.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()
class FileCache:
    def __init__(self, skill_dir: str, ctx=None):
        self.skill_dir = os.path.abspath(skill_dir)
        self._ctx = ctx
        self._entries: list[FileEntry] = []
        self._by_rel: dict[str, FileEntry] = {}
        self._by_stem: dict[str, FileEntry] = {}
        self._loaded = False
        self._test_dir_entries: list[FileEntry] | None = None
        self.all_functions: dict[str, list[dict]] = {}
        self.all_classes: dict[str, list[dict]] = {}
        self.import_graph: dict[str, set[str]] = defaultdict(set)
        self.internal_mods: set[str] = set()
        self._init_entry: FileEntry | None = None
    _CACHE_FILENAME = '.filecache.json'
    _CACHE_TMP_ORPHAN_GRACE_S = 60.0
    # schema 14: 由 pickle 改为 JSON（CWE-502 安全反序列化）。
    _CACHE_SCHEMA = 14
    def _cache_path(self) -> str:
        cache_dir = get_temp_base(self.skill_dir)
        return os.path.join(cache_dir, self._CACHE_FILENAME)
    def _sweep_orphan_cache_tmp(self, cache_dir: str) -> None:
        try:
            now = time.time()
            for fn in os.listdir(cache_dir):
                fp = self._orphan_cache_tmp(fn, cache_dir, now)
                if fp is not None and safe_delete(fp):
                    _log.info("[TestCore] 已清扫缓存孤儿 tmp: %s", fn)
        except OSError as e:
            _log.debug("_sweep_orphan_cache_tmp: %s", e)
    def _orphan_cache_tmp(self, fn: str, cache_dir: str, now: float) -> str | None:
        prefix = self._CACHE_FILENAME + ".tmp."
        if not fn.startswith(prefix):
            return None
        fp = os.path.join(cache_dir, fn)
        try:
            age = now - os.path.getmtime(fp)
        except OSError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='FileCache._orphan_cache_tmp:OSError')
            return None
        if age < self._CACHE_TMP_ORPHAN_GRACE_S:
            return None
        return fp
    def _read_cache_payload(self, cp: str) -> dict[str, dict] | None:
        # 缓存目录位于工作空间 Temp，可被本地其他进程写入；pickle 反序列化
        # 等于给了写入方一次代码执行机会（CWE-502）。改用 JSON 后即使
        # 内容被篡改，最坏也只是解析失败回退重建。
        with open(cp, encoding='utf-8') as f:
            cached = json.load(f)
        if (not isinstance(cached, dict)
                or cached.get('schema') != self._CACHE_SCHEMA):
            return None
        entries = cached.get('data')
        return entries if isinstance(entries, dict) else {}
    def _try_load_cache(self) -> dict[str, dict]:
        try:
            cache_dir = get_temp_base(self.skill_dir)
            if os.path.isdir(cache_dir):
                self._sweep_orphan_cache_tmp(cache_dir)
            cp = self._cache_path()
            if not os.path.exists(cp):
                return {}
            return self._read_cache_payload(cp) or {}
        except Exception as e:
            _log.debug("[TestCore] 加载缓存失败,返回空: %s", e)
            return {}
    def _save_cache(self, cached: dict[str, dict]) -> None:
        tmp: str | None = None
        try:
            cache_dir = get_temp_base(self.skill_dir)
            os.makedirs(cache_dir, exist_ok=True)
            cp = self._cache_path()
            fd, tmp = tempfile.mkstemp(
                dir=cache_dir, prefix=self._CACHE_FILENAME + '.tmp.')
            current_paths = {e.rel_path for e in self._entries}
            pruned = {k: v for k, v in cached.items()
                      if self._cached_entry_alive(k, current_paths)}
            with os.fdopen(fd, 'w', encoding='utf-8') as f:
                json.dump({'schema': self._CACHE_SCHEMA, 'data': pruned},
                          f, ensure_ascii=False)
            os.replace(tmp, cp)
            tmp = None
        except Exception:
            _log.debug("_save_cache: suppressed", exc_info=True)
            if tmp is not None:
                self._discard_failed_tmp(tmp)
    @staticmethod
    def _safe_rel_key(rel_path: str) -> bool:
        if not rel_path or os.path.isabs(rel_path) or ":" in rel_path:
            return False
        return ".." not in rel_path.replace("\\", "/").split("/")
    def _cached_entry_alive(self, rel_path: str,
                            loaded: set[str]) -> bool:
        if rel_path in loaded:
            return True
        if not self._safe_rel_key(rel_path):
            return False
        return os.path.isfile(os.path.join(self.skill_dir, rel_path))
    @staticmethod
    def _discard_failed_tmp(tmp: str) -> None:
        if safe_delete(tmp):
            return
        try:
            os.remove(tmp)
        except OSError as rm_exc:
            _log.debug("_save_cache: 孤儿 tmp 清理失败（残留待人工回收）: %s: %s",
                       tmp, rm_exc)
    def _restore_or_build_entry(self, fp: str, cached: dict) -> tuple:
        rel_path = os.path.relpath(fp, self.skill_dir)
        try:
            _st = os.stat(fp)
            digest = file_content_digest(fp)
        except OSError:
            _log.debug("load: suppressed OSError", exc_info=True)
            return FileEntry(fp, self.skill_dir, ctx=self._ctx), False
        mtime, size = _st.st_mtime, _st.st_size
        entry, dropped = self._restore_cached_entry(
            cached, rel_path, mtime, size, digest)
        if entry is not None:
            rebound = entry.path != fp or entry.rel_path != rel_path
            if rebound:
                entry.path = fp
                entry.rel_path = rel_path
                entry.mod_stem = os.path.splitext(os.path.basename(fp))[0]
                cached_data = cached.get(rel_path, {}).get('data')
                if isinstance(cached_data, dict):
                    cached_data['path'] = fp
                    cached_data['rel_path'] = rel_path
                    cached_data['mod_stem'] = entry.mod_stem
            return entry, dropped or rebound
        entry = FileEntry(fp, self.skill_dir, ctx=self._ctx)
        stored = self._store_cached_entry(
            cached, rel_path, entry, mtime, size, digest)
        return entry, dropped or stored
    @staticmethod
    def _restore_cached_entry(cached: dict, rel_path: str, mtime: float,
                              size: int, digest: str) -> tuple:
        cached_entry = cached.get(rel_path)
        if not isinstance(cached_entry, dict):
            return None, False
        identity = (cached_entry.get('mtime'), cached_entry.get('size'),
                    cached_entry.get('digest'))
        if identity != (mtime, size, digest):
            return None, False
        data = cached_entry.get('data')
        if not isinstance(data, dict):
            return None, False
        if is_transient_io_error(data.get('parse_error')):
            del cached[rel_path]
            return None, True
        if data.get('tree') is None:
            # JSON 无法序列化 AST：落盘时不存树，回读时按源码重建。
            # 源码解析失败说明缓存不可信，当作未命中重新读盘。
            try:
                data['tree'] = ast.parse(data.get('source') or '')
            except (SyntaxError, ValueError, TypeError):
                del cached[rel_path]
                return None, True
        return _entry_from_cached(FileEntry, data), False
    @staticmethod
    def _store_cached_entry(cached: dict, rel_path: str, entry,
                            mtime: float, size: int, digest: str) -> bool:
        if is_transient_io_error(entry.parse_error):
            return False
        payload = _serialize_entry(entry)
        # 只存源码与派生索引；AST 由 ``_restore_cached_entry`` 重建。
        payload['tree'] = None
        cached[rel_path] = {
            'mtime': mtime,
            'size': size,
            'digest': digest,
            'data': payload,
        }
        return True
    def load(self) -> list[FileEntry]:
        if self._loaded:
            return self._entries
        _t0 = time.monotonic()
        cached = self._try_load_cache()
        cache_updated = False
        for fp in self._load_paths():
            entry, _updated = self._restore_or_build_entry(fp, cached)
            cache_updated = cache_updated or _updated
            self._register_entry(entry)
        cache_updated = cache_updated or self._cache_shrank(cached)
        if cache_updated:
            self._save_cache(cached)
        self._loaded = True
        self._build_global_index()
        write_module_run(
            "diag_testing_source", "FileCache.load",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            entries=len(self._entries),
            cache_updated=bool(cache_updated))
        return self._entries
    def _load_paths(self) -> list:
        if self._ctx is not None:
            return sorted(fp for fp in self._ctx.py_files
                          if in_scope_py_file(fp, self.skill_dir))
        return collect_py_files(self.skill_dir)
    @staticmethod
    def _rel_key(rel_path: str) -> str:
        return str(rel_path or '').replace('\\', '/')
    def _register_entry(self, entry) -> None:
        self._entries.append(entry)
        self._by_rel[self._rel_key(entry.rel_path)] = entry
        if entry.mod_stem:
            self._by_stem[entry.mod_stem] = entry
        if entry.is_init and entry.rel_path == '__init__.py':
            self._init_entry = entry
    def _cache_shrank(self, cached: dict) -> bool:
        if not cached:
            return False
        loaded = {e.rel_path for e in self._entries}
        return any(not self._cached_entry_alive(rel, loaded) for rel in cached)
    def _build_global_index(self) -> None:
        self.internal_mods = {e.mod_stem for e in self._entries if e.mod_stem and not e.is_init}
        for entry in self._entries:
            if entry.tree is None:
                continue
            self.all_functions[entry.rel_path] = entry.functions
            self.all_classes[entry.rel_path] = entry.classes
        self.import_graph = build_import_graph_excluding_lazy(
            self.valid_entries, self.internal_mods)
    @property
    def entries(self) -> list[FileEntry]:
        if not self._loaded:
            self.load()
        return self._entries
    @property
    def test_dir_entries(self) -> list[FileEntry]:
        if self._test_dir_entries is None:
            _t0 = time.monotonic()
            self._test_dir_entries = [
                FileEntry(fp, self.skill_dir, ctx=self._ctx,
                           precompute=False)
                for fp in iter_test_py_files(self.skill_dir)
            ]
            write_module_run(
                "diag_testing_source", "FileCache.test_dir_entries",
                duration_ms=(time.monotonic() - _t0) * 1000.0,
                entries=len(self._test_dir_entries))
        return self._test_dir_entries
    @property
    def valid_entries(self) -> list[FileEntry]:
        return [e for e in self.entries if e.tree is not None]
    def _ensure_loaded(self) -> None:
        if not getattr(self, '_loaded', True):
            self.load()
    def get(self, rel_path: str) -> FileEntry | None:
        self._ensure_loaded()
        return self._by_rel.get(self._rel_key(rel_path))
    def get_by_stem(self, mod_stem: str) -> FileEntry | None:
        self._ensure_loaded()
        return self._by_stem.get(mod_stem)
    @property
    def total_functions(self) -> int:
        self._ensure_loaded()
        return sum(len(funcs) for funcs in self.all_functions.values())
    @property
    def total_classes(self) -> int:
        self._ensure_loaded()
        return sum(len(classes) for classes in self.all_classes.values())
    def get_all_function_names(self) -> set[str]:
        self._ensure_loaded()
        names: set[str] = set()
        for funcs in self.all_functions.values():
            for f in funcs:
                names.add(f['name'])
        for classes in self.all_classes.values():
            for c in classes:
                for m in c.get('methods', ()):
                    names.add(m)
        return names
    @property
    def init_entry(self) -> FileEntry | None:
        if not self._loaded:
            self.load()
        return self._init_entry
def resolve_file_cache(skill_dir, kwargs: dict) -> FileCache | None:
    cache = kwargs.get('_cache')
    if cache is not None:
        return cache
    try:
        skill_path = os.fsdecode(skill_dir)
    except (TypeError, ValueError):
        return None
    if not os.path.isdir(skill_path):
        return None
    cache = FileCache(skill_path)
    cache.load()
    return cache
def entry_module_dotted(entry) -> str:
    rel_path = getattr(entry, 'rel_path', '').replace('\\', '/')
    if not rel_path.lower().endswith('.py'):
        return ''
    parts = rel_path.split('/')
    if parts[-1].lower() == '__init__.py':
        parts.pop()
    else:
        parts[-1] = parts[-1][:-3]
    return '.'.join(part for part in parts if part)
def module_entry_indexes(cache) -> tuple[dict, dict]:
    by_path: dict[str, object] = {}
    by_stem: dict[str, list] = {}
    for entry in cache.valid_entries:
        dotted = entry_module_dotted(entry)
        if dotted or entry_rel_path(entry).replace('\\', '/') == '__init__.py':
            by_path.setdefault(dotted, entry)
        if entry.mod_stem:
            by_stem.setdefault(entry.mod_stem, []).append(entry)
    return by_path, by_stem
def import_node_dotted(node: ast.ImportFrom, own_rel: str, *,
                       root_is_package: bool = False) -> str | None:
    """解析 ``from`` 语句的基模块点分名（与 ``entry_module_dotted`` 同一口径）。

    ``own_rel`` 相对技能根目录；技能根本身是包（根目录带 ``__init__.py``）时
    须传 ``root_is_package=True``，否则子包内 ``from .. import x`` 这类合法的
    上溯到根包的相对导入会被误判为越界而返回 ``None``。
    """
    if not node.level:
        return node.module or None
    package_parts = own_rel.replace('\\', '/').split('/')[:-1]
    ascent = node.level - 1
    max_ascent = (len(package_parts) if root_is_package
                  else max(0, len(package_parts) - 1))
    if ascent > max_ascent:
        return None
    if ascent:
        package_parts = package_parts[:-ascent]
    module_parts = node.module.split('.') if node.module else []
    return '.'.join([*package_parts, *module_parts])
_ROOT_PACKAGE_FLAG_CACHE: dict[str, bool] = {}
_ROOT_PACKAGE_FLAG_CACHE_MAX = 256
def _root_is_package(scan_root: str) -> bool:
    if not scan_root:
        return False
    cached = _ROOT_PACKAGE_FLAG_CACHE.get(scan_root)
    if cached is None:
        cached = os.path.isfile(os.path.join(scan_root, '__init__.py'))
        if len(_ROOT_PACKAGE_FLAG_CACHE) >= _ROOT_PACKAGE_FLAG_CACHE_MAX:
            _ROOT_PACKAGE_FLAG_CACHE.clear()
        _ROOT_PACKAGE_FLAG_CACHE[scan_root] = cached
    return cached
def entry_import_node_dotted(node: ast.ImportFrom, entry) -> str | None:
    """按条目所属技能根是否为包来解析相对导入基模块。"""
    return import_node_dotted(
        node, entry_rel_path(entry),
        root_is_package=_root_is_package(_entry_scan_root(entry)))
_NAMEDEXPR_BINDINGS_MEMO: weakref.WeakKeyDictionary = (
    weakref.WeakKeyDictionary())
_NAMEDEXPR_BINDINGS_LOCK = threading.Lock()
_NAMEDEXPR_BINDINGS_CAP = 8192
def _namedexpr_bindings_of(node: ast.AST) -> frozenset[str]:
    """返回该节点子树内海象表达式（:=）绑定的名字（按节点身份缓存）。

    遍历只读取语法树、结果只与节点子树有关，是纯函数；而它被
    `collect_scope_binding_names` 的每一层调用链反复触发：实测 20,591 次
    调用只对应 2,566 个不同节点（去重率 87.5%，累计 448 ms）。
    """
    with _NAMEDEXPR_BINDINGS_LOCK:
        cached = _NAMEDEXPR_BINDINGS_MEMO.get(node)
    if cached is not None:
        return cached
    names: set[str] = set()
    _walk_namedexpr_bindings(node, names)
    result = frozenset(names)
    with _NAMEDEXPR_BINDINGS_LOCK:
        if len(_NAMEDEXPR_BINDINGS_MEMO) >= _NAMEDEXPR_BINDINGS_CAP:
            _NAMEDEXPR_BINDINGS_MEMO.clear()
        _NAMEDEXPR_BINDINGS_MEMO[node] = result
    return result
def _collect_namedexpr_bindings(node: ast.AST, names: set[str]) -> None:
    names.update(_namedexpr_bindings_of(node))
def _walk_namedexpr_bindings(node: ast.AST, names: set[str]) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        stack = _definition_header_exprs(node)
    else:
        stack = list(ast.iter_child_nodes(node))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            stack.extend(_definition_header_exprs(current))
            continue
        if isinstance(current, ast.NamedExpr):
            names.update(iter_unpack_target_names(current.target))
        stack.extend(ast.iter_child_nodes(current))
def _collect_module_level_bindings(tree: ast.AST, *,
                                  include_imports: bool) -> set[str]:
    names: set[str] = set()
    declared_outer: set[str] = set()
    for node in iter_module_level_stmts(getattr(tree, 'body', [])):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if include_imports:
                names |= import_binds_of(node)
            continue
        collect_scope_binding_names(node, names, declared_outer)
        _collect_namedexpr_bindings(node, names)
        if MATCH_T is not None and isinstance(node, MATCH_T):
            for case in node.cases:
                collect_scope_binding_names(case, names, declared_outer)
    return names
def module_level_bound_names(tree: ast.AST, *,
                              include_imports: bool) -> set[str]:
    if tree is None:
        return set()
    return _collect_module_level_bindings(tree, include_imports=include_imports)
def reuse_or_build_import_graph(cache: FileCache, internal_mods: set):
    _ = cache.entries
    if internal_mods == cache.internal_mods:
        return cache.import_graph
    return build_import_graph_excluding_lazy(cache.valid_entries, internal_mods)
def iter_module_stmts(tree: ast.Module):
    stack: deque[ast.stmt] = deque(tree.body)
    while stack:
        stmt = stack.popleft()
        yield stmt
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        stack.extend(_module_scope_children(stmt))
def _module_scope_children(stmt) -> list[ast.stmt]:
    children: list[ast.stmt] = []
    for child in ast.iter_child_nodes(stmt):
        if isinstance(child, ast.stmt):
            children.append(child)
        elif isinstance(child, _BODY_CONTAINER_TYPES):
            children.extend(child.body)
    return children
def iter_module_level_stmts(stmts: list[ast.AST]):
    tree = ast.Module(body=list(stmts), type_ignores=[])
    nodes = list(iter_module_stmts(tree))
    for node in list(nodes):
        if isinstance(node, (ast.With, ast.AsyncWith)):
            nodes.extend(node.items)
        elif isinstance(node, ast.Try) or (
                TRY_STAR_T and isinstance(node, TRY_STAR_T)):
            nodes.extend(node.handlers)
    def _position(node: ast.AST) -> tuple[int, int]:
        line = getattr(node, 'lineno', None)
        if line is None:
            ctx = getattr(node, 'context_expr', None)
            line = getattr(ctx, 'lineno', 0)
        return line, getattr(node, 'col_offset', 0)
    return iter(sorted(nodes, key=_position))
def collect_module_assign_names(tree: ast.AST) -> set[str]:
    if tree is None:
        return set()
    return _collect_module_level_bindings(tree, include_imports=False)
class _EntryIndexes:
    __slots__ = ('all_names', 'calls', 'classes', 'docstring', 'functions',
                 'has_all', 'has_future', 'has_version', 'imports')
    def __init__(self) -> None:
        self.all_names: list[str] = []
        self.calls: list[dict] = []
        self.classes: list[dict] = []
        self.docstring: str | None = None
        self.functions: list[dict] = []
        self.has_all = False
        self.has_future = False
        self.has_version = False
        self.imports: list[dict] = []
def _dunder_pairs(stmt) -> list:
    if isinstance(stmt, ast.Assign):
        return [(_t, stmt.value) for _t in stmt.targets
                if isinstance(_t, ast.Name)]
    if (isinstance(stmt, ast.AnnAssign)
            and stmt.value is not None
            and isinstance(stmt.target, ast.Name)):
        return [(stmt.target, stmt.value)]
    return []
def _all_value_names(value, previous=()) -> list[str]:
    if isinstance(value, ast.Name) and value.id == '__all__':
        return list(previous)
    if isinstance(value, (ast.List, ast.Tuple)):
        return [_e.value for _e in value.elts
                if isinstance(_e, ast.Constant) and isinstance(_e.value, str)]
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
        return (_all_value_names(value.left, previous)
                + _all_value_names(value.right, previous))
    return []
def _merge_all_states(states) -> list[str]:
    merged: list[str] = []
    seen: set[str] = set()
    for state in states:
        for name in state:
            if name not in seen:
                seen.add(name)
                merged.append(name)
    return merged
def _dunder_update(stmt, all_names) -> tuple[bool, bool, list[str]]:
    has_version = False
    has_all = False
    names = list(all_names)
    for _t, _v in _dunder_pairs(stmt):
        if _t.id == '__version__':
            has_version = True
        elif _t.id == '__all__':
            has_all = True
            names = _all_value_names(_v, all_names)
    if isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
        if stmt.target.id == '__version__':
            has_version = True
        elif (stmt.target.id == '__all__'
              and isinstance(stmt.op, (ast.Add, ast.BitOr))):
            has_all = True
            names = all_names + _all_value_names(stmt.value, all_names)
    if isinstance(stmt, ast.Expr):
        _added = dunder_all_node_names(stmt)
        if _added:
            has_all = True
            names = names + _added
    return has_version, has_all, names
class _ImportTimeBranchView(ast.NodeTransformer):
    def __init__(self, typing_context) -> None:
        self.typing_context = typing_context
    def _visit_stmts(self, stmts) -> list:
        visited = []
        for stmt in stmts:
            result = self.visit(stmt)
            if result is None:
                continue
            if isinstance(result, list):
                visited.extend(result)
            else:
                visited.append(result)
        return visited
    def visit_If(self, node):
        live = _live_if_body(node, self.typing_context)
        if live is None:
            return self.generic_visit(node)
        return self._visit_stmts(live)
    def visit_While(self, node):
        static = static_if_branch(node.test)
        if static is False:
            return self._visit_stmts(node.orelse)
        if static is True:
            node.orelse = []
        return self.generic_visit(node)
def _import_time_branch_view(tree):
    typing_context = collect_typing_tc_bindings(tree)
    needs_view = any(
        (isinstance(node, ast.If)
         and _live_if_body(node, typing_context) is not None)
        or (isinstance(node, ast.While)
            and static_if_branch(node.test) is not None)
        for node in iter_module_stmts(tree))
    if not needs_view:
        return tree
    view = copy.deepcopy(tree)
    return _ImportTimeBranchView(typing_context).visit(view)
class _DunderWalker:
    __slots__ = ('has_all', 'has_version')
    def __init__(self) -> None:
        self.has_version = False
        self.has_all = False
    def walk(self, stmts, initial) -> list[str]:
        names = list(initial)
        for stmt in stmts:
            names = self._step(stmt, names)
        return names
    def _step(self, stmt, names) -> list[str]:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            return names
        branch = _DUNDER_BRANCH_WALKERS.get(stmt.__class__)
        if branch is not None:
            return branch(self, stmt, names)
        return self._walk_simple(stmt, names)
    def _walk_if(self, stmt, names) -> list[str]:
        body_names = self.walk(stmt.body, names)
        else_names = (self.walk(stmt.orelse, names)
                      if stmt.orelse else list(names))
        return _merge_all_states((body_names, else_names))
    def _walk_loop(self, stmt, names) -> list[str]:
        body_names = self.walk(stmt.body, names)
        paths = [names, body_names]
        if stmt.orelse:
            paths.extend((self.walk(stmt.orelse, names),
                          self.walk(stmt.orelse, body_names)))
        return _merge_all_states(paths)
    def _walk_try(self, stmt, names) -> list[str]:
        body_states = [list(names)]
        body_names = list(names)
        for body_stmt in stmt.body:
            body_names = self.walk([body_stmt], body_names)
            body_states.append(body_names)
        handler_start = _merge_all_states(body_states)
        paths = [self.walk(stmt.orelse, body_names)]
        paths.extend(self.walk(handler.body, handler_start)
                     for handler in stmt.handlers)
        if stmt.finalbody:
            paths = [self.walk(stmt.finalbody, path) for path in paths]
        return _merge_all_states(paths)
    def _walk_match(self, stmt, names) -> list[str]:
        paths = [self.walk(case.body, names) for case in stmt.cases]
        if not _match_has_catch_all(stmt.cases):
            paths.append(names)
        return _merge_all_states(paths)
    def _walk_simple(self, stmt, names) -> list[str]:
        has_version, has_all, names = _dunder_update(stmt, names)
        self.has_version = self.has_version or has_version
        self.has_all = self.has_all or has_all
        children = _module_scope_children(stmt)
        return self.walk(children, names) if children else names
def _match_has_catch_all(cases) -> bool:
    match_as = getattr(ast, 'MatchAs', None)
    return any(
        match_as is not None and isinstance(case.pattern, match_as)
        and case.pattern.pattern is None and case.guard is None
        for case in cases)
_DUNDER_BRANCH_WALKERS = {
    ast.If: _DunderWalker._walk_if,
    ast.For: _DunderWalker._walk_loop,
    ast.AsyncFor: _DunderWalker._walk_loop,
    ast.While: _DunderWalker._walk_loop,
    ast.Try: _DunderWalker._walk_try,
    TRY_STAR_T: _DunderWalker._walk_try,
}
if MATCH_T is not None:
    _DUNDER_BRANCH_WALKERS[MATCH_T] = _DunderWalker._walk_match
def _collect_module_dunders(tree) -> tuple[bool, bool, list[str]]:
    view = _import_time_branch_view(tree)
    walker = _DunderWalker()
    local_names = walker.walk(getattr(view, 'body', []), [])
    exports, _exact = collect_module_exports_ordered(view)
    export_names = set(exports)
    all_names = list(dict.fromkeys(
        name for name in local_names if name in export_names))
    all_names.extend(name for name in exports if name not in all_names)
    return walker.has_version, walker.has_all, all_names
def _signature_args(node) -> tuple:
    _args_all = (*node.args.posonlyargs, *node.args.args)
    if node.args.vararg is not None:
        _args_all = (*_args_all, node.args.vararg)
    _args_all = (*_args_all, *node.args.kwonlyargs)
    if node.args.kwarg is not None:
        _args_all = (*_args_all, node.args.kwarg)
    return _args_all
def _annotation_text(node):
    if node is None:
        return None
    try:
        return ast.unparse(node)
    except Exception as e:
        _log.debug("[TestCore] 预计算签名注解失败,降级None: %s", e)
        return None
_MAX_ANNOTATION_STR_DEPTH = 10
def _collect_annotation_refs(node, out: set[str], depth: int = 0) -> None:
    if node is None or depth > _MAX_ANNOTATION_STR_DEPTH:
        return
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        text = node.value.strip()
        if not text:
            return
        try:
            parsed = ast.parse(text, mode='eval').body
        except (SyntaxError, ValueError, TypeError) as _e:
            log_swallowed(__name__, _e,
                          context='collect_string_annotation_refs:parse')
            return
        _collect_annotation_refs(parsed, out, depth + 1)
        return
    if isinstance(node, ast.Name):
        out.add(node.id)
        return
    if isinstance(node, ast.Attribute):
        root_id = first_segment(dotted_name(node))
        if root_id:
            out.add(root_id)
        return
    if (isinstance(node, ast.Subscript)
            and type_last_name(node.value) == 'Literal'):
        _collect_annotation_refs(node.value, out, depth + 1)
        return
    for child in ast.iter_child_nodes(node):
        _collect_annotation_refs(child, out, depth + 1)
def _annotation_nodes(entry):
    for node in entry_nodes(entry):
        if isinstance(node, ast.arg):
            yield node.annotation
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node.returns
        elif isinstance(node, ast.AnnAssign):
            yield node.annotation
def collect_string_annotation_refs(entry) -> set[str]:
    names: set[str] = set()
    for annotation in _annotation_nodes(entry):
        _collect_annotation_refs(annotation, names)
    return names
def _index_function(functions: list, node, func_scopes: dict) -> None:
    func_len = getattr(node, 'end_lineno', node.lineno) - node.lineno + 1
    _args_all = _signature_args(node)
    arg_count = len(_args_all)
    has_annotations = (node.returns is not None or
                       any(a.annotation for a in _args_all))
    is_async = isinstance(node, ast.AsyncFunctionDef)
    _arg_names = [a.arg for a in _args_all]
    _arg_types = [_annotation_text(a.annotation) for a in _args_all]
    _return_annotation = _annotation_text(node.returns)
    functions.append({
        'name': node.name, 'line': node.lineno, 'end_line': getattr(node, 'end_lineno', node.lineno),
        'length': func_len, 'arg_count': arg_count, 'has_annotations': has_annotations,
        'is_async': is_async, 'is_private': node.name.startswith('_'),
        'decorators': [ast.dump(d) for d in node.decorator_list],
        'returns': node.returns is not None,
        'arg_names': _arg_names,
        'arg_types': _arg_types,
        'return_annotation': _return_annotation,
        'scope': func_scopes.get(id(node), ()),
    })
def _index_class(classes: list, node, func_scopes: dict) -> None:
    methods = [n.name for n in iter_class_scope_methods(node)]
    classes.append({
        'name': node.name, 'line': node.lineno,
        'methods': methods, 'method_count': len(methods),
        'decorators': [ast.dump(d) for d in node.decorator_list],
        'bases': [ast.dump(b) for b in node.bases],
        'scope': func_scopes.get(id(node), ()),
    })
def _index_import(imports: list, node, import_idx_by_id: dict) -> None:
    for alias in node.names:
        dep = alias.name.split('.')[0]
        imports.append({
            'name': alias.name, 'dep': dep, 'alias': alias.asname,
            'line': node.lineno, 'type': 'import',
            'type_checking': False,
        })
        import_idx_by_id.setdefault(id(node), []).append(len(imports) - 1)
def _index_import_from(imports: list, node,
                       import_idx_by_id: dict) -> bool:
    is_future = node.module == '__future__' and not node.level
    mod = node.module or ''
    dep = mod.split('.')[0]
    for alias in node.names:
        imports.append({
            'name': f'{mod}.{alias.name}' if mod else alias.name,
            'dep': dep, 'alias': alias.asname,
            'line': node.lineno, 'type': 'from', 'module': mod,
            'type_checking': False,
        })
        import_idx_by_id.setdefault(id(node), []).append(len(imports) - 1)
    return is_future
def _index_call(calls: list, node) -> None:
    func_name = ''
    func_module = ''
    if isinstance(node.func, ast.Name):
        func_name = node.func.id
    elif isinstance(node.func, ast.Attribute):
        func_name = node.func.attr
        func_module = dotted_name(node.func.value) or ast.unparse(node.func.value)
    calls.append({
        'name': func_name, 'module': func_module,
        'line': node.lineno, 'column': node.col_offset,
    })
def _index_node(acc: _EntryIndexes, node, func_scopes: dict,
                import_idx_by_id: dict) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _index_function(acc.functions, node, func_scopes)
        return
    if isinstance(node, ast.ClassDef):
        _index_class(acc.classes, node, func_scopes)
        return
    if isinstance(node, ast.Import):
        _index_import(acc.imports, node, import_idx_by_id)
        return
    if isinstance(node, ast.ImportFrom):
        if _index_import_from(acc.imports, node, import_idx_by_id):
            acc.has_future = True
        return
    if isinstance(node, ast.Call):
        _index_call(acc.calls, node)
def _build_entry_indexes(tree, nodes) -> _EntryIndexes:
    acc = _EntryIndexes()
    acc.docstring = ast.get_docstring(tree)
    acc.has_version, acc.has_all, acc.all_names = _collect_module_dunders(tree)
    func_scopes = collect_func_scopes(tree)
    import_idx_by_id: dict[int, list[int]] = {}
    _typing_refs, _tc_binds = collect_typing_tc_bindings(nodes)
    for node in nodes:
        _index_node(acc, node, func_scopes, import_idx_by_id)
    tc_node_ids = set()
    for _if in nodes:
        static_body = type_checking_static_body(
            _if, _typing_refs, _tc_binds)
        if static_body is not None:
            tc_node_ids.update(
                id(_c) for _stmt in static_body for _c in walk_nodes(_stmt))
    for _nid in tc_node_ids.intersection(import_idx_by_id):
        for _i in import_idx_by_id[_nid]:
            acc.imports[_i]['type_checking'] = True
    return acc
def _serialize_entry(entry) -> dict:
    return {key: getattr(entry, entry._SLOT_BY_KEY.get(key, key))
            for key in entry._SER_KEYS}
def _entry_from_cached(cls, data: dict):
    if (not isinstance(data, dict)
            or not all(k in data for k in cls._SER_KEYS)):
        return None
    for _key, _types in cls._SER_TYPE_CONTRACT:
        if not isinstance(data.get(_key), _types):
            return None
    entry = cls.__new__(cls)
    for slot in ('_walk_nodes', '_where_cache'):
        setattr(entry, slot, None)
    entry._deferred_precompute = False
    for key in cls._SER_KEYS:
        setattr(entry, cls._SLOT_BY_KEY.get(key, key), data.get(key))
    return entry
_IO_ERROR_TYPES = (OSError, UnicodeDecodeError)
_AST_PARSE_SOFT_ERRORS = PARSE_DEGRADE_EXC
_ANNOTATION_PARSE_ERRORS = _IO_ERROR_TYPES + PARSE_DEGRADE_EXC
def _parse_error_prefix(e: BaseException) -> str:
    if isinstance(e, _IO_ERROR_TYPES):
        return "IO"
    return type(e).__name__
def _degrade_entry(entry, e: BaseException) -> None:
    entry.source = ''
    entry.tree = None
    entry.lines = 0
    basename = os.path.basename(getattr(entry, 'path', '') or '')
    entry.mod_stem = os.path.splitext(basename)[0]
    entry.parse_error = f"{_parse_error_prefix(e)}: {e}"
    entry._docstring = None
    entry._functions = []
    entry._classes = []
    entry._imports = []
    entry._calls = []
    entry._all_names = []
    entry._has_future = False
    entry._has_version = False
    entry._has_all = False
    entry._walk_nodes = None
    entry._where_cache = None
    entry._deferred_precompute = False
def entry_nodes(entry: Any) -> Iterator[ast.AST]:
    _wn = getattr(entry, 'walk_nodes', None)
    if _wn is not None:
        return _wn()
    _tree = getattr(entry, 'tree', None)
    if _tree is None:
        return []
    return walk_nodes(_tree)
def entry_rel_path(entry) -> str:
    _v = getattr(entry, 'rel_path', '')
    return _v if isinstance(_v, str) else ''
def entry_calls(entry: Any) -> Any:
    return getattr(entry, 'calls', None)
def entry_lines(entry) -> int:
    _lines = getattr(entry, 'lines', None)
    return _lines if isinstance(_lines, int) else 0
def entry_used_names(entry) -> set[str]:
    used: set[str] = set()
    for node in entry_nodes(entry):
        if isinstance(node, ast.Name):
            if isinstance(getattr(node, 'ctx', None), ast.Load):
                used.add(node.id)
        elif isinstance(node, ast.Attribute):
            used.add(node.attr)
    return used
FUNCTION_SCOPE_CONTAINERS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def entry_class_method_ids(entry) -> frozenset[int]:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return frozenset()
    boundary = (*FUNCTION_SCOPE_CONTAINERS, ast.ClassDef)
    parents: dict[int, ast.AST] = {}
    for node in entry_nodes(entry):
        for child in ast.iter_child_nodes(node):
            parents[id(child)] = node
    method_ids: set[int] = set()
    for _fn in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _cur: ast.AST = _fn
        while id(_cur) in parents:
            _parent = parents[id(_cur)]
            if isinstance(_parent, boundary):
                if isinstance(_parent, ast.ClassDef):
                    method_ids.add(id(_fn))
                break
            _cur = _parent
    return frozenset(method_ids)
def nodes_where(entry, types: tuple[type, ...]) -> tuple:
    _nw = getattr(entry, 'nodes_where', None)
    if _nw is not None:
        return _nw(types)
    return tuple(n for n in entry_nodes(entry) if isinstance(n, types))
def node_first_line(node: ast.AST) -> int:
    _line = getattr(node, 'lineno', None)
    return _line if isinstance(_line, int) else 1
_COMPREHENSION_NODE_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                             ast.GeneratorExp)
def iter_direct_scope_nodes(scope: ast.AST, *,
                            include_class_body: bool = False):
    stack = list(ast.iter_child_nodes(scope))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node
            continue
        if isinstance(node, (ast.Lambda,) + _COMPREHENSION_NODE_TYPES):
            continue
        if isinstance(node, ast.ClassDef):
            yield node
            if include_class_body:
                stack.extend(ast.iter_child_nodes(node))
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def collect_scope_binding_names(node: ast.AST, names: set,
                                declared_outer: set) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        names.add(node.name)
    if _TYPE_ALIAS_T is not None and isinstance(node, _TYPE_ALIAS_T):
        alias_name = getattr(node, 'name', None)
        if isinstance(alias_name, ast.Name):
            names.add(alias_name.id)
    if isinstance(node, ast.Assign):
        for _t in node.targets:
            names.update(iter_unpack_target_names(_t))
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        names.update(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.AugAssign, ast.For, ast.AsyncFor,
                         ast.comprehension)):
        names.update(iter_unpack_target_names(node.target))
    if isinstance(node, ast.withitem) and node.optional_vars is not None:
        names.update(iter_unpack_target_names(node.optional_vars))
    if isinstance(node, ast.ExceptHandler) and node.name:
        names.add(node.name)
    if MATCH_CASE_T is not None and isinstance(node, MATCH_CASE_T):
        names.update(iter_pattern_capture_names(node.pattern))
    if isinstance(node, ast.NamedExpr):
        names.update(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        declared_outer.update(node.names)
def import_binding_names(node: ast.AST) -> tuple[set[str], bool]:
    if isinstance(node, ast.ImportFrom):
        names = {alias.asname or alias.name
                 for alias in node.names if alias.name != '*'}
        return names, any(alias.name == '*' for alias in node.names)
    if isinstance(node, ast.Import):
        return {alias.asname or alias.name.split('.')[0]
                for alias in node.names}, False
    return set(), False
def container_names_of_stmt(stmt: ast.AST) -> set[str]:
    if not isinstance(stmt, ast.Assign) and not (
            isinstance(stmt, ast.AnnAssign) and stmt.value is not None):
        return set()
    names: set[str] = set()
    declared_outer: set[str] = set()
    collect_scope_binding_names(stmt, names, declared_outer)
    return names - declared_outer
def scope_direct_bindings(scope: ast.AST) -> set[str]:
    names: set[str] = set()
    declared_outer: set[str] = set()
    for node in iter_direct_scope_nodes(scope):
        collect_scope_binding_names(node, names, declared_outer)
        if (isinstance(scope, FUNCTION_SCOPE_CONTAINERS)
                and isinstance(node, ast.AnnAssign) and node.value is None):
            names.update(iter_unpack_target_names(node.target))
        if isinstance(node, ast.stmt):
            _collect_namedexpr_bindings(node, names)
    return names - declared_outer
def _definition_header_exprs(node) -> list[ast.AST]:
    exprs: list[ast.AST] = []
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        exprs.extend(node.decorator_list)
        exprs.extend(node.args.defaults)
        exprs.extend(item for item in node.args.kw_defaults if item is not None)
        for arg in (*node.args.posonlyargs, *node.args.args,
                    *node.args.kwonlyargs):
            if arg.annotation is not None:
                exprs.append(arg.annotation)
        for arg in (node.args.vararg, node.args.kwarg):
            if arg is not None and arg.annotation is not None:
                exprs.append(arg.annotation)
        if node.returns is not None:
            exprs.append(node.returns)
    elif isinstance(node, ast.Lambda):
        exprs.extend(node.args.defaults)
        exprs.extend(item for item in node.args.kw_defaults if item is not None)
    elif isinstance(node, ast.ClassDef):
        exprs.extend(node.decorator_list)
        exprs.extend(node.bases)
        exprs.extend(item.value for item in node.keywords)
    return exprs
def _scope_shadow_names(scope) -> set[str]:
    names = scope_direct_bindings(scope)
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        names |= collect_param_names(scope)
    for node in iter_direct_scope_nodes(scope):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names.update(import_binding_names(node)[0])
    return names
def _comprehension_loads(comp, shadowed: set[str], names: set[str]) -> None:
    inner = set(shadowed)
    for gen in comp.generators:
        _collect_scope_loads([gen.iter], inner, names)
        inner.update(iter_unpack_target_names(gen.target))
        _collect_scope_loads(gen.ifs, inner, names)
    tail = [comp.key, comp.value] if isinstance(comp, ast.DictComp) \
        else [comp.elt]
    _collect_scope_loads(tail, inner, names)
def _collect_scope_loads(nodes, shadowed: set[str], names: set[str]) -> None:
    stack: list[ast.AST] = list(nodes)
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Name):
            if isinstance(current.ctx, ast.Load) and current.id not in shadowed:
                names.add(current.id)
            continue
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            _collect_scope_loads(_definition_header_exprs(current),
                                 shadowed, names)
            body = ([current.body] if isinstance(current, ast.Lambda)
                    else current.body)
            _collect_scope_loads(body,
                                 shadowed | _scope_shadow_names(current), names)
            continue
        if isinstance(current, _COMPREHENSION_NODE_TYPES):
            _comprehension_loads(current, shadowed, names)
            continue
        stack.extend(ast.iter_child_nodes(current))
def own_scope_loaded_names(node) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        body = list(node.body)
    elif isinstance(node, ast.Lambda):
        body = [node.body]
    else:
        body = [node]
    names: set[str] = set()
    _collect_scope_loads(body, set(), names)
    return names
def iter_module_binding_nodes(tree: ast.Module):
    stack = list(ast.iter_child_nodes(tree))
    stack.reverse()
    while stack:
        cur = stack.pop()
        yield cur
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef)):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
def iter_own_scope_nodes(node: ast.AST):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        queue = deque(node.body)
    elif isinstance(node, ast.Lambda):
        queue = deque((node.body,))
    else:
        queue = deque(ast.iter_child_nodes(node))
    while queue:
        cur = queue.popleft()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Lambda)):
            continue
        yield cur
        queue.extend(ast.iter_child_nodes(cur))
def qualified_name(scope, name: str) -> str:
    return '.'.join((*scope, name))
def collect_func_scopes(tree: ast.Module) -> dict[int, tuple[str, ...]]:
    scopes: dict[int, tuple[str, ...]] = {}
    stack: list[tuple[ast.AST, tuple[str, ...]]] = [(tree, ())]
    while stack:
        node, path = stack.pop()
        for _ch in ast.iter_child_nodes(node):
            if isinstance(_ch, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)):
                scopes[id(_ch)] = path
                stack.append((_ch, (*path, _ch.name)))
            else:
                stack.append((_ch, path))
    return scopes
_FUNC_DEF_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
def _build_entry_import_edges(entry, internal_mods: set[str], graph,
                              recorder=None, internal_dotted=None) -> None:
    _typing_refs, _tc_binds = collect_typing_tc_bindings(
        iter_module_binding_nodes(entry.tree))
    stack: list[tuple[ast.AST, int]] = [(entry.tree, 0)]
    while stack:
        node, _fd = stack.pop()
        if (isinstance(node, ast.ImportFrom) and node.level
                and entry_import_node_dotted(node, entry) is None):
            continue
        _tc_static_body = (
            type_checking_static_body(node, _typing_refs, _tc_binds)
            if isinstance(node, ast.If) else None)
        if isinstance(node, _FUNC_DEF_TYPES):
            _fd += 1
        elif _fd == 0 and _tc_static_body is None:
            if recorder is None:
                record_module_import(
                    node, internal_mods, entry.mod_stem, graph,
                    internal_dotted=internal_dotted)
            else:
                recorder(node)
        _push_import_children(node, _fd, _tc_static_body, stack)
def _live_import_branch(node, tc_static_body):
    if isinstance(node, ast.While):
        static = static_if_branch(node.test)
        if static is False:
            return node.orelse
        if static is True:
            return node.body
        return None
    if not isinstance(node, ast.If):
        return None
    if tc_static_body is not None:
        return node.orelse if tc_static_body is node.body else node.body
    if is_main_entry_guard(node):
        return main_guard_live_body(node)
    static = static_if_branch(node.test)
    if static is None:
        return None
    return node.body if static else node.orelse
def _has_mod_stem_collision(entries: list) -> bool:
    counts: dict[str, int] = {}
    for entry in entries:
        stem = getattr(entry, 'mod_stem', '')
        if stem and stem != '__init__':
            counts[stem] = counts.get(stem, 0) + 1
    return any(count > 1 for count in counts.values())
def _qualified_entry_graph_key(entry) -> str:
    dotted = entry_module_dotted(entry).removeprefix('src.')
    return dotted or entry.mod_stem
def _entry_scan_root(entry) -> str:
    parts = [part for part in entry_rel_path(entry).replace('\\', '/').split('/')
             if part and part != '.']
    root = os.path.dirname(getattr(entry, 'path', '') or '')
    for _part in parts[:-1]:
        root = os.path.dirname(root)
    return root
def _runtime_import_module_names(entries) -> set[str]:
    names: set[str] = set()
    for entry in entries:
        if entry.mod_stem == '__init__':
            continue
        raw_dotted = entry_module_dotted(entry)
        root_name = os.path.basename(_entry_scan_root(entry))
        for dotted in {raw_dotted, raw_dotted.removeprefix('src.')}:
            if not dotted:
                continue
            names.add(dotted)
            if root_name:
                names.add(f'{root_name}.{dotted}')
    return names
def _add_qualified_import_edge(graph, source: str, raw_name: str,
                               internal_keys: set[str]) -> None:
    raw_name = raw_name.removeprefix('src.')
    if not raw_name:
        return
    matches = {key for key in internal_keys if key == raw_name}
    if not matches:
        matches = {key for key in internal_keys
                   if key.endswith('.' + raw_name)}
    for target in matches:
        if target != source:
            graph[source].add(target)
def _record_qualified_import(node: ast.AST, entry, source: str,
                             internal_keys: set[str], graph) -> None:
    if isinstance(node, ast.Import):
        raw_names = [alias.name for alias in node.names]
    elif isinstance(node, ast.ImportFrom):
        base = entry_import_node_dotted(node, entry) or ''
        raw_names = [base] if node.module else []
        raw_names.extend(
            f'{base}.{alias.name}' if base else alias.name
            for alias in node.names)
    else:
        return
    for raw_name in raw_names:
        _add_qualified_import_edge(graph, source, raw_name, internal_keys)
def _build_qualified_import_graph(entries: list,
                                    graph: defaultdict[str, set[str]]):
    keys_by_entry = {id(entry): _qualified_entry_graph_key(entry)
                     for entry in entries}
    internal_keys = set(keys_by_entry.values())
    for entry in entries:
        if entry.mod_stem == '__init__':
            continue
        source = keys_by_entry[id(entry)]
        _build_entry_import_edges(
            entry, internal_keys, graph,
            recorder=lambda node, current=entry, source_key=source:
                _record_qualified_import(
                    node, current, source_key, internal_keys, graph))
    return graph
def build_import_graph_excluding_lazy(entries, internal_mods: set[str]) -> defaultdict[str, set[str]]:
    entries = list(entries)
    valid_entries = [entry for entry in entries if entry.tree is not None]
    graph: defaultdict[str, set[str]] = defaultdict(set)
    if _has_mod_stem_collision(valid_entries):
        return _build_qualified_import_graph(valid_entries, graph)
    internal_dotted = _runtime_import_module_names(valid_entries)
    for entry in valid_entries:
        if entry.mod_stem == '__init__':
            continue
        _build_entry_import_edges(
            entry, internal_mods, graph, internal_dotted=internal_dotted)
    return graph
def _push_import_children(node, func_depth: int,
                          tc_static_body, stack: list) -> None:
    _live = _live_import_branch(node, tc_static_body)
    if _live is None:
        for _c in ast.iter_child_nodes(node):
            stack.append((_c, func_depth))
        return
    stack.append((node.test, func_depth))
    for _c in _live:
        stack.append((_c, func_depth))
def record_module_import(node: ast.AST, internal_mods: set[str],
                          mod_stem: str,
                          graph: defaultdict[str, set[str]], *,
                          internal_dotted=None) -> None:
    if isinstance(node, ast.ImportFrom):
        _record_from_import(
            node, internal_mods, mod_stem, graph,
            internal_dotted=internal_dotted)
        return
    if isinstance(node, ast.Import):
        for _alias in node.names:
            _add_import_edge(
                graph, mod_stem, _alias.name, internal_mods,
                internal_dotted=internal_dotted)
def _record_from_import(node: ast.ImportFrom, internal_mods: set[str],
                        mod_stem: str, graph, *, internal_dotted=None) -> None:
    dotted_context = internal_dotted if not node.level else None
    if node.module:
        _add_import_edge(
            graph, mod_stem, node.module, internal_mods,
            internal_dotted=dotted_context)
        if node.module.rsplit('.', maxsplit=1)[-1] in internal_mods:
            return
        for _alias in node.names:
            raw_name = (f'{node.module}.{_alias.name}'
                        if dotted_context is not None else _alias.name)
            _add_import_edge(
                graph, mod_stem, raw_name, internal_mods,
                internal_dotted=dotted_context)
        return
    if (node.level or 0) > 0:
        for _alias in node.names:
            _add_import_edge(graph, mod_stem, _alias.name, internal_mods)
def _add_import_edge(graph, mod_stem: str, raw_name: str,
                     internal_mods: set[str], *, internal_dotted=None) -> None:
    if (internal_dotted is not None and '.' in raw_name
            and raw_name not in internal_dotted
            and raw_name.removeprefix('src.') not in internal_dotted):
        return
    leaf = raw_name.rsplit('.', maxsplit=1)[-1]
    if leaf in internal_mods and leaf != mod_stem:
        graph[mod_stem].add(leaf)
def collect_typing_tc_bindings(source) -> tuple[set[str], set[str]]:
    tree = (source if isinstance(source, ast.Module)
            else ast.Module(body=[n for n in source
                                  if isinstance(n, ast.stmt)],
                            type_ignores=[]))
    return (typing_guard_aliases(tree),
            typing_type_checking_names(tree) | {'TYPE_CHECKING'})
def is_main_entry_guard(node: ast.AST) -> bool:
    return isinstance(node, ast.If) and is_main_check(node.test)
def _prod_prune_view(skill_dir: str) -> frozenset[str]:
    if os.path.isfile(os.path.join(skill_dir, 'SKILL.md')):
        return SCAN_COLLECT_PRUNE_DIRS_LOWER | TEST_ARTIFACT_DIRS
    return scan_prune_dirs(skill_dir) | TEST_ARTIFACT_DIRS
def _is_prod_scan_file(rel_path: str, prune: frozenset[str]) -> bool:
    parts = rel_path.replace('\\', '/').split('/')
    if not parts or not is_scan_py_name(parts[-1]):
        return False
    if is_test_source_basename(parts[-1]):
        return False
    return not any(is_pruned_scan_dir(part, prune) for part in parts[:-1])
def _nested_layout_skip(skill_dir: str) -> frozenset[str]:
    skip = _prod_prune_view(skill_dir)
    if os.path.isfile(os.path.join(skill_dir, 'SKILL.md')):
        return skip | {'references', 'assets'}
    return skip
def skill_has_nested_sources(skill_dir: str) -> bool:
    root_init = os.path.join(skill_dir, '__init__.py')
    has_root_init = os.path.isfile(root_init)
    nested = _has_nested_py_sources(skill_dir, include_root=not has_root_init)
    if not has_root_init:
        return nested
    if not nested:
        return False
    return not _root_init_has_api_face(root_init)
def _has_nested_py_sources(skill_dir: str, *, include_root: bool = False) -> bool:
    root_abs = os.path.normcase(os.path.abspath(skill_dir))
    prune = _nested_layout_skip(skill_dir)
    for _root, dirs, files in os.walk(skill_dir):
        dirs[:] = [d for d in dirs if not is_pruned_scan_dir(d, prune)]
        in_root = os.path.normcase(os.path.abspath(_root)) == root_abs
        for name in files:
            if not is_py_source_file(name) or is_test_source_basename(name):
                continue
            if in_root and not include_root:
                continue
            return True
    return False
def _assignment_target_names(node: ast.AST) -> list[str]:
    if _TYPE_ALIAS_T is not None and isinstance(node, _TYPE_ALIAS_T):
        targets = [node.name]
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        targets = [node.target]
    else:
        targets = list(getattr(node, 'targets', None) or ())
    names: list[str] = []
    stack = list(targets)
    while stack:
        target = stack.pop()
        if isinstance(target, ast.Name):
            names.append(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            stack.extend(target.elts)
        elif isinstance(target, ast.Starred):
            stack.append(target.value)
    return names
def _root_init_node_has_api_face(node: ast.stmt) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return not node.name.startswith('_')
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        if (isinstance(node, ast.ImportFrom)
                and node.module == '__future__' and not node.level):
            return False
        names, star_import = import_binding_names(node)
        return star_import or any(
            not name.startswith('_') for name in names)
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return False
    if (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign))
            or (_TYPE_ALIAS_T is not None and isinstance(node, _TYPE_ALIAS_T))):
        return any(not name.startswith('_')
                   for name in _assignment_target_names(node))
    return False
def _root_init_has_api_face(init_path: str) -> bool:
    try:
        source, _fingerprint = read_source_with_fingerprint(init_path)
    except (OSError, ValueError, UnicodeDecodeError) as exc:
        log_swallowed(__name__, exc, context='_root_init_has_api_face:read')
        return True
    if not isinstance(source, str) or not source.strip():
        return False
    try:
        tree = ast.parse(source, filename=init_path)
    except _AST_PARSE_SOFT_ERRORS as exc:
        log_swallowed(__name__, exc, context='_root_init_has_api_face:parse')
        return True
    export_names, _exact = collect_module_exports_ordered(tree)
    return bool(export_names) or any(
        _root_init_node_has_api_face(node) for node in tree.body)
def collect_py_files(skill_dir: str, exclude_init: bool = False) -> list[str]:
    files = sorted(collect_py_files_default(skill_dir))
    if not exclude_init:
        return files
    return [p for p in files if os.path.basename(p) != '__init__.py']
def in_scope_py_file(fp: str, skill_dir: str) -> bool:
    try:
        rel_path = os.path.relpath(fp, skill_dir)
    except ValueError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='in_scope_py_file:ValueError')
        return False
    if os.path.isabs(rel_path) or '..' in rel_path.replace('\\', '/').split('/'):
        return False
    return _is_prod_scan_file(rel_path, _prod_prune_view(skill_dir))
def _root_test_container_map(root: str) -> dict[str, str]:
    try:
        entries = sorted(os.listdir(root))
    except OSError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context='_root_test_container_map:OSError')
        return {}
    actual: dict[str, str] = {}
    for entry in entries:
        path = os.path.join(root, entry)
        if os.path.isdir(path):
            actual.setdefault(entry.lower(), path)
    return actual
def _nested_test_dirs(root: str, known: frozenset[str] = frozenset()
                      ) -> list[str]:
    found: list[str] = []
    prune = scan_prune_dirs(root)
    for current, dirs, _files in os.walk(root):
        if os.path.normcase(os.path.abspath(current)) in known:
            dirs[:] = []
            continue
        if is_test_dir_candidate(os.path.basename(current)):
            found.append(current)
            dirs[:] = []
            continue
        dirs[:] = sorted(d for d in dirs if not is_pruned_scan_dir(d, prune))
    return found
def iter_test_dirs(project_root: str) -> list[str]:
    if not project_root or not os.path.isdir(project_root):
        return []
    root = os.path.abspath(project_root)
    actual = _root_test_container_map(root)
    ordered = [actual[name] for name in TEST_DIR_CANDIDATES if name in actual]
    known = frozenset(os.path.normcase(os.path.abspath(path))
                      for path in ordered)
    return ordered + _nested_test_dirs(root, known)
def _root_py_names(root: str) -> list[str]:
    try:
        names = sorted(os.listdir(root))
    except OSError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_root_py_names:OSError')
        return []
    return [name for name in names
            if is_py_source_file(name)
            and os.path.isfile(os.path.join(root, name))]
def resolve_tests_dir(project_root: str,
                      tests_dir: str | None = None) -> str | None:
    if not project_root or not os.path.isdir(project_root):
        return None
    root = os.path.abspath(project_root)
    if tests_dir is not None:
        explicit = str(tests_dir)
        return (explicit if os.path.isabs(explicit)
                else os.path.join(root, explicit))
    containers = iter_test_dirs(root)
    if containers:
        return containers[0]
    if any(is_test_source_basename(name) for name in _root_py_names(root)):
        return root
    return None
def iter_test_py_files(skill_dir: str) -> Iterator[str]:
    if not skill_dir or not os.path.isdir(skill_dir):
        return
    prune = scan_prune_dirs(skill_dir)
    for root, dirs, filenames in os.walk(skill_dir):
        dirs[:] = sorted(d for d in dirs if not is_pruned_scan_dir(d, prune))
        rel_root = os.path.relpath(root, skill_dir)
        in_test_tree = (rel_root != os.curdir and any(
            is_test_dir_candidate(part)
            for part in rel_root.split(os.sep)
        ))
        for fname in sorted(filenames):
            if not is_scan_py_name(fname):
                continue
            if in_test_tree or is_test_source_basename(fname):
                yield os.path.join(root, fname)
def get_internal_modules(skill_dir: str) -> set[str]:
    result = set()
    for py in collect_py_files(skill_dir, exclude_init=True):
        result.add(os.path.splitext(os.path.basename(py))[0])
    return result
_SAFETY_TEST_PATTERNS = frozenset({
    "test_security", "test_injection", "test_xss",
    "test_sql", "assertsec", "security_test",
})
def annotate_safety_finding(f: dict, filepath: str) -> None:
    source = read_source(filepath) if os.path.isfile(filepath) else None
    if source is None:
        _log.warning("[XV_Mutation] 变异安全注解跳过（源码不可读）: %s",
                     filepath)
        return
    f["_mutation_annotation_done"] = True
    f["_mutation_safety_has_tests"] = any(
        p in source.lower() for p in _SAFETY_TEST_PATTERNS)
def _function_span(node) -> tuple[int, int]:
    start = definition_start_line(node)
    end = getattr(node, 'end_lineno', None)
    if not isinstance(end, int) or isinstance(end, bool) or end < start:
        end = start
    return start, end
def _innermost_function_at(tree: ast.AST, line: int):
    if not isinstance(line, int) or isinstance(line, bool):
        return None
    candidates: list[tuple[int, object]] = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        start, end = _function_span(node)
        if start <= line <= end:
            candidates.append((end - start, node))
    if not candidates:
        return None
    return min(candidates, key=lambda item: item[0])[1]
def parse_python_file(filepath: str) -> ast.AST:
    source = read_source(filepath)
    if source is None:
        raise OSError(f"源码不可读: {filepath}")
    return parse_cached(source, filename=filepath)
def annotate_complexity_finding(f: dict, filepath: str, line: int) -> None:
    try:
        tree = parse_python_file(filepath)
    except _ANNOTATION_PARSE_ERRORS as e:
        _log.warning("[XV_Mutation] 变异复杂度注解跳过（源码不可用）: %s: %s",
                     filepath, e)
        return
    target_node = _innermost_function_at(tree, line)
    f["_mutation_annotation_done"] = True
    f["_mutation_complexity_score"] = (
        cyclomatic_complexity(target_node, iter_own_nodes)
        if target_node is not None else 0)
def find_function_boundary(
    filepath: str, line: int
) -> tuple[str, int, int]:
    try:
        tree = parse_python_file(filepath)
    except _ANNOTATION_PARSE_ERRORS as e:
        _log.warning("[XV_Mutation] 解析源码失败,返回空边界: %s: %s", filepath, e)
        return ("", 0, 0)
    innermost = _innermost_function_at(tree, line)
    if innermost is not None:
        start, end = _function_span(innermost)
        return (innermost.name, start, end)
    return ("", 0, 0)
def main_guard_live_body(node: ast.If) -> list[ast.stmt] | None:
    branch = main_guard_branch(node.test)
    if branch is None:
        return None
    return node.orelse if branch else node.body
def _class_header_exprs(node: ast.ClassDef):
    yield from node.decorator_list
    yield from node.bases
    yield from (kw.value for kw in node.keywords)
def static_if_branch(test: ast.expr) -> bool | None:
    if isinstance(test, ast.Constant):
        return bool(test.value)
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        branch = static_if_branch(test.operand)
        return None if branch is None else not branch
    if is_type_checking_guard(test):
        return False
    return None
def _live_if_body(node: ast.If, typing_context) -> list[ast.stmt] | None:
    if typing_context is not None:
        tc_static_body = type_checking_static_body(node, *typing_context)
        if tc_static_body is not None:
            return node.orelse if tc_static_body is node.body else node.body
    _live = main_guard_live_body(node)
    if _live is not None:
        return _live
    _static = static_if_branch(node.test)
    if _static is None:
        return None
    return node.body if _static else node.orelse
def _iter_if_executed_stmts(node: ast.If, typing_context):
    _live = _live_if_body(node, typing_context)
    if _live is not None:
        yield from _iter_executed_stmts(_live, typing_context)
        return
    yield node.test
    yield from _iter_executed_stmts(node.body, typing_context)
    yield from _iter_executed_stmts(node.orelse, typing_context)
def _iter_try_executed_stmts(node, typing_context):
    for _handler in node.handlers:
        if _handler.type is not None:
            yield _handler.type
        yield from _iter_executed_stmts(_handler.body, typing_context)
    yield from _iter_executed_stmts(node.body, typing_context)
    yield from _iter_executed_stmts(node.orelse, typing_context)
    yield from _iter_executed_stmts(node.finalbody, typing_context)
def _iter_match_executed_stmts(node, typing_context):
    yield node.subject
    for _case in node.cases:
        if _case.guard is not None:
            yield _case.guard
        yield from _iter_executed_stmts(_case.body, typing_context)
def _iter_executed_stmts(body: list[ast.stmt], typing_context=None):
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node
        elif isinstance(node, ast.ClassDef):
            yield from _class_header_exprs(node)
            yield from _iter_executed_stmts(node.body, typing_context)
        elif isinstance(node, ast.If):
            yield from _iter_if_executed_stmts(node, typing_context)
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            yield node.target
            yield node.iter
            yield from _iter_executed_stmts(node.body, typing_context)
            yield from _iter_executed_stmts(node.orelse, typing_context)
        elif isinstance(node, ast.While):
            yield node.test
            static = static_if_branch(node.test)
            if static is not False:
                yield from _iter_executed_stmts(node.body, typing_context)
            if static is not True:
                yield from _iter_executed_stmts(node.orelse, typing_context)
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            yield from node.items
            yield from _iter_executed_stmts(node.body, typing_context)
        elif isinstance(node, (ast.Try, TRY_STAR_T)):
            yield from _iter_try_executed_stmts(node, typing_context)
        elif MATCH_T is not None and isinstance(node, MATCH_T):
            yield from _iter_match_executed_stmts(node, typing_context)
        else:
            yield node
def _iter_default_exprs(args: ast.arguments):
    yield from args.defaults
    yield from (kw for kw in args.kw_defaults if kw is not None)
def _funcdef_annotations(node: ast.FunctionDef):
    _ann = list(node.args.posonlyargs) + list(node.args.args) \
        + list(node.args.kwonlyargs)
    _va = node.args.vararg
    if _va is not None:
        _ann.append(_va)
    _vk = node.args.kwarg
    if _vk is not None:
        _ann.append(_vk)
    for _arg in _ann:
        if _arg.annotation is not None:
            yield _arg.annotation
    if node.returns is not None:
        yield node.returns
def _iter_lambda_calls(node: ast.Lambda, annotations_lazy: bool):
    for _d in _iter_default_exprs(node.args):
        yield from _iter_executed_calls(_d, annotations_lazy)
def _iter_funcdef_calls(node: ast.FunctionDef, annotations_lazy: bool):
    for _d in _iter_default_exprs(node.args):
        yield from _iter_executed_calls(_d, annotations_lazy)
    for _dec in node.decorator_list:
        yield from _iter_executed_calls(_dec, annotations_lazy)
    if not annotations_lazy:
        for _a in _funcdef_annotations(node):
            yield from _iter_executed_calls(_a, annotations_lazy)
def _guard_live_branch_calls(node: ast.If, annotations_lazy: bool):
    live = main_guard_live_body(node)
    if live is None:
        return None
    calls = list(_iter_executed_calls(node.test, annotations_lazy))
    for stmt in live:
        calls.extend(_iter_executed_calls(stmt, annotations_lazy))
    return calls
def _iter_executed_calls(node: ast.AST, annotations_lazy: bool = False):
    if _TYPE_ALIAS_T is not None and isinstance(node, _TYPE_ALIAS_T):
        return
    if isinstance(node, ast.Lambda):
        yield from _iter_lambda_calls(node, annotations_lazy)
        return
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        yield from _iter_funcdef_calls(node, annotations_lazy)
        return
    if isinstance(node, ast.AnnAssign):
        for child in (node.target, node.value):
            if child is not None:
                yield from _iter_executed_calls(child, annotations_lazy)
        if not annotations_lazy:
            yield from _iter_executed_calls(node.annotation, annotations_lazy)
        return
    if isinstance(node, ast.Call):
        yield node
    if isinstance(node, ast.If):
        guarded = _guard_live_branch_calls(node, annotations_lazy)
        if guarded is not None:
            yield from guarded
            return
    for _child in ast.iter_child_nodes(node):
        yield from _iter_executed_calls(_child, annotations_lazy)
_TOPLEVEL_DANGEROUS_ATTRS = (
    "subprocess", "requests", "urllib", "socket", "http", "ftplib",
    "smtplib", "telnetlib", "paramiko", "selenium", "playwright",
    "os.system", "os.popen", "os.startfile", "os.remove", "os.unlink",
    "os.rmdir", "os.mkdir", "os.makedirs", "os.rename", "os.chdir",
    "shutil", "signal", "multiprocessing", "threading",
    "write_text", "write_bytes", "unlink", "touch", "mkdir", "rmdir",
)
_TOPLEVEL_DANGEROUS_CALLS = (
    "sleep", "input", "exec", "eval", "compile", "exit", "quit",
    "main", "run", "start", "serve", "wait", "getpass", "pause",
    "open",
)
_TOPLEVEL_DANGEROUS_IMPORTS = (
    "requests", "urllib", "socket", "http", "paramiko", "selenium",
    "playwright", "boto3", "mysql", "psycopg", "redis", "pymongo",
)
def _dangerous_module_root(name: str | None) -> bool:
    return (name or "").split(".")[0] in _TOPLEVEL_DANGEROUS_IMPORTS
def _import_is_dangerous(node: ast.stmt) -> bool:
    if isinstance(node, ast.Import):
        return any(_dangerous_module_root(alias.name) for alias in node.names)
    if isinstance(node, ast.ImportFrom):
        return _dangerous_module_root(node.module)
    return False
def _executed_call_name(sub: ast.AST) -> str:
    fname = resolve_call_name(sub)
    if fname:
        return fname
    func = getattr(sub, "func", None)
    return func.attr if isinstance(func, ast.Attribute) else ""
def _executed_call_is_dangerous(sub: ast.Call) -> bool:
    fname = _executed_call_name(sub)
    if fname and any(d in fname for d in _TOPLEVEL_DANGEROUS_ATTRS):
        return True
    return bool(fname) and fname.split(".")[-1] in _TOPLEVEL_DANGEROUS_CALLS
def _executed_stmt_is_dangerous(node: ast.AST, annotations_lazy: bool) -> bool:
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return _import_is_dangerous(node)
    return any(_executed_call_is_dangerous(sub)
               for sub in _iter_executed_calls(node, annotations_lazy))
def module_has_toplevel_side_effect(tree: ast.AST) -> bool:
    _lazy = module_postpones_annotations(tree, require_absolute=True)
    typing_context = collect_typing_tc_bindings(tree)
    return any(_executed_stmt_is_dangerous(node, _lazy)
               for node in _iter_executed_stmts(tree.body, typing_context))
_NESTED_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                       ast.ClassDef, ast.Lambda)
def _nested_scope_body_lines(node) -> int:
    body = getattr(node, 'body', ())
    stack = [body] if isinstance(body, ast.AST) else list(body or ())
    nested_lines: set[int] = set()
    while stack:
        child = stack.pop()
        if isinstance(child, _NESTED_SCOPE_TYPES):
            _start = getattr(child, 'lineno', None)
            for _dec in getattr(child, 'decorator_list', ()) or ():
                _dec_line = getattr(_dec, 'lineno', None)
                if isinstance(_dec_line, int) and isinstance(_start, int):
                    _start = min(_start, _dec_line)
            _end = getattr(child, 'end_lineno', None)
            if (isinstance(_start, int) and not isinstance(_start, bool)
                    and isinstance(_end, int)
                    and not isinstance(_end, bool)
                    and _end >= _start):
                nested_lines.update(range(_start, _end + 1))
            continue
        stack.extend(ast.iter_child_nodes(child))
    return len(nested_lines)
def _function_node_metrics(node) -> dict:
    cc = cyclomatic_complexity(node, iter_own_nodes)
    try_count = return_count = body_lines = 0
    call_targets = set()
    _end = getattr(node, 'end_lineno', None)
    _start = getattr(node, 'lineno', None)
    if (isinstance(_end, int) and not isinstance(_end, bool) and _end
            and isinstance(_start, int) and not isinstance(_start, bool)):
        body_lines = max(_end - _start - _nested_scope_body_lines(node), 0)
    for child in iter_own_nodes(node):
        if isinstance(child, (ast.Try, TRY_STAR_T)):
            try_count += 1
            continue
        if isinstance(child, ast.Return):
            return_count += 1
            continue
        if isinstance(child, ast.Call):
            _collect_call_target(child, call_targets)
    return {
        'cyclomatic_complexity': cc,
        'body_lines': body_lines,
        'try_count': try_count,
        'return_count': return_count,
        'call_targets': frozenset(call_targets),
    }
def _collect_call_target(child: ast.Call, call_targets: set) -> None:
    if isinstance(child.func, ast.Name):
        call_targets.add(child.func.id)
    elif isinstance(child.func, ast.Attribute):
        call_targets.add(child.func.attr)
def collect_function_behavior_metrics(cache) -> dict:
    behavior: dict = {}
    for entry in cache.valid_entries:
        tree = getattr(entry, 'tree', None)
        if tree is None:
            continue
        _scopes: dict[tuple, tuple] = {}
        for _fi in getattr(entry, 'functions', None) or ():
            _scopes[(_fi.get('name'), _fi.get('line'))] = tuple(
                _fi.get('scope') or ())
        for node in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _scope = _scopes.get(
                (node.name, getattr(node, 'lineno', None)), ())
            _rel = entry_rel_path(entry).replace('\\', '/')
            _key = f"{_rel}::{qualified_name(_scope, node.name)}"
            behavior[_key] = _function_node_metrics(node)
    return behavior
class _TestIndex(NamedTuple):
    files: list[str]
    imports: dict[str, set[str]]
    unparseable: set[str]
def _list_test_files(skill_dir) -> list:
    try:
        return sorted(
            os.path.relpath(fp, skill_dir).replace(os.sep, '/')
            for fp in iter_test_py_files(skill_dir))
    except (OSError, ValueError) as e:
        _log.warning(
            "build_mutation_test_mapping: 测试目录列举失败（降级空映射）: %s (%s)",
            skill_dir, e)
        return []
def _import_node_names(node) -> set[str]:
    if isinstance(node, ast.Import):
        return {part for alias in node.names for part in alias.name.split('.')}
    if isinstance(node, ast.ImportFrom):
        names = set(node.module.split('.')) if node.module else set()
        names.update(alias.name for alias in node.names if alias.name != '*')
        return names
    return set()
def _test_module_imported_names(tree: ast.AST) -> set[str]:
    imported: set[str] = set()
    for node in walk_nodes(tree):
        imported |= _import_node_names(node)
    return imported
def _parse_test_imports(tf_path: str) -> set[str]:
    source = read_source(tf_path)
    if source is None:
        raise OSError(f"源码不可读: {tf_path}")
    return _test_module_imported_names(ast.parse(source))
def _collect_test_imports(test_files, skill_dir) -> tuple[dict, set]:
    test_imports = {}
    unparseable_tests: set[str] = set()
    for tf in test_files:
        try:
            test_imports[tf] = _parse_test_imports(os.path.join(skill_dir, tf))
        except (OSError, *_AST_PARSE_SOFT_ERRORS):
            unparseable_tests.add(tf)
            test_imports[tf] = set()
            _log.debug("[TestQuality] 测试文件导入解析失败(降级空导入集): %s", tf, exc_info=True)
    return test_imports, unparseable_tests
def _is_mutation_target_file(filename: str) -> bool:
    if not filename.lower().endswith('.py'):
        return False
    if is_test_source_basename(filename):
        return False
    return filename not in ('__init__.py', 'conftest.py')
def _collect_source_files(skill_dir) -> list[tuple[str, str]]:
    source_files: list[tuple[str, str]] = []
    for filepath in collect_py_files(skill_dir):
        rel = os.path.relpath(filepath, skill_dir).replace(os.sep, '/')
        filename = os.path.basename(filepath)
        if not _is_mutation_target_file(filename):
            continue
        source_files.append((rel, os.path.splitext(filename)[0]))
    source_files.sort(key=lambda item: item[0])
    return source_files
_IMPORT_SMOKE_TEST_TOKENS: frozenset[str] = frozenset(
    ('smoke', 'smokes', 'import', 'imports'))
_WORD_SPLIT = re.compile(r'[^a-z0-9]+')
def _is_import_smoke_test(filename: str) -> bool:
    stem = os.path.splitext(filename)[0].lower()
    return bool(_IMPORT_SMOKE_TEST_TOKENS & set(_WORD_SPLIT.split(stem)))
def _module_package_root(rel_path: str, module_name: str) -> str:
    parts = [p for p in rel_path.replace(os.sep, '/').split('/') if p]
    if parts and parts[0] == 'src':
        return parts[1] if len(parts) > 2 else module_name
    if len(parts) > 1:
        return parts[0]
    return module_name
def _import_smoke_test_files(index: _TestIndex, rel_path: str,
                             module_name: str) -> list[str]:
    root = _module_package_root(rel_path, module_name)
    return [tf for tf in index.files
            if tf not in index.unparseable
            and _is_import_smoke_test(tf)
            and root in index.imports.get(tf, set())]
def _fuzzy_test_files(module_name, index: _TestIndex) -> list[str]:
    return [tf for tf, mods in index.imports.items() if module_name in mods]
def _package_scoped_test_files(test_files: list[str], index: _TestIndex,
                               package_root: str) -> list[str]:
    return [
        tf for tf in test_files
        if (package_root in index.imports.get(tf, set())
            or package_root in tf.split('/')[:-1])
    ]
def _match_test_files_for_module(module_name, index: _TestIndex,
                                 rel_path: str, package_root: str | None):
    exact_tests = {f'test_{module_name}.py', f'{module_name}_test.py'}
    exact_matches = [tf for tf in index.files
                     if os.path.basename(tf) in exact_tests
                     and tf not in index.unparseable]
    if package_root is not None:
        exact_matches = _package_scoped_test_files(
            exact_matches, index, package_root)
    if exact_matches:
        return _test_mapping(exact_matches, 'high')
    smoke_matches = _import_smoke_test_files(index, rel_path, module_name)
    fuzzy_matches = _fuzzy_test_files(module_name, index)
    if package_root is not None:
        fuzzy_matches = _package_scoped_test_files(
            fuzzy_matches, index, package_root)
    if fuzzy_matches:
        fuzzy_matches.extend(
            path for path in smoke_matches if path not in fuzzy_matches)
        return _test_mapping(fuzzy_matches, 'medium')
    if smoke_matches:
        return _test_mapping(smoke_matches, 'low')
    return None
def _test_mapping(test_files: list[str], confidence: str) -> dict:
    return {'test_files': test_files, 'confidence': confidence}
def build_mutation_test_mapping(skill_dir: str) -> dict:
    test_files = _list_test_files(skill_dir)
    if not test_files:
        return {}
    test_imports, unparseable_tests = _collect_test_imports(test_files, skill_dir)
    index = _TestIndex(test_files, test_imports, unparseable_tests)
    source_files = _collect_source_files(skill_dir)
    module_counts: dict[str, int] = {}
    for _rel_path, module_name in source_files:
        module_counts[module_name] = module_counts.get(module_name, 0) + 1
    mapping = {}
    for rel_path, module_name in source_files:
        package_root = (_module_package_root(rel_path, module_name)
                        if module_counts[module_name] > 1 else None)
        matched = _match_test_files_for_module(
            module_name, index, rel_path, package_root)
        if matched is not None:
            mapping[rel_path] = matched
    return mapping

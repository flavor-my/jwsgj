from __future__ import annotations

import logging
import os
import re
from bisect import bisect_left
from collections import Counter
from collections.abc import Iterator
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    is_dunder_name,
    normalize_node_str,
    normalize_torn_name,
    path_to_dotted_module,
    strip_pkg_root,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC, POLYMORPHIC_METHODS
from jwsgj.runtime_scope import (
    count_py_files_under,
    is_test_caller_name,
    is_test_file_path,
)

_logger = logging.getLogger(__name__)
__all__ = [
    'CALLGRAPH_BUILD_ERRORS',
    'CALLGRAPH_PARSE_FAILURE_EXCS',
    'DECORATOR_CLOSURE_NAMES',
    'EXEMPTION_RISK',
    'MAGIC_METHODS',
    'CallEdge',
    'FunctionNode',
    'ScopedNameResolver',
    'assignment_name_index',
    'build_assignment_scope_index',
    'build_exemption_classification',
    'build_symbol_lookup_index',
    'check_framework_decorators',
    'check_source_markers',
    'classify_exemption',
    'collect_cross_skill_names',
    'count_project_py_files',
    'functions_by_attr_name',
    'functions_ending_with',
    'is_entry_point_name',
    'method_to_classes_index',
    'property_maps',
    'reset_index_caches',
    'reset_query_caches',
    'resolve_callee_file',
    'short_name_index',
    'str_decorators',
    'symbol_hit',
    'symbol_owner_index',
]
def _qualify_module_member(module_name: str, name: str) -> str:
    return f"{module_name}.{name}" if module_name else name
@dataclass
class CallEdge:
    caller_file: str
    caller_func: str
    callee_func: str
    callee_file: str | None = None
    line: int = 0
    is_external: bool = False
    is_self_call: bool = False
    args_count: int = 0
    type_resolution_blocked: bool = False
@dataclass
class FunctionNode:
    name: str
    filepath: str
    start_line: int
    end_line: int
    is_public: bool = False
    is_async: bool = False
    is_method: bool = False
    class_name: str | None = None
    decorators: list[str] = field(default_factory=list)
    decorator_args: dict[str, list[str]] = field(default_factory=dict)
    params: list[str] = field(default_factory=list)
    returns: str | None = None
    docstring: str | None = None
    complexity: int = 0
    is_property: bool = False
    is_synthetic: bool = False
    caller_weight: float = 0.0
    decor_line: int = 0
    confidence: str = 'unknown'
_MEMO_LIMIT = 65536
class _FunctionTable(dict):
    __slots__ = ("revision",)
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.revision = 0
    def __setitem__(self, key, value) -> None:
        super().__setitem__(key, value)
        self.revision += 1
    def __delitem__(self, key) -> None:
        super().__delitem__(key)
        self.revision += 1
    def pop(self, *args):  # jwsgj:suppress public_untested — dict 协议覆盖：结构变更版本号必须覆盖 pop 路径，调用方为 dict 协议消费方
        existed = args[0] in self if args else False
        value = super().pop(*args)
        if existed:
            self.revision += 1
        return value
    def popitem(self):
        item = super().popitem()
        self.revision += 1
        return item
    def clear(self) -> None:  # jwsgj:suppress public_untested — dict 协议覆盖：结构变更版本号必须覆盖 clear 路径，调用方为 dict 协议消费方
        if self:
            super().clear()
            self.revision += 1
    def update(self, *args, **kwargs) -> None:
        before = len(self)
        try:
            super().update(*args, **kwargs)
        finally:
            if len(self) != before or args or kwargs:
                self.revision += 1
    def __ior__(self, other):
        self.update(other)
        return self
    def setdefault(self, key, default=None):
        if key in self:
            return self[key]
        value = super().setdefault(key, default)
        self.revision += 1
        return value
def _funcs_revision(graph_funcs: dict) -> int | None:
    if isinstance(graph_funcs, _FunctionTable):
        return graph_funcs.revision
    return None
_suffix_cache: dict[str, tuple[tuple[str, ...], int]] = {}
_rev_index: list = []
_rev_index_graph: dict | None = None
_rev_index_len: int = -1
_rev_index_rev: int | None = None
_rev_index_keys: tuple | None = None
_suffix_cache_len: int = -1
_suffix_cache_graph: dict | None = None
_suffix_cache_keys: tuple | None = None
_suffix_cache_rev: int | None = None
_attr_cache: dict[str, list[tuple[str, bool, bool]]] = {}
_attr_index: dict[str, list[tuple[str, bool, bool]]] = {}
_attr_index_len: int = -1
_attr_index_graph: dict | None = None
_attr_index_signature: tuple | None = None
_attr_index_rev: int | None = None
_tail_index: dict[str, list[str]] = {}
_key_pos: dict[str, int] = {}
_tail_index_len: int = 0
_tail_index_graph: dict | None = None
_tail_index_keys: tuple | None = None
_tail_index_rev: int | None = None
_dotted_index: dict[str, list[str]] = {}
_property_map: dict[str, str] = {}
_prop_by_attr: dict[str, list[str]] = {}
_propmaps_len: int = -1
_propmaps_graph: dict | None = None
_propmaps_signature: tuple | None = None
_propmaps_rev: int | None = None
def reset_query_caches() -> None:
    global _attr_index, _property_map, _prop_by_attr, _suffix_cache_len
    global _attr_index_len, _tail_index_len, _tail_index_graph, _propmaps_len
    global _suffix_cache_graph, _attr_index_graph, _propmaps_graph
    global _suffix_cache_keys, _suffix_cache_rev, _tail_index_keys
    global _tail_index_rev, _attr_index_signature, _propmaps_signature
    global _attr_index_rev, _propmaps_rev
    global _rev_index, _rev_index_graph, _rev_index_len
    global _rev_index_rev, _rev_index_keys
    _suffix_cache.clear()
    _rev_index = []
    _rev_index_graph = None
    _rev_index_len = -1
    _rev_index_rev = None
    _rev_index_keys = None
    _attr_cache.clear()
    _suffix_cache_len = -1
    _suffix_cache_graph = None
    _suffix_cache_keys = None
    _suffix_cache_rev = None
    _attr_index = {}
    _attr_index_len = -1
    _attr_index_graph = None
    _attr_index_signature = None
    _attr_index_rev = None
    _property_map = {}
    _prop_by_attr = {}
    _propmaps_len = -1
    _propmaps_graph = None
    _propmaps_signature = None
    _propmaps_rev = None
    _tail_index.clear()
    _dotted_index.clear()
    _key_pos.clear()
    _tail_index_len = 0
    _tail_index_graph = None
    _tail_index_keys = None
    _tail_index_rev = None
def _ensure_tail_index(graph_funcs: dict) -> None:
    global _tail_index_len, _tail_index_graph, _tail_index_keys
    global _tail_index_rev
    n = len(graph_funcs)
    rev = _funcs_revision(graph_funcs)
    if rev is not None:
        if _tail_index_graph is graph_funcs and _tail_index_rev == rev:
            return
        _tail_index.clear()
        _dotted_index.clear()
        _key_pos.clear()
        _tail_index_len = 0
        _tail_index_graph = graph_funcs
        _tail_index_rev = rev
        _digest_new_tail_keys(graph_funcs, 0)
        _tail_index_len = n
        return
    current_keys = tuple(graph_funcs)
    _identity_changed = _tail_index_graph is not graph_funcs
    previous_keys = _tail_index_keys or ()
    prefix_changed = current_keys[:_tail_index_len] != previous_keys
    if _tail_index_len > n or _identity_changed or prefix_changed:
        _logger.debug(
            "tail 索引守卫触发整体重建: 水位=%d 规模=%d 图身份变化=%s",
            _tail_index_len, n, _identity_changed)
        _tail_index.clear()
        _dotted_index.clear()
        _key_pos.clear()
        _tail_index_len = 0
        _tail_index_graph = graph_funcs
    if _tail_index_len == n:
        return
    _digest_new_tail_keys(graph_funcs, _tail_index_len)
    _tail_index_len = n
    _tail_index_keys = current_keys
def _digest_new_tail_keys(graph_funcs: dict, watermark: int) -> None:
    idx = _tail_index
    didx = _dotted_index
    pos = _key_pos
    for i, k in enumerate(graph_funcs):
        if i < watermark:
            continue
        key = normalize_torn_name(k)
        idx.setdefault(key.rsplit(".", 1)[-1], []).append(k)
        pos[k] = i
        parts = key.split(".")
        for _i in range(1, len(parts)):
            didx.setdefault(".".join(parts[_i:]), []).append(k)
def functions_ending_with(graph_funcs: dict, suffix: str,
                          dot_or_equal: bool = True) -> tuple[str, ...]:
    if not isinstance(suffix, str):
        return ()
    _refresh_suffix_cache(graph_funcs)
    if "." not in suffix:
        return _query_simple_suffix(graph_funcs, suffix, dot_or_equal)
    if dot_or_equal:
        return _query_dotted_suffix(graph_funcs, suffix)
    return _memoized_suffix_scan(graph_funcs, suffix)
def _cache_stale(watermark: int, cached_funcs, graph_funcs: dict) -> bool:
    return watermark != len(graph_funcs) or cached_funcs is not graph_funcs
def _refresh_suffix_cache(graph_funcs: dict) -> None:
    global _suffix_cache_len, _suffix_cache_graph, _suffix_cache_keys
    global _suffix_cache_rev
    rev = _funcs_revision(graph_funcs)
    if rev is not None:
        if _suffix_cache_graph is graph_funcs and _suffix_cache_rev == rev:
            return
        _suffix_cache.clear()
        _suffix_cache_len = len(graph_funcs)
        _suffix_cache_graph = graph_funcs
        _suffix_cache_rev = rev
        return
    current_keys = tuple(graph_funcs)
    if (_cache_stale(_suffix_cache_len, _suffix_cache_graph, graph_funcs)
            or _suffix_cache_keys != current_keys):
        _suffix_cache.clear()
        _suffix_cache_len = len(graph_funcs)
        _suffix_cache_graph = graph_funcs
        _suffix_cache_keys = current_keys
def _rev_index_of(graph_funcs: dict) -> list:
    global _rev_index, _rev_index_graph, _rev_index_len
    global _rev_index_rev, _rev_index_keys
    n = len(graph_funcs)
    rev = _funcs_revision(graph_funcs)
    if rev is not None:
        keys = None
        fresh = (_rev_index_graph is graph_funcs and _rev_index_len == n
                 and _rev_index_rev == rev)
    else:
        keys = tuple(graph_funcs)
        fresh = (_rev_index_graph is graph_funcs and _rev_index_len == n
                 and _rev_index_rev is None and _rev_index_keys == keys)
    if fresh:
        return _rev_index
    _rev_index = sorted(
        (normalize_torn_name(k)[::-1], i, k)
        for i, k in enumerate(graph_funcs))
    _rev_index_graph = graph_funcs
    _rev_index_len = n
    _rev_index_rev = rev
    _rev_index_keys = keys
    return _rev_index
def _memoized_suffix_scan(graph_funcs: dict, suffix: str) -> tuple:
    n = len(graph_funcs)
    cached = _suffix_cache.get(suffix)
    if cached is not None and cached[1] == n:
        return cached[0]
    index = _rev_index_of(graph_funcs)
    rev = suffix[::-1]
    lo = bisect_left(index, (rev,))
    hits: list[tuple[int, str]] = []
    for rev_key, pos, key in index[lo:]:
        if not rev_key.startswith(rev):
            break
        hits.append((pos, key))
    hits.sort()
    result = tuple(key for _pos, key in hits)
    if len(_suffix_cache) >= _MEMO_LIMIT:
        _suffix_cache.clear()
    _suffix_cache[suffix] = (result, n)
    return result
def _sorted_by_insertion(keys: list) -> tuple:
    if len(keys) > 1:
        pos = _key_pos
        keys.sort(key=pos.__getitem__)
    return tuple(keys)
def _query_simple_suffix(graph_funcs: dict, suffix: str,
                         dot_or_equal: bool) -> tuple:
    _ensure_tail_index(graph_funcs)
    idx = _tail_index
    if dot_or_equal:
        return tuple(idx.get(suffix, ()))
    keys = [
        k
        for seg, ks in idx.items()
        if seg.endswith(suffix)
        for k in ks
    ]
    return _sorted_by_insertion(keys)
def _query_dotted_suffix(graph_funcs: dict, suffix: str) -> tuple:
    _ensure_tail_index(graph_funcs)
    keys = list(
        _dotted_index.get(suffix, ()))
    if suffix in graph_funcs:
        keys.append(suffix)
    return _sorted_by_insertion(keys)
def _attr_mapping_signature(graph_funcs: dict) -> tuple:
    return tuple(
        (key, fnode.name, fnode.is_synthetic, fnode.is_property)
        for key, fnode in graph_funcs.items())
def functions_by_attr_name(graph_funcs: dict,
                           attr_name: str) -> list[tuple[str, bool, bool]]:
    global _attr_index, _attr_index_len, _attr_index_graph
    global _attr_index_signature, _attr_index_rev
    if not isinstance(attr_name, str) or not attr_name:
        return []
    _n = len(graph_funcs)
    rev = _funcs_revision(graph_funcs)
    signature = _attr_mapping_signature(graph_funcs)
    stale = (_cache_stale(_attr_index_len, _attr_index_graph, graph_funcs)
             or _attr_index_rev != rev
             or _attr_index_signature != signature)
    if stale:
        _attr_cache.clear()
        _attr_index = _rebuild_attr_index(graph_funcs)
        _attr_index_len = _n
        _attr_index_graph = graph_funcs
        _attr_index_signature = signature
        _attr_index_rev = rev
    entries = _attr_cache.get(attr_name)
    if entries is None:
        if "." in attr_name:
            entries = _scan_dotted_attr_entries(graph_funcs, attr_name)
        else:
            entries = list(_attr_index.get(attr_name, ()))
        if len(_attr_cache) >= _MEMO_LIMIT:
            _attr_cache.clear()
        _attr_cache[attr_name] = entries
    return entries
def _attr_entry(full_key: str, fnode) -> tuple[str, bool, bool]:
    return (full_key, bool(fnode.is_synthetic), bool(fnode.is_property))
def _rebuild_attr_index(graph_funcs: dict) -> dict:
    _idx: dict[str, list[tuple[str, bool, bool]]] = {}
    for full_key, fnode in graph_funcs.items():
        _nm = normalize_torn_name(fnode.name)
        if "." in _nm:
            _idx.setdefault(_nm.rsplit(".", 1)[-1], []).append(
                _attr_entry(full_key, fnode))
    return _idx
def _scan_dotted_attr_entries(graph_funcs: dict, attr_name: str) -> list:
    dot_suffix = "." + attr_name
    return [
        _attr_entry(full_key, fnode)
        for full_key, fnode in graph_funcs.items()
        if (normalize_torn_name(fnode.name) == attr_name
            or normalize_torn_name(fnode.name).endswith(dot_suffix))
    ]
def property_maps(graph_funcs: dict) -> tuple[dict[str, str], dict[str, list[str]]]:
    global _property_map, _prop_by_attr, _propmaps_len, _propmaps_graph
    global _propmaps_signature, _propmaps_rev
    _n_funcs = len(graph_funcs)
    rev = _funcs_revision(graph_funcs)
    signature = _attr_mapping_signature(graph_funcs)
    stale = (_cache_stale(_propmaps_len, _propmaps_graph, graph_funcs)
             or _propmaps_rev != rev
             or _propmaps_signature != signature)
    if stale:
        _pm: dict[str, str] = {}
        _pba: dict[str, list[str]] = {}
        for full_key, fnode in graph_funcs.items():
            if fnode.is_property:
                _prop_name = normalize_torn_name(fnode.name)
                _pm[_prop_name] = full_key
                _pba.setdefault(_simple_name(_prop_name), []).append(full_key)
        _property_map = _pm
        _prop_by_attr = _pba
        _propmaps_len = _n_funcs
        _propmaps_graph = graph_funcs
        _propmaps_signature = signature
        _propmaps_rev = rev
    return _property_map, _prop_by_attr
def assignment_name_index(graph, *, include_methods: bool = True,
                          include_torn: bool = True,
                          require_declared: bool = False,
                          include_non_str: bool = False
                          ) -> dict[str, list[str]]:
    index: dict[str, list[str]] = {}
    for fqn, fnode in graph.functions.items():
        if require_declared:
            if not isinstance(fqn, str) or not fqn:
                continue
        elif not include_non_str and not isinstance(fqn, str):
            continue
        key = normalize_torn_name(fqn)
        if not include_torn and key.startswith("."):
            continue
        if (not include_methods
                and getattr(fnode, "class_name", None) is not None):
            continue
        index.setdefault(key.rsplit(".", 1)[-1], []).append(fqn)
    return index
def _as_name_tuple(value) -> tuple:
    if isinstance(value, str):
        return (value,) if value else ()
    if isinstance(value, (list, tuple, set, frozenset)):
        return tuple(value)
    return ()
def symbol_owner_index(file_symbols, path_key=None) -> dict[str, str]:
    index: dict[str, str] = {}
    ambiguous: set[str] = set()
    items = file_symbols.items()
    if path_key is not None:
        items = sorted(items, key=lambda item: path_key(item[0]))
    for fpath, syms in items:
        if not syms:
            continue
        for sym, fnode in syms.items():
            if not isinstance(sym, str) or not sym or sym in ambiguous:
                continue
            if "." not in sym and getattr(fnode, "is_method", False):
                continue
            if sym in index:
                del index[sym]
                ambiguous.add(sym)
            else:
                index[sym] = fpath
    return index
def build_assignment_scope_index(
        index: dict[str, list[str]]) -> tuple[dict[str, dict[str, str]],
                                             dict[str, dict[str, str | None]],
                                             dict[str, str]]:
    own_map: dict[str, dict[str, str]] = {}
    prefix_map: dict[str, dict[str, str | None]] = {}
    unique_names: dict[str, str] = {}
    for simple, candidates in index.items():
        candidates = [candidate for candidate in candidates
                      if isinstance(candidate, str) and candidate]
        if not candidates:
            continue
        if len(candidates) == 1:
            unique_names[simple] = candidates[0]
        own_by_module: dict[str, list[str]] = {}
        for fqn in candidates:
            module = fqn.rsplit(".", 1)[0] if "." in fqn else ""
            own_by_module.setdefault(module, []).append(fqn)
        for module, fqns in own_by_module.items():
            if len(fqns) == 1:
                own_map.setdefault(module, {})[simple] = fqns[0]
            parts = module.split(".")
            for depth in range(1, len(parts)):
                prefix = ".".join(parts[:depth])
                bucket = prefix_map.setdefault(prefix, {})
                if simple in bucket:
                    bucket[simple] = None
                else:
                    bucket[simple] = fqns[0] if len(fqns) == 1 else None
    return own_map, prefix_map, unique_names
class ScopedNameResolver:
    __slots__ = ("_own", "_prefix", "_unique")
    def __init__(self, own, prefix, unique) -> None:
        self._own = own or {}
        self._prefix = prefix or {}
        self._unique = unique or {}
    def __contains__(self, name: str) -> bool:
        return self.get(name) is not None
    def get(self, name: str, default=None):
        fqn = self._own.get(name)
        if fqn is not None:
            return fqn
        if name in self._prefix:
            return self._prefix[name]
        return self._unique.get(name, default)
def symbol_hit(callee_name: str, simple: str, syms,
               module_name: str) -> str | None:
    if callee_name in syms:
        return callee_name
    if "." not in callee_name:
        return simple if simple in syms else None
    prefix = module_name + "." if module_name else ""
    if not prefix or not callee_name.startswith(prefix):
        return None
    rest = callee_name[len(prefix):]
    return rest if rest in syms else None
def build_symbol_lookup_index(file_symbols) -> dict:
    index: dict[str, list[tuple[str, str, str]]] = {}
    for fpath, syms in file_symbols.items():
        if not syms:
            continue
        module_name = path_to_dotted_module(fpath)
        for key in syms:
            if not isinstance(key, str) or not key:
                continue
            index.setdefault(key, []).append((module_name, fpath, key))
        if module_name:
            prefix = module_name + "."
            for key in syms:
                if not isinstance(key, str) or not key:
                    continue
                index.setdefault(prefix + key, []).append(
                    (module_name, fpath, key))
    return index
def _file_symbol_resolution(graph, fpath, syms, qualified, simple):
    if syms is None:
        return None
    scan_module = path_to_dotted_module(fpath)
    hit = symbol_hit(qualified, simple, syms, scan_module)
    if hit is None:
        return None
    fqn = _qualify_module_member(scan_module, hit)
    return (fqn, fpath) if fqn in graph.functions else None


def _resolve_callee_file_linear(graph, filepath: str, file_symbols,
                                qualified: str, simple: str,
                                callee_name: str) -> tuple[str, str | None]:
    if callee_name in graph.functions:
        return callee_name, graph.functions[callee_name].filepath
    own_hit = _file_symbol_resolution(
        graph, filepath, file_symbols.get(filepath), qualified, simple)
    if own_hit is not None:
        return own_hit
    candidates = []
    for fpath, syms in file_symbols.items():
        if fpath == filepath:
            continue
        hit = _file_symbol_resolution(
            graph, fpath, syms, qualified, simple)
        if hit is not None:
            candidates.append(hit)
    if len(candidates) == 1:
        return candidates[0]
    return callee_name, None
def resolve_callee_file(graph, filepath: str, file_symbols, pkg_root: str,
                        module_name: str, symbol_index,
                        callee_name: str) -> tuple[str, str | None]:
    if callee_name in graph.functions:
        return callee_name, graph.functions[callee_name].filepath
    qualified = strip_pkg_root(callee_name, pkg_root)
    simple = qualified.rsplit(".", maxsplit=1)[-1]
    if symbol_index is None:
        return _resolve_callee_file_linear(
            graph, filepath, file_symbols, qualified, simple, callee_name)
    own = file_symbols.get(filepath)
    if own is not None:
        hit = symbol_hit(qualified, simple, own, module_name)
        if hit is not None:
            fqn = f"{module_name}.{hit}" if module_name else hit
            if fqn in graph.functions:
                return fqn, filepath
    candidates = []
    for _m, _fp, _key in symbol_index.get(qualified, ()):
        if _fp == filepath:
            continue
        fqn = f"{_m}.{_key}" if _m else _key
        if fqn in graph.functions:
            candidates.append((fqn, _fp))
    if len(candidates) == 1:
        return candidates[0]
    return callee_name, None
def short_name_index(graph) -> dict[str, str]:
    return {simple: fqns[-1] for simple, fqns
            in assignment_name_index(graph, include_non_str=True).items()}
def method_to_classes_index(class_methods) -> dict[str, list[str]]:
    index: dict[str, list[str]] = {}
    for cls_fqn, methods in class_methods.items():
        for method in _as_name_tuple(methods):
            index.setdefault(method, []).append(cls_fqn)
    return index
def _class_method_index(graph) -> dict[str, set[str]]:
    """``graph.class_methods`` 的归一化索引。

    缓存失效判据必须是 O(类数) 的**廉价投影**：原实现用
    ``tuple((k, frozenset(_as_name_tuple(v))) for k, v in ...items())``
    作签名，每次调用都要对每个类做字符串规范化 + frozenset 构造——
    验证成本 ≥ 重建成本，等价于没有缓存。而 ``is_project_class`` 对**每个
    调用点**都要问一次，于是退化成 O(调用点 × 全库方法数) = O(n²)。

    现在改用 ``(id, 类数, 方法总数)``：三项都是 C 级廉价运算（实测快 5 个
    数量级），且**自动派生、无需人工维护版本号**——只要增删方法就会变，
    不存在「改了规则忘了升版本号导致静默漏报」的路径。

    安全性：``graph.class_methods`` 的全部写入点（``diag_callgraph_source``
    与 ``diag_implicit_calls`` 的 dataclass 合成）都只调 ``.add()``，
    无移除、无整体替换，故方法总数单调递增即能识别任何内容变化。
    """
    class_methods = getattr(graph, "class_methods", None) or {}
    signature = (
        id(class_methods),
        len(class_methods),
        sum(len(methods) for methods in class_methods.values()),
    )
    cached = getattr(graph, "_class_method_index_cache", None)
    if cached is not None and cached[0] == signature:
        return cached[1]
    index: dict[str, set[str]] = {}
    for cls_key, methods in class_methods.items():
        names = set(_as_name_tuple(methods))
        index.setdefault(normalize_torn_name(cls_key), set()).update(names)
        index.setdefault(_simple_name(cls_key), set()).update(names)
    graph._class_method_index_cache = (signature, index)
    return index
# 类名**尾段**索引：``最后一段 -> [原始类名]``。
#
# 多处需要回答「哪些类的 basename 等于 X」（mixin 跳转、类名解析、继承查找）。
# 原实现每次调用都 ``set(a) | set(b)`` 再全量遍历 + 逐键 ``normalize_torn_name``，
# 在 1404 个类 × 数万个调用点的规模下退化为 O(n²)。
# 本索引把该查询降为 O(1)，且**自动派生**（容器长度变则重建），无需人工维护。
_CLASS_TAIL_INDEX_CACHE: dict[tuple, dict] = {}
_CLASS_TAIL_INDEX_CACHE_MAX = 64
def class_tail_index(graph, *container_names: str) -> dict[str, list[str]]:
    """返回 ``{basename: [原始类名, ...]}``（已去重）。

    ``basename`` 口径与 ``_ref_basename`` 一致：
    ``normalize_torn_name(value).rsplit(".", 1)[-1]``。
    """
    containers = tuple(
        (name, getattr(graph, name, None) or {}) for name in container_names)
    signature = (id(graph),
                 tuple((name, tuple(c)) for name, c in containers))
    cached = _CLASS_TAIL_INDEX_CACHE.get(signature)
    if cached is not None:
        return cached
    index: dict[str, list[str]] = {}
    for _name, container in containers:
        for candidate in container:
            if not isinstance(candidate, str):
                continue
            tail = normalize_torn_name(candidate).rsplit(".", 1)[-1]
            bucket = index.setdefault(tail, [])
            if candidate not in bucket:
                bucket.append(candidate)
    _CLASS_TAIL_INDEX_CACHE[signature] = index
    while len(_CLASS_TAIL_INDEX_CACHE) > _CLASS_TAIL_INDEX_CACHE_MAX:
        _CLASS_TAIL_INDEX_CACHE.pop(
            next(iter(_CLASS_TAIL_INDEX_CACHE)), None)
    return index
def class_method_names(graph, class_name: str) -> set[str]:
    index = _class_method_index(graph)
    normalized = normalize_torn_name(class_name)
    if normalized in index:
        return index[normalized]
    if "." in normalized:
        return set()
    return index.get(_simple_name(normalized), set())
def reset_index_caches() -> None:
    reset_query_caches()
    _CLASS_TAIL_INDEX_CACHE.clear()
    _logger.info("[CallGraph] 索引/查询缓存已归零（build 复位 SSOT 入口）")
CALLGRAPH_PARSE_FAILURE_EXCS: tuple[type[BaseException], ...] = (
    PARSE_DEGRADE_EXC + (OSError, UnicodeDecodeError)
)
CALLGRAPH_BUILD_ERRORS: tuple[type[BaseException], ...] = (
    PARSE_DEGRADE_EXC + (OSError, RuntimeError)
)
MAGIC_METHODS = frozenset({
    "__init__", "__new__", "__del__", "__str__", "__repr__", "__eq__",
    "__hash__", "__call__", "__getitem__", "__setitem__", "__len__",
    "__iter__", "__next__", "__contains__", "__enter__", "__exit__",
    "__getattr__", "__setattr__", "__post_init__", "__init_subclass__",
    "__lt__", "__le__", "__gt__", "__ge__", "__ne__",
    "__getstate__", "__setstate__", "__copy__", "__deepcopy__",
    "__get__", "__set__", "__delete__", "__set_name__",
    "__bool__", "__nonzero__", "__format__", "__sizeof__",
    "__neg__", "__pos__", "__abs__", "__invert__",
    "__add__", "__sub__", "__mul__", "__truediv__", "__floordiv__",
    "__mod__", "__pow__", "__and__", "__or__", "__xor__",
    "__lshift__", "__rshift__", "__iadd__", "__isub__",
})
_FRAMEWORK_PATTERNS = frozenset({
    "get", "post", "put", "delete", "patch", "head", "options",
    "route", "websocket", "api_route",
    "on_event", "middleware", "exception_handler",
    "add_event_handler", "add_exception_handler",
    "add_middleware", "add_route",
    "before_request", "after_request", "teardown_request",
    "teardown_appcontext", "errorhandler", "before_first_request",
    "before_websocket", "after_websocket",
    "task", "periodic_task", "on_after_configure", "on_after_finalize",
    "signals", "actor",
    "command", "group", "argument", "option",
    "pass_context", "pass_obj", "make_pass_decorator",
    "click.command", "click.group", "click.argument", "click.option",
    "click.pass_context", "click.pass_obj", "click.make_pass_decorator",
    "click.option_group", "click.confirmation_option",
    "fixture", "hookimpl", "hookspec",
    "pytest.fixture", "pytest.mark.parametrize", "pytest.hookimpl",
    "pytest.hookspec", "pytest.skip", "pytest.xfail",
    "receiver", "register", "admin_action",
    "django.dispatch.receiver", "admin.register",
    "django.contrib.admin.register",
    "message", "callback_query", "inline_query", "channel_post",
    "edited_message", "poll", "poll_answer", "chat_member",
    "chat_join_request", "error",
    "listens_for", "sqlalchemy.event.listens_for",
    "litestar.get", "litestar.post", "litestar.put", "litestar.delete",
    "typer.app", "typer.command",
    "bottle.route", "bottle.get", "bottle.post",
    "validator", "root_validator", "pydantic.validator",
    "pydantic.field_validator", "pydantic.model_validator",
    "retry", "tenacity.retry",
    "entry_point", "main", "click_command",
})
_SOURCE_MARKERS = ("# UNUSED", "# API:", "# STUB:", "# COVERAGE:", "# BLINDSPOT:")
DECORATOR_CLOSURE_NAMES = frozenset({
    "wrapper", "decorator", "inner", "wrapped", "_wrapper", "_inner", "_wrapped",
})
_NAME_CATEGORY_PATTERNS = (
    ("factory_util", re.compile(
        r'^_(get_|build_|ensure_|init_|create_|make_|lazy_|load_|'
        'save_|fetch_|store_|check_|validate_|compute_|generate_|'
        'parse_|format_|convert_|extract_|resolve_|find_|search_|'
        'update_|insert_|delete_|cleanup_|migrate_|sync_|merge_)')),
    ("db_operation", re.compile(
        r'^_(sql_|db_|conn_|cursor_|query_|execute_|commit_|rollback_)')),
    ("fs_operation", re.compile(
        r'^_(read_|write_|open_|close_|path_|file_|dir_|copy_|move_|remove_|rename_)')),
    ("serialization", re.compile(
        r'^_(json_|yaml_|pickle_|encode_|decode_|serialize_|deserialize_)')),
    ("crypto_auth", re.compile(
        r'^_(hash_|encrypt_|decrypt_|sign_|verify_|token_|auth_)')),
    ("logging_debug", re.compile(
        r'^_(log_|debug_|trace_|print_|dump_|inspect_)')),
    ("network_io", re.compile(
        r'^_(http_|url_|request_|response_|download_|upload_)')),
    ("config_env", re.compile(
        r'^_(config_|env_|setting_|option_|param_|flag_)')),
    ("type_convert", re.compile(
        r'^_(to_|from_|as_|cast_|convert_|transform_)')),
    ("error_handling", re.compile(
        r'^_(error_|warn_|fail_|retry_|fallback_|recover_)')),
)
def _iter_cross_skill_imports(cross_skill_imports) -> Iterator[dict]:
    by_skill = getattr(cross_skill_imports, "by_skill", None)
    if not isinstance(by_skill, dict):
        return
    for files in by_skill.values():
        if not isinstance(files, dict):
            continue
        for imports in files.values():
            if not isinstance(imports, (list, tuple)):
                continue
            for imp in imports:
                if isinstance(imp, dict):
                    yield imp
def _path_text(value) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, (bytes, bytearray)):
        return os.fsdecode(bytes(value))
    if isinstance(value, os.PathLike):
        try:
            return os.fsdecode(os.fspath(value))
        except (TypeError, ValueError):  # jwsgj:silent-ok 纯值降级：非法路径载体按空处理，无副作用可留痕
            return ""
    return ""
def _path_key(path) -> str:
    text = _path_text(path)
    if not text:
        return ""
    return os.path.normcase(os.path.normpath(text)).replace("\\", "/")
def count_project_py_files(project_root) -> int:
    root = _path_text(project_root)
    if not root.strip():
        raise ValueError(
            "count_project_py_files: project_root 不得为空；"
            "空路径不得回退到进程 cwd")
    return count_py_files_under(root)
def _is_windows_drive_colon(text: str, index: int) -> bool:
    return (
        0 < index < len(text) - 1
        and text[index - 1].isalpha()
        and text[index + 1] in "/\\"
        and (index == 1 or text[index - 2] in ":/\\")
    )
def _caller_file_suffix(caller) -> str:
    text = normalize_torn_name(caller)
    for index in range(len(text) - 1, -1, -1):
        if text[index] != ":" or _is_windows_drive_colon(text, index):
            continue
        head, tail = text[:index], text[index + 1:]
        if head and ("/" in tail or "\\" in tail
                     or tail.lower().endswith(".py")):
            return tail
    return ""
def _caller_node_key(caller) -> str:
    text = normalize_torn_name(caller)
    suffix = _caller_file_suffix(text)
    return text[:-(len(suffix) + 1)] if suffix else text
def _caller_is_test(caller, functions: dict) -> bool:
    suffix = _caller_file_suffix(caller)
    if suffix and is_test_file_path(suffix):
        return True
    return is_test_caller_name(_caller_node_key(caller), functions)
def _is_cross_file_call(caller_file, callee_file) -> bool:
    caller_text = _path_text(caller_file)
    callee_text = _path_text(callee_file)
    caller_key = _path_key(caller_text)
    callee_key = _path_key(callee_text)
    if not caller_key or not callee_key:
        return False
    if caller_key == callee_key:
        return False
    if os.path.isabs(caller_text) == os.path.isabs(callee_text):
        return True
    return not (caller_key.endswith("/" + callee_key)
                or callee_key.endswith("/" + caller_key))
def _cross_skill_file_buckets(cross_skill_imports) -> list[dict]:
    by_skill = getattr(cross_skill_imports, "by_skill", None)
    if not isinstance(by_skill, dict):
        return []
    return [files for files in by_skill.values()
            if isinstance(files, dict) and files]
def collect_cross_skill_names(cross_skill_imports) -> set[str]:
    ref_names: set[str] = set()
    for imp in _iter_cross_skill_imports(cross_skill_imports):
        name = imp.get("name")
        if name and not isinstance(name, str):
            name = str(name)
        if name:
            ref_names.add(name)
            ref_names.add(_simple_name(name))
    return ref_names
def _match_name_category(simple_name: str) -> str:
    for category, pattern in _NAME_CATEGORY_PATTERNS:
        if pattern.match(simple_name):
            return category
    return ""
def str_decorators(fnode) -> list[str]:
    decorators = getattr(fnode, "decorators", None)
    if isinstance(decorators, str):
        return [decorators] if decorators else []
    if isinstance(decorators, (list, tuple, set, frozenset)):
        return [d for d in decorators if isinstance(d, str)]
    return []
def _simple_name(value) -> str:
    return normalize_torn_name(value).rsplit(".", 1)[-1]
def _declared_name(value) -> str:
    return value if isinstance(value, str) and value else ""
def _break_identity(filepath, line, name) -> tuple[str, int, str]:
    _line = line if isinstance(line, int) and not isinstance(line, bool) else 0
    return (normalize_torn_name(filepath), _line, normalize_torn_name(name))
def _has_decorator(fnode: Any, name: str) -> bool:
    return any(d == name or d.endswith("." + name)
               for d in str_decorators(fnode))
_ENTRY_POINT_NAMES: frozenset[str] = frozenset({
    "main", "cli", "run", "app", "start", "serve",
})
_ENTRY_POINT_PREFIXES: tuple[str, ...] = ("cmd_",)
_STRONG_ENTRY_POINT_NAMES: frozenset[str] = frozenset({"main", "cli"})
def is_entry_point_name(simple_name: str, *, strong_only: bool = False) -> bool:
    text = normalize_torn_name(simple_name)
    if strong_only:
        return text in _STRONG_ENTRY_POINT_NAMES
    if text.startswith(_ENTRY_POINT_PREFIXES):
        return True
    return text in _ENTRY_POINT_NAMES
def check_framework_decorators(fnode) -> bool:
    for dec in str_decorators(fnode):
        if dec in _FRAMEWORK_PATTERNS:
            return True
        if "." in dec:
            last_part = dec.rsplit(".", 1)[-1]
            if last_part in _FRAMEWORK_PATTERNS:
                return True
    return False
def check_source_markers(fnode, file_lines_cache: dict,
                         project_root: str | None = None) -> bool:
    resolved = next(
        (path for path in _source_path_candidates(fnode, project_root)
         if os.path.isfile(path)), "")
    if not resolved:
        return False
    lines = _read_lines_cached(resolved, file_lines_cache)
    if not lines:
        return False
    return any(m in _marker_context(fnode, lines) for m in _SOURCE_MARKERS)
def _source_path_candidates(
        fnode, project_root: str | None) -> list[str]:
    filepath = _path_text(getattr(fnode, 'filepath', ''))
    if not filepath:
        return []
    if os.path.isabs(filepath):
        return [filepath]
    root = project_root
    if root is None:
        root = getattr(fnode, '_project_root', None)
    root = _path_text(root)
    if not root:
        return [filepath]
    try:
        root_path = os.path.realpath(root)
        candidate = os.path.realpath(os.path.join(root_path, filepath))
        root_key = os.path.normcase(root_path)
        candidate_key = os.path.normcase(candidate)
        if os.path.commonpath((root_key, candidate_key)) != root_key:
            return []
    except (OSError, TypeError, ValueError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return []
    return [candidate]
def _marker_context(fnode, lines: list) -> str:
    base_line = (getattr(fnode, "decor_line", 0)
                 or getattr(fnode, "start_line", 0) or 0)
    line_idx = max(0, base_line - 1)
    end_line = getattr(fnode, "end_line", 0)
    end_idx = (end_line if isinstance(end_line, int) and end_line > line_idx
               else line_idx + 5)
    return "".join(lines[max(0, line_idx - 3):end_idx])
def _read_lines_cached(resolved: str, file_lines_cache: dict) -> list | None:
    if resolved in file_lines_cache:
        return file_lines_cache[resolved]
    try:
        with open(resolved, encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
    except OSError as e:
        _logger.debug("行读取失败: %s", e)
        lines = None
    file_lines_cache[resolved] = lines
    return lines
def build_exemption_classification(orphans) -> dict:
    orphans = list(orphans) if orphans is not None else []
    categories: Counter = Counter()
    by_risk: Counter = Counter(dict.fromkeys(EXEMPTION_RISK.values(), 0))
    for fnode in orphans:
        category = classify_exemption(fnode) or UNCLASSIFIED_CATEGORY
        categories[category] += 1
        by_risk[EXEMPTION_RISK.get(category, "medium")] += 1
    ordered = {name: categories[name] for name in EXEMPTION_CATEGORY_ORDER
               if name in categories}
    return {
        "total": len(orphans),
        "categories": ordered,
        "by_risk": dict(by_risk),
        "risk_labels": {name: EXEMPTION_LABELS.get(name, name)
                        for name in ordered},
    }
def classify_exemption(fnode) -> str:
    simple_name = _simple_name(fnode.name)
    class_name = fnode.class_name
    is_method = fnode.is_method
    decorators = str_decorators(fnode)
    filepath = normalize_node_str(fnode.filepath or "")
    return (_classify_entry_forms(fnode, simple_name, filepath)
            or _classify_export_forms(fnode)
            or _classify_kind_forms(fnode, simple_name, is_method)
            or _classify_risk_forms(fnode, simple_name, is_method,
                                    class_name, decorators))
def _is_package_init_file(filepath: str) -> bool:
    return os.path.basename(normalize_torn_name(filepath or "")).lower() == "__init__.py"
def _classify_entry_forms(fnode, simple_name: str, filepath: str) -> str:
    if is_entry_point_name(simple_name, strong_only=True):
        return "cli_entry"
    if simple_name.startswith("test_"):
        return "test_func"
    if fnode.is_public and _is_package_init_file(filepath):
        return "init_py_entry"
    return ""
def _is_exported_member(exports, fnode) -> bool:
    if getattr(fnode, '_in_all_exports', False):
        return True
    if isinstance(exports, str):
        exports = {exports} if exports else set()
    if not exports:
        return False
    name = normalize_torn_name(getattr(fnode, 'name', '') or '')
    if name and name in exports:
        return True
    filepath = _path_text(getattr(fnode, 'filepath', ''))
    if name and filepath:
        if os.path.isabs(filepath):
            root = _path_text(getattr(fnode, '_project_root', ''))
            abs_root = os.path.abspath(root) if root else ''
            if (not abs_root
                    or os.path.splitdrive(filepath)[0]
                    != os.path.splitdrive(abs_root)[0]):
                filepath = ''
            else:
                filepath = os.path.relpath(filepath, abs_root)
        if filepath:
            module_name = path_to_dotted_module(filepath)
            if _qualify_module_member(module_name, name) in exports:
                return True
    if getattr(fnode, 'is_method', False):
        class_name = normalize_torn_name(
            getattr(fnode, 'class_name', '') or '')
        return bool(class_name and class_name in exports)
    return bool(name and _simple_name(name) in exports)
def _classify_export_forms(fnode) -> str:
    if fnode.is_public:
        return "public_api"
    exports = getattr(fnode, '_global_exports', None) or set()
    if _is_exported_member(exports, fnode):
        return "public_api"
    return ""
def _classify_kind_forms(fnode, simple_name: str, is_method: bool) -> str:
    for category, matched in (
        ("magic_method", is_dunder_name(simple_name)),
        ("polymorphic_method",
         is_method and simple_name in POLYMORPHIC_METHODS),
        ("ast_visitor", is_method and simple_name.startswith("visit_")),
        ("property_method", fnode.is_property),
        ("decorator_closure", simple_name in DECORATOR_CLOSURE_NAMES),
        ("event_callback", simple_name.startswith(("on_", "handle_"))),
    ):
        if matched:
            return category
    return ""
def _classify_risk_forms(fnode, simple_name: str, is_method: bool,
                         class_name, decorators: list) -> str:
    if _is_register_decorated(decorators):
        return "decorator_register"
    if check_framework_decorators(fnode):
        return "framework_decorator"
    category = _match_name_category(simple_name)
    if category:
        return category
    return _classify_fallback_forms(simple_name, is_method, class_name)
def _is_register_decorated(decorators: list) -> bool:
    return any(
        re.search(r"(?<!un)(?<!de)register", d.lower()) is not None
        for d in decorators)
def _classify_fallback_forms(simple_name: str, is_method: bool,
                             class_name) -> str:
    if is_method and class_name:
        return "instance_method"
    if simple_name.startswith("_"):
        return "internal_util"
    return ""
UNCLASSIFIED_CATEGORY = "unclassified"
EXEMPTION_RISK = MappingProxyType({
    "magic_method": "zero", "public_api": "zero", "cli_entry": "zero",
    "test_func": "zero", "init_py_entry": "zero", "property_method": "zero",
    "decorator_closure": "zero", "framework_decorator": "zero",
    "instance_method": "low", "polymorphic_method": "low", "ast_visitor": "low",
    "event_callback": "low", "decorator_register": "low", "serialization": "low",
    "crypto_auth": "low", "logging_debug": "low", "network_io": "low",
    "config_env": "low", "type_convert": "low", "error_handling": "low",
    "factory_util": "medium", "internal_util": "medium",
    "fs_operation": "medium", "db_operation": "medium",
    UNCLASSIFIED_CATEGORY: "medium",
})
EXEMPTION_CATEGORY_ORDER: tuple[str, ...] = tuple(EXEMPTION_RISK)
EXEMPTION_LABELS = MappingProxyType({
    "magic_method": "魔术方法", "public_api": "公开API", "cli_entry": "CLI入口",
    "test_func": "测试函数", "init_py_entry": "包入口", "property_method": "属性方法",
    "decorator_closure": "装饰器闭包", "framework_decorator": "框架装饰器",
    "instance_method": "实例方法", "polymorphic_method": "多态方法",
    "ast_visitor": "AST Visitor", "event_callback": "事件回调",
    "decorator_register": "装饰器注册", "serialization": "序列化",
    "crypto_auth": "加密认证", "logging_debug": "日志调试",
    "network_io": "网络IO", "config_env": "配置环境",
    "type_convert": "类型转换", "error_handling": "错误处理",
    "factory_util": "工厂工具", "internal_util": "内部工具",
    "fs_operation": "文件系统", "db_operation": "数据库操作",
    UNCLASSIFIED_CATEGORY: "未分类",
})

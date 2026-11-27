from __future__ import annotations

import ast
import bisect
import importlib
import inspect
import io
import logging
import math
import os
import re
import threading
import time
import tokenize
from collections.abc import Callable, Mapping
from typing import Any, NamedTuple

from jwsgj.diag_detector_findings import (
    REGISTRY_BUILDABLE_PARAMS,
    REGISTRY_CID_EMITS,
    REGISTRY_SKIP_IDS,
    RETIRED_RULE_IDS,
    as_text,
    build_detector_kwargs,
    collect_findings,
    finding_file,
    finding_line,
    finding_rule_id,
    normalize_id_set,
    retired_rule_key,
)
from jwsgj.diag_shared_ast_nodes import (
    is_mutable_default,
    is_star_import,
    parse_ast_safely,
)
from jwsgj.diag_shared_ast_views import (
    register_cache_release,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    aligned_source_lines,
    is_memory_source,
    parse_py_file,
    read_py_source,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
    string_comment_spans,
)
from jwsgj.diag_types_normalize import (
    int_or,
    severity_rank_of,
)
from jwsgj.diag_types_vocab import (
    CONCLUSION_V2_MAP,
)
from jwsgj.log_config import (
    log_swallowed,
    write_detector_liveness,
    write_module_run,
)
from jwsgj.prevention_refs_main import (
    CODE_REFS,
    enrich_diag_findings,
    norm_rule_id,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'EXEC_SWALLOWED_EXCEPTIONS',
    'GATE_RULE_MODULES',
    'WIRING_MODULES',
    'DetectorFn',
    'DetectorRegistry',
    'apply_detector_liveness_gate',
    'build_solidified_detector',
    'detector_catalog',
    'early_channel',
    'early_channels',
    'engine_channels',
    'ensure_tree',
    'generate_module_detectors',
    'get_registry',
    'init_reentrant',
    'iter_heuristic_matches',
    'iter_regex_matches',
    'make_detector',
    'pattern_matches_ast_heuristics',
    'penalize_dead_detector_findings',
    'preflight_diagnostic_check',
    'probe_filepath_for_rule',
    'rebuild_registry',
    'register_detector_catalog',
    'register_rebuild_hook',
    'reset_detector_catalogs',
    'reset_registry',
    'run_bounded_channel',
    'run_channel',
    'run_detector_liveness_probe',
    'run_rebuild_hooks',
    'set_auto_register_hook',
    'set_registry_reset_hook',
]
_log = logging.getLogger(__name__)
_DEFAULT_SOLIDIFIED_PATTERN_TYPE = "ast"
_DEFAULT_SOLIDIFIED_PATTERN = ""
_DEFAULT_SOLIDIFIED_SEVERITY = "P2"
_DEFAULT_PREFLIGHT_MIN_SEVERITY = "P2"
_DEFAULT_PREFLIGHT_MAX_FINDINGS = 100
_DETECTOR_REQUIRES_TREE_ATTR = "_jwsgj_requires_tree"
_MODULE_RUN_RESERVED_KEYS = frozenset(
    {"module", "entry", "outcome", "duration_ms"})
def _parse_or_none(source: str, channel: str = "") -> ast.Module | None:
    tree, error = parse_ast_safely(source)
    if error is None:
        return tree
    if channel:
        log_swallowed(
            __name__, error,
            context=f'{channel}:{type(error).__name__}')
    else:
        _log.warning("[Detectors] 解析代码失败,返回已收集: %s", error)
    return None
def ensure_tree(tree: ast.AST | None, filepath: str) -> ast.AST | None:
    if tree is not None:
        return tree
    if not filepath:
        return None
    if is_memory_source(filepath):
        _source, mem_tree = parse_py_file(filepath, quiet=True)
        return mem_tree
    if not os.path.isfile(filepath):
        return None
    source = read_py_source(filepath)
    if source is None:
        return None
    return _parse_or_none(source)
DetectorFn = Callable[..., list[dict[str, Any]]]
EXEC_SWALLOWED_EXCEPTIONS = (
    AttributeError, IndexError, KeyError, TypeError, ValueError,
    RuntimeError, SyntaxError, re.error,
)
_CONTEXT_PARAM_ALIASES: dict[str, str] = {
    "source_code": "code",
    "source_text": "code",
    "file_path": "filepath",
}
def _canonicalize_context_kwargs(kwargs: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(kwargs)
    for alias, canonical in _CONTEXT_PARAM_ALIASES.items():
        if alias not in normalized:
            continue
        value = normalized.pop(alias)
        if not normalized.get(canonical):
            normalized[canonical] = value
    return normalized
def _context_value_missing(key: str, value: Any) -> bool:
    return (key in REGISTRY_BUILDABLE_PARAMS
            and (value is None or value == ""
                 or (key == "source_lines" and not value)))
def _source_text_from_lines(source_lines: Any) -> str:
    if isinstance(source_lines, str):
        return source_lines
    if not isinstance(source_lines, (list, tuple)):
        return ""
    chunks = [str(line) for line in source_lines]
    return "".join(
        chunk if index == len(chunks) - 1 or chunk.endswith(("\n", "\r"))
        else chunk + "\n"
        for index, chunk in enumerate(chunks))
def _detector_context_values(kwargs: dict[str, Any]) -> dict[str, Any]:
    code = kwargs.get("code")
    if not code:
        code = (kwargs.get("source_code") or kwargs.get("source_text")
                or kwargs.get("source") or code)
    source_lines = kwargs.get("source_lines")
    if isinstance(source_lines, str):
        if not code:
            code = source_lines
        source_lines = aligned_source_lines(source_lines)
    else:
        line_text = _source_text_from_lines(source_lines)
        if not code and line_text:
            code = line_text
    if not source_lines and isinstance(code, str):
        source_lines = aligned_source_lines(code)
    tree = kwargs.get("tree")
    if tree is None and isinstance(code, str) and code:
        tree = _parse_or_none(code, "DetectorRegistry.run")
    return {
        "tree": tree,
        "filepath": kwargs.get("filepath") or kwargs.get("file_path") or "",
        "source_lines": source_lines if source_lines is not None else [],
        "code": code if code is not None else "",
    }
def _normalize_detector_id(value: Any) -> str:
    if value is None:
        return ""
    text = value if isinstance(value, str) else str(value)
    return text.strip()
class _SignatureInfo(NamedTuple):
    params: frozenset[str]
    accepts_var_keyword: bool
    positional_only: tuple[inspect.Parameter, ...]
def _inspect_signature_params(fn: Callable) -> _SignatureInfo | None:
    try:
        parameters = list(inspect.signature(fn).parameters.values())
    except (TypeError, ValueError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_inspect_signature_params:TypeError+')
        return None
    return _SignatureInfo(
        params=frozenset(
            p.name for p in parameters
            if p.kind not in (inspect.Parameter.VAR_KEYWORD,
                              inspect.Parameter.VAR_POSITIONAL)),
        accepts_var_keyword=any(
            p.kind is inspect.Parameter.VAR_KEYWORD for p in parameters),
        positional_only=tuple(
            p for p in parameters
            if p.kind is inspect.Parameter.POSITIONAL_ONLY),
    )
def _call_with_signature(
    fn: DetectorFn,
    kwargs: dict[str, Any],
    positional_only: tuple[inspect.Parameter, ...],
) -> list[dict[str, Any]]:
    if not positional_only:
        return fn(**kwargs)
    args: list[Any] = []
    remaining = dict(kwargs)
    for parameter in positional_only:
        if parameter.name in remaining:
            args.append(remaining.pop(parameter.name))
        elif parameter.default is not inspect.Parameter.empty:
            args.append(parameter.default)
        else:
            raise TypeError(
                f"missing required positional-only argument: "
                f"{parameter.name!r}")
    return fn(*args, **remaining)
class _DetectorRunContext(NamedTuple):
    tree: Any
    filepath: str
    source_lines: list[str]
    code: str
    channel: str
def _canonical_id_set(ids: Any) -> set[str]:
    return {_norm for _norm in
            (norm_rule_id(_raw) for _raw in normalize_id_set(ids)) if _norm}
def _id_matches(cid: str, ids: set[str] | None) -> bool:
    if ids is None:
        return False
    return cid in ids or norm_rule_id(cid) in ids
def _warn_unbuildable_detector(check_id: str, params: frozenset[str]) -> None:
    unbuildable = params - REGISTRY_BUILDABLE_PARAMS
    if not unbuildable or _id_matches(check_id, REGISTRY_SKIP_IDS):
        return
    _log.warning(
        "[Detectors] 检测器 %s 形参 %s 不在注册表可构建集合，"
        "文件通道将跳过该检测器", check_id, sorted(unbuildable))
def _detector_selected(cid: str,
                       incl: set[str] | None,
                       excl: set[str] | None) -> bool:
    if incl is not None:
        return _id_matches(cid, incl) and not _id_matches(cid, excl)
    if _id_matches(cid, REGISTRY_SKIP_IDS):
        return False
    return not _id_matches(cid, excl)
def _resolve_adhoc_target(target: Any) -> DetectorFn | None:
    if callable(target):
        return target
    if isinstance(target, str):
        _mod, _, _fname = target.rpartition(".")
        try:
            return getattr(importlib.import_module(_mod), _fname, None)  # lazy-by-design — 插件/注册表按名装载，静态导入会破坏插件边界
        except Exception:
            _log.warning("run_adhoc_detectors: 解析 %s 失败", target)
            return None
    return None
def _prepare_adhoc_run(
        code: Any, checks: Any) -> tuple[ast.Module | None, list[str]] | None:
    if not isinstance(code, str) or not code or not checks:
        return None
    if not isinstance(checks, Mapping):
        _log.debug(
            "run_adhoc_detectors: checks 非映射结构(%s),已跳过",
            type(checks).__name__,
        )
        return None
    tree = _parse_or_none(
        code, "DetectorRegistry.run_adhoc_detectors")
    return tree, aligned_source_lines(code)
class DetectorRegistry:
    def __init__(self) -> None:
        self._detectors: dict[str, DetectorFn] = {}
        self._param_names: dict[str, frozenset] = {}
        self._accepts_var_keyword: dict[str, bool] = {}
        self._positional_only: dict[str, tuple[inspect.Parameter, ...]] = {}
        self._solidified_authority: dict[str, tuple[Callable, Any]] = {}
    def register(self, check_id: str, fn: DetectorFn) -> None:
        check_id = _normalize_detector_id(check_id)
        if not check_id:
            raise ValueError(
                "detector id 不能为空：空 ID 无法被按名通道选中，"
                "登记成功即为静默死检测器")
        if not callable(fn):
            raise TypeError(
                f"detector {check_id!r} 不可调用"
                f"（{type(fn).__name__}）：接线错误必须显式失败")
        self._detectors[check_id] = fn
        info = _inspect_signature_params(fn)
        if info is None:
            _log.debug("Detector %s 签名不可内省：全透传", check_id)
            self._param_names[check_id] = frozenset()
            self._accepts_var_keyword[check_id] = True
            self._positional_only[check_id] = ()
        else:
            self._param_names[check_id] = info.params
            self._accepts_var_keyword[check_id] = info.accepts_var_keyword
            self._positional_only[check_id] = info.positional_only
            _warn_unbuildable_detector(check_id, info.params)
        _log.debug("Registered detector: %s", check_id)
    def register_batch(self, mapping: dict[str, DetectorFn]) -> None:
        for check_id, fn in mapping.items():
            self.register(check_id, fn)
    def run(self, check_id: str, **kwargs: Any) -> list[dict[str, Any]]:
        check_id = _normalize_detector_id(check_id)
        fn = self._detectors.get(check_id)
        if fn is None:
            return []
        try:
            adapted = self._adapt_kwargs(check_id, kwargs)
            return _call_with_signature(
                fn, adapted, self._positional_only.get(check_id, ()))
        except EXEC_SWALLOWED_EXCEPTIONS:
            _log.exception("Detector %s raised exception", check_id)
            return []
    def _adapt_kwargs(
            self, check_id: str, kwargs: dict[str, Any],
    ) -> dict[str, Any]:
        allowed = self._param_names.get(check_id)
        if allowed is None:
            return kwargs
        normalized = _canonicalize_context_kwargs(kwargs)
        adapted = {
            key: value for key, value in normalized.items()
            if key in allowed and not _context_value_missing(key, value)}
        missing = allowed - adapted.keys()
        context: dict[str, Any] | None = None
        if missing:
            context = _detector_context_values(normalized)
            adapted.update(build_detector_kwargs(
                frozenset(missing), **context))
            if "index" in missing and context["tree"] is not None:
                adapted["index"] = tree_nodes(context["tree"])
        if self._accepts_var_keyword.get(check_id, True):  # jwsgj:suppress CQ-06 — dict.get 默认值为 true 哨兵，条件判定有意为之
            adapted.update({key: value for key, value in normalized.items()
                            if key not in allowed})
            if context is None:
                context = _detector_context_values(normalized)
            for key, value in context.items():
                if _context_value_missing(key, adapted.get(key)):
                    adapted[key] = value
        return adapted
    @staticmethod
    def _invoke_detector(
        cid: str,
        fn: DetectorFn,
        params: frozenset[str] | None,
        ctx: _DetectorRunContext,
        index_nodes: list[Any] | None = None,
        *,
        accepts_var_keyword: bool = True,
        positional_only: tuple[inspect.Parameter, ...] = (),
    ) -> list[dict[str, Any]] | None:
        if not _detector_can_run_with_tree(fn, ctx.tree):
            return None
        if params is None or not params <= REGISTRY_BUILDABLE_PARAMS:
            return None
        if not params and not accepts_var_keyword:
            kwargs: dict[str, Any] = {}
        else:
            kwargs = build_detector_kwargs(
                params, ctx.tree, ctx.filepath, ctx.source_lines, ctx.code)
        if accepts_var_keyword:
            for key, value in (
                ("tree", ctx.tree), ("filepath", ctx.filepath),
                ("source_lines", ctx.source_lines), ("code", ctx.code),
            ):
                kwargs.setdefault(key, value)
        if "index" in params:
            kwargs["index"] = (
                index_nodes if index_nodes is not None
                else tree_nodes(ctx.tree))
        try:
            return _call_with_signature(fn, kwargs, positional_only)
        except EXEC_SWALLOWED_EXCEPTIONS as _e:
            _log.debug("%s suppressed %s: %s", ctx.channel, cid, _e)
            return []
    def run_file_detectors(
        self,
        code: str,
        filepath: str = "",
        *,
        tree: Any = None,
        include_ids: set[str] | None = None,
        exclude_ids: set[str] | None = None,
    ) -> list[dict[str, Any]]:
        if not isinstance(code, str) or not code:
            return []
        if tree is None:
            tree = _parse_or_none(
                code, "DetectorRegistry.run_file_detectors")
        ctx = _DetectorRunContext(
            tree, filepath, aligned_source_lines(code), code,
            "run_file_detectors")
        incl = (_canonical_id_set(include_ids)
                if include_ids is not None else None)
        excl = (_canonical_id_set(exclude_ids)
                if exclude_ids is not None else None)
        return self._collect_file_findings(ctx, incl, excl)
    def _collect_file_findings(
        self,
        ctx: _DetectorRunContext,
        include_ids: set[str] | None,
        exclude_ids: set[str] | None,
    ) -> list[dict[str, Any]]:
        findings: list[dict[str, Any]] = []
        index_nodes: list[Any] | None = None
        suppress_map = None
        for cid, fn in list(self._detectors.items()):
            if not _detector_selected(cid, include_ids, exclude_ids):
                continue
            params = self._param_names.get(cid)
            if params is not None and "index" in params and index_nodes is None:
                index_nodes = tree_nodes(ctx.tree)
            result = self._invoke_detector(
                cid, fn, params, ctx, index_nodes,
                accepts_var_keyword=self._accepts_var_keyword.get(cid, True),
                positional_only=self._positional_only.get(cid, ()))
            if result is None:
                continue
            harvested, suppress_map = collect_findings(
                result, cid, ctx.filepath, ctx.code, suppress_map)
            findings.extend(harvested)
        return findings
    def run_adhoc_detectors(
        self,
        code: str,
        filepath: str = "",
        checks: dict[str, Any] | None = None,
        *,
        exclude_ids: set[str] | None = None,
    ) -> tuple[list[dict[str, Any]], int]:
        findings: list[dict[str, Any]] = []
        prepared = _prepare_adhoc_run(code, checks)
        if prepared is None:
            return findings, 0
        tree, source_lines = prepared
        _normalized_exclude = (_canonical_id_set(exclude_ids)
                               if exclude_ids is not None else None)
        suppress_map = None
        invoked = 0
        ctx = _DetectorRunContext(tree, filepath, source_lines, code,
                                  "run_adhoc_detectors")
        for cid, target in list(checks.items()):
            harvested, suppress_map, ran = self._run_adhoc_check(
                str(cid), target, ctx, _normalized_exclude, suppress_map)
            invoked += 1 if ran else 0
            findings.extend(harvested)
        return findings, invoked
    def _run_adhoc_check(
        self,
        cid: str,
        target: Any,
        ctx: _DetectorRunContext,
        exclude_ids: set[str] | None,
        suppress_map: Any,
    ) -> tuple[list[dict[str, Any]], Any, bool]:
        if _id_matches(cid, exclude_ids):
            return [], suppress_map, False
        fn = _resolve_adhoc_target(target)
        if fn is None:
            return [], suppress_map, False
        info = _inspect_signature_params(fn)
        if info is None:
            _log.debug("run_adhoc_detectors: 解析 %s 签名失败", cid)
            return [], suppress_map, False
        result = self._invoke_detector(
            cid, fn, info.params, ctx,
            accepts_var_keyword=info.accepts_var_keyword,
            positional_only=info.positional_only)
        if result is None:
            _log.debug(
                "run_adhoc_detectors: %s 签名不兼容逐文件执行，跳过", cid)
            return [], suppress_map, False
        harvested, suppress_map = collect_findings(
            result, cid, ctx.filepath, ctx.code, suppress_map)
        return harvested, suppress_map, True
    def runs_in_file_channel(self, check_id: str) -> bool:
        params = self._param_names.get(_normalize_detector_id(check_id))
        return params is not None and params <= REGISTRY_BUILDABLE_PARAMS
    def is_registered(self, check_id: str) -> bool:
        return _normalize_detector_id(check_id) in self._detectors
    def list_registered(self) -> list[str]:
        return sorted(self._detectors.keys())
    def get(self, check_id: str) -> DetectorFn | None:
        return self._detectors.get(_normalize_detector_id(check_id))
    def count(self) -> int:
        return len(self._detectors)
    def get_status(self) -> dict[str, Any]:
        return {
            "timestamp": time.time(),
            "class": self.__class__.__name__,
            "registered": len(self._detectors),
            "initialized": self is _global_registry and _registry_initialized,
        }
    def clear(self) -> None:
        self._detectors = {}
        self._param_names = {}
        self._accepts_var_keyword = {}
        self._positional_only = {}
        self._solidified_authority = {}
    def unregister(self, check_id: str) -> bool:
        check_id = _normalize_detector_id(check_id)
        existed = (check_id in self._detectors
                   or check_id in self._param_names
                   or check_id in self._accepts_var_keyword
                   or check_id in self._positional_only
                   or check_id in self._solidified_authority)
        self._detectors.pop(check_id, None)
        self._param_names.pop(check_id, None)
        self._accepts_var_keyword.pop(check_id, None)
        self._positional_only.pop(check_id, None)
        self._solidified_authority.pop(check_id, None)
        if existed:
            _log.debug("Unregistered detector: %s", check_id)
        return existed
    def install_solidified_authority(
        self, authority: Mapping[str, tuple[Callable, Any]],
    ) -> int:
        installed = 0
        if not isinstance(authority, Mapping):
            _log.warning(
                "[Detectors] 固化权威登记入参非映射(%s)，按未安装处理",
                type(authority).__name__)
            return 0
        for rid, pair in authority.items():
            try:
                checker, rule = pair
            except (TypeError, ValueError) as _e:
                log_swallowed(
                    __name__, _e,
                    context=("DetectorRegistry.install_solidified_authority:"
                             f"{type(_e).__name__}"))
                continue
            if not callable(checker):
                _log.warning(
                    "[Detectors] 固化权威规则 %r 的 checker 不可调用(%s)，"
                    "跳过安装", rid, type(checker).__name__)
                continue
            _rid = _normalize_detector_id(rid)
            if not _rid:
                _log.debug("[Detectors] 跳过空权威规则 ID: %r", rid)
                continue
            self._solidified_authority[_rid] = (checker, rule)
            installed += 1
        return installed
    def register_solidified_rule(
        self,
        rule_id: str,
        pattern_type: str | None = None,
        pattern: str | None = None,
        severity: str | None = None,
        exempt_cli_entry: bool = False,
        code_only: bool = False,
    ) -> None:
        rule_id = _normalize_detector_id(rule_id)
        spec = _resolve_solidified_spec(pattern_type, pattern, severity)
        _authority_pair = (self._solidified_authority.get(rule_id)
                           if spec.pattern_type == "ast" else None)
        detector = build_solidified_detector(
            rule_id, spec.pattern_type, spec.pattern, spec.severity,
            _authority_pair, exempt_cli_entry, code_only)
        self.register(rule_id, detector)
        _log.info("Registered solidified rule as detector: %s", rule_id)
_DETECTOR_CATALOGS: dict[str, dict] = {}
_global_registry: DetectorRegistry | None = None
_registry_initialized: bool = False
_registry_init_lock = threading.RLock()
init_reentrant = threading.local()
_auto_register_hook: Callable[[], None] | None = None
_registry_reset_hook: Callable[[], None] | None = None
_hook_missing_warned: bool = False
_REBUILD_HOOKS: dict[str, Callable[[], None]] = {}
def get_registry() -> DetectorRegistry:
    global _registry_initialized
    if _registry_initialized and _global_registry is not None:
        return _global_registry
    if getattr(init_reentrant, "active", False):
        return _ensure_registry_instance()
    with _registry_init_lock:
        registry = _ensure_registry_instance()
        if not _registry_initialized:
            _run_auto_register_hook()
            _registry_initialized = True
    return registry
def _ensure_registry_instance() -> DetectorRegistry:
    global _global_registry
    if _global_registry is None:
        _global_registry = DetectorRegistry()
    return _global_registry
def _run_auto_register_hook() -> None:
    global _hook_missing_warned
    if _auto_register_hook is None:
        if not _hook_missing_warned:
            _log.warning(
                "[Registry] 自动注册钩子缺失（接线引导模块未注入），"
                "按空注册表放行；注入后自动补全注册")
            _hook_missing_warned = True
        return
    _auto_register_hook()
def set_auto_register_hook(hook: Callable[[], None] | None) -> None:
    global _auto_register_hook, _registry_initialized
    _auto_register_hook = hook
    _registry_initialized = False
def set_registry_reset_hook(hook: Callable[[], None] | None) -> None:
    global _registry_reset_hook
    _registry_reset_hook = hook
def register_detector_catalog(name: str, entries: dict[str, Any]) -> None:
    _DETECTOR_CATALOGS.setdefault(name, {}).update(entries)
def detector_catalog(name: str) -> dict:
    get_registry()
    if name not in _DETECTOR_CATALOGS:
        raise KeyError(
            f"检测器目录未登记: {name}"
            "（规则族自注册器/接线声明缺失或未派发）")
    return dict(_DETECTOR_CATALOGS[name])
def reset_detector_catalogs() -> None:
    _DETECTOR_CATALOGS.clear()
_EARLY_CHANNEL_CATALOG = "early_channels"
_ENGINE_CHANNEL_CATALOG = "engine_channels"
def _channel_entries(catalog_name: str,
                     min_len: int) -> list[tuple[str, tuple]]:
    valid: list[tuple[str, tuple]] = []
    for label, spec in detector_catalog(catalog_name).items():
        if not isinstance(spec, (tuple, list)) or len(spec) < min_len:
            _log.warning("[Detectors] %s 通道 %s 声明缺列(%s)，已跳过",
                         catalog_name, label, type(spec).__name__)
            continue
        order = spec[0]
        if (not isinstance(order, (int, float)) or isinstance(order, bool)
                or (isinstance(order, float) and not math.isfinite(order))):
            _log.warning("[Detectors] %s 通道 %s 的 order 非有限数值(%r)，已跳过",
                         catalog_name, label, order)
            continue
        valid.append((label, tuple(spec)))
    return sorted(valid, key=lambda kv: kv[1][0])
def early_channels() -> list[tuple[str, Callable[..., Any], bool]]:
    return [(label, spec[1], bool(spec[2]))
            for label, spec in _channel_entries(_EARLY_CHANNEL_CATALOG, 3)]
def early_channel(label: str) -> tuple[Callable[..., Any], bool]:
    for name, run, post_exclude in early_channels():
        if name == label:
            return run, post_exclude
    raise KeyError(f"早期检查通道未登记: {label}")
def engine_channels() -> list[tuple[str, Callable[..., Any]]]:
    return [(label, spec[1])
            for label, spec in _channel_entries(_ENGINE_CHANNEL_CATALOG, 2)]
def register_rebuild_hook(label: str, fn: Callable[[], None]) -> None:
    _REBUILD_HOOKS.setdefault(label, fn)
def run_rebuild_hooks() -> bool:
    succeeded = True
    for label, fn in list(_REBUILD_HOOKS.items()):
        try:
            fn()
        except Exception:
            succeeded = False
            _log.warning("注册表重建参与者 %s 失败，保留既有状态", label,
                         exc_info=True)
    return succeeded
WIRING_MODULES: tuple[str, ...] = (
    "jwsgj.diag_symbol_integrity",
    "jwsgj.diag_wiring_exc",
    "jwsgj.diag_wiring_exc_flow",
    "jwsgj.diag_wiring_import_scan",
    "jwsgj.diag_wiring_symbol_scan",
    "jwsgj.diag_wiring_imports",
    "jwsgj.diag_structure_rules",
    "jwsgj.diag_gate_arch",
    "jwsgj.diag_gate_io_control",
    "jwsgj.diag_gate_class",
    "jwsgj.diag_gate_class_protocol",
    "jwsgj.diag_guard_sql_connection",
    "jwsgj.diag_guard_sql_statement",
    "jwsgj.diag_merge_safety",
    "jwsgj.diag_rules_api_risk",
    "jwsgj.diag_rules_py_syntax",
    "jwsgj.diag_rules_expr_forms",
    "jwsgj.diag_rules_numeric_guard",
    "jwsgj.diag_rules_runtime",
    "jwsgj.diag_rules_text_damage",
    "jwsgj.diag_runtime_objects",
    "jwsgj.diag_traps_async",
    "jwsgj.diag_traps_blocking",
    "jwsgj.diag_traps_coding",
    "jwsgj.diag_traps_payload",
    "jwsgj.diag_traps_binding",
    "jwsgj.diag_traps_guard",
    "jwsgj.diag_se_data",
    "jwsgj.diag_se_injection",
    "jwsgj.diag_se_stdlib",
    "jwsgj.diag_security_diagnoser",
    "jwsgj.diag_pattern_rules",
    "jwsgj.diag_testing_static",
    "jwsgj.diag_smell_detector",
    "jwsgj.diag_solidify_rules",
    "jwsgj.diag_verify_contract",
    "jwsgj.diag_audit_container",
    "jwsgj.diag_audit_none_guard",
    "jwsgj.prevention_logic_refs",
    "jwsgj.prevention_write_checks",
)
GATE_RULE_MODULES: tuple[str, ...] = (
    "jwsgj.diag_structure_rules",
    "jwsgj.diag_gate_arch",
    "jwsgj.diag_gate_expr",
    "jwsgj.diag_gate_expr_flow",
    "jwsgj.diag_gate_loop",
    "jwsgj.diag_gate_scope_bind",
    "jwsgj.diag_gate_io_control",
    "jwsgj.diag_gate_class",
    "jwsgj.diag_gate_class_protocol",
)
def make_detector(check_id: str) -> DetectorFn:
    def detector(
        tree=None, source_lines=None, filepath="", node=None,
        context=None, **kwargs: Any,
    ) -> Any:
        return get_registry().run(
            check_id,
            tree=tree, source_lines=source_lines, filepath=filepath,
            node=node, context=context, **kwargs
        )
    detector.__name__ = f"check_{check_id}"
    detector.__qualname__ = f"check_{check_id}"
    detector.__doc__ = f"检测器 {check_id} — 通过 DetectorRegistry 动态调度."
    return detector
def generate_module_detectors(module: Any, check_ids: list[str]) -> None:
    for cid in check_ids:
        setattr(module, f"check_{cid}", make_detector(cid))
def reset_registry() -> dict[str, int]:
    global _registry_initialized, _global_registry
    before = get_registry().count()
    with _registry_init_lock:
        previous_registry = _global_registry
        previous_initialized = _registry_initialized
        previous_catalogs = {
            name: dict(entries) for name, entries in _DETECTOR_CATALOGS.items()}
        try:
            if _registry_reset_hook is not None:
                _registry_reset_hook()
            _registry_initialized = False
            _global_registry = DetectorRegistry()
            reset_detector_catalogs()
            reg = get_registry()
        except Exception:
            _global_registry = previous_registry
            _registry_initialized = previous_initialized
            _DETECTOR_CATALOGS.clear()
            _DETECTOR_CATALOGS.update(previous_catalogs)
            raise
    after = reg.count()
    _log.info(
        "DetectorRegistry rebuilt: %d -> %d detectors", before, after)
    return {"before": before, "after": after}
def rebuild_registry() -> bool:
    try:
        if not run_rebuild_hooks():
            _log.warning("检测器注册表重建中止，保留既有注册表")
            return False
        reset_registry()
    except Exception:
        _log.warning("DetectorRegistry 重建失败，保留既有注册表", exc_info=True)
        return False
    _log.info("检测器注册表已重建")
    return True
def _release_detector_registry() -> dict:
    rebuilt = rebuild_registry()
    return {"registries": rebuilt, "project_context": rebuilt}
register_cache_release(
    "registries", _release_detector_registry, "检测器注册表/项目上下文",
    scope="process", order=5)
_HEURISTIC_BARE_EXCEPT = "bareexcept"
_HEURISTIC_MUTABLE_DEFAULT = ("mutable", "default")
_HEURISTIC_ASSERT = "assert"
_HEURISTIC_STAR_IMPORT = ("star", "import")
def _is_bare_except(node: Any) -> bool:
    return isinstance(node, ast.ExceptHandler) and node.type is None
def _has_mutable_default(node: Any) -> bool:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return False
    return any(is_mutable_default(default)
               for default in (*node.args.defaults, *node.args.kw_defaults)
               if default is not None)
def _is_assert(node: Any) -> bool:
    return isinstance(node, ast.Assert)
_HEURISTIC_RULES: tuple[tuple[tuple[str, ...], Callable[[Any], bool]], ...] = (
    ((_HEURISTIC_BARE_EXCEPT,), _is_bare_except),
    (("except", "none"), _is_bare_except),
    (_HEURISTIC_MUTABLE_DEFAULT, _has_mutable_default),
    ((_HEURISTIC_ASSERT,), _is_assert),
    (_HEURISTIC_STAR_IMPORT, is_star_import),
)
def _matching_heuristics(
        pattern_lower: str) -> tuple[Callable[[Any], bool], ...]:
    return tuple(
        predicate for keywords, predicate in _HEURISTIC_RULES
        if all(k in pattern_lower for k in keywords))
def pattern_matches_ast_heuristics(pattern: str) -> bool:
    return bool(_matching_heuristics(str(pattern or "").lower()))
def _validate_registration(rule_id: str, pattern_type: str,
                           pattern: str,
                           authority_pair: tuple[Callable, Any] | None) -> None:
    if not rule_id:
        raise ValueError("empty rule_id for solidified rule")
    if pattern_type not in ("regex", "ast"):
        raise ValueError(
            f"invalid pattern_type for solidified rule {rule_id}: "
            f"{pattern_type!r} (expected 'ast' or 'regex')")
    if authority_pair is not None:
        try:
            checker, _rule = authority_pair
        except (TypeError, ValueError) as exc:
            raise ValueError(
                f"invalid authority_pair for solidified rule {rule_id}: "
                "expected (checker, rule)") from exc
        if not callable(checker):
            raise ValueError(
                f"invalid authority checker for solidified rule {rule_id}: "
                f"{type(checker).__name__} is not callable")
        if pattern_type != "ast":
            raise ValueError(
                f"solidified rule {rule_id} authority checker only applies to "
                f"ast pattern_type, got {pattern_type!r}")
    if not isinstance(pattern, str):
        raise ValueError(
            f"invalid pattern for solidified rule {rule_id}: "
            f"{type(pattern).__name__} (expected str)")
    if pattern_type == "regex":
        if not pattern:
            raise ValueError(
                f"empty regex pattern for solidified rule {rule_id}")
    elif not pattern and authority_pair is None:
        raise ValueError(
            f"solidified rule {rule_id} has neither pattern nor "
            f"authority checker; detector would never match")
    elif (pattern and authority_pair is None
            and not pattern_matches_ast_heuristics(pattern)):
        raise ValueError(
            f"solidified rule {rule_id} pattern matches no known ast "
            f"heuristic; detector would never fire: {pattern!r}")
def _compile_pattern(rule_id: str, pattern_type: str,
                     pattern: str) -> re.Pattern[str] | None:
    if pattern_type != "regex" or not pattern:
        return None
    try:
        return re.compile(pattern)
    except re.error as e:
        raise ValueError(
            f"invalid regex pattern for solidified rule {rule_id}: {e}"
        ) from e
def _normalize_source_inputs(
    source_code: str,
    file_path: str,
    kwargs: dict[str, Any],
) -> tuple[str, str] | None:
    file_path = _file_path_alias(file_path, kwargs)
    if not source_code:
        source_code = _source_from_kwargs(kwargs)
    if not source_code:
        if not file_path:
            return None
        source_code = read_py_source(file_path)
        if source_code is None:
            return None
    if not isinstance(source_code, str):
        _log.debug("[Detectors] 固化检测器源码非 str，按无输入降级: %s",
                   type(source_code).__name__)
        return None
    return (source_code, file_path)
def _file_path_alias(file_path: str, kwargs: dict[str, Any]) -> str:
    primary = as_text(file_path).strip()
    return primary or as_text(kwargs.get("filepath")).strip()
def _source_from_kwargs(kwargs: dict[str, Any]) -> Any:
    return (_source_text_from_lines(kwargs.get("source_lines"))
            or kwargs.get("source") or kwargs.get("code") or "")
def _resolve_runtime(
    source_code: str,
    file_path: str,
    kwargs: dict[str, Any],
    tree: Any,
) -> tuple[str, str, ast.Module] | None:
    ast_tree = tree if isinstance(tree, ast.Module) else None
    _normalized = _normalize_source_inputs(source_code, file_path, kwargs)
    if _normalized is None:
        if ast_tree is None:
            return None
        source_code = ast.unparse(ast_tree)
        file_path = _file_path_alias(file_path, kwargs)
    else:
        source_code, file_path = _normalized
    if ast_tree is None:
        ast_tree = _parse_or_none(source_code, "solidified_detector")
        if ast_tree is None:
            return None
    return source_code, file_path, ast_tree
def _heuristic_match(node: Any, pattern_lower: str) -> bool:
    return any(
        predicate(node)
        for predicate in _matching_heuristics(pattern_lower))
def iter_heuristic_matches(tree: ast.AST, pattern: str) -> list[Any]:
    pattern_lower = str(pattern or "").lower()
    if not pattern_lower:
        return []
    return [node for node in tree_nodes(tree)
            if _heuristic_match(node, pattern_lower)]
def _authority_findings(
    authority: tuple[Callable, Any],
    ast_tree: ast.Module,
    file_path: str,
    rule_id: str,
    severity: str,
) -> list[dict[str, Any]]:
    checker, rule = authority
    raw: list[dict] = []
    checker(ast_tree, rule, raw, file_path)
    normalized: list[dict[str, Any]] = []
    for finding in raw:
        if not isinstance(finding, Mapping):
            _log.debug("[Detectors] 权威规则 %s 跳过非映射 finding: %s",
                       rule_id, type(finding).__name__)
            continue
        normalized.append({
            "rule_id": rule_id,
            "file": finding_file(finding) or file_path,
            "line": finding_line(finding),
            "severity": severity,
            "message": str(
                finding.get("description") or finding.get("message") or ""),
        })
    return normalized
def _detector_can_run_with_tree(fn: DetectorFn, tree: Any) -> bool:
    return (tree is not None
            or getattr(fn, _DETECTOR_REQUIRES_TREE_ATTR, True) is False)
def _runtime_scanner(scan: Callable, *, requires_tree: bool = True) -> DetectorFn:
    def _detector(
        source_code: str = "",
        file_path: str = "",
        tree: Any = None,
        **kwargs: Any,
    ) -> list[dict[str, Any]]:
        if requires_tree:
            runtime = _resolve_runtime(source_code, file_path, kwargs, tree)
        else:
            normalized = _normalize_source_inputs(source_code, file_path, kwargs)
            runtime = ((*normalized, None) if normalized is not None else None)
        if runtime is None:
            return []
        return scan(*runtime)
    setattr(_detector, _DETECTOR_REQUIRES_TREE_ATTR, requires_tree)
    return _detector
_LITERAL_TEXT_QUOTES = ("'", '"')
def _pattern_targets_literal_text(pattern: str) -> bool:
    return any(quote in pattern for quote in _LITERAL_TEXT_QUOTES)
def _tokenize_failure_line(source: str) -> int | None:
    normalized = source.replace("\r\n", "\n").replace("\r", "\n")
    try:
        for _token in tokenize.generate_tokens(io.StringIO(normalized).readline):
            pass
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        lineno = getattr(exc, "lineno", None)
        if lineno is None and len(exc.args) > 1:
            location = exc.args[1]
            if isinstance(location, (tuple, list)) and location:
                lineno = location[0]
        if (isinstance(lineno, int) and not isinstance(lineno, bool)
                and lineno > 0):
            _log.debug(
                "[Detectors] 词法掩码失败，仅保留第 %s 行前的可验证前缀: %s",
                lineno, exc)
            return lineno
    return None
def _mask_token_failure_prefix(source: str, keep_strings: bool) -> str | None:
    failure_line = _tokenize_failure_line(source)
    if failure_line is None:
        return None
    line_starts = [0]
    line_starts.extend(match.end() for match in
                       re.finditer(r"\r\n|\r|\n", source))
    prefix_end = (line_starts[failure_line - 1]
                  if failure_line - 1 < len(line_starts) else len(source))
    prefix = source[:prefix_end]
    masked_prefix = mask_non_code(prefix, keep_strings=keep_strings)
    if masked_prefix is None:
        return None
    tail = source[len(prefix):]
    return masked_prefix + "".join(
        char if char in "\r\n" else " " for char in tail)
def mask_non_code(source: Any, keep_strings: bool = False) -> str | None:
    if not isinstance(source, str):
        return None
    spans = (comment_only_spans(source) if keep_strings
             else string_comment_spans(source))
    if spans is None:
        return _mask_token_failure_prefix(source, keep_strings)
    if not spans:
        return source
    line_starts = [0]
    line_starts.extend(match.end() for match in
                       re.finditer(r"\r\n|\r|\n", source))
    chars = list(source)
    total = len(chars)
    for line_no, pairs in spans.items():
        if not 0 < line_no <= len(line_starts):
            continue
        base = line_starts[line_no - 1]
        limit = (line_starts[line_no] - 1
                 if line_no < len(line_starts) else total)
        for start, end in pairs:
            for index in range(max(base, base + start), min(limit, base + end)):
                if chars[index] not in "\r\n":
                    chars[index] = " "
    return "".join(chars)
def _match_in_code(
    source: str,
    code_subject: str | None,
    match: re.Match[str],
) -> bool:
    """匹配区间是否落在可执行代码上（而非字符串/注释内部）。

    ``code_subject`` 由 ``mask_non_code(source, keep_strings=False)`` 生成，
    字符串与注释内容被替换为等长空格。只比较非空白字符：匹配文本中的
    空白无法区分「代码空白」与「被掩码空白」，比较它们只会引入误判。
    """
    if code_subject is None:
        return True
    raw = source[match.start():match.end()]
    masked = code_subject[match.start():match.end()]
    if len(raw) != len(masked):
        return True
    return all(ch.isspace() or masked[i] == ch for i, ch in enumerate(raw))
def iter_regex_matches(
    source: str,
    pattern: str | re.Pattern[str],
    *,
    code_only: bool = False,
) -> list[tuple[int, str, re.Match[str]]]:
    """在源码上执行正则匹配。

    ``code_only=True`` 时只保留起点落在代码区的匹配：模式本身含引号时
    ``mask_non_code`` 会保留字符串内容（供 ``print("[ok]")`` 一类字面量
    判据使用），但字符串/文档串里的 ``print(`` 不是可执行调用，必须剔除。
    """
    compiled = pattern if isinstance(pattern, re.Pattern) else re.compile(pattern)
    subject = mask_non_code(
        source,
        keep_strings=_pattern_targets_literal_text(compiled.pattern),
    )
    if subject is None:
        return []
    code_subject = mask_non_code(source, keep_strings=False) if code_only else None
    raw_lines = aligned_source_lines(source)
    line_starts = [0]
    line_starts.extend(match.end() for match in
                       re.finditer(r"\r\n|\r|\n", source))
    matches: list[tuple[int, str, re.Match[str]]] = []
    for match in compiled.finditer(subject):
        if code_only and not _match_in_code(source, code_subject, match):
            continue
        line_no = bisect.bisect_right(line_starts, match.start())
        raw = (raw_lines[line_no - 1]
               if 0 < line_no <= len(raw_lines) else "")
        matches.append((line_no, raw, match))
    return matches
_CLI_ENTRY_CALLEES = frozenset({"main", "_cli", "cli"})

def _is_main_guard_test(test: ast.AST) -> bool:
    """``__name__ == "__main__"`` 判定。"""
    return (isinstance(test, ast.Compare)
            and isinstance(test.left, ast.Name) and test.left.id == "__name__"
            and len(test.comparators) == 1
            and isinstance(test.comparators[0], ast.Constant)
            and test.comparators[0].value == "__main__")

def _call_tail_name(func: ast.AST) -> str:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return ""

def is_cli_entry_module_source(source: str) -> bool:
    """模块是否为 CLI 入口：``if __name__ == "__main__": sys.exit(main(...))``。

    这类模块的 stdout 就是产品交付面——``print`` 不是「调试残留」而是契约
    （CLI 用例通常直接断言 stdout）。判据收紧到「守卫体把执行委托给
    main/_cli」：纯演示块（``__main__`` 里直接 print 两行）不算入口。

    放在本模块（检测器底层）而不是 solidify 域，是因为规则同步时会经
    ``build_solidified_detector`` 生成运行时检测器；豁免必须跟着规则一起
    下发到运行时，否则静态固化路径豁免了、诊断路径照报。
    """
    try:
        tree = ast.parse(source)
    except (SyntaxError, ValueError):
        return False
    for node in tree.body:
        if not (isinstance(node, ast.If) and _is_main_guard_test(node.test)):
            continue
        for sub in walk_nodes(node):
            if (isinstance(sub, ast.Call)
                    and _call_tail_name(sub.func) in _CLI_ENTRY_CALLEES):
                return True
    return False

def _make_regex_detector(
    rule_id: str,
    severity: str,
    compiled: re.Pattern[str],
    exempt_cli_entry: bool = False,
    code_only: bool = False,
) -> DetectorFn:
    def _scan(source_code: str, file_path: str,
              _ast_tree: ast.Module | None) -> list[dict[str, Any]]:
        if exempt_cli_entry and is_cli_entry_module_source(source_code):
            return []
        return [{
            "rule_id": rule_id,
            "file": file_path,
            "line": line_no,
            "severity": severity,
            "message": f"固化规则 {rule_id}: {raw.strip()[:80]}",
        } for line_no, raw, _match in iter_regex_matches(
            source_code, compiled, code_only=code_only)]
    return _runtime_scanner(_scan, requires_tree=False)
def _make_authority_detector(
    rule_id: str,
    severity: str,
    authority: tuple[Callable, Any],
) -> DetectorFn:
    def _scan(_source_code: str, file_path: str,
              ast_tree: ast.Module) -> list[dict[str, Any]]:
        return _authority_findings(
            authority, ast_tree, file_path, rule_id, severity)
    return _runtime_scanner(_scan)
def _make_heuristic_detector(
    rule_id: str,
    severity: str,
    pattern: str,
) -> DetectorFn:
    def _scan(_source_code: str, file_path: str,
              ast_tree: ast.Module) -> list[dict[str, Any]]:
        return [{
            "rule_id": rule_id,
            "file": file_path,
            "line": getattr(node, "lineno", 0),
            "severity": severity,
            "message": f"固化规则 {rule_id}: {pattern[:60]}",
        } for node in iter_heuristic_matches(ast_tree, pattern)]
    return _runtime_scanner(_scan)
class _SolidifiedSpec(NamedTuple):
    pattern_type: str
    pattern: str
    severity: str
def _resolve_solidified_spec(
    pattern_type: str | None,
    pattern: str | None,
    severity: str | None,
) -> _SolidifiedSpec:
    return _SolidifiedSpec(
        _DEFAULT_SOLIDIFIED_PATTERN_TYPE if pattern_type is None else pattern_type,
        _DEFAULT_SOLIDIFIED_PATTERN if pattern is None else pattern,
        _DEFAULT_SOLIDIFIED_SEVERITY if severity is None else severity,
    )
def build_solidified_detector(
    rule_id: str,
    pattern_type: str | None = None,
    pattern: str | None = None,
    severity: str | None = None,
    authority_pair: tuple[Callable, Any] | None = None,
    exempt_cli_entry: bool = False,
    code_only: bool = False,
) -> DetectorFn:
    rule_id = _normalize_detector_id(rule_id)
    spec = _resolve_solidified_spec(pattern_type, pattern, severity)
    _validate_registration(rule_id, spec.pattern_type, spec.pattern,
                           authority_pair)
    compiled = _compile_pattern(rule_id, spec.pattern_type, spec.pattern)
    if compiled is not None:
        return _make_regex_detector(rule_id, spec.severity, compiled,
                                    exempt_cli_entry, code_only)
    if authority_pair is not None:
        return _make_authority_detector(rule_id, spec.severity, authority_pair)
    return _make_heuristic_detector(rule_id, spec.severity, spec.pattern)
def run_channel(module: str, label: str, fn: Callable[..., Any],
                *args: Any, **kwargs: Any) -> Any:
    try:
        return fn(*args, **kwargs)
    except EXEC_SWALLOWED_EXCEPTIONS as e:
        logging.getLogger(module).warning(
            "[Detectors] %s 执行失败，仅跳过该检测器: %s", label, e)
        return []
def run_bounded_channel(module: str, name: str,
                        produce: Callable[[], Any], *,
                        count_key: str = "findings",
                        extra: dict[str, Any] | None = None,
                        label: str | None = None,
                        propagate_errors: bool = False) -> list[dict[str, Any]]:
    if (not isinstance(count_key, str) or not count_key.strip()
            or count_key in _MODULE_RUN_RESERVED_KEYS):
        raise ValueError(
            f"count_key 必须是非空且非保留日志字段: {count_key!r}")
    _t0 = time.monotonic()
    outcome, count = "ok", 0
    result: list[dict[str, Any]] = []
    try:
        findings = produce()
        if isinstance(findings, list):
            count = len(findings)
            result = findings
        else:
            _log.warning(
                "[Detectors] %s 返回非 list 形态(%s)，按契约置空并标记降级",
                label or name, type(findings).__name__)
            outcome = "degraded"
    except Exception as e:
        _log.warning("[Detectors] %s failed: %s", label or name, e)
        outcome = "degraded"
        if propagate_errors:
            # 部分通道的失败哨兵（空分析结果/非法根目录）是「结论不可用」，
            # 静默返回 [] 会与真正的零发现不可区分；由调用方决定是否把
            # 异常交给维度级失败账本记录。
            raise
    finally:
        try:
            reserved = _MODULE_RUN_RESERVED_KEYS | {count_key}
            payload = {k: v for k, v in (extra or {}).items()
                       if k not in reserved}
            payload["outcome"] = outcome
            payload["duration_ms"] = (time.monotonic() - _t0) * 1000.0
            payload[count_key] = count
            write_module_run(module, name, **payload)
        except Exception as trace_error:
            _log.warning(
                "[Detectors] %s 运行记录写入失败（不阻断通道）: %s",
                label or name, trace_error)
    return result
PROBE_FILEPATH_OVERRIDES: dict[str, str] = {
    "EP-02": "pkg/__init__.py",
    "TT-01": "test_probe_sample.py",
    "TT-02": "test_probe_sample.py",
    "TT-03": "test_probe_sample.py",
}
def probe_filepath_for_rule(rule_id: str) -> str:
    rid = str(rule_id or "")
    return PROBE_FILEPATH_OVERRIDES.get(rid, f"<liveness_probe_{rid}>")
_MAX_SAMPLES = 40
_MIN_SAMPLES_FOR_PENALTY = 10
def _norm_max_samples(max_samples) -> int:
    if isinstance(max_samples, bool):
        return _MAX_SAMPLES
    if isinstance(max_samples, int):
        return max_samples
    if isinstance(max_samples, float) and math.isfinite(max_samples):
        return int(max_samples)
    return _MAX_SAMPLES
_SKIP_NORM: frozenset[str] = frozenset(
    norm_rule_id(i or "") for i in REGISTRY_SKIP_IDS)
_RULE_OUTPUT_ALIASES: dict[str, tuple[str, ...]] = {
    norm_rule_id(cid or ""): tuple(sorted(emits))
    for cid, emits in REGISTRY_CID_EMITS.items()
}
def _is_probe_candidate(rid: str, ref: Any, reg_ids: set[str]) -> bool:
    if not getattr(ref, "self_verifiable", False):
        return False
    if not (getattr(ref, "bad_example", "") or "").strip():
        return False
    norm = norm_rule_id(rid or "")
    return norm in reg_ids and norm not in _SKIP_NORM
def _probe_candidates() -> list[tuple[str, str]]:
    reg_ids = {norm_rule_id(i or "") for i in get_registry().list_registered()}
    return [
        (rid, ref.bad_example)
        for rid, ref in sorted(CODE_REFS.items())
        if _is_probe_candidate(rid, ref, reg_ids)
    ]
class _ProbeContext(NamedTuple):
    reg: Any
    norm_to_cids: dict[str, list[str]]
def _probe_accept_set(rid: str) -> set[str]:
    _self_norm = norm_rule_id(rid or "")
    return {_self_norm} | {
        norm_rule_id(a or "") for a in _RULE_OUTPUT_ALIASES.get(_self_norm, ())}
def _probe_include_ids(ctx: _ProbeContext, accept: set[str]) -> set[str]:
    return {cid for m in accept
            for cid in ctx.norm_to_cids.get(m, ())
            if m not in _SKIP_NORM}
def _probe_one_sample(ctx: _ProbeContext, rid: str, bad: str) -> bool:
    try:
        probe_fp = probe_filepath_for_rule(rid)
        accept = _probe_accept_set(rid)
        include = _probe_include_ids(ctx, accept)
        fired = {norm_rule_id(f.get("rule_id") or "")
                 for f in ctx.reg.run_file_detectors(
                     bad, probe_fp, include_ids=include)}
        if fired & accept:
            return True
        fired_all = {norm_rule_id(f.get("rule_id") or "")
                     for f in ctx.reg.run_file_detectors(bad, probe_fp)}
        return bool(fired_all & accept)
    except Exception as _run_e:
        _log.warning("[LivenessProbe] %s 执行异常，按未存活计: %s", rid, _run_e)
        return False
def _sample_probe_candidates(
    candidates: list[tuple[str, str]], max_samples: int,
) -> list[tuple[str, str]]:
    n = min(max_samples, len(candidates))
    if not candidates or n <= 0:
        return []
    step = len(candidates) / n
    return [candidates[int(i * step)] for i in range(n)]
def _empty_probe_report(
    start: float, candidates: list[tuple[str, str]],
) -> dict[str, Any]:
    report = _liveness_report_skeleton(start)
    report["note"] = (
        "无可用阳性对照样本（CODE_REFS/注册表交集为空）"
        if not candidates else
        "抽样预算为零（max_samples<=0），未执行探测")
    return report
def _build_registry_cid_map(reg) -> dict[str, list[str]]:
    norm_to_cids: dict[str, list[str]] = {}
    for cid in reg.list_registered():
        norm_to_cids.setdefault(norm_rule_id(cid or ""), []).append(cid)
    return norm_to_cids
def _probe_batch(
    sampled: list[tuple[str, str]], ctx: _ProbeContext,
) -> tuple[list[str], list[str], list[dict]]:
    alive: list[str] = []
    dead: list[str] = []
    details: list[dict] = []
    for rid, bad in sampled:
        hit = _probe_one_sample(ctx, rid, bad)
        (alive if hit else dead).append(rid)
        details.append({"rule_id": rid, "alive": hit})
    return alive, dead, details
def run_detector_liveness_probe(max_samples: int = _MAX_SAMPLES) -> dict:
    start = time.perf_counter()
    try:
        max_samples = _norm_max_samples(max_samples)
        candidates = _probe_candidates()
        sampled = _sample_probe_candidates(candidates, max_samples)
        if not sampled:
            return _empty_probe_report(start, candidates)
        reg = get_registry()
        ctx = _ProbeContext(reg, _build_registry_cid_map(reg))
        alive, dead, details = _probe_batch(sampled, ctx)
        dead_ratio = round(len(dead) / max(len(sampled), 1), 4)
        penalty_eligible = len(sampled) >= _MIN_SAMPLES_FOR_PENALTY
        elapsed = int((time.perf_counter() - start) * 1000)
        if dead:
            _log.warning(
                "[LivenessProbe] 检测器活性探针: %d/%d 失效 %s",
                len(dead), len(sampled), dead[:10])
        else:
            _log.info("[LivenessProbe] 检测器活性探针: %d/%d 全部存活 (%dms)",
                        len(alive), len(sampled), elapsed)
        report = _liveness_report_skeleton(start)
        report.update({
            "probed": len(sampled), "alive": len(alive), "dead": len(dead),
            "dead_rules": dead, "dead_ratio": dead_ratio,
            "penalty_eligible": penalty_eligible,
            "details": details[:50],
        })
        return report
    except Exception as e:
        _log.warning("[LivenessProbe] 探针执行失败(降级): %s", e, exc_info=True)
        report = _liveness_report_skeleton(start)
        report.update({"status": "error",
                       "error": f"{type(e).__name__}: {e}"})
        return report
def _liveness_report_skeleton(start: float) -> dict[str, Any]:
    return {
        "status": "ok", "probed": 0, "alive": 0, "dead": 0,
        "dead_rules": [], "dead_ratio": 0.0,
        "penalty_eligible": False, "details": [],
        "elapsed_ms": int((time.perf_counter() - start) * 1000),
    }
def _dead_rule_set(probe: dict[str, Any]) -> set[str]:
    dead_set: set[str] = set()
    _dead = probe.get("dead_rules")
    if not isinstance(_dead, (list, tuple)):
        return dead_set
    for _r in _dead:
        normalized = norm_rule_id(_r or "")
        dead_set.add(normalized)
        for _alias in _RULE_OUTPUT_ALIASES.get(normalized, ()):
            dead_set.add(norm_rule_id(_alias or ""))
    return dead_set
def _penalize_entry(f: dict[str, Any], dead_set: set[str]) -> bool:
    _rids = {str(f.get("rule_id", ""))}
    _inner = f.get("findings")
    if isinstance(_inner, (list, tuple)):
        for inner in _inner:
            if isinstance(inner, dict):
                _rids.add(str(inner.get("rule_id", "")))
    if any(norm_rule_id(r) in dead_set for r in _rids if r):
        f["conclusion"] = "investigated"
        f["conclusion_v2"] = CONCLUSION_V2_MAP["investigated"]
        f["_detector_liveness_failed"] = True
        f["_liveness_note"] = "阳性对照探针证实该规则检测器失效，confirmed 降级待复扫"
        f["_review_required"] = True
        f["_review_reason"] = (
            "检测器活性探针降级(confirmed→investigated)：产出规则的"
            "检测器经阳性对照证实失效——AI复核裁决降级是否成立")
        return True
    return False
def _penalize_confirmed(
        xv_findings: list[Any], dead_set: set[str]) -> int:
    downgraded = 0
    for f in xv_findings:
        if not isinstance(f, dict) or f.get("conclusion") != "confirmed":
            continue
        if _penalize_entry(f, dead_set):
            downgraded += 1
    return downgraded
def penalize_dead_detector_findings(
        xv_findings: list[Any], probe: dict[str, Any]) -> int:
    try:
        if not isinstance(probe, dict) or not probe.get("penalty_eligible"):
            return 0
        dead_set = _dead_rule_set(probe)
        if not dead_set:
            return 0
        downgraded = _penalize_confirmed(xv_findings, dead_set)
        if downgraded:
            _log.info("[LivenessProbe] %d 条 confirmed 因检测器失效降级 investigated",
                        downgraded)
        return downgraded
    except Exception as e:
        _log.warning("[LivenessProbe] finding 降级失败(跳过): %s", e)
        return 0
def apply_detector_liveness_gate(xv_findings: list[Any]) -> dict[str, Any]:
    try:
        report = run_detector_liveness_probe()
        try:
            if report.get("status") == "ok":
                write_detector_liveness(
                    probed=report.get("probed", 0),
                    alive=report.get("alive", 0),
                    dead_rules=report.get("dead_rules", []),
                    dead_ratio=report.get("dead_ratio", 0.0),
                    penalty_eligible=report.get("penalty_eligible", False),
                )
        except Exception as _lw_exc:
            _log.warning("[LivenessProbe] 活性探针日志打点失败: %s",
                         _lw_exc, exc_info=True)
        penalize_dead_detector_findings(xv_findings, report)
        return report
    except Exception as exc:
        _log.warning("[LivenessProbe] 活性探针降级: %s", exc)
        return {"status": "error", "error": str(exc)}
def _rule_is_excluded(item: Any, retired_keys: frozenset[str],
                      explicit_excludes: set[str] | None = None) -> bool:
    if not isinstance(item, dict):
        return False
    _rid = finding_rule_id(item)
    if not _rid:
        return False
    if explicit_excludes and norm_rule_id(_rid) in explicit_excludes:
        return True
    return retired_rule_key(_rid) in retired_keys
def _normalize_preflight_args(
        exclude_ids: Any, max_findings: Any,
) -> tuple[set[str], int]:
    if isinstance(exclude_ids, str):
        exclude_ids = {exclude_ids} if exclude_ids else set()
    try:
        raw_excludes = {
            str(_rid) for _rid in exclude_ids if _rid
        } if exclude_ids else set()
    except TypeError:
        _log.debug(
            "preflight_diagnostic_check: exclude_ids 不可迭代，按无追加排除处理")
        raw_excludes = set()
    normalized_excludes = {
        _norm for _norm in (norm_rule_id(_rid) for _rid in raw_excludes) if _norm}
    max_findings = max(
        0, int_or(max_findings, _DEFAULT_PREFLIGHT_MAX_FINDINGS))
    return normalized_excludes, max_findings
def _retired_rule_keys(
        registered_cids: list[str] | None,
) -> frozenset[str]:
    keys = {retired_rule_key(_rid) for _rid in RETIRED_RULE_IDS}
    if registered_cids:
        keys -= {retired_rule_key(_cid) for _cid in registered_cids}
    return frozenset(keys)
def _retired_detector_excludes(retired_keys: frozenset[str]) -> set[str]:
    return {
        norm_rule_id(_rid) for _rid in RETIRED_RULE_IDS
        if retired_rule_key(_rid) in retired_keys
    }
def _finding_dedupe_key(item: dict[str, Any]) -> tuple[str, str, str, str]:
    return (
        finding_file(item),
        norm_rule_id(finding_rule_id(item)),
        str(item.get("line") or 0),
        str(item.get("message", "") or ""),
    )
def _dedupe_findings(raw: list[Any]) -> list[Any]:
    seen: set[tuple[str, str, str]] = set()
    out: list[Any] = []
    for item in raw:
        if not isinstance(item, dict):
            out.append(item)
            continue
        key = _finding_dedupe_key(item)
        if key in seen:
            continue
        seen.add(key)
        out.append(item)
    return out
def _run_registry_channel(code: str, filepath: str,
                          excludes: set[str],
                          extra_checks: dict[str, Any] | None,
                          ) -> tuple[list[dict[str, Any]], int, str]:
    tree = _parse_or_none(code, "preflight_diagnostic_check")
    degraded_reason = (
        "" if tree is not None else
        "代码解析失败，AST 检测器已跳过，文本检测器继续执行")
    _registry = get_registry()
    _registered_cids = _registry.list_registered()
    _retired_keys = _retired_rule_keys(_registered_cids)
    explicit_excludes: set[str] | None = excludes or None
    registry_excludes = excludes | _retired_detector_excludes(_retired_keys)
    raw: list[Any] = list(_registry.run_file_detectors(
        code, filepath, tree=tree, exclude_ids=registry_excludes))
    checked = sum(
        1 for _cid in _registered_cids
        if (_registry.runs_in_file_channel(_cid)
            and _detector_can_run_with_tree(_registry.get(_cid), tree)
            and _detector_selected(_cid, None, registry_excludes))
    )
    if extra_checks:
        try:
            extra_map = {
                str(cid): target for cid, target in dict(extra_checks).items()
                if not _rule_is_excluded(
                    {"rule_id": str(cid)}, _retired_keys, explicit_excludes)
            }
            adhoc_findings, adhoc_checked = _registry.run_adhoc_detectors(
                code, filepath, extra_map, exclude_ids=explicit_excludes,
            )
            raw = raw + adhoc_findings
            checked += adhoc_checked
        except Exception as e:
            extra_error = f"extra_checks 通道异常: {type(e).__name__}: {e}"
            degraded_reason = "; ".join(
                part for part in (degraded_reason, extra_error) if part)
            _log.warning(
                "preflight_diagnostic_check: extra_checks 通道降级跳过: %s", e)
    return (
        [item for item in _dedupe_findings(raw)
         if not _rule_is_excluded(item, _retired_keys, explicit_excludes)],
        checked,
        degraded_reason,
    )
def _diagnostic_result(findings: list[dict], checked: int,
                       *, degraded: bool = False,
                       degraded_reason: str = "") -> dict:
    enriched = enrich_diag_findings(findings)
    return {
        "ok": not enriched,
        "findings": enriched,
        "blocked": [
            item for item in enriched if severity_rank_of(item.get("severity")) <= 1],
        "by_rule": _count_by_rule(enriched),
        "checked_detectors": checked,
        "degraded": degraded,
        "degraded_reason": degraded_reason,
    }
def _retain_findings(raw: list[Any], min_severity: str,
                     max_findings: int) -> list[dict[str, Any]]:
    threshold = severity_rank_of(min_severity)
    findings = [
        dict(item) for item in raw
        if isinstance(item, dict)
        and severity_rank_of(item.get("severity")) <= threshold
    ]
    findings.sort(
        key=lambda item: (severity_rank_of(item.get("severity")),
                          finding_rule_id(item).strip()))
    return findings[:max_findings]
def _count_by_rule(findings: list[dict]) -> dict[str, int]:
    by_rule: dict[str, int] = {}
    for item in findings:
        rid = finding_rule_id(item).strip()
        if rid:
            by_rule[rid] = by_rule.get(rid, 0) + 1
    return by_rule
def preflight_diagnostic_check(
    code: str,
    filepath: str = "<preflight_diag>",
    *,
    min_severity: str = _DEFAULT_PREFLIGHT_MIN_SEVERITY,
    exclude_ids: set[str] | None = None,
    max_findings: int = _DEFAULT_PREFLIGHT_MAX_FINDINGS,
    extra_checks: dict[str, Any] | None = None,
) -> dict:
    if not (isinstance(code, str) and code.strip()):
        return _diagnostic_result([], 0)
    excludes, max_findings = _normalize_preflight_args(
        exclude_ids, max_findings)
    try:
        raw, checked, degraded_reason = _run_registry_channel(
            code, filepath, excludes, extra_checks)
        findings = _retain_findings(raw, min_severity, max_findings)
    except Exception as e:
        _log.debug("preflight_diagnostic_check: 诊断引擎降级跳过: %s", e)
        return _diagnostic_result(
            [], 0, degraded=True,
            degraded_reason=f"诊断引擎异常: {type(e).__name__}: {e}")
    return _diagnostic_result(findings, checked,
                              degraded=bool(degraded_reason),
                              degraded_reason=degraded_reason)

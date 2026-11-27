from __future__ import annotations

import ast as _ast
import functools
import hashlib
import json
import logging
import os
import time as _time
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field, replace
from itertools import islice
from typing import Any, ClassVar

from jwsgj.diag_guard_io import atomic_write_text
from jwsgj.diag_regression_exec import (
    DEFAULT_BEHAVIOR_TIMEOUT_SEC,
    REAL_TEST_RESTORE_FAILED,
    VERIFY_EXC,
    BehaviorRegressionExecutor,
    BehaviorRegressionReport,
    EquivalenceStatus,
    TestCase,
    disk_baseline_path,
    run_real_tests,
)
from jwsgj.diag_shared_ast_nodes import (
    iter_class_scope_methods,
    iter_module_scope_entities,
)
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.diag_types_normalize import (
    finite_float_or_none,
    rule_id_of,
    safe_str,
)
from jwsgj.log_config import log_swallowed, perf_trace
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import get_temp_base
from jwsgj.shared_cache import SharedCache, require_warmed
from jwsgj.skill_profile import detect_layout, python_import_roots

__all__ = [
    'EQUIVALENCE_GUARD_MAX_TEST_CASES',
    'EQUIVALENCE_GUARD_TIMEOUT_SEC',
    'LOG_DETAIL_MAX_CHARS',
    'APISignatureComparator',
    'APISurfaceExtractor',
    'BehaviorRegressionGuard',
    'EquivalenceGuard',
    'EquivalenceTestGenerator',
    'FunctionSignature',
    'describe_behavior_regression',
    'equivalence_required',
    'guarded_fix',
    'guarded_fix_with_retry',
    'run_equivalence_gate',
    'short_hash',
]
_log = logging.getLogger(__name__)
_log.addHandler(logging.NullHandler())
EQUIVALENCE_GUARD_TIMEOUT_SEC = 3.0
EQUIVALENCE_GUARD_MAX_TEST_CASES = 30
_DEFAULT_MAX_TEST_CASES = 50
_DEFAULT_MAX_FIX_ATTEMPTS = 5
_DEFAULT_MIN_PASS_RATE = 1.0
_DEFAULT_RULE_ID = "UNKNOWN"
_CACHE_MAX_ENTRIES = 128
LOG_DETAIL_MAX_CHARS = 120
_SHORT_HASH_HEX_LEN = 16
_NO_DEFAULT = object()
_SOURCE_SYNTAX_ERRORS = (SyntaxError, ValueError, TypeError,
                         RecursionError, MemoryError)
def _source_syntax_error(source: Any) -> Exception | None:
    try:
        compile(source, "<behavior-baseline>", "exec")
    except _SOURCE_SYNTAX_ERRORS as exc:
        return exc
    return None
@dataclass(frozen=True)
class _NonLiteralDefault:
    expression: str
# 查询「进程外实时状态」的 API：COM 会话、窗口/桌面、输入硬件。
# 只构造值（如 win32com.client.VARIANT）不算——那是纯计算。
_ENV_QUERY_APIS = frozenset({
    "GetActiveObject", "GetObject", "Dispatch", "DispatchEx",
    "CoCreateInstance", "CoGetObject",
    "EnumWindows", "EnumChildWindows", "EnumThreadWindows",
    "GetWindowText", "GetWindowTextLength", "GetClassName",
    "IsWindowVisible", "ShowWindow", "SetForegroundWindow",
    "GetForegroundWindow", "GetWindowRect", "GetClientRect",
    "GetWindowDC", "GetDC", "PrintWindow", "FindWindow", "FindWindowEx",
    "GetCursorPos", "GetSystemMetrics", "GetAsyncKeyState",
    "OpenProcess", "ReadProcessMemory", "EnumProcesses",
    "RegOpenKey", "RegOpenKeyEx", "GetKey",
    # 等待：挂起直到外部状态变化，本身就是「依赖外部时序」的判据
    "sleep",
})
def _calls_env_query(node: Any) -> bool:
    """函数体是否**调用**了查询外部实时状态的 API（含 sleep 等待）。"""
    for sub in walk_nodes(node):
        if not isinstance(sub, _ast.Call):
            continue
        func = sub.func
        name = ""
        if isinstance(func, _ast.Attribute):
            name = func.attr
        elif isinstance(func, _ast.Name):
            name = func.id
        if name in _ENV_QUERY_APIS:
            return True
    return False
def _called_local_targets(
    node: Any, owner: str, known: set[str],
) -> set[str]:
    """解析函数体内对当前模块及类方法的静态调用目标。"""
    by_tail: dict[str, set[str]] = {}
    classes: set[str] = set()
    for key in known:
        by_tail.setdefault(key.rsplit(".", 1)[-1], set()).add(key)
        if "." in key:
            classes.add(key.rsplit(".", 1)[0])
    targets: set[str] = set()
    for sub in walk_nodes(node):
        if not isinstance(sub, _ast.Call):
            continue
        func = sub.func
        if isinstance(func, _ast.Name):
            if func.id in known:
                targets.add(func.id)
            continue
        if not isinstance(func, _ast.Attribute):
            continue
        receiver = func.value
        if (isinstance(receiver, _ast.Name)
                and receiver.id in {"self", "cls"} and owner):
            candidate = f"{owner}.{func.attr}"
            if candidate in known:
                targets.add(candidate)
        elif (isinstance(receiver, _ast.Name)
                and receiver.id in classes):
            candidate = f"{receiver.id}.{func.attr}"
            if candidate in known:
                targets.add(candidate)
        else:
            targets.update(by_tail.get(func.attr, set()))
    return targets
def _owner_of_api_id(api_id: str) -> str:
    """成员所属类：访问器 id（``Class.prop.setter``）需先剥离访问器后缀。"""
    parts = api_id.split(".")
    if len(parts) >= 3 and parts[-1] in {"setter", "deleter"}:
        parts.pop()
    return ".".join(parts[:-1])
def _mark_env_bound(signatures: list, nodes: dict[str, Any]) -> None:
    """补全环境绑定的**传递闭包**。

    ``active_doc`` 自身不查外部状态，但它调用 ``connect``（同模块，查询 COM
    会话），因此同样无法建立可重放基线。迭代到不动点即可（模块内调用图很小）。
    """
    known = set(nodes)
    calls = {
        name: _called_local_targets(node, _owner_of_api_id(name), known)
        for name, node in nodes.items()
    }
    bound = {name for name, node in nodes.items() if _calls_env_query(node)}
    changed = True
    while changed:
        changed = False
        for name in nodes:
            if name not in bound and calls[name] & bound:
                bound.add(name)
                changed = True
    for sig in signatures:
        sig.env_bound = _signature_api_id(sig) in bound
@dataclass
class FunctionSignature:
    name: str
    args: list[str]
    defaults: list[Any]
    is_async: bool = False
    is_method: bool = False
    class_name: str = ""
    decorators: list[str] = field(default_factory=list)
    return_annotation: str = ""
    kwonly_args: list[str] = field(default_factory=list)
    kwonly_defaults: list[Any] = field(default_factory=list)
    vararg: str = ""
    kwarg: str = ""
    posonly_count: int = 0
    implicit_first_arg: str = ""
    arg_annotations: dict[str, str] = field(default_factory=dict)
    kwonly_annotations: dict[str, str] = field(default_factory=dict)
    vararg_annotation: str = ""
    kwarg_annotation: str = ""
    env_bound: bool = False
    @property
    def func_id(self) -> str:
        return f"{self.class_name}.{self.name}" if self.class_name else self.name
def _decorator_tail(decorator: str) -> str:
    return decorator.rsplit(".", 1)[-1]
def _method_binding(sig: FunctionSignature) -> str:
    if not sig.is_method:
        return "function"
    if sig.name == '__new__':
        return "staticmethod"
    tails = {_decorator_tail(d) for d in sig.decorators}
    if "getter" in tails:
        return "property"
    for kind in ("property", "cached_property", "staticmethod", "classmethod"):
        if kind in tails:
            return kind
    return "instancemethod"
def _posonly_len(sig: FunctionSignature) -> int:
    return max(0, min(sig.posonly_count, len(sig.args)))
def _posonly_names(sig: FunctionSignature) -> set[str]:
    return set(sig.args[:_posonly_len(sig)])
def _keyword_passable_names(sig: FunctionSignature) -> set[str]:
    return set(sig.args[_posonly_len(sig):]) | set(sig.kwonly_args)
def _positional_match_pairs(
    o: FunctionSignature, f: FunctionSignature,
) -> list[tuple[int, int, str, str]]:
    pairs: list[tuple[int, int, str, str]] = []
    matched_old: set[int] = set()
    matched_new: set[int] = set()
    for index in range(min(len(o.args), len(f.args))):
        if index < _posonly_len(o) and index < _posonly_len(f):
            if (len(o.args) != len(f.args)
                    and (o.args[index] in f.args or f.args[index] in o.args)):
                continue
            pairs.append((index, index, o.args[index], f.args[index]))
            matched_old.add(index)
            matched_new.add(index)
    for old_index, old_name in enumerate(o.args):
        if old_index in matched_old:
            continue
        for new_index, new_name in enumerate(f.args):
            if new_index not in matched_new and old_name == new_name:
                pairs.append((old_index, new_index, old_name, new_name))
                matched_old.add(old_index)
                matched_new.add(new_index)
                break
    for old_index, old_name in enumerate(o.args):
        new_index = old_index
        if (old_index in matched_old or new_index >= len(f.args)
                or new_index in matched_new):
            continue
        if (old_index < _posonly_len(o)
                or new_index < _posonly_len(f)):
            pairs.append((old_index, new_index, old_name, f.args[new_index]))
            matched_old.add(old_index)
            matched_new.add(new_index)
    return sorted(pairs)
def _same_layout_except_posonly_names(
    o: FunctionSignature, f: FunctionSignature,
) -> bool:
    pairs = _positional_match_pairs(o, f)
    return (
        len(o.args) == len(f.args) == len(pairs)
        and o.args != f.args
        and all(old_index == new_index
                for old_index, new_index, _old_name, _new_name in pairs)
    )
def _trim_implicit_first_for_call(
    sig: FunctionSignature,
) -> tuple[list[str], list[Any], int]:
    _posonly_n = max(0, min(sig.posonly_count, len(sig.args)))
    if not (sig.implicit_first_arg and sig.args
            and sig.args[0] == sig.implicit_first_arg):
        return sig.args, sig.defaults, _posonly_n
    _defaults = (sig.defaults[1:] if len(sig.defaults) == len(sig.args)
                 else sig.defaults)
    return sig.args[1:], _defaults, max(0, _posonly_n - 1)
def _signature_for_call_compare(sig: FunctionSignature) -> FunctionSignature:
    args, defaults, posonly_count = _trim_implicit_first_for_call(sig)
    if args is sig.args:
        return sig
    return replace(
        sig, args=args, defaults=defaults, posonly_count=posonly_count,
        implicit_first_arg="",
        arg_annotations={
            name: annotation
            for name, annotation in sig.arg_annotations.items()
            if name in args
        })
def _accessor_api_id(func_id: str, decorators: list[str]) -> str:
    for decorator in decorators:
        tail = _decorator_tail(decorator)
        if tail in {"setter", "deleter"}:
            return f"{func_id}.{tail}"
    return func_id
def _signature_api_id(sig: FunctionSignature) -> str:
    return _accessor_api_id(sig.func_id, sig.decorators)
class APISurfaceExtractor:
    @staticmethod
    def _should_extract(name: str, *, is_method: bool = False) -> bool:
        if name.startswith('__') and name.endswith('__'):
            return is_method or name in {'__getattr__', '__dir__'}
        return not name.startswith('_')
    def extract(self, code: str) -> list[FunctionSignature]:
        signatures: list[FunctionSignature] = []
        try:
            tree = _ast.parse(code)
        except (SyntaxError, ValueError, TypeError,
                RecursionError, MemoryError) as e:
            _log.warning(
                "APISurfaceExtractor.extract: failed to parse code: %s", e)
            return signatures
        nodes: dict[str, Any] = {}
        for node in iter_module_scope_entities(tree):
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                nodes[node.name] = node
                if self._should_extract(node.name):
                    signatures.append(self._extract_function(
                        node,
                        is_async=isinstance(node, _ast.AsyncFunctionDef)))
            elif (isinstance(node, _ast.ClassDef)
                  and self._should_extract(node.name)):
                for item in iter_class_scope_methods(node):
                    if isinstance(item, (_ast.FunctionDef,
                                         _ast.AsyncFunctionDef)):
                        decorators, _ = self._collect_decorators(item)
                        nodes[_accessor_api_id(
                            f"{node.name}.{item.name}", decorators)] = item
                signatures.extend(self._extract_class_members(node))
        _mark_env_bound(signatures, nodes)
        return signatures
    @staticmethod
    def _public_class_names(code: str) -> set[str]:
        try:
            tree = _ast.parse(code)
        except _SOURCE_SYNTAX_ERRORS:
            return set()
        return {
            node.name for node in iter_module_scope_entities(tree)
            if (isinstance(node, _ast.ClassDef)
                and APISurfaceExtractor._should_extract(node.name))
        }
    def _extract_class_members(self, node: _ast.ClassDef) -> list[FunctionSignature]:
        members: list[FunctionSignature] = []
        for item in iter_class_scope_methods(node):
            if (isinstance(item, (_ast.FunctionDef, _ast.AsyncFunctionDef))
                    and self._should_extract(item.name, is_method=True)):
                members.append(self._extract_function(
                    item, is_method=True, class_name=node.name,
                    is_async=isinstance(item, _ast.AsyncFunctionDef),
                ))
        return members
    @staticmethod
    def _strip_implicit_first(args: list[str], posonly_count: int,
                              is_method: bool, is_static: bool) -> tuple[list[str], int, str]:
        if not (is_method and not is_static and args):
            return args, posonly_count, ""
        first = args[0]
        if first in ('self', 'cls'):
            return args[1:], max(0, posonly_count - 1), ""
        return args, posonly_count, first
    def _extract_function(self, node: Any, is_method=False,
                           class_name="", is_async=False) -> Any:
        decorators, _is_static = self._collect_decorators(node)
        raw_args, posonly_count = self._positional_names(node)
        args, posonly_count, _implicit_first = self._strip_implicit_first(
            raw_args, posonly_count, is_method, _is_static)
        defaults = [self._eval_default(d) for d in node.args.defaults]
        if len(args) < len(raw_args) and len(defaults) == len(raw_args):
            defaults = defaults[1:]
        kwonly_args = [a.arg for a in node.args.kwonlyargs]
        kwonly_defaults = [self._eval_default(d)
                           for d in (node.args.kw_defaults or [])]
        return_annotation = _ast.unparse(node.returns) if node.returns else ""
        positional_nodes = [*(node.args.posonlyargs or ()), *node.args.args]
        arg_annotations = {
            arg.arg: _ast.unparse(arg.annotation)
            for arg in positional_nodes
            if arg.arg in args and arg.annotation is not None
        }
        kwonly_annotations = {
            arg.arg: _ast.unparse(arg.annotation)
            for arg in node.args.kwonlyargs
            if arg.annotation is not None
        }
        return FunctionSignature(
            name=node.name,
            args=args,
            defaults=defaults,
            is_async=is_async,
            is_method=is_method,
            class_name=class_name,
            decorators=decorators,
            return_annotation=return_annotation,
            kwonly_args=kwonly_args,
            kwonly_defaults=kwonly_defaults,
            vararg=node.args.vararg.arg if node.args.vararg else "",
            kwarg=node.args.kwarg.arg if node.args.kwarg else "",
            posonly_count=posonly_count,
            implicit_first_arg=_implicit_first,
            arg_annotations=arg_annotations,
            kwonly_annotations=kwonly_annotations,
            vararg_annotation=(
                _ast.unparse(node.args.vararg.annotation)
                if node.args.vararg and node.args.vararg.annotation else ""),
            kwarg_annotation=(
                _ast.unparse(node.args.kwarg.annotation)
                if node.args.kwarg and node.args.kwarg.annotation else ""),
            env_bound=False,
        )
    @staticmethod
    def _positional_names(node: Any) -> tuple[list[str], int]:
        _posonly = node.args.posonlyargs or ()
        args = [a.arg for a in _posonly]
        args += [a.arg for a in node.args.args]
        return args, len(_posonly)
    @staticmethod
    def _collect_decorators(node: Any) -> tuple[list[str], bool]:
        decorators: list[str] = []
        for dec in node.decorator_list:
            if isinstance(dec, _ast.Name):
                decorators.append(dec.id)
            elif isinstance(dec, _ast.Attribute):
                decorators.append(_ast.unparse(dec))
        _is_static = any(_decorator_tail(d) == 'staticmethod'
                         for d in decorators)
        return decorators, _is_static
    @staticmethod
    def _eval_default(d: Any) -> Any:
        if d is None:
            return _NO_DEFAULT
        try:
            return _ast.literal_eval(d)
        except (ValueError, TypeError, RecursionError) as _e:
            _log.debug('静默降级[APISurfaceExtractor._eval_default]: %s: %s', type(_e).__name__, _e)
            return _NonLiteralDefault(_ast.dump(d))
class _ChangeLog:
    def __init__(self) -> None:
        self.items: list[str] = []
        self.has_breaking = False
        self.has_enhancing = False
    def breaking(self, message: str) -> None:
        self.items.append(message)
        self.has_breaking = True
    def enhancing(self, message: str) -> None:
        self.items.append(message)
        self.has_enhancing = True
@dataclass(frozen=True)
class _CompareCtx:
    o: FunctionSignature
    f: FunctionSignature
    name: str
    log: _ChangeLog
def _literal_identity(value: Any) -> Any:
    if isinstance(value, list):
        return (list, tuple(_literal_identity(item) for item in value))
    if isinstance(value, tuple):
        return (tuple, tuple(_literal_identity(item) for item in value))
    if isinstance(value, dict):
        return (dict, frozenset(
            (_literal_identity(key), _literal_identity(item))
            for key, item in value.items()))
    if isinstance(value, set):
        return (set, frozenset(_literal_identity(item) for item in value))
    if isinstance(value, frozenset):
        return (frozenset, frozenset(_literal_identity(item) for item in value))
    return (type(value), repr(value))
def _partition_new_params(
    new_params: list[str], kwonly_args: list[str],
) -> tuple[list[str], list[str]]:
    moved: list[str] = []
    added: list[str] = []
    for name in new_params:
        if name in kwonly_args:
            moved.append(name)
        else:
            added.append(name)
    return moved, added
class APISignatureComparator:
    def compare(
        self, original_code: str, fixed_code: str,
        *, orig_sigs: list[FunctionSignature] | None = None,
    ) -> tuple[str, list[str]]:
        extractor = APISurfaceExtractor()
        if orig_sigs is None:
            orig_sigs = extractor.extract(original_code)
        orig_map = {_signature_api_id(s): _signature_for_call_compare(s)
                    for s in orig_sigs}
        fixed_map = {_signature_api_id(s): _signature_for_call_compare(s)
                     for s in extractor.extract(fixed_code)}
        orig_classes = extractor._public_class_names(original_code)
        fixed_classes = extractor._public_class_names(fixed_code)
        log = _ChangeLog()
        self._diff_class_keys(orig_classes, fixed_classes, log)
        self._diff_surface_keys(orig_map, fixed_map, log)
        for name in sorted(set(orig_map.keys()) & set(fixed_map.keys())):
            self._compare_signature(_CompareCtx(
                o=orig_map[name], f=fixed_map[name], name=name, log=log))
        if log.has_breaking:
            verdict = "regressed"
        elif log.has_enhancing:
            verdict = "enhanced"
        else:
            verdict = "passed"
        _log.info(
            "[BehaviorRegression] API 签名比较: %d 项基线签名 → 裁决 %s（%d 项变更）",
            len(orig_map), verdict, len(log.items))
        return verdict, log.items
    @staticmethod
    def _diff_class_keys(
        orig_classes: set[str], fixed_classes: set[str], log: _ChangeLog,
    ) -> None:
        for name in sorted(orig_classes - fixed_classes):
            log.breaking(f"[BREAKING] 公开类 '{name}' 被删除")
        for name in sorted(fixed_classes - orig_classes):
            log.enhancing(f"[ENHANCED] 新增公开类 '{name}'")
    @staticmethod
    def _diff_surface_keys(
        orig_map: dict[str, FunctionSignature],
        fixed_map: dict[str, FunctionSignature],
        log: _ChangeLog,
    ) -> None:
        for name in orig_map:
            if name not in fixed_map:
                log.breaking(f"[BREAKING] 公开函数 '{name}' 被删除")
        for name in fixed_map:
            if name not in orig_map:
                log.enhancing(f"[ENHANCED] 新增公开函数 '{name}'")
    def _compare_signature(self, ctx: _CompareCtx) -> None:
        self._compare_positional(ctx)
        self._compare_defaults(ctx)
        self._compare_kwonly(ctx)
        self._compare_varargs(ctx)
        self._compare_annotations(ctx)
        self._compare_modifiers(ctx)
    def _compare_positional(self, ctx: _CompareCtx) -> None:
        o, f = ctx.o, ctx.f
        if len(f.args) < len(o.args):
            self._positional_shrink(ctx)
        elif len(f.args) > len(o.args):
            self._positional_growth(ctx)
        elif (o.args != f.args
              and not _same_layout_except_posonly_names(o, f)):
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数列表变化 {o.args} → {f.args}")
    @staticmethod
    def _positional_shrink(ctx: _CompareCtx) -> None:
        pairs = _positional_match_pairs(ctx.o, ctx.f)
        matched_old = {old_index for old_index, _new, _old, _name in pairs}
        missing = {
            name for index, name in enumerate(ctx.o.args)
            if index not in matched_old
        }
        moved = {name for name in missing if name in ctx.f.kwonly_args}
        removed = missing - moved
        if removed:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数被删除 {sorted(removed)}")
        if moved:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 位置参数转为kwonly参数 "
                f"{sorted(moved)}（旧位置调用失效）")
    def _positional_growth(self, ctx: _CompareCtx) -> None:
        o, f = ctx.o, ctx.f
        pairs = _positional_match_pairs(o, f)
        matched_old = {old_index for old_index, _new, _old, _name in pairs}
        matched_new = {new_index for _old, new_index, _name, _new_name in pairs}
        removed = [name for index, name in enumerate(o.args)
                   if index not in matched_old]
        if removed:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数被删除/重命名 {removed}")
        new_params = [name for index, name in enumerate(f.args)
                      if index not in matched_new]
        _moved, _added = _partition_new_params(new_params, o.kwonly_args)
        self._check_vararg_keyword_shadowing(ctx, _added, _moved)
        if any(old_index != new_index
               for old_index, new_index, _old_name, _new_name in pairs):
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数位置重排 {o.args} → {f.args}")
        if _added:
            if self._new_params_optional(f, _added):
                ctx.log.enhancing(
                    f"[ENHANCED] {ctx.name}: 新增可选参数 {_added}")
            else:
                ctx.log.breaking(
                    f"[BREAKING] {ctx.name}: 新增必选参数 {_added}")
    @staticmethod
    def _check_vararg_keyword_shadowing(
        ctx: _CompareCtx, new_positional: list[str],
        moved_kwonly: list[str],
    ) -> None:
        o = ctx.o
        if not (o.vararg or o.kwarg):
            return
        _shadow_source: set[str] = set()
        if o.vararg:
            _shadow_source.update(new_positional)
            _shadow_source.update(moved_kwonly)
        if o.kwarg:
            _shadow_source.update(
                name for name in new_positional
                if name not in _posonly_names(ctx.f))
        shadowed = sorted(_shadow_source)
        if shadowed:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 新增/移入位置参数遮蔽 "
                f"旧调用的实参路由 {shadowed}")
    def _kwonly_to_positional(self, ctx: _CompareCtx, pname: str) -> None:
        o, f = ctx.o, ctx.f
        old_default = self._kwonly_default_at(o, pname)
        index = f.args.index(pname)
        if index < _posonly_len(f):
            return
        offset = len(f.args) - len(f.defaults)
        if index < offset:
            if old_default is _NO_DEFAULT:
                ctx.log.enhancing(
                    f"[ENHANCED] {ctx.name}: kwonly参数 '{pname}' "
                    f"转为必选位置参数（调用面扩大）")
            else:
                ctx.log.breaking(
                    f"[BREAKING] {ctx.name}: kwonly参数 '{pname}' "
                    f"转为必选位置参数（默认值被删除）")
            return
        new_default = f.defaults[index - offset]
        if (old_default is not _NO_DEFAULT
                and self._literal_values_differ(old_default, new_default)):
            ctx.log.breaking(
                f"[SIGNATURE] {ctx.name}: kwonly参数 '{pname}' "
                f"转为位置参数时默认值变化 "
                f"{old_default!r} → {new_default!r}")
            return
        ctx.log.enhancing(
            f"[ENHANCED] {ctx.name}: kwonly参数 '{pname}' "
            f"转为位置参数（调用面扩大）")
    def _positional_to_kwonly(self, ctx: _CompareCtx, pname: str) -> None:
        old_default = self._positional_default_at(ctx.o, pname)
        new_default = self._kwonly_default_at(ctx.f, pname)
        if old_default is _NO_DEFAULT and new_default is not _NO_DEFAULT:
            ctx.log.enhancing(
                f"[ENHANCED] {ctx.name}: 参数 '{pname}' "
                f"转为kwonly参数时新增默认值")
        elif old_default is not _NO_DEFAULT and new_default is _NO_DEFAULT:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数 '{pname}' "
                f"转为kwonly参数时默认值被删除")
        else:
            self._diff_default_values(ctx, pname, old_default, new_default)
    @staticmethod
    def _positional_default_at(sig: FunctionSignature, pname: str) -> Any:
        index = sig.args.index(pname)
        offset = len(sig.args) - len(sig.defaults)
        if index < offset:
            return _NO_DEFAULT
        return sig.defaults[index - offset]
    @staticmethod
    def _new_params_optional(f: FunctionSignature, new_params: list[str]) -> bool:
        offset = len(f.args) - len(f.defaults)
        return all(f.args.index(p) >= offset for p in new_params)
    def _compare_defaults(self, ctx: _CompareCtx) -> None:
        o, f = ctx.o, ctx.f
        for _old_index, _new_index, old_name, new_name in (
                _positional_match_pairs(o, f)):
            self._diff_default(
                ctx, new_name,
                self._positional_default_at(o, old_name),
                self._positional_default_at(f, new_name),
            )
    def _diff_default(self, ctx: _CompareCtx, pname: str,
                      old_default: Any, new_default: Any) -> None:
        if old_default is _NO_DEFAULT and new_default is not _NO_DEFAULT:
            ctx.log.enhancing(
                f"[ENHANCED] {ctx.name}: 参数 '{pname}' 新增默认值")
        elif old_default is not _NO_DEFAULT and new_default is _NO_DEFAULT:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数 '{pname}' 默认值被删除")
        else:
            self._diff_default_values(ctx, pname, old_default, new_default)
    @staticmethod
    def _diff_default_values(
        ctx: _CompareCtx, pname: str, ov: Any, fv: Any,
    ) -> None:
        if APISignatureComparator._literal_values_differ(ov, fv):
            ctx.log.breaking(
                f"[SIGNATURE] {ctx.name}: 默认值变化 "
                f"{pname}: {ov!r} → {fv!r}")
    def _compare_kwonly(self, ctx: _CompareCtx) -> None:
        _o_kwset = set(ctx.o.kwonly_args)
        _f_kwset = set(ctx.f.kwonly_args)
        _moved_to_positional = {
            p for p in _o_kwset - _f_kwset if p in ctx.f.args}
        _moved_to_kwonly = {
            p for p in _f_kwset - _o_kwset if p in ctx.o.args}
        _removed_kw = _o_kwset - _f_kwset - _moved_to_positional
        _added_kw = _f_kwset - _o_kwset - _moved_to_kwonly
        if _removed_kw:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: kwonly参数被删除 {sorted(_removed_kw)}")
        for _pn in sorted(_moved_to_positional):
            self._kwonly_to_positional(ctx, _pn)
        for _pn in sorted(_moved_to_kwonly):
            self._positional_to_kwonly(ctx, _pn)
        if _added_kw:
            self._diff_kwonly_added(ctx, _added_kw)
        for _pn in sorted(_o_kwset & _f_kwset):
            self._diff_kwonly_default(ctx, _pn)
    def _diff_kwonly_added(
        self, ctx: _CompareCtx, added_kw: set[str],
    ) -> None:
        f = ctx.f
        new_kw = sorted(added_kw)
        new_kw_idx = [f.kwonly_args.index(p) for p in new_kw]
        if all(k < len(f.kwonly_defaults)
               and f.kwonly_defaults[k] is not _NO_DEFAULT
               for k in new_kw_idx):
            ctx.log.enhancing(
                f"[ENHANCED] {ctx.name}: 新增可选kwonly参数 {new_kw}")
        else:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 新增必选kwonly参数 {new_kw}")
        if ctx.o.kwarg:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 新增kwonly参数遮蔽 "
                f"**{ctx.o.kwarg} 旧调用的关键字路由 {new_kw}")
    def _diff_kwonly_default(self, ctx: _CompareCtx, pn: str) -> None:
        _od = self._kwonly_default_at(ctx.o, pn)
        _fd = self._kwonly_default_at(ctx.f, pn)
        if _od is _NO_DEFAULT and _fd is not _NO_DEFAULT:
            ctx.log.enhancing(
                f"[ENHANCED] {ctx.name}: kwonly参数 '{pn}' 新增默认值")
        elif _od is not _NO_DEFAULT and _fd is _NO_DEFAULT:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: kwonly参数 '{pn}' 默认值被删除")
        elif self._literal_values_differ(_od, _fd):
            ctx.log.breaking(
                f"[SIGNATURE] {ctx.name}: kwonly默认值变化 "
                f"{pn}: {_od!r} → {_fd!r}")
    @staticmethod
    def _kwonly_default_at(sig: FunctionSignature, pname: str) -> Any:
        idx = sig.kwonly_args.index(pname)
        if idx >= len(sig.kwonly_defaults):
            return _NO_DEFAULT
        return sig.kwonly_defaults[idx]
    @staticmethod
    def _literal_values_differ(ov: Any, fv: Any) -> bool:
        if ov is _NO_DEFAULT or fv is _NO_DEFAULT:
            return False
        ov_dynamic = isinstance(ov, _NonLiteralDefault)
        fv_dynamic = isinstance(fv, _NonLiteralDefault)
        if ov_dynamic or fv_dynamic:
            return (ov_dynamic != fv_dynamic
                    or (ov_dynamic and fv_dynamic
                        and ov.expression != fv.expression))
        return _literal_identity(ov) != _literal_identity(fv)
    def _compare_varargs(self, ctx: _CompareCtx) -> None:
        self._diff_vararg_pair(ctx, ctx.o.vararg, ctx.f.vararg, "*")
        self._diff_vararg_pair(ctx, ctx.o.kwarg, ctx.f.kwarg, "**")
    @staticmethod
    def _diff_vararg_pair(ctx: _CompareCtx, o_val: str, f_val: str,
                          prefix: str) -> None:
        if o_val and not f_val:
            ctx.log.breaking(f"[BREAKING] {ctx.name}: {prefix}{o_val} 被删除")
        elif not o_val and f_val:
            ctx.log.enhancing(f"[ENHANCED] {ctx.name}: 新增 {prefix}{f_val}")
    def _compare_annotations(self, ctx: _CompareCtx) -> None:
        o, f = ctx.o, ctx.f
        for _old_index, _new_index, old_name, new_name in (
                _positional_match_pairs(o, f)):
            self._diff_annotation(
                ctx, f"参数 '{new_name}'",
                o.arg_annotations.get(old_name, ""),
                f.arg_annotations.get(new_name, ""))
        for name in sorted(set(o.kwonly_args) & set(f.kwonly_args)):
            self._diff_annotation(
                ctx, f"kwonly参数 '{name}'",
                o.kwonly_annotations.get(name, ""),
                f.kwonly_annotations.get(name, ""))
        moved = ((set(o.args) & set(f.kwonly_args))
                 | (set(o.kwonly_args) & set(f.args)))
        for name in sorted(moved):
            self._diff_annotation(
                ctx, f"迁移参数 '{name}'",
                o.arg_annotations.get(
                    name, o.kwonly_annotations.get(name, "")),
                f.arg_annotations.get(
                    name, f.kwonly_annotations.get(name, "")))
        if o.vararg and f.vararg:
            self._diff_annotation(
                ctx, "可变位置参数", o.vararg_annotation, f.vararg_annotation)
        if o.kwarg and f.kwarg:
            self._diff_annotation(
                ctx, "可变关键字参数", o.kwarg_annotation, f.kwarg_annotation)
    @staticmethod
    def _diff_annotation(
            ctx: _CompareCtx, label: str, original: str, fixed: str) -> None:
        if original != fixed:
            ctx.log.breaking(
                f"[SIGNATURE] {ctx.name}: {label}注解变化 "
                f"{original!r} → {fixed!r}")
    def _compare_modifiers(self, ctx: _CompareCtx) -> None:
        o, f = ctx.o, ctx.f
        self._compare_posonly(ctx)
        if o.is_async != f.is_async:
            ctx.log.breaking(f"[BREAKING] {ctx.name}: async 属性变化")
        if o.return_annotation != f.return_annotation:
            ctx.log.breaking(
                f"[SIGNATURE] {ctx.name}: 返回注解变化 "
                f"{o.return_annotation!r} → {f.return_annotation!r}")
        o_binding = _method_binding(o)
        f_binding = _method_binding(f)
        if o_binding != f_binding:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 方法绑定方式变化 "
                f"{o_binding} → {f_binding}")
    @staticmethod
    def _compare_posonly(ctx: _CompareCtx) -> None:
        o, f = ctx.o, ctx.f
        became_names = _keyword_passable_names(o) & _posonly_names(f)
        opened_names = _posonly_names(o) & _keyword_passable_names(f)
        for old_index, new_index, old_name, new_name in _positional_match_pairs(o, f):
            old_posonly = old_index < _posonly_len(o)
            new_posonly = new_index < _posonly_len(f)
            if old_posonly == new_posonly:
                continue
            if new_posonly:
                became_names.add(old_name)
            else:
                opened_names.add(new_name)
        _became_posonly = sorted(became_names)
        if _became_posonly:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 参数转为位置限定 "
                f"{_became_posonly}（原关键字调用失效）")
        _opened = sorted(opened_names)
        if not _opened:
            return
        if o.kwarg:
            ctx.log.breaking(
                f"[BREAKING] {ctx.name}: 位置限定参数转为关键字可用改变 "
                f"**{o.kwarg} 旧调用的关键字路由 {_opened}")
        else:
            ctx.log.enhancing(
                f"[ENHANCED] {ctx.name}: 位置限定参数转为关键字可用 "
                f"{_opened}")
@dataclass
class _SynthView:
    args: list[str]
    defaults: list[Any]
    posonly_names: list[str]
    kwonly_fill: dict[str, Any]
    default_fill: dict[str, Any]
    @property
    def offset(self) -> int:
        return len(self.args) - len(self.defaults)
_NAME_POOL_FAMILIES: tuple[tuple[tuple[str, ...], tuple[Any, ...]], ...] = (
    (("path", "file", "dir"),
     (os.path.join("tmp", "test.txt"), "",
      os.path.join("nonexistent", "path"))),
    (("name", "label", "title", "key", "word", "token", "prefix",
      "suffix", "msg", "message"), ("test", "", "hello world")),
    (("count", "size", "num", "index"), (0, 1, -1, 100)),
    (("flag", "enable", "debug"), (True, False)),
    (("data", "content", "text"), ("", "test data", None)),
)
_NUMERIC_POOL: tuple[Any, ...] = (0, 1, -1, 100)
_SHORT_NAME_POOL: tuple[Any, ...] = (-1, 0, 1, 2, 10)
def _name_pool(name_lower: str) -> list[Any] | None:
    for keywords, pool in _NAME_POOL_FAMILIES:
        if any(kw in name_lower for kw in keywords):
            return list(pool)
    return None
class EquivalenceTestGenerator:
    _TYPE_TEST_VALUES: ClassVar[dict[str, list]] = {
        "int": [-1, 0, 1, 100],
        "float": [-1.0, 0.0, 1.0],
        "str": ["", "hello", "test"],
        "bool": [True, False],
        "list": [[], [1, 2, 3]],
        "dict": [{}, {"key": "value"}],
        "None": [None],
        "any": [None, 0, "test", "", []],
    }
    def generate(self, signatures: list[FunctionSignature]) -> list[TestCase]:
        cases = []
        for sig in signatures:
            cases.extend(self._generate_for_function(sig))
        _log.info("[BehaviorRegression] 等价用例合成: %d 签名 → %d 用例",
                  len(signatures), len(cases))
        return cases
    def _generate_for_function(self, sig: FunctionSignature) -> list[TestCase]:
        _kind = self._target_kind(sig)
        view = self._build_synth_view(sig)
        cases: list[TestCase] = []
        cases.extend(self._baseline_cases(sig, view, _kind))
        cases.extend(self._variadic_cases(sig, view, _kind))
        cases.extend(self._per_arg_cases(sig, view, _kind))
        cases.extend(self._kwonly_cases(sig, view, _kind))
        for case in cases:
            case.env_bound = sig.env_bound
        return cases
    def _baseline_cases(self, sig: FunctionSignature, view: _SynthView,
                        kind: str) -> list[TestCase]:
        func_id = sig.func_id
        target_name = self._call_target_name(sig)
        if not view.args:
            return [TestCase(case_id=f"{func_id}_noargs",
                             function_name=target_name,
                             kwargs=dict(view.kwonly_fill),
                             target_kind=kind)]
        if len(view.defaults) == len(view.args):
            return [TestCase(case_id=f"{func_id}_all_defaults",
                             function_name=target_name,
                             kwargs=dict(view.kwonly_fill),
                             target_kind=kind)]
        return []
    def _variadic_cases(self, sig: FunctionSignature, view: _SynthView,
                        kind: str) -> list[TestCase]:
        if not (sig.vararg or sig.kwarg):
            return []
        inputs, kwargs = self._split_call(view, self._base_kwargs(view))
        target_name = self._call_target_name(sig)
        cases: list[TestCase] = []
        if sig.vararg:
            value = self._first_test_value(sig.vararg, fallback=0)
            cases.append(TestCase(
                case_id=(f"{sig.func_id}_{sig.vararg}_extra_"
                         f"{self._val_repr(value)}"),
                function_name=target_name,
                inputs=(*inputs, value), kwargs=dict(kwargs),
                target_kind=kind,
            ))
        if sig.kwarg:
            reserved = set(view.args) | set(sig.kwonly_args)
            extra_name = "_jwsgj_extra"
            while extra_name in reserved:
                extra_name = f"_{extra_name}"
            value = self._first_test_value(sig.kwarg, fallback=0)
            extra_kwargs = dict(kwargs)
            extra_kwargs[extra_name] = value
            cases.append(TestCase(
                case_id=(f"{sig.func_id}_{sig.kwarg}_extra_"
                         f"{self._val_repr(value)}"),
                function_name=target_name,
                inputs=inputs, kwargs=extra_kwargs,
                target_kind=kind,
            ))
        return cases
    def _per_arg_cases(self, sig: FunctionSignature, view: _SynthView,
                       kind: str) -> list[TestCase]:
        cases: list[TestCase] = []
        for arg_name in view.args:
            for val in self._get_test_values(arg_name)[:3]:
                kwargs = self._base_kwargs(view)
                kwargs[arg_name] = val
                inputs, kwargs = self._split_call(view, kwargs, arg_name)
                cases.append(TestCase(
                    case_id=f"{sig.func_id}_{arg_name}_{self._val_repr(val)}",
                    function_name=self._call_target_name(sig),
                    inputs=inputs, kwargs=kwargs,
                    target_kind=kind,
                ))
        return cases
    def _kwonly_cases(self, sig: FunctionSignature, view: _SynthView,
                      kind: str) -> list[TestCase]:
        cases: list[TestCase] = []
        for name in sig.kwonly_args:
            for val in self._get_test_values(name):
                if val is None:
                    continue
                kwargs = self._base_kwargs(view)
                kwargs[name] = val
                inputs, kwargs = self._split_call(view, kwargs)
                cases.append(TestCase(
                    case_id=f"{sig.func_id}_{name}_{self._val_repr(val)}",
                    function_name=self._call_target_name(sig),
                    inputs=inputs, kwargs=kwargs,
                    target_kind=kind,
                ))
                break
        return cases
    @staticmethod
    def _call_target_name(sig: FunctionSignature) -> str:
        return sig.class_name if sig.name == '__new__' else sig.func_id
    @staticmethod
    def _target_kind(sig: FunctionSignature) -> str:
        if not sig.is_method:
            return "function"
        if sig.name in {"__init__", "__new__"}:
            return "ctor"
        decorator_tails = {_decorator_tail(d) for d in sig.decorators}
        if "setter" in decorator_tails:
            return "property_setter"
        if "deleter" in decorator_tails:
            return "property_deleter"
        binding = _method_binding(sig)
        if binding in {"property", "cached_property"}:
            return "property"
        if binding in {"staticmethod", "classmethod"}:
            return "function"
        return "method"
    def _first_test_value(self, name: str, fallback: Any = None) -> Any:
        for v in self._get_test_values(name):
            if v is not None:
                return v
        return fallback
    def _build_synth_view(self, sig: FunctionSignature) -> _SynthView:
        _args, _defaults, _posonly_n = _trim_implicit_first_for_call(sig)
        return _SynthView(
            args=_args, defaults=_defaults,
            posonly_names=_args[:_posonly_n],
            kwonly_fill=self._kwonly_fill(sig),
            default_fill=self._default_fill(_args, _defaults, _posonly_n),
        )
    def _kwonly_fill(self, sig: FunctionSignature) -> dict[str, Any]:
        fill: dict[str, Any] = {}
        for k, name in enumerate(sig.kwonly_args):
            has_default = (k < len(sig.kwonly_defaults)
                           and sig.kwonly_defaults[k] is not _NO_DEFAULT)
            if not has_default:
                fill[name] = self._first_test_value(name, fallback=None)
        return fill
    def _default_fill(
        self, args: list[str], defaults: list[Any], posonly_n: int,
    ) -> dict[str, Any]:
        offset = len(args) - len(defaults)
        fill: dict[str, Any] = {}
        for j, name in enumerate(args):
            if j < offset or j < posonly_n:
                fill[name] = self._first_test_value(name, fallback=0)
        return fill
    def _base_kwargs(self, view: _SynthView) -> dict[str, Any]:
        kw: dict[str, Any] = {}
        for j, name in enumerate(view.args):
            if j >= view.offset:
                _dv = view.defaults[j - view.offset]
                if isinstance(_dv, _NonLiteralDefault):
                    continue
                kw[name] = _dv
            else:
                kw[name] = view.default_fill.get(name, 0)
        kw.update(view.kwonly_fill)
        return kw
    def _split_call(self, view: _SynthView, kw: dict[str, Any],
                    target_name: str = "") -> tuple[tuple, dict[str, Any]]:
        inputs: list[Any] = []
        _target_pos = (view.posonly_names.index(target_name)
                       if target_name in view.posonly_names else -1)
        for i, n in enumerate(view.posonly_names):
            if n not in kw:
                if _target_pos > i:
                    kw[n] = view.default_fill.get(n, 0)
                else:
                    for _n2 in view.posonly_names[i:]:
                        kw.pop(_n2, None)
                    break
            inputs.append(kw.pop(n))
        return tuple(inputs), kw
    def _get_test_values(self, arg_name: str) -> list[Any]:
        name_lower = arg_name.lower()
        if name_lower == 'n':
            return list(_NUMERIC_POOL)
        pool = _name_pool(name_lower)
        if pool is not None:
            return pool
        if len(arg_name) <= 2 and arg_name.isalpha():
            return list(_SHORT_NAME_POOL)
        return list(self._TYPE_TEST_VALUES.get("any", [None, 0, ""]))
    @staticmethod
    def _val_repr(val: Any) -> str:
        if val is None:
            return "None"
        if isinstance(val, str):
            return val[:10].replace("/", "_")
        return str(val)[:10]
def _log_equivalence_reject(
    tag: str, subject: str, report: BehaviorRegressionReport,
    detail: str = "",
) -> None:
    _log.warning(
        "%s %s未通过等价性验证: %d/%d 失败%s",
        tag, subject, report.failed_tests, report.total_tests,
        f"，{detail}" if detail else "",
    )
def _reject_message(report: BehaviorRegressionReport | None) -> str:
    if report is None:
        return "等价性验证异常"
    if report.status == EquivalenceStatus.ERROR:
        return f"等价性验证异常: {report.error_detail}"
    return (f"等价性验证失败: {report.failed_tests}/"
            f"{report.total_tests} 测试不通过")
def _mark_fix_result_failed(fix_result: Any, message: str) -> None:
    if hasattr(fix_result, 'status'):
        fix_result.status = "failed"
    if hasattr(fix_result, 'error'):
        fix_result.error = message
@dataclass(frozen=True)
class _Verdict:
    accepted: bool
    report: BehaviorRegressionReport | None = None
    exc: Exception | None = None
    @property
    def raised(self) -> bool:
        return self.exc is not None
def _evaluate_candidate(
    guard: BehaviorRegressionGuard, original_code: str, fixed_code: str,
    *, filepath: str = "", policy: _DecoPolicy | None = None,
) -> _Verdict:
    try:
        report = guard.verify(original_code, fixed_code, filepath=filepath)
    except VERIFY_EXC as exc:
        log_swallowed(
            __name__, exc,
            context=f'_evaluate_candidate:{type(exc).__name__}')
        return _Verdict(False, None, exc)
    if report.is_equivalent:
        return _Verdict(True, report)
    if policy is not None and _no_api_skip_allowed(
            original_code, fixed_code, report, policy):
        return _Verdict(True, report)
    return _Verdict(False, report)
@dataclass(frozen=True)
class _DecoPolicy:
    timeout_sec: float
    max_test_cases: int
    skip_if_no_api: bool
def _no_api_skip_allowed(
    original_code: str, fixed_code: str,
    report: BehaviorRegressionReport, policy: _DecoPolicy,
) -> bool:
    if (not policy.skip_if_no_api
            or report.status != EquivalenceStatus.UNVERIFIABLE):
        return False
    for source in (original_code, fixed_code):
        if not isinstance(source, str):
            return False
        syntax_error = _source_syntax_error(source)
        if syntax_error is not None:
            log_swallowed(
                __name__, syntax_error,
                context=f'_no_api_skip_allowed:{type(syntax_error).__name__}')
            return False
    extractor = APISurfaceExtractor()
    if extractor.extract(original_code) or extractor.extract(fixed_code):
        return False
    original_evidence = _public_module_declaration_evidence(original_code)
    fixed_evidence = _public_module_declaration_evidence(fixed_code)
    if original_evidence is None or fixed_evidence is None:
        return False
    original_nodes, original_direct = original_evidence
    fixed_nodes, fixed_direct = fixed_evidence
    original_classes = [node for node in original_nodes
                        if isinstance(node, _ast.ClassDef)]
    fixed_classes = [node for node in fixed_nodes
                     if isinstance(node, _ast.ClassDef)]
    if len(original_classes) != len(original_direct):
        return False
    for name, original_node in original_direct.items():
        matching = [node for node in fixed_classes if node.name == name]
        if len(matching) != 1 or fixed_direct.get(name) is not matching[0]:
            return False
        if _ast.dump(original_node) != _ast.dump(matching[0]):
            return False
    return True
def _public_module_declaration_evidence(
    code: str,
) -> tuple[list[_ast.AST], dict[str, _ast.ClassDef]] | None:
    try:
        tree = _ast.parse(code)
    except _SOURCE_SYNTAX_ERRORS as exc:
        log_swallowed(
            __name__, exc,
            context=f'_public_module_declaration_evidence:{type(exc).__name__}')
        return None
    declarations = [
        node for node in iter_module_scope_entities(tree)
        if APISurfaceExtractor._should_extract(node.name)
    ]
    direct_classes = {
        node.name: node for node in tree.body
        if isinstance(node, _ast.ClassDef)
        and APISurfaceExtractor._should_extract(node.name)
    }
    return declarations, direct_classes
def _equivalence_rollback(
    code: str, fixed_code: str, rule_id: str, policy: _DecoPolicy,
) -> tuple[str, bool]:
    guard = _equivalence_tier_guard(
        policy.timeout_sec, policy.max_test_cases)
    verdict = _evaluate_candidate(guard, code, fixed_code, policy=policy)
    if verdict.accepted:
        return fixed_code, True
    if verdict.raised:
        _log.warning(
            "[EquivGuard] 修复 %s 等价性验证异常,已回滚: %s",
            rule_id, safe_str(verdict.exc))
        return code, False
    _log_equivalence_reject(
        "[EquivGuard]", f"修复 {rule_id}", verdict.report,
        detail=f"API变化: {verdict.report.api_surface_changes[:3] or '无'}")
    return code, False
class EquivalenceGuard:
    def __init__(self, timeout_sec: float = EQUIVALENCE_GUARD_TIMEOUT_SEC,
                 max_test_cases: int = EQUIVALENCE_GUARD_MAX_TEST_CASES) -> None:
        self._guard = _equivalence_tier_guard(timeout_sec, max_test_cases)
    def guard(
        self,
        original_code: str,
        fixed_code: str,
        issue: dict,
        fix_result: Any,
    ) -> tuple[str, Any]:
        if fixed_code == original_code:
            return original_code, fix_result
        verdict = _evaluate_candidate(
            self._guard, original_code, fixed_code)
        if verdict.accepted:
            return fixed_code, fix_result
        if verdict.raised:
            _log.warning(
                "[EquivGuard] 验证异常（回滚到原始代码）: %s",
                safe_str(verdict.exc))
            _mark_fix_result_failed(
                fix_result, f"等价性验证异常: {safe_str(verdict.exc)}")
            return original_code, fix_result
        _log_equivalence_reject(
            "[EquivGuard]", f"修复 {rule_id_of(issue)}", verdict.report,
            detail="已回滚")
        _mark_fix_result_failed(fix_result, _reject_message(verdict.report))
        return original_code, fix_result
def guarded_fix(
    original_code: str,
    fixed_code: str,
    rule_id: str = _DEFAULT_RULE_ID,
    timeout_sec: float = EQUIVALENCE_GUARD_TIMEOUT_SEC,
    filepath: str = "",
    max_test_cases: int = EQUIVALENCE_GUARD_MAX_TEST_CASES,
) -> tuple[str, bool]:
    if fixed_code == original_code:
        return original_code, False
    guard = _equivalence_tier_guard(timeout_sec, max_test_cases)
    verdict = _evaluate_candidate(
        guard, original_code, fixed_code, filepath=filepath)
    if verdict.accepted:
        return fixed_code, True
    if verdict.raised:
        _log.warning(
            "[guarded_fix] 验证异常（回滚到原始代码）: %s",
            safe_str(verdict.exc))
        return original_code, False
    _log_equivalence_reject("[guarded_fix]", rule_id, verdict.report)
    return original_code, False
def _candidate_entries(candidate_fixes, rule_id: str, limit: int) -> list:
    if isinstance(candidate_fixes, (str, bytes, dict)):
        _log.warning("[retry] %s 候选清单传入 %s（会被逐字符/逐键展开），"
                     "按空清单处理", rule_id, type(candidate_fixes).__name__)
        return []
    try:
        return list(islice(candidate_fixes, limit))
    except TypeError:
        _log.warning("[retry] %s 候选清单非可迭代形态(%s)，按空清单处理",
                     rule_id, type(candidate_fixes).__name__)
        return []
def guarded_fix_with_retry(
    original_code: str,
    candidate_fixes: list,
    rule_id: str = _DEFAULT_RULE_ID,
    timeout_sec: float = EQUIVALENCE_GUARD_TIMEOUT_SEC,
    max_attempts: int = _DEFAULT_MAX_FIX_ATTEMPTS,
    filepath: str = "",
    max_test_cases: int = EQUIVALENCE_GUARD_MAX_TEST_CASES,
) -> tuple[str, bool, int]:
    attempted = 0
    max_attempts = _nonnegative_int_or_default(
        max_attempts, _DEFAULT_MAX_FIX_ATTEMPTS)
    _retry_guard = _equivalence_tier_guard(timeout_sec, max_test_cases)
    for entry in _candidate_entries(candidate_fixes, rule_id, max_attempts):
        attempted += 1
        if not (isinstance(entry, (tuple, list)) and len(entry) == 2):
            _log.warning("[retry] %s 方案%d 载荷非 (code, strategy) 二元组"
                         "（%s），跳过", rule_id, attempted,
                         type(entry).__name__)
            continue
        fixed_code, strategy_name = entry
        if fixed_code == original_code:
            _log.debug("[retry] %s 方案%d(%s) 无变化", rule_id, attempted, strategy_name)
            continue
        verdict = _evaluate_candidate(
            _retry_guard, original_code, fixed_code, filepath=filepath)
        if verdict.raised:
            _log.warning("[retry] %s 方案%d(%s) 异常(跳过此方案): %s",
                         rule_id, attempted, strategy_name,
                         safe_str(verdict.exc))
            continue
        if verdict.accepted:
            _log.info("[retry] %s 方案%d(%s) 通过(%s)",
                      rule_id, attempted, strategy_name,
                      verdict.report.status.value)
            return fixed_code, True, attempted
        _log_equivalence_reject(
            "[retry]", f"{rule_id} 方案{attempted}({strategy_name})",
            verdict.report)
    _log.error("[retry] %s 全部%d个方案未通过,已放弃", rule_id, attempted)
    return original_code, False, attempted
def equivalence_required(
    timeout_sec: float = EQUIVALENCE_GUARD_TIMEOUT_SEC,
    max_test_cases: int = EQUIVALENCE_GUARD_MAX_TEST_CASES,
    skip_if_no_api: bool = True,
) -> Callable:
    def decorator(fix_func):
        policy = _DecoPolicy(
            timeout_sec=timeout_sec,
            max_test_cases=max_test_cases,
            skip_if_no_api=skip_if_no_api,
        )
        @functools.wraps(fix_func)
        def wrapper(self_or_cls, code: str, issue: dict, *args, **kwargs):
            result = fix_func(self_or_cls, code, issue, *args, **kwargs)
            if not (isinstance(result, tuple) and len(result) == 2):
                return result
            fixed_code, success = result
            if not success or fixed_code == code:
                return result
            return _equivalence_rollback(
                code, fixed_code, rule_id_of(issue), policy)
        return wrapper
    return decorator
def _group_cases_by_function(cases: list) -> tuple[list[str], dict[str, list]]:
    by_func: dict[str, list] = {}
    order: list[str] = []
    for case in cases:
        name = safe_str(getattr(case, "function_name", ""))
        if name not in by_func:
            by_func[name] = []
            order.append(name)
        by_func[name].append(case)
    return order, by_func
def _fair_round_robin(order: list[str], by_func: dict[str, list], limit: int) -> list:
    selected: list = []
    depth = 0
    while len(selected) < limit:
        progressed = False
        for name in order:
            cases = by_func[name]
            if depth >= len(cases):
                continue
            selected.append(cases[depth])
            progressed = True
            if len(selected) >= limit:
                break
        if not progressed:
            break
        depth += 1
    return selected
def _coerce_timeout_sec(value: Any,
                      default: float = DEFAULT_BEHAVIOR_TIMEOUT_SEC) -> float:
    number = finite_float_or_none(value)
    if number is None or number <= 0:
        return default
    return number
def _nonnegative_int_or_default(value: Any, default: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        return default
    return value
def _equivalence_tier_guard(
    timeout_sec: Any = EQUIVALENCE_GUARD_TIMEOUT_SEC,
    max_test_cases: Any = EQUIVALENCE_GUARD_MAX_TEST_CASES,
    extra_pythonpath: list[str] | None = None,
) -> BehaviorRegressionGuard:
    """按等价门禁层默认值归一后构造 guard。

    等价门禁层（EQUIVALENCE_GUARD_*）与裸 BehaviorRegressionGuard 层
    （DEFAULT_BEHAVIOR_TIMEOUT_SEC/_DEFAULT_MAX_TEST_CASES）是两套默认：
    非法 timeout/max_test_cases 必须回退到调用方所在层的默认，否则
    EquivalenceGuard(timeout_sec=-1) 会静默变成 5.0s/50 例而非 3.0s/30 例。
    """
    return BehaviorRegressionGuard(
        timeout_sec=_coerce_timeout_sec(timeout_sec, EQUIVALENCE_GUARD_TIMEOUT_SEC),
        max_test_cases=_nonnegative_int_or_default(
            max_test_cases, EQUIVALENCE_GUARD_MAX_TEST_CASES),
        extra_pythonpath=extra_pythonpath)
def _coerce_min_pass_rate(value: Any) -> float:
    number = finite_float_or_none(value)
    if number is None or not 0.0 <= number <= 1.0:
        return _DEFAULT_MIN_PASS_RATE
    return number
def _coerce_existing_cases(existing_tests) -> list:
    if not existing_tests:
        return []
    if isinstance(existing_tests, (str, bytes, dict)):
        _log.warning(
            "[BehaviorRegression] existing_tests 传入 %s（非用例容器），"
            "按空清单处理", type(existing_tests).__name__)
        return []
    if isinstance(existing_tests, (list, tuple)):
        candidates = list(existing_tests)
    else:
        try:
            candidates = list(existing_tests)
        except TypeError as _swallow_e:
            log_swallowed(
                __name__, _swallow_e,
                context=f'_coerce_existing_cases:{type(_swallow_e).__name__}')
            candidates = [existing_tests]
    valid = [case for case in candidates if isinstance(case, TestCase)]
    _dropped = len(candidates) - len(valid)
    if _dropped:
        _log.warning(
            "[BehaviorRegression] existing_tests 丢弃 %d 个非 TestCase 元素",
            _dropped)
    return valid
def _log_verify_outcome(report: BehaviorRegressionReport) -> None:
    if report.status == EquivalenceStatus.REGRESSED:
        _log.warning(
            "[BehaviorRegression] verify 判定退化: %d/%d 用例失败%s",
            report.failed_tests, report.total_tests,
            f"（{report.error_detail[:LOG_DETAIL_MAX_CHARS]}）" if report.error_detail else "")
        return
    _log.info(
        "[BehaviorRegression] verify 完成: status=%s passed=%d/%d elapsed=%.0fms",
        report.status.value, report.passed_tests, report.total_tests,
        report.elapsed_ms)
def _source_fingerprint(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="surrogatepass")).hexdigest()
def short_hash(text: str) -> str:
    return _source_fingerprint(text)[:_SHORT_HASH_HEX_LEN]
class BehaviorRegressionGuard:
    _SIGS_CACHE_MAX: ClassVar[int] = _CACHE_MAX_ENTRIES
    @property
    def timeout_sec(self) -> float:
        return self._timeout_sec
    @timeout_sec.setter
    def timeout_sec(self, value: Any) -> None:
        normalized = _coerce_timeout_sec(value)
        self._timeout_sec = normalized
        executor = getattr(self, '_executor', None)
        if executor is not None and executor.timeout_sec != normalized:
            self._executor = BehaviorRegressionExecutor(
                timeout_sec=normalized,
                extra_pythonpath=executor.extra_pythonpath)
    @property
    def max_test_cases(self) -> int:
        return self._max_test_cases
    @max_test_cases.setter
    def max_test_cases(self, value: Any) -> None:
        self._max_test_cases = _nonnegative_int_or_default(
            value, _DEFAULT_MAX_TEST_CASES)
    @property
    def min_pass_rate(self) -> float:
        return self._min_pass_rate
    @min_pass_rate.setter
    def min_pass_rate(self, value: Any) -> None:
        self._min_pass_rate = _coerce_min_pass_rate(value)
    def __init__(self, timeout_sec: float = DEFAULT_BEHAVIOR_TIMEOUT_SEC,
                 max_test_cases: int = _DEFAULT_MAX_TEST_CASES,
                 min_pass_rate: float = _DEFAULT_MIN_PASS_RATE,
                 extra_pythonpath: list[str] | None = None) -> None:
        self.timeout_sec = timeout_sec
        self.max_test_cases = max_test_cases
        self.min_pass_rate = min_pass_rate
        self._extractor = APISurfaceExtractor()
        self._generator = EquivalenceTestGenerator()
        self._executor = BehaviorRegressionExecutor(
            timeout_sec=self.timeout_sec, extra_pythonpath=extra_pythonpath)
        self._sig_comparator = APISignatureComparator()
        self._sigs_cache: dict[str, list[FunctionSignature]] = {}
    def verify(
        self, original_code: str, fixed_code: str,
        existing_tests: list[TestCase] | None = None,
        filepath: str = "",
    ) -> BehaviorRegressionReport:
        _rejected = self._source_reject_report(original_code, fixed_code)
        if _rejected is not None:
            return _rejected
        _report = self._verify_uncached(
            original_code, fixed_code, existing_tests, filepath)
        _log_verify_outcome(_report)
        return _report
    @staticmethod
    def _round_robin_select(cases: list, limit: int) -> list:
        if limit <= 0:
            return []
        if limit >= len(cases):
            return list(cases)
        order, by_func = _group_cases_by_function(cases)
        return _fair_round_robin(order, by_func, limit)
    @staticmethod
    def _promote_sig_enhanced(
            report: BehaviorRegressionReport, sig_verdict: str) -> None:
        if (sig_verdict == "enhanced"
                and report.status == EquivalenceStatus.PASSED):
            report.status = EquivalenceStatus.ENHANCED
    def _final_reconcile(
        self, report: BehaviorRegressionReport,
        real_result: tuple[str, str] | None,
        sig_verdict: str, sig_changes: list,
    ) -> BehaviorRegressionReport:
        if (real_result is not None and real_result[0] == "passed"
                and report.status == EquivalenceStatus.UNVERIFIABLE):
            report = BehaviorRegressionReport(
                status=EquivalenceStatus.PASSED,
                api_surface_changes=sig_changes,
                error_detail="合成通道环境异常不构成行为证据, 采信已通过的真实测试",
                total_tests=1, passed_tests=1, failed_tests=0,
                environment_excluded_cases=list(
                    report.environment_excluded_cases),
            )
        if (report.status in (EquivalenceStatus.PASSED, EquivalenceStatus.REGRESSED)
                and report.pass_rate < self.min_pass_rate):
            report.status = EquivalenceStatus.REGRESSED
            report.requires_manual_review = True
        self._promote_sig_enhanced(report, sig_verdict)
        return report
    def _orig_signatures(self, original_code: str):
        _okey = _source_fingerprint(original_code)
        orig_sigs = self._sigs_cache.get(_okey)
        if orig_sigs is None:
            orig_sigs = self._extractor.extract(original_code)
            if len(self._sigs_cache) >= self._SIGS_CACHE_MAX:
                self._sigs_cache.clear()
            self._sigs_cache[_okey] = orig_sigs
        return orig_sigs
    def _verify_uncached(
        self, original_code: str, fixed_code: str,
        existing_tests: list[TestCase] | None = None,
        filepath: str = "",
    ) -> BehaviorRegressionReport:
        t0 = _time.time()
        _rejected = self._syntax_reject_report(original_code, fixed_code)
        if _rejected is not None:
            return self._stamp(_rejected, t0)
        orig_sigs = self._orig_signatures(original_code)
        sig_verdict, sig_changes = self._sig_comparator.compare(
            original_code, fixed_code, orig_sigs=orig_sigs)
        if sig_verdict == "regressed":
            return self._stamp(self._signature_regression_report(sig_changes), t0)
        _inplace_path = disk_baseline_path(filepath, original_code)
        real_result = (run_real_tests(
            _inplace_path, fixed_code,
            source_roots=self._executor.extra_pythonpath,
        ) if _inplace_path else None)
        if real_result is not None and real_result[0] == REAL_TEST_RESTORE_FAILED:
            return self._stamp(
                self._restore_failed_report(real_result[1], sig_changes), t0)
        real_report = self._real_regression_report(real_result, sig_changes)
        if real_report is not None:
            return self._stamp(real_report, t0)
        test_cases, env_excluded = self._synthetic_cases(
            existing_tests, orig_sigs)
        if not test_cases:
            _report = self._no_case_report(
                real_result, sig_changes, sig_verdict)
            _report.environment_excluded_cases = [
                c.case_id for c in env_excluded]
            return self._stamp(_report, t0)
        report = self._executor.verify_equivalence(
            original_code, fixed_code, test_cases, filepath=_inplace_path)
        report.environment_excluded_cases = [
            c.case_id for c in env_excluded]
        report.api_surface_changes = sig_changes
        report = self._final_reconcile(report, real_result, sig_verdict, sig_changes)
        return self._stamp(report, t0)
    @staticmethod
    def _stamp(
        report: BehaviorRegressionReport, t0: float,
    ) -> BehaviorRegressionReport:
        report.elapsed_ms = (_time.time() - t0) * 1000
        return report
    @staticmethod
    def _signature_regression_report(sig_changes: list) -> BehaviorRegressionReport:
        return BehaviorRegressionReport(
            status=EquivalenceStatus.REGRESSED,
            requires_manual_review=True,
            api_surface_changes=sig_changes,
            error_detail="API签名退化",
        )
    @staticmethod
    def _source_reject_report(
        original_code: Any, fixed_code: Any,
    ) -> BehaviorRegressionReport | None:
        for _label, _value in (("original_code", original_code),
                               ("fixed_code", fixed_code)):
            if isinstance(_value, str):
                continue
            _log.warning(
                "[BehaviorRegression] %s 非源码字符串形态(%s)，"
                "无法建立行为基线，按不可验证降级",
                _label, type(_value).__name__)
            return BehaviorRegressionReport(
                status=EquivalenceStatus.UNVERIFIABLE,
                requires_manual_review=True,
                error_detail=(f"{_label} 非源码字符串形态"
                              f"({type(_value).__name__})，无法建立行为基线"),
            )
        return None
    @staticmethod
    def _syntax_reject_report(
        original_code: Any, fixed_code: Any,
    ) -> BehaviorRegressionReport | None:
        for label, value in (("original_code", original_code),
                             ("fixed_code", fixed_code)):
            syntax_error = _source_syntax_error(value)
            if syntax_error is not None:
                detail = safe_str(syntax_error)[:LOG_DETAIL_MAX_CHARS]
                _log.warning(
                    "[BehaviorRegression] %s 源码不可解析(%s: %s)，"
                    "按不可验证降级", label,
                    type(syntax_error).__name__, detail)
                return BehaviorRegressionReport(
                    status=EquivalenceStatus.UNVERIFIABLE,
                    requires_manual_review=True,
                    error_detail=(
                        f"{label} 源码不可解析"
                        f"({type(syntax_error).__name__}: {detail})"),
                )
        return None
    @staticmethod
    def _restore_failed_report(
        detail: str, sig_changes: list,
    ) -> BehaviorRegressionReport:
        return BehaviorRegressionReport(
            status=EquivalenceStatus.ERROR,
            requires_manual_review=True,
            restore_failed=True,
            api_surface_changes=sig_changes,
            error_detail=detail,
        )
    @staticmethod
    def _real_regression_report(
        real_result: tuple[str, str] | None, sig_changes: list,
    ) -> BehaviorRegressionReport | None:
        if real_result is None or real_result[0] != "regressed":
            return None
        return BehaviorRegressionReport(
            status=EquivalenceStatus.REGRESSED,
            requires_manual_review=True,
            api_surface_changes=sig_changes,
            error_detail=f"真实测试退化: {real_result[1]}",
            total_tests=1, passed_tests=0, failed_tests=1,
        )
    def _synthetic_cases(self, existing_tests, orig_sigs
                         ) -> tuple[list, list]:
        """合成用例并剔除环境绑定用例。

        返回 (参与等价判定的用例, 被剔除的环境绑定用例)。剔除必须发生
        在 max_test_cases 截断**之前**，否则剔除后剩余用例数会不足。
        """
        test_cases = (_coerce_existing_cases(existing_tests)
                      or self._generator.generate(orig_sigs))
        runnable = [c for c in test_cases
                    if not getattr(c, "env_bound", False)]
        excluded = [c for c in test_cases
                    if getattr(c, "env_bound", False)]
        if len(runnable) > self.max_test_cases:
            return (self._round_robin_select(runnable, self.max_test_cases),
                    excluded)
        return runnable, excluded
    def _no_case_report(
        self, real_result: tuple[str, str] | None,
        sig_changes: list, sig_verdict: str,
    ) -> BehaviorRegressionReport:
        if real_result is not None and real_result[0] == "passed":
            report = BehaviorRegressionReport(
                status=EquivalenceStatus.PASSED,
                total_tests=1,
                passed_tests=1,
                failed_tests=0,
                api_surface_changes=sig_changes,
            )
            self._promote_sig_enhanced(report, sig_verdict)
            return report
        return BehaviorRegressionReport(
            status=EquivalenceStatus.UNVERIFIABLE,
            requires_manual_review=True,
            api_surface_changes=sig_changes,
            error_detail="无可测试用例，行为等价性未验证",
        )
_BEHAVIOR_REJECT_DETAIL_MAX_CHARS = 200
def _as_change_list(changes: Any) -> list[str]:
    if isinstance(changes, str):
        return [changes] if changes else []
    if isinstance(changes, (list, tuple)):
        return [change for change in changes if isinstance(change, str)]
    return []
def describe_behavior_regression(
        report: BehaviorRegressionReport) -> dict[str, Any]:
    api_changes = _as_change_list(report.api_surface_changes)
    failed_tests = int(report.failed_tests)
    total_tests = int(report.total_tests)
    return {
        'status': report.status.value,
        'equivalent': report.status in (EquivalenceStatus.PASSED,
                                        EquivalenceStatus.ENHANCED),
        'is_regressed': report.status == EquivalenceStatus.REGRESSED,
        'objective_break': bool(
            failed_tests > 0
            or any(change.startswith(('[BREAKING]', '[SIGNATURE]'))
                   for change in api_changes)),
        'reject_reason': _behavior_reject_detail(
            report, api_changes, failed_tests, total_tests),
        'total_tests': total_tests,
        'passed_tests': int(report.passed_tests),
        'failed_tests': failed_tests,
        'pass_rate': report.pass_rate,
        'api_changes': api_changes,
        'requires_manual_review': bool(report.requires_manual_review),
        'error_detail': str(getattr(report, 'error_detail', '') or ''),
        'restore_failed': bool(getattr(report, 'restore_failed', False)),
        'elapsed_ms': report.elapsed_ms,
    }
def _behavior_reject_detail(report: BehaviorRegressionReport,
                            api_changes: list, failed_tests: int,
                            total_tests: int) -> str:
    reason_parts: list[str] = []
    if api_changes:
        reason_parts.append(
            'API签名变化: ' + '; '.join(str(change) for change in api_changes[:3]))
    if failed_tests > 0:
        reason_parts.append(f'行为测试失败: {failed_tests}/{total_tests}')
        for tr in getattr(report, 'test_results', []) or []:
            if not getattr(tr, 'passed', True):
                _case = getattr(tr, 'case_id', '')
                _diff = getattr(tr, 'diff_detail', '')
                reason_parts.append(f'  {_case}: {_diff}')
    return '; '.join(reason_parts)[:_BEHAVIOR_REJECT_DETAIL_MAX_CHARS]
_FILE_HASH_CHUNK_BYTES = 64 * 1024
_G4_VERIFIED_INDEX_NAME = "_g4_verified_index.json"
_G4_MAX_BUCKET_WORKERS = 4
_G4_PROCESS_EXC = (OSError, ValueError, KeyError, TypeError,
                   AttributeError, RuntimeError)
_G4_VERIFIER_SOURCE_NAMES = (
    "diag_regression_guard.py", "diag_regression_exec.py",
    "diag_shared_ast_nodes.py")
@dataclass(frozen=True)
class _G4Tally:
    total: int
    passed: int
    failed: int
    unverifiable: int
def _file_sha256(path: str) -> str:
    try:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(_FILE_HASH_CHUNK_BYTES), b""):
                h.update(chunk)
        return h.hexdigest()
    except OSError as _e:
        _log.debug("[G4] 产物指纹计算失败（按重验处理）: %s: %s", path, _e)
        return ""
def _g4_verifier_fingerprint(guard: BehaviorRegressionGuard) -> str:
    module_dir = os.path.dirname(os.path.abspath(__file__))
    source_hashes = [
        _file_sha256(os.path.join(module_dir, name))
        for name in _G4_VERIFIER_SOURCE_NAMES
    ]
    if not all(source_hashes):
        return ""
    config = json.dumps({
        "timeout_sec": guard.timeout_sec,
        "max_test_cases": guard.max_test_cases,
        "min_pass_rate": guard.min_pass_rate,
        "extra_pythonpath": guard._executor.extra_pythonpath,
    }, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return _source_fingerprint("\n".join([*source_hashes, config]))
def _g4_index_entries(data) -> dict:
    entries = data.get("entries") if isinstance(data, dict) else None
    if not isinstance(entries, dict):
        return {}
    return {k: v for k, v in entries.items()
            if isinstance(k, str) and isinstance(v, dict)}
def _load_g4_verified_index(temp_dir: str) -> dict:
    p = os.path.join(temp_dir, _G4_VERIFIED_INDEX_NAME)
    try:
        with open(p, encoding="utf-8-sig") as f:
            data = json.load(f)
    except FileNotFoundError:
        _log.debug("[G4] 已验证清单不存在（首轮全量验证）")
        return {}
    except (OSError, ValueError, RecursionError) as _e:
        _log.warning("[G4] 已验证清单损坏，按空清单全量重验: %s: %s", p, _e)
        return {}
    return _g4_index_entries(data)
def _save_g4_verified_index(temp_dir: str, entries: dict) -> bool:
    p = os.path.join(temp_dir, _G4_VERIFIED_INDEX_NAME)
    try:
        atomic_write_text(
            p, json.dumps({"entries": entries,
                           "_updated": _time.strftime("%Y%m%d%H%M%S")},
                          ensure_ascii=False, default=str),
            tag="g4_index")
    except (OSError, ValueError) as e:
        log_swallowed(
            __name__, e,
            context=f'_save_g4_verified_index:{type(e).__name__}')
        return False
    return True
def _g4_source_file(fix_data) -> str:
    if not isinstance(fix_data, dict):
        return ''
    _ref = fix_data.get('original_file') or fix_data.get('file_path') or ''
    return _ref if isinstance(_ref, str) else ''
def _g4_source_field(fix_data: dict, primary: str, fallback: str):
    for key in (primary, fallback):
        if key not in fix_data:
            continue
        value = fix_data[key]
        if value is not None:
            return value
    return None
def _g4_extract_fields(fix_data: dict) -> tuple[object, object, str]:
    original_code = _g4_source_field(
        fix_data, 'original_source', 'original_code')
    fixed_code = _g4_source_field(fix_data, 'fixed_source', 'fixed_code')
    return original_code, fixed_code, _g4_source_file(fix_data)
def _g4_side_names(original_bad: bool, fixed_bad: bool) -> str:
    return '+'.join(name for name, bad in (('original', original_bad),
                                           ('fixed', fixed_bad)) if bad)
def _g4_source_pair_skip(original_code, fixed_code) -> str | None:
    _orig_bad = original_code is not None and not isinstance(original_code, str)
    _fixed_bad = fixed_code is not None and not isinstance(fixed_code, str)
    if _orig_bad or _fixed_bad:
        return (f'invalid_source: {_g4_side_names(_orig_bad, _fixed_bad)}'
                f' 源码形态异常({type(original_code).__name__}/'
                f'{type(fixed_code).__name__})')
    if original_code is None or fixed_code is None:
        return (f'missing_source: '
                f'{_g4_side_names(original_code is None, fixed_code is None)}'
                ' 源码对缺失')
    return None
def _g4_prepare_payload(result_path: str) -> dict:
    try:
        with open(result_path, 'rb') as rf:
            raw = rf.read()
        fix_data = json.loads(raw.decode('utf-8-sig'))
        if not isinstance(fix_data, dict):
            return {'skip_reason':
                    'invalid_payload: 顶层非 dict 载荷'
                    f'({type(fix_data).__name__})'}
        original_code, fixed_code, original_file = _g4_extract_fields(fix_data)
        _skip = _g4_source_pair_skip(original_code, fixed_code)
        if _skip:
            return {'skip_reason': _skip, 'fix_data': fix_data}
        return {'fix_data': fix_data, 'original_code': original_code,
                'fixed_code': fixed_code, 'original_file': original_file,
                'base_name': os.path.basename(result_path),
                'content_sha256': hashlib.sha256(raw).hexdigest()}
    except _G4_PROCESS_EXC as _e:
        _log.warning('[G4] 语义等价验证跳过: %s', _e)
        return {'skip_reason':
                f'prepare_error: {type(_e).__name__}: {str(_e)[:80]}'}
def _g4_rule_id(fix_data) -> str:
    _rid = fix_data.get('rule_id') if isinstance(fix_data, dict) else None
    return _rid if isinstance(_rid, str) and _rid else 'EQ-CHECK'
def _g4_unverifiable(fix_data, result_path: str,
                     reason: str) -> tuple[list, int, int, int]:
    _rid = _g4_rule_id(fix_data)
    _fref = _g4_source_file(fix_data) or result_path
    _msg = f'等价性无法验证: {os.path.basename(result_path)} ({reason})'
    return ([{'rule_id': _rid, 'file': _fref, 'line': 0, 'source': 'G4',
              'severity': 'P1', 'confidence': 0.6,
              'equivalence_ok': False, 'verdict': 'unverifiable',
              'verify_status': 'unverifiable', 'total_tests': 0, 'failed_tests': 0,
              'message': _msg}],
            0, 0, 1)
def _g4_report_finding(fix_data, result_path: str, base_name: str,
                       common: dict, report) -> tuple[list, int, int, int]:
    detail = _g4_report_detail(report)
    if report.status in (EquivalenceStatus.PASSED, EquivalenceStatus.ENHANCED):
        return _g4_passed_finding(base_name, common, detail, report)
    if report.restore_failed:
        return _g4_restore_failed_finding(base_name, common, detail, report)
    if report.status == EquivalenceStatus.REGRESSED:
        return _g4_regressed_finding(base_name, common, detail, report)
    return _g4_unverifiable_from_report(
        fix_data, result_path, base_name, common, detail, report)
def _g4_report_detail(report) -> dict:
    _excluded = list(report.environment_excluded_cases)
    return {
        'verify_status': report.status.value, 'total_tests': report.total_tests,
        'failed_tests': report.failed_tests, 'pass_rate': round(report.pass_rate, 4),
        'baseline_unavailable_tests': report.baseline_unavailable_tests,
        # 环境绑定用例（真实桌面/COM/硬件）无头环境建立不了可重放基线，
        # 不参与等价判定；显式列入报告，不静默丢弃。
        'environment_excluded_tests': len(_excluded),
        'environment_excluded_sample': _excluded[:5],
        'api_surface_changes': _as_change_list(report.api_surface_changes)[:5],
    }
def _g4_passed_finding(base_name: str, common: dict, detail: dict,
                       report) -> tuple[list, int, int, int]:
    _enh_tag = ('' if report.status == EquivalenceStatus.PASSED
                else '，行为增强无回归')
    _msg = (f"等价性通过: {base_name} "
            f"({report.passed_tests}/{report.total_tests} 测试{_enh_tag})")
    return ([{**common, **detail, 'severity': 'P3', 'confidence': 0.9,
        'equivalence_ok': True, 'message': _msg}],
        1, 0, 0)
def _g4_restore_failed_finding(
    base_name: str, common: dict, detail: dict, report,
) -> tuple[list, int, int, int]:
    _msg = (f"等价性验证后还原原始源码失败: {base_name} "
            f"({report.error_detail[:LOG_DETAIL_MAX_CHARS]})")
    return ([{**common, **detail, 'severity': 'P0', 'confidence': 1.0,
        'equivalence_ok': False, 'restore_failed': True, 'message': _msg}],
        0, 1, 0)
def _g4_regressed_finding(base_name: str, common: dict, detail: dict,
                          report) -> tuple[list, int, int, int]:
    _objective_changes = [
        c for c in report.api_surface_changes
        if isinstance(c, str) and c.startswith(('[BREAKING]', '[SIGNATURE]'))]
    _sig = (f"; {'; '.join(_objective_changes[:2])}"
            if _objective_changes else '')
    _msg = (f"等价性失败: {base_name} "
            f"({report.failed_tests}/{report.total_tests} 测试不通过{_sig})")
    return ([{**common, **detail, 'severity': 'P0', 'confidence': 0.9,
        'equivalence_ok': False, 'message': _msg}],
        0, 1, 0)
def _g4_unverifiable_from_report(
    fix_data, result_path: str, base_name: str, common: dict,
    detail: dict, report,
) -> tuple[list, int, int, int]:
    if report.dangerous_content:
        return _g4_unverifiable(
            fix_data, result_path,
            f'危险模式拦截: {report.error_detail[:60]}')
    _reason = report.error_detail[:80] if report.error_detail else '无可测试API'
    _msg = (f'等价性无法验证: {base_name} '
            f'(status={report.status.value}, {_reason})')
    return ([{**common, **detail, 'severity': 'P1', 'confidence': 0.6,
        'equivalence_ok': False, 'verdict': 'unverifiable', 'message': _msg}],
        0, 0, 1)
def _g4_verify_one(guard: BehaviorRegressionGuard, payload: dict,
                   result_path: str) -> tuple[list, int, int, int]:
    fix_data = payload['fix_data']
    original_code, fixed_code = payload['original_code'], payload['fixed_code']
    original_file, base_name = payload['original_file'], payload['base_name']
    try:
        file_ref = original_file or result_path
        common = {
            'rule_id': _g4_rule_id(fix_data),
            'file': file_ref,
            'line': 0,
            'source': 'G4',
        }
        if original_code == fixed_code:
            return ([{**common, 'severity': 'P3', 'confidence': 0.9,
                'equivalence_ok': True, 'verify_status': 'passed',
                'total_tests': 0, 'failed_tests': 0, 'pass_rate': 1.0,
                'message': f'等价性通过: {base_name} (源码零差异)'}], 1, 0, 0)
        report = guard.verify(
            original_code, fixed_code, filepath=original_file)
        return _g4_report_finding(fix_data, result_path, base_name,
                                  common, report)
    except ContractViolationError as _e:
        _log.warning("[G4] 危险模式拦截（产物无法安全执行验证）: %s",
                     str(_e)[:LOG_DETAIL_MAX_CHARS])
        return _g4_unverifiable(
            fix_data, result_path, f'危险模式拦截: {str(_e)[:60]}')
    except _G4_PROCESS_EXC as _e:
        _log.warning('[G4] 语义等价验证处理产物异常: %s', _e, exc_info=True)
        return _g4_unverifiable(
            fix_data, result_path,
            f'验证异常: {type(_e).__name__}: {str(_e)[:60]}')
def _g4_scan_product_files(temp_dir: str) -> list[str]:
    fix_results: list[str] = []
    if os.path.isdir(temp_dir):
        for fn in os.listdir(temp_dir):
            if fn.endswith(('.fix_result.json', '.autofix.json')):
                fix_results.append(os.path.join(temp_dir, fn))
    fix_results.sort()
    return fix_results
def _g4_prepare_all(fix_results: list[str]) -> tuple[list, list]:
    payloads: list[dict | None] = []
    skipped_products: list[dict] = []
    for _rp in fix_results:
        _p = _g4_prepare_payload(_rp)
        if 'skip_reason' in _p:
            _skipped_data = _p.get('fix_data') or {}
            skipped_products.append({
                'file': os.path.basename(_rp),
                'reason': _p['skip_reason'],
                'rule_id': _g4_rule_id(_skipped_data),
                'source_file': _g4_source_file(_skipped_data),
            })
            payloads.append(None)
        else:
            payloads.append(_p)
    return payloads, skipped_products
def _g4_signature_regression_replay(
        status, findings: list[dict]) -> tuple[list, int, int, int] | None:
    if status != EquivalenceStatus.REGRESSED.value or not findings:
        return None
    for item in findings:
        changes = _as_change_list(item.get('api_surface_changes'))
        if not any(change.startswith(('[BREAKING]', '[SIGNATURE]'))
                   for change in changes):
            return None
    return [dict(item) for item in findings], 0, 1, 0
def _g4_cached_verification(entry) -> tuple[list, int, int, int] | None:
    if not isinstance(entry, dict):
        return None
    status = entry.get('verify_status')
    findings = entry.get('findings')
    if not isinstance(status, str):
        return None
    if (not isinstance(findings, list) or not findings
            or not all(isinstance(item, dict) for item in findings)):
        return None
    if any(item.get('verify_status') != status for item in findings):
        return None
    return _g4_signature_regression_replay(status, findings)
def _g4_filter_verified(
        fix_results: list[str], payloads: list,
        verified_index: dict, *, verifier_key: str,
) -> tuple[dict, dict[int, str], set[int], dict[int, tuple], int]:
    _current_files = {os.path.basename(_p) for _p in fix_results}
    kept_entries = {k: v for k, v in verified_index.items()
                     if k in _current_files}
    orphans_pruned = len(verified_index) - len(kept_entries)
    file_hashes: dict[int, str] = {}
    verified_skip: set[int] = set()
    replayed: dict[int, tuple] = {}
    for idx, _rp in enumerate(fix_results):
        if payloads[idx] is None:
            continue
        _current_hash = _file_sha256(_rp)
        _payload_hash = payloads[idx].get('content_sha256', '')
        file_hashes[idx] = (_current_hash
                            if _payload_hash and _current_hash == _payload_hash
                            else '')
        _entry = kept_entries.get(os.path.basename(_rp))
        if not (_entry and file_hashes[idx] and verifier_key
                and _entry.get('sha256') == file_hashes[idx]
                and _entry.get('verifier_key') == verifier_key):
            continue
        _cached = _g4_cached_verification(_entry)
        if _cached is None:
            continue
        verified_skip.add(idx)
        replayed[idx] = _cached
    return kept_entries, file_hashes, verified_skip, replayed, orphans_pruned
def _g4_bucket_indices(payloads: list,
                        verified_skip: set[int]) -> dict[str, list[int]]:
    buckets: dict[str, list[int]] = {}
    for idx, payload in enumerate(payloads):
        if payload is None or idx in verified_skip:
            continue
        _source_file = payload['original_file']
        if _source_file:
            _bucket_key = os.path.normcase(os.path.realpath(_source_file))
        else:
            _bucket_key = short_hash(payload['original_code'])
        buckets.setdefault(_bucket_key, []).append(idx)
    return buckets
def _run_buckets_serial(run_bucket, buckets) -> list:
    return [run_bucket(indices) for indices in buckets.values()]
def _g4_run_buckets(
        guard: BehaviorRegressionGuard, payloads: list,
        fix_results: list[str],
        buckets: dict[str, list[int]]) -> dict[int, tuple]:
    def _run_bucket(indices: list[int]) -> list[tuple[int, tuple]]:
        return [(idx, _g4_verify_one(guard, payloads[idx], fix_results[idx]))
                for idx in indices]
    max_workers = min(_G4_MAX_BUCKET_WORKERS, len(buckets),
                      (os.cpu_count() or 1))
    bucket_results: list = []
    if max_workers >= 2:
        try:
            with ThreadPoolExecutor(max_workers=max_workers,
                                    thread_name_prefix='g4-equiv') as ex:
                bucket_results = list(ex.map(_run_bucket, buckets.values()))
        except (OSError, RuntimeError) as _e:
            _log.warning("[G4] 桶间并行线程池不可用，退化为全串行: %s", _e)
            bucket_results = _run_buckets_serial(_run_bucket, buckets)
    else:
        bucket_results = _run_buckets_serial(_run_bucket, buckets)
    return {idx: per_result
            for bucket in bucket_results
            for idx, per_result in bucket}
def _g4_aggregate_results(
        fix_results: list[str],
        bucket_map: dict[int, tuple]) -> tuple[list, int, int, int]:
    findings: list = []
    n_pass = n_fail = n_unverifiable = 0
    for idx in range(len(fix_results)):
        per_result = bucket_map.get(idx)
        if per_result is None:
            continue
        _finds, _p, _f, _u = per_result
        findings.extend(_finds)
        n_pass += _p
        n_fail += _f
        n_unverifiable += _u
    return findings, n_pass, n_fail, n_unverifiable
def _g4_update_verified_index(
        temp_dir: str, verified_index: dict, file_hashes: dict,
        bucket_map: dict[int, tuple], fix_results: list[str], *,
        verifier_key: str, pruned: bool = False) -> bool:
    if not any((bucket_map, verified_index, pruned)):
        return False
    _now = _time.strftime('%Y%m%d%H%M%S')
    for idx, per_result in bucket_map.items():
        _fn = os.path.basename(fix_results[idx])
        _digest = file_hashes.get(idx, '')
        if not _digest:
            continue
        _st = ''
        if per_result[0] and isinstance(per_result[0][0], dict):
            _st = str(per_result[0][0].get('verify_status', ''))
        _replay = (_g4_signature_regression_replay(_st, per_result[0])
                   if verifier_key else None)
        if _replay is None:
            verified_index.pop(_fn, None)
            continue
        verified_index[_fn] = {
            'sha256': _digest, 'verify_status': _st,
            'verifier_key': verifier_key,
            'findings': _replay[0], 'verified_at': _now,
        }
    return _save_g4_verified_index(temp_dir, verified_index)
def _g4_skipped_regressed_count(verified_skip: set[int], verified_index: dict,
                                fix_results: list[str]) -> int:
    count = 0
    for idx in verified_skip:
        entry = verified_index.get(os.path.basename(fix_results[idx]))
        if isinstance(entry, dict) and entry.get('verify_status') == 'regressed':
            count += 1
    return count
def _g4_build_summary(fix_results: list[str], verified_index: dict,
                      verified_skip: set[int], skipped_products: list[dict],
                      tally: _G4Tally) -> tuple[str, int]:
    summary = f'语义等价性验证: {tally.total}个发现'
    if tally.total:
        summary += (f'（通过{tally.passed}/失败{tally.failed}/'
                    f'无法验证{tally.unverifiable}）')
    if skipped_products:
        _kinds = sorted({s['reason'].split(':')[0] for s in skipped_products})
        summary += (f'；{len(skipped_products)}个产物跳过'
                    f'（{"/".join(_kinds)}，明细见 skipped_products）')
    _skipped_regressed = 0
    if verified_skip:
        _skipped_regressed = _g4_skipped_regressed_count(
            verified_skip, verified_index, fix_results)
        summary += (f'；{len(verified_skip)}个历史产物已验证跳过'
                    f'（单次复验，结论见 {_G4_VERIFIED_INDEX_NAME}）')
        if _skipped_regressed:
            summary += (f'，其中 {_skipped_regressed} 个历史结论为 REGRESSED'
                        f'（P0 等价性失败，未处置前本轮门禁判失败）')
    return summary, _skipped_regressed
def _g4_status(n_fail: int, n_unverifiable: int) -> str:
    if n_fail > 0:
        return 'fail'
    if n_unverifiable > 0:
        return 'warn'
    return 'pass'
def _g4_skipped_product_results(
        temp_dir: str, skipped_products: list[dict]) -> tuple[list, int]:
    findings: list = []
    for skipped in skipped_products:
        result_path = os.path.join(temp_dir, skipped['file'])
        _fix_ref = {'rule_id': skipped.get('rule_id', ''),
                    'original_file': skipped.get('source_file', '')}
        per_findings, _p, _f, _u = _g4_unverifiable(
            _fix_ref, result_path, skipped['reason'])
        findings.extend(per_findings)
    return findings, len(skipped_products)
def _g4_recheck_product_snapshots(
        payloads: list, fix_results: list[str], bucket_map: dict[int, tuple],
        verified_skip: set[int],
) -> None:
    for idx in tuple(bucket_map):
        payload = payloads[idx]
        expected = payload.get('content_sha256', '')
        if expected and _file_sha256(fix_results[idx]) == expected:
            continue
        bucket_map[idx] = _g4_unverifiable(
            payload['fix_data'], fix_results[idx],
            'source_changed_during_run: 修复产物在验证期间变化，旧结论已丢弃')
        verified_skip.discard(idx)
def _g4_verify_product_outcomes(
        guard: BehaviorRegressionGuard, temp_dir: str, fix_results: list[str],
        payloads: list, replayed: dict[int, tuple], verified_skip: set[int],
        skipped_products: list[dict],
) -> tuple[dict[int, tuple], list, _G4Tally]:
    buckets = _g4_bucket_indices(payloads, verified_skip)
    bucket_map = dict(replayed)
    bucket_map.update(_g4_run_buckets(guard, payloads, fix_results, buckets))
    _g4_recheck_product_snapshots(
        payloads, fix_results, bucket_map, verified_skip)
    findings, n_pass, n_fail, n_unverifiable = _g4_aggregate_results(
        fix_results, bucket_map)
    skipped_findings, skipped_unverifiable = _g4_skipped_product_results(
        temp_dir, skipped_products)
    findings.extend(skipped_findings)
    n_unverifiable += skipped_unverifiable
    tally = _G4Tally(len(findings), n_pass, n_fail, n_unverifiable)
    return bucket_map, findings, tally
def _g4_result_payload(
        temp_dir: str, fix_results: list[str], verified_index: dict,
        verified_skip: set[int], skipped_products: list[dict],
        findings: list, tally: _G4Tally, wrote_index: bool,
) -> dict:
    summary, skipped_regressed = _g4_build_summary(
        fix_results, verified_index, verified_skip, skipped_products, tally)
    status = ('fail' if skipped_regressed
              else _g4_status(tally.failed, tally.unverifiable))
    return {'status': status, 'findings_count': tally.total, 'summary': summary,
            'findings': findings, 'skipped_products': skipped_products,
            'skipped_verified': len(verified_skip),
            'skipped_regressed': skipped_regressed,
            'verified_index_path': (os.path.join(temp_dir, _G4_VERIFIED_INDEX_NAME)
                                    if wrote_index else '')}
def run_equivalence_gate(skill_dir: str, cache: SharedCache | None = None) -> dict:
    require_warmed(cache, "G4 语义等价性验证")
    _g4_start = _time.time()
    try:
        _pythonpath = list(python_import_roots(
            skill_dir, detect_layout(skill_dir)))
        guard = _equivalence_tier_guard(
            EQUIVALENCE_GUARD_TIMEOUT_SEC,
            EQUIVALENCE_GUARD_MAX_TEST_CASES,
            extra_pythonpath=_pythonpath)
        verifier_key = _g4_verifier_fingerprint(guard)
        temp_dir = get_temp_base(skill_dir)
        fix_results = _g4_scan_product_files(temp_dir)
        if not fix_results:
            return {'status': 'pass', 'findings_count': 0,
                    'summary': '语义等价性验证: 无修复产物可验证',
                    'findings': [], 'skipped_products': [],
                    'skipped_verified': 0, 'skipped_regressed': 0,
                    'verified_index_path': ''}
        payloads, skipped_products = _g4_prepare_all(fix_results)
        verified_index = _load_g4_verified_index(temp_dir)
        (verified_index, file_hashes, verified_skip, replayed,
         orphans_pruned) = _g4_filter_verified(
            fix_results, payloads, verified_index, verifier_key=verifier_key)
        bucket_map, findings, tally = _g4_verify_product_outcomes(
            guard, temp_dir, fix_results, payloads, replayed,
            verified_skip, skipped_products)
        _wrote_index = _g4_update_verified_index(
            temp_dir, verified_index, file_hashes, bucket_map, fix_results,
            verifier_key=verifier_key, pruned=bool(orphans_pruned))
        return _g4_result_payload(
            temp_dir, fix_results, verified_index, verified_skip,
            skipped_products, findings, tally, _wrote_index)
    except _G4_PROCESS_EXC as e:
        _log.warning('[G4] 语义等价性验证处理异常(%s): %s',
                     type(e).__name__, e, exc_info=True)
        return {'status': 'warn',
                'summary': f'语义等价性验证异常: {type(e).__name__}: {e}',
                'findings': [], 'findings_count': 0,
                'skipped_products': [], 'skipped_verified': 0,
                'skipped_regressed': 0, 'verified_index_path': ''}
    finally:
        perf_trace('g4_equivalence', round((_time.time() - _g4_start) * 1000, 1))

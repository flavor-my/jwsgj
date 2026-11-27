from __future__ import annotations

import ast
import logging
import os
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    assign_targets_value,
    attr_chain_key,
    dotted_name,
    handler_exc_names,
    iter_def_site_nodes,
    iter_pattern_capture_names,
    iter_scope_statements,
    iter_unpack_target_names,
    latest_prior,
    module_postpones_annotations,
    scope_roots,
)
from jwsgj.diag_shared_source_core import CONTEXT_ACCESS_ERRORS
from jwsgj.diag_shared_source_core import parse_py_file as _parse_py_file
from jwsgj.diag_shared_source_scan import is_suppressed, parse_suppressions
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import is_irrefutable_pattern, walk_nodes
from jwsgj.runtime_scope import (
    TEST_DIR_CANDIDATES_LOWER,
    is_pruned_scan_dir,
    is_scan_py_name,
    is_test_file_path,
    safe_relpath,
    scan_exclude_dirs,
)

logger = logging.getLogger(__name__)
_LOG_TAG = __name__.rsplit(".", 1)[-1]
__all__ = [
    "ExceptionPropagationAnalyzer",
    "ExceptionPropagationEntry",
    "ExceptionPropagationReport",
    "collect_exception_scan_files",
    "detect_resource_leaks_inline",
    "exception_type_lineage",
    "handler_exc_name",
    "handler_exc_names",
    "is_protocol_exc_site",
    "load_source_and_tree",
    "log_swallowed_entries",
    "run_exception_miner_detector",
    "run_tryceratops_detector",
    "summarize_type_flow",
]
_EM004_CONTROL_FLOW_TYPES = frozenset({
    'KeyError', 'IndexError', 'ValueError',
    'AttributeError', 'StopIteration', 'TypeError',
})
def _visit_groups(visitor, *groups) -> None:
    for group in groups:
        for stmt in group or ():
            visitor.visit(stmt)
def _finding(line: int, pattern: str, severity: str, exception: str,
             reason: str) -> dict:
    return {
        'line': line,
        'pattern': pattern,
        'severity': severity,
        'exception': exception,
        'reason': reason,
    }
@dataclass
class ExceptionPropagationEntry:
    filepath: str = ""
    raise_line: int = 0
    raise_type: str = ""
    except_line: int = 0
    except_type: str = ""
    is_swallowed: bool = False
    swallow_kind: str = ""
    severity: str = "low"
    message: str = ""
    suggestion: str = ""
    raise_in_try_body: bool = False
    raise_msg: str = ""
    raise_transparent: bool = False
@dataclass
class ExceptionPropagationReport:
    project_root: str = ""
    entries: list[ExceptionPropagationEntry] = field(default_factory=list)
    total_raises: int = 0
    total_caught: int = 0
    total_uncaught: int = 0
    total_swallowed: int = 0
@dataclass(frozen=True)
class _RaiseRecord:
    line: int
    exc_type: str
    node: ast.Raise
    transparent: bool = False
def _unwrap_with_traceback(exc):
    while (isinstance(exc, ast.Call)
           and isinstance(exc.func, ast.Attribute)
           and exc.func.attr == 'with_traceback'):
        exc = exc.func.value
    return exc
def _exception_carrier_name(exc) -> str | None:
    exc = _unwrap_with_traceback(exc)
    return exc.id if isinstance(exc, ast.Name) else None
def _is_param_raise(node: ast.Raise, param_exc_names: set,
                    rebind_lines: dict[str, int]) -> bool:
    carrier = _exception_carrier_name(node.exc)
    if not param_exc_names or carrier not in param_exc_names:
        return False
    rebind_line = rebind_lines.get(carrier)
    return rebind_line is None or node.lineno < rebind_line
_ATTRIBUTE_PROTOCOL_EXCS = frozenset({
    "AttributeError", "ImportError", "ModuleNotFoundError"})
_PROTOCOL_EXC_BY_FUNC = {
    **{name: _ATTRIBUTE_PROTOCOL_EXCS for name in (
        "__getattr__", "__getattribute__", "__setattr__", "__delattr__")},
    "__getitem__": frozenset({"IndexError", "KeyError"}),
    "__next__": frozenset({"StopIteration"}),
    "__anext__": frozenset({"StopAsyncIteration"}),
}
_PROTOCOL_EXC_TYPES = frozenset({
    exc_type for types in _PROTOCOL_EXC_BY_FUNC.values() for exc_type in types})
def is_protocol_exc_site(func_name: str, exc_type: str) -> bool:
    return exc_type in _PROTOCOL_EXC_BY_FUNC.get(func_name, ())
def _fstring_static_text(joined: ast.JoinedStr) -> str:
    return "".join(
        v.value for v in joined.values
        if isinstance(v, ast.Constant) and isinstance(v.value, str))
def _static_message_text(node, depth: int = 0) -> str:
    if depth > 3 or node is None:
        return ""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.JoinedStr):
        return _fstring_static_text(node)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
        return _static_message_text(node.left, depth + 1)
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "format"):
        return _static_message_text(node.func.value, depth + 1)
    return ""
def _raise_message_text(raise_node: ast.Raise) -> str:
    try:
        _exc = _unwrap_with_traceback(raise_node.exc)
        if _exc is None:
            return ""
        if getattr(_exc, "args", None):
            return _static_message_text(_exc.args[0])[:200]
        # ``raise RuntimeError("..." % (x,))`` 的 exc 是 BinOp 而不是 Call：
        # 没有 .args 就直接取表达式自身的静态文本。漏这一步会让“故意抛出、
        # 消息里带守卫关键字”的异常读不到消息，is_intentional_guard 的
        # 豁免整体失效，EX-UNCAUGHT 把它报成未捕获异常。
        return _static_message_text(_exc)[:200]
    except Exception as _e:
        log_swallowed(
            __name__, _e,
            context=f'_raise_message_text:{type(_e).__name__}')
    return ""
def _is_neutral_return(value) -> bool:
    if value is None:
        return True
    return (isinstance(value, ast.Constant)
            and (value.value is None or value.value is False))
_HANDLER_LOG_METHODS = frozenset({
    "debug", "info", "warning", "warn", "error", "critical", "fatal",
    "exception", "log",
})
def _classify_expr_stmt(value) -> str:
    if isinstance(value, ast.Constant):
        return "neutral"
    return "real"
_UNKNOWN_RAISE_TYPES = frozenset({"unknown", "bare re-raise", "re-raise variable"})
_DEFAULT_KNOWN_EXC_TYPES: tuple[str, ...] = ()
_BUILTIN_EXC_BASES = {
    'BaseException': None,
    'Exception': 'BaseException',
    'BaseExceptionGroup': 'BaseException',
    'ExceptionGroup': 'Exception',
    'GeneratorExit': 'BaseException',
    'KeyboardInterrupt': 'BaseException',
    'SystemExit': 'BaseException',
    'ArithmeticError': 'Exception',
    'FloatingPointError': 'ArithmeticError',
    'OverflowError': 'ArithmeticError',
    'ZeroDivisionError': 'ArithmeticError',
    'AssertionError': 'Exception',
    'AttributeError': 'Exception',
    'BufferError': 'Exception',
    'EOFError': 'Exception',
    'ImportError': 'Exception',
    'ModuleNotFoundError': 'ImportError',
    'LookupError': 'Exception',
    'IndexError': 'LookupError',
    'KeyError': 'LookupError',
    'MemoryError': 'Exception',
    'NameError': 'Exception',
    'UnboundLocalError': 'NameError',
    'OSError': 'Exception',
    'BlockingIOError': 'OSError',
    'ChildProcessError': 'OSError',
    'ConnectionError': 'OSError',
    'BrokenPipeError': 'ConnectionError',
    'ConnectionAbortedError': 'ConnectionError',
    'ConnectionRefusedError': 'ConnectionError',
    'ConnectionResetError': 'ConnectionError',
    'FileExistsError': 'OSError',
    'FileNotFoundError': 'OSError',
    'InterruptedError': 'OSError',
    'IsADirectoryError': 'OSError',
    'NotADirectoryError': 'OSError',
    'PermissionError': 'OSError',
    'ProcessLookupError': 'OSError',
    'TimeoutError': 'OSError',
    'ReferenceError': 'Exception',
    'RuntimeError': 'Exception',
    'NotImplementedError': 'RuntimeError',
    'RecursionError': 'RuntimeError',
    'StopAsyncIteration': 'Exception',
    'StopIteration': 'Exception',
    'SyntaxError': 'Exception',
    'IndentationError': 'SyntaxError',
    'TabError': 'IndentationError',
    'SystemError': 'Exception',
    'TypeError': 'Exception',
    'ValueError': 'Exception',
    'UnicodeError': 'ValueError',
    'UnicodeDecodeError': 'UnicodeError',
    'UnicodeEncodeError': 'UnicodeError',
    'UnicodeTranslateError': 'UnicodeError',
    'Warning': 'Exception',
    'BytesWarning': 'Warning',
    'DeprecationWarning': 'Warning',
    'EncodingWarning': 'Warning',
    'FutureWarning': 'Warning',
    'ImportWarning': 'Warning',
    'PendingDeprecationWarning': 'Warning',
    'ResourceWarning': 'Warning',
    'RuntimeWarning': 'Warning',
    'SyntaxWarning': 'Warning',
    'UnicodeWarning': 'Warning',
    'UserWarning': 'Warning',
}
_EXC_TYPE_ALIASES = {
    'IOError': 'OSError',
    'EnvironmentError': 'OSError',
    'WindowsError': 'OSError',
}
_BUILTIN_EXC_SECONDARY_BASES = {
    'ExceptionGroup': ('BaseExceptionGroup',),
}
def _canonical_exc_name(name: str) -> str:
    tail = name.rsplit('.', 1)[-1]
    return _EXC_TYPE_ALIASES.get(tail, tail)
def exception_type_lineage(type_name: str,
                           bases: dict[str, tuple[str, ...]] | None = None
                           ) -> frozenset:
    lineage: set[str] = set()
    pending = [_canonical_exc_name(type_name)]
    while pending:
        current = pending.pop()
        if not current or current in lineage:
            continue
        lineage.add(current)
        builtin_base = _BUILTIN_EXC_BASES.get(current)
        if builtin_base:
            pending.append(builtin_base)
        pending.extend(_BUILTIN_EXC_SECONDARY_BASES.get(current, ()))
        for base in (bases or {}).get(current, ()):
            pending.append(_canonical_exc_name(base))
    return frozenset(lineage)
def _lineage_catches(lineage: frozenset, handler_types: set) -> bool:
    if lineage & handler_types:
        return True
    # 谱系未触达内建根（基类在其它模块、本文件不可见）时无法证明它不是
    # Exception 子类；``except Exception`` 按 Python 惯例视为捕获，与
    # diag_exception_verdict._call_site_catches 的谱系未知兜底口径一致。
    return "Exception" in handler_types and "BaseException" not in lineage
def _is_broad_catch(names, bare: bool = False) -> bool:
    return bare or "BaseException" in names
def _is_unknown_raise_type(raise_type: str) -> bool:
    return (not raise_type
            or raise_type[:1].islower()
            or raise_type in _UNKNOWN_RAISE_TYPES)
def _is_exception_type_name(name: str | None, known) -> bool:
    return bool(name) and (name.endswith(("Error", "Exception"))
                          or name in known)
def _raise_target_type_names(tree: ast.AST) -> frozenset[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Raise) or node.exc is None:
            continue
        exc = _unwrap_with_traceback(node.exc)
        tail = (_exc_type_tail(exc.func) if isinstance(exc, ast.Call)
                else _exc_type_tail(exc))
        if tail and not _is_unknown_raise_type(tail):
            names.add(tail)
    return frozenset(names)
def _exc_type_tail(t: ast.expr) -> str | None:
    if isinstance(t, ast.Name):
        return t.id
    if isinstance(t, ast.Attribute):
        return t.attr
    return None
def _class_exc_bases(tree: ast.AST) -> dict[str, tuple[str, ...]]:
    bases: dict[str, list[str]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        tails = [tail for base in node.bases
                 if (tail := _exc_type_tail(base))]
        if not tails:
            continue
        bucket = bases.setdefault(node.name, [])
        for tail in tails:
            if tail not in bucket:
                bucket.append(tail)
    return {name: tuple(values) for name, values in bases.items()}
def handler_exc_name(handler: ast.ExceptHandler, bare_label: str) -> str:
    if handler.type is None:
        return bare_label
    return " | ".join(handler_exc_names(handler)) or "unknown"
@dataclass(frozen=True)
class _FileAnchors:
    protocol_sites: dict[int, str] = field(default_factory=dict)
    reraise_contexts: dict[int, ast.ExceptHandler | None] = field(
        default_factory=dict)
    def is_protocol_raise(self, exc_type: str, node: ast.Raise) -> bool:
        if exc_type not in _PROTOCOL_EXC_TYPES:
            return False
        func_name = self.protocol_sites.get(id(node), "")
        return is_protocol_exc_site(func_name, exc_type)
    def reraise_context(self, node: ast.Raise) -> tuple[frozenset, str]:
        handler = self.reraise_contexts.get(id(node))
        if handler is None:
            return frozenset(), ""
        return (frozenset(handler_exc_names(handler)),
                handler_exc_name(handler, "bare except"))
def _protocol_raise_sites(tree: ast.AST) -> dict[int, str]:
    sites: dict[int, str] = {}
    stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while stack:
        node, func_name = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            body_ids = {id(stmt) for stmt in node.body}
            for child in ast.iter_child_nodes(node):
                stack.append((
                    child, node.name if id(child) in body_ids else func_name))
            continue
        if isinstance(node, ast.Lambda):
            stack.extend((child, "") for child in ast.iter_child_nodes(node))
            continue
        if isinstance(node, ast.Raise):
            sites[id(node)] = func_name
        stack.extend((child, func_name) for child in ast.iter_child_nodes(node))
    return sites
def _reraise_contexts(tree: ast.AST) -> dict[int, ast.ExceptHandler | None]:
    contexts: dict[int, ast.ExceptHandler | None] = {}
    stack: list[tuple[ast.AST, ast.ExceptHandler | None]] = [(tree, None)]
    while stack:
        node, active_handler = stack.pop()
        if isinstance(node, ast.Raise):
            contexts[id(node)] = active_handler
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            stack.extend((child, None) for child in ast.iter_child_nodes(node))
            continue
        if isinstance(node, (ast.Try, TRY_STAR)):
            for group in (node.body, node.orelse, node.finalbody):
                stack.extend((child, active_handler) for child in group)
            for handler in node.handlers:
                stack.extend((child, handler) for child in handler.body)
            continue
        stack.extend((child, active_handler)
                     for child in ast.iter_child_nodes(node))
    return contexts
def _build_file_anchors(raises, tree) -> _FileAnchors:
    _has_protocol = any(r.exc_type in _PROTOCOL_EXC_TYPES for r in raises)
    _has_reraise = any(
        r.exc_type in {"bare re-raise", "re-raise variable"} for r in raises)
    return _FileAnchors(
        protocol_sites=_protocol_raise_sites(tree) if _has_protocol else {},
        reraise_contexts=_reraise_contexts(tree) if _has_reraise else {},
    )
def _with_bound_names(stmt) -> list[str]:
    return list(iter_unpack_target_names(
        [item.optional_vars for item in stmt.items]))
def _import_bound_names(stmt) -> list[str]:
    if isinstance(stmt, ast.Import):
        return [alias.asname or alias.name.split(".")[0] for alias in stmt.names]
    return [alias.asname or alias.name
            for alias in stmt.names if alias.name != "*"]
def _delete_bound_names(stmt) -> list[str]:
    return list(iter_unpack_target_names(stmt.targets))
def _statement_bound_names(stmt) -> list[str]:
    pair = assign_targets_value(stmt)
    if pair is not None:
        return list(iter_unpack_target_names(pair[0]))
    if isinstance(stmt, ast.ExceptHandler):
        return [stmt.name] if stmt.name else []
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return [stmt.name]
    return _rebound_names(stmt)
def _rebound_names(stmt) -> list[str]:
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return list(iter_unpack_target_names(stmt.target))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _with_bound_names(stmt)
    if isinstance(stmt, ast.AugAssign):
        return list(iter_unpack_target_names(stmt.target))
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return _import_bound_names(stmt)
    if isinstance(stmt, ast.Delete):
        return _delete_bound_names(stmt)
    if isinstance(stmt, ast.Match):
        return [name for case in stmt.cases
                for name in iter_pattern_capture_names(case.pattern)]
    return []
def _is_exc_info_exception_subscript(value) -> bool:
    if not (isinstance(value, ast.Subscript)
            and isinstance(value.value, ast.Call)):
        return False
    index = value.slice
    if not (isinstance(index, ast.Constant)
            and isinstance(index.value, int)
            and not isinstance(index.value, bool) and index.value == 1):
        return False
    func = value.value.func
    return ((isinstance(func, ast.Name) and func.id == "exc_info")
            or (isinstance(func, ast.Attribute) and func.attr == "exc_info"))
def _is_reraise_carrier(v, in_handler: bool,
                        carriers: dict[str, int]) -> bool:
    if _is_exc_info_exception_subscript(v):
        return True
    if not in_handler:
        return False
    if isinstance(v, ast.Name) and v.id in carriers:
        return True
    if isinstance(v, ast.Call):
        carrier = _exception_carrier_name(v)
        return carrier is not None and carrier in carriers
    return False
def _iter_named_expr_assignments(stmt):
    stack = [stmt]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Lambda):
            defaults = [
                *node.args.defaults,
                *(default for default in node.args.kw_defaults
                  if default is not None),
            ]
            stack.extend(reversed(defaults))
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            continue
        if isinstance(node, ast.NamedExpr):
            yield node.target, node.value
            stack.append(node.value)
            continue
        for child in reversed(list(ast.iter_child_nodes(node))):
            if isinstance(child, (ast.stmt, ast.ExceptHandler)):
                continue
            stack.append(child)
def _bind_reraise_carriers(v, targets, in_handler: bool,
                           carriers: dict[str, int], line: int,
                           history: dict | None = None) -> None:
    updates = []
    for target in targets:
        for leaf, bound_value in _iter_assignment_target_values(target, v):
            if isinstance(leaf, ast.Name):
                updates.append((
                    leaf.id,
                    _is_reraise_carrier(bound_value, in_handler, carriers)))
    for name, is_carrier in updates:
        if is_carrier:
            carriers[name] = line
        else:
            carriers.pop(name, None)
        if history is not None:
            history.setdefault(name, []).append((line, is_carrier))
def _scope_reraise_var_history(scope_node) -> dict[str, list[tuple[int, bool]]]:
    carriers: dict[str, int] = {}
    history: dict[str, list[tuple[int, bool]]] = {}
    for stmt, in_handler in iter_scope_statements(
            scope_node, include_defs=True):
        if isinstance(stmt, ast.ExceptHandler):
            if stmt.name:
                carriers[stmt.name] = stmt.lineno
                history.setdefault(stmt.name, []).append((stmt.lineno, True))
            continue
        for _target, _value in _iter_named_expr_assignments(stmt):
            _bind_reraise_carriers(
                _value, [_target], in_handler, carriers, _target.lineno,
                history)
        _pair = assign_targets_value(stmt)
        if _pair is not None:
            targets, v = _pair
            _bind_reraise_carriers(
                v, targets, in_handler, carriers, stmt.lineno, history)
            continue
        for name in _statement_bound_names(stmt):
            carriers.pop(name, None)
            history.setdefault(name, []).append((stmt.lineno, False))
    return history
class _TypeBindingState(NamedTuple):
    line: int
    types: frozenset[str]
    bind_line: int | None
    polluted: bool
@dataclass
class _TypeBindings:
    known: tuple[str, ...] = _DEFAULT_KNOWN_EXC_TYPES
    candidates: dict[str, set[str]] = field(default_factory=dict)
    bind_line: dict[str, int] = field(default_factory=dict)
    polluted: set[str] = field(default_factory=set)
    history: dict[str, list[_TypeBindingState]] = field(default_factory=dict)
    def _record(self, name: str, line: int) -> None:
        self.history.setdefault(name, []).append(_TypeBindingState(
            line=line,
            types=frozenset(self.candidates.get(name, ())),
            bind_line=self.bind_line.get(name),
            polluted=name in self.polluted,
        ))
    def reset(self, name: str, line: int) -> None:
        self.candidates.pop(name, None)
        self.bind_line.pop(name, None)
        self.polluted.discard(name)
        self._record(name, line)
    def bind(self, name: str, type_name: str, line: int) -> None:
        if name in self.polluted:
            return
        self.candidates.setdefault(name, set()).add(type_name)
        self.bind_line[name] = line
        self._record(name, line)
    def pollute(self, name: str, line: int) -> None:
        self.candidates.pop(name, None)
        self.bind_line.pop(name, None)
        self.polluted.add(name)
        self._record(name, line)
    def resolved(self) -> dict[str, tuple[str, int]]:
        return {name: (next(iter(types)), self.bind_line[name])
                for name, types in self.candidates.items()
                if len(types) == 1 and name in self.bind_line}
def _iter_params(scope_node):
    _args = getattr(scope_node, "args", None)
    if _args is None:
        return
    yield from _args.posonlyargs
    yield from _args.args
    yield from _args.kwonlyargs
    if _args.vararg is not None:
        yield _args.vararg
    if _args.kwarg is not None:
        yield _args.kwarg
def _iter_param_exception_types(scope_node, known):
    if not isinstance(scope_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return
    for _arg in _iter_params(scope_node):
        if _arg.annotation is None:
            continue
        _tail = _exc_type_tail(_arg.annotation)
        if _is_exception_type_name(_tail, known):
            yield _arg.arg, _tail
def _bind_one_assign(v, targets, line: int, bindings: _TypeBindings,
                     *, rebind: bool = False) -> None:
    updates = []
    for target in targets:
        for leaf, bound_value in _iter_assignment_target_values(target, v):
            if not isinstance(leaf, ast.Name):
                continue
            _tail = (_exc_type_tail(bound_value.func)
                     if isinstance(bound_value, ast.Call)
                     else _exc_type_tail(bound_value))
            _alias_types = (
                bindings.candidates.get(bound_value.id)
                if isinstance(bound_value, ast.Name)
                and bound_value.id not in bindings.polluted else None)
            updates.append((leaf.id, _tail, _alias_types))
    if rebind:
        for name in iter_unpack_target_names(targets):
            bindings.reset(name, line)
    for name, tail, alias_types in updates:
        _bind_exact_target(name, tail, alias_types, line, bindings)
def _bind_exact_target(name: str, tail: str | None, alias_types,
                       line: int, bindings: _TypeBindings) -> None:
    if _is_exception_type_name(tail, bindings.known):
        bindings.bind(name, tail, line)
        return
    if alias_types:
        for alias_type in alias_types:
            bindings.bind(name, alias_type, line)
        return
    bindings.pollute(name, line)
def _scope_body_stmts(scope_node) -> list:
    body = getattr(scope_node, "body", None)
    return body if isinstance(body, list) else []
def _bind_assign_chain(scope_node, bindings: _TypeBindings) -> None:
    unconditional = {id(stmt) for stmt in _scope_body_stmts(scope_node)}
    for stmt, _ih in iter_scope_statements(
            scope_node, include_defs=True):
        for _target, _value in _iter_named_expr_assignments(stmt):
            _bind_one_assign(
                _value, [_target], _target.lineno, bindings,
                rebind=id(stmt) in unconditional)
        _pair = assign_targets_value(stmt)
        if _pair is not None:
            targets, v = _pair
            _bind_one_assign(
                v, targets, stmt.lineno, bindings,
                rebind=id(stmt) in unconditional)
            continue
        for name in _statement_bound_names(stmt):
            bindings.pollute(name, stmt.lineno)
def _scope_exception_type_facts(scope_node, known) -> tuple[
        set[str], dict[str, tuple[str, int]],
        dict[str, list[_TypeBindingState]]]:
    bindings = _TypeBindings(known=known)
    param_names: set[str] = set()
    _line = getattr(scope_node, "lineno", 0) or 0
    for _name, _tail in _iter_param_exception_types(scope_node, bindings.known):
        param_names.add(_name)
        bindings.bind(_name, _tail, _line)
    _bind_assign_chain(scope_node, bindings)
    return param_names, bindings.resolved(), bindings.history
def _parameter_rebind_lines(scope_node, param_names: set[str]) -> dict[str, int]:
    lines: dict[str, int] = {}
    for stmt, _ih in iter_scope_statements(
            scope_node, include_defs=True):
        for name in _statement_bound_names(stmt):
            if name in param_names:
                lines.setdefault(name, stmt.lineno)
        for target, _value in _iter_named_expr_assignments(stmt):
            if target.id in param_names:
                lines.setdefault(target.id, target.lineno)
    return lines
class ExceptionPropagationAnalyzer:
    def __init__(self, project_root: str) -> None:
        self.project_root = os.path.abspath(project_root)
    def analyze(self, source_paths: list[str] | None = None) -> ExceptionPropagationReport:
        report = ExceptionPropagationReport(project_root=self.project_root)
        files = collect_exception_scan_files(
            [self.project_root] if source_paths is None else source_paths)
        for filepath in files:
            file_entries = self._analyze_file(filepath)
            report.entries.extend(file_entries)
        _counts = _entry_counts(report.entries)
        report.total_raises = _counts["total_raises"]
        report.total_caught = _counts["total_caught"]
        report.total_uncaught = _counts["total_uncaught"]
        report.total_swallowed = _counts["swallowed_exceptions"]
        log_swallowed_entries(report.entries)
        return report
    def _analyze_file(self, filepath: str) -> list[ExceptionPropagationEntry]:
        source, tree = _parse_py_file(filepath, quiet=True)
        if source is None or tree is None:
            return []
        return self.analyze_file_preparsed(filepath, tree)
    def analyze_file_preparsed(self, filepath: str, tree: ast.AST) -> list[ExceptionPropagationEntry]:
        rel = safe_relpath(filepath, self.project_root)
        raises = self._collect_raises(tree)
        if not raises:
            return []
        node_map, handler_map = self._build_try_maps(tree)
        anchors = _build_file_anchors(raises, tree)
        exc_bases = _class_exc_bases(tree)
        return [
            self._build_entry(rel, record, tree, node_map, handler_map,
                              anchors, exc_bases)
            for record in raises
        ]
    def _collect_raises(self, tree: ast.AST) -> list[_RaiseRecord]:
        raises: list[_RaiseRecord] = []
        known_exc_types = _raise_target_type_names(tree)
        for scope in scope_roots(tree):
            rr_history = _scope_reraise_var_history(scope)
            (param_exc_names, exc_var_types,
             exc_var_history) = _scope_exception_type_facts(
                scope, known_exc_types)
            param_rebind_lines = _parameter_rebind_lines(
                scope, param_exc_names)
            for stmt, _ih in iter_scope_statements(scope):
                if not isinstance(stmt, ast.Raise):
                    continue
                raises.append(_RaiseRecord(
                    line=stmt.lineno,
                    exc_type=self._anchor_name_raise_type(
                        stmt, rr_history, exc_var_types,
                        self._get_raise_type(stmt),
                        exc_var_history=exc_var_history),
                    node=stmt,
                    transparent=_is_param_raise(
                        stmt, param_exc_names, param_rebind_lines),
                ))
        raises.sort(key=lambda record: record.line)
        return raises
    @staticmethod
    def _anchor_name_raise_type(node: ast.Raise, rr_lines: dict,
                               exc_var_types: dict,
                               raw_type: str,
                               exc_var_history: dict | None = None) -> str:
        name = _exception_carrier_name(node.exc)
        binding_name = name
        if binding_name is None:
            exc = _unwrap_with_traceback(node.exc)
            if isinstance(exc, ast.Call):
                binding_name = _exc_type_tail(exc.func)
        if binding_name is None:
            return raw_type
        _candidates: list[tuple[int, int, str]] = []
        if exc_var_history is not None:
            for state in reversed(exc_var_history.get(binding_name, ())):
                if state.line > node.lineno:
                    continue
                if (not state.polluted and len(state.types) == 1
                        and state.bind_line is not None):
                    _candidates.append((
                        state.bind_line, 0, next(iter(state.types))))
                break
        else:
            _type_binding = exc_var_types.get(binding_name)
            if (_type_binding is not None
                    and _type_binding[1] <= node.lineno):
                _candidates.append((_type_binding[1], 0, _type_binding[0]))
        _carrier_line = None
        _carrier_states = rr_lines.get(name) if name is not None else None
        if isinstance(_carrier_states, int):
            if _carrier_states <= node.lineno:
                _carrier_line = _carrier_states
        else:
            for state_line, is_carrier in reversed(_carrier_states or ()):
                if state_line > node.lineno:
                    continue
                if is_carrier:
                    _carrier_line = state_line
                break
        if _carrier_line is not None:
            _candidates.append((_carrier_line, 1, "re-raise variable"))
        if not _candidates:
            return raw_type
        return max(_candidates)[2]
    def _build_entry(self, rel: str, record: _RaiseRecord, tree: ast.AST,
                     node_map: dict, handler_map: dict,
                     anchors: _FileAnchors,
                     exc_bases: dict) -> ExceptionPropagationEntry:
        _match_type = record.exc_type
        _reraise_types = None
        if record.exc_type in {"bare re-raise", "re-raise variable"}:
            _active_types, _source = anchors.reraise_context(record.node)
            if _source:
                _reraise_types = _active_types
            elif record.exc_type == "bare re-raise":
                _match_type = "RuntimeError"
        matched = self._resolve_catching_handler(
            record.node, tree, raise_type=_match_type,
            node_map=node_map, handler_map=handler_map, exc_bases=exc_bases,
            reraise_types=_reraise_types)
        if matched:
            return self._matched_entry(rel, record, matched)
        return self._uncaught_entry(rel, record, anchors)
    @staticmethod
    def _matched_entry(rel: str, record: _RaiseRecord,
                       matched: dict) -> ExceptionPropagationEntry:
        _swallowed = matched["is_swallow"]
        return ExceptionPropagationEntry(
            filepath=rel, raise_line=record.line, raise_type=record.exc_type,
            except_line=matched["line"], except_type=matched["exc_name"],
            is_swallowed=_swallowed,
            swallow_kind=matched.get("swallow_kind", ""),
            raise_in_try_body=matched.get("raise_in_try_body", False),
            raise_transparent=record.transparent,
            severity="high" if _swallowed else "low",
            message=f"{record.exc_type} at line {record.line} caught at line {matched['line']}"
                     + (" and SWALLOWED" if _swallowed else ""),
            suggestion="避免吞没异常：至少记录日志或重新抛出" if _swallowed else "",
        )
    def _uncaught_entry(self, rel: str, record: _RaiseRecord,
                        anchors: _FileAnchors) -> ExceptionPropagationEntry:
        _raise_msg = _raise_message_text(record.node)
        _transparent = record.transparent or anchors.is_protocol_raise(
            record.exc_type, record.node)
        return ExceptionPropagationEntry(
            filepath=rel, raise_line=record.line, raise_type=record.exc_type,
            raise_msg=_raise_msg,
            raise_transparent=_transparent,
            except_type=(
                anchors.reraise_context(record.node)[1]
                if record.exc_type in {"bare re-raise", "re-raise variable"}
                else ""),
            severity="medium",
            message=(f"{record.exc_type} at line {record.line}: {_raise_msg}"
                     if _raise_msg else
                     f"{record.exc_type} at line {record.line} may propagate uncaught"),
            suggestion="确保调用方有适当的异常处理",
        )
    def _get_raise_type(self, node: ast.Raise) -> str:
        if node.exc is None:
            return "bare re-raise"
        exc = _unwrap_with_traceback(node.exc)
        if isinstance(exc, ast.Name):
            return exc.id
        if isinstance(exc, ast.Subscript):
            return ("re-raise variable"
                    if _is_exc_info_exception_subscript(exc) else "unknown")
        if isinstance(exc, ast.Attribute):
            return exc.attr
        if isinstance(exc, ast.Call) and isinstance(exc.func, ast.Name):
            return exc.func.id
        if isinstance(exc, ast.Call) and isinstance(exc.func, ast.Attribute):
            return exc.func.attr
        return "unknown"
    def _handler_info(self, handler: ast.ExceptHandler) -> dict:
        return {
            "line": handler.lineno,
            "exc_name": handler_exc_name(handler, "bare except"),
            "exc_names": handler_exc_names(handler),
            "bare": handler.type is None,
            "is_swallow": self._is_swallow_handler(handler),
            "swallow_kind": self._swallow_kind(handler),
        }
    def _swallow_kind(self, handler: ast.ExceptHandler) -> str:
        if not self._is_swallow_handler(handler):
            return ""
        for stmt in handler.body:
            if isinstance(stmt, (ast.Continue, ast.Break, ast.Return)):
                return "control_flow"
        return "pass"
    def _is_swallow_handler(self, handler: ast.ExceptHandler) -> bool:
        if not handler.body:
            return True
        has_reraise = False
        for stmt in handler.body:
            _cls = self._classify_swallow_stmt(stmt)
            if _cls == "real":
                return False
            if _cls == "reraise":
                has_reraise = True
        return not has_reraise
    @staticmethod
    def _classify_swallow_stmt(stmt) -> str:
        if isinstance(stmt, (ast.Pass, ast.Continue, ast.Break)):
            return "neutral"
        if isinstance(stmt, ast.Raise):
            return "reraise"
        if isinstance(stmt, ast.Return):
            return "neutral" if _is_neutral_return(stmt.value) else "real"
        if isinstance(stmt, ast.Expr):
            return _classify_expr_stmt(stmt.value)
        return "real"
    def _resolve_catching_handler(self, node: ast.AST, tree: ast.AST,
                                   raise_type: str | None = None,
                                   node_map: dict | None = None,
                                   handler_map: dict | None = None, *,
                                   exc_bases: dict,
                                   reraise_types: frozenset | None = None,
                                   ) -> dict | None:
        if node_map is None or handler_map is None:
            node_map, handler_map = self._build_try_maps(tree)
        _raise_type = raise_type if raise_type is not None else self._get_raise_type(node)
        _raise_own_in_body = bool(node_map.get(id(node), (None, False))[1])
        cur = node
        while True:
            parent_try, in_body = node_map.get(id(cur), (None, False))
            if parent_try is None:
                return None
            if in_body:
                matched = self._match_handler(
                    handler_map.get(id(parent_try)), _raise_type, exc_bases,
                    reraise_types=reraise_types)
                if matched is not None:
                    matched["raise_in_try_body"] = _raise_own_in_body
                    return matched
            cur = parent_try
    def _match_handler(self, handlers, raise_type: str,
                       exc_bases: dict, *,
                       reraise_types: frozenset | None = None) -> dict | None:
        for handler in handlers or ():
            caught = (self._handler_catches(handler, raise_type, exc_bases)
                      if reraise_types is None else
                      self._handler_catches_reraise(
                          handler, reraise_types, exc_bases))
            if caught:
                return dict(handler)
        return None
    def _push_try_scope(self, stack: list, try_node) -> None:
        for child in try_node.finalbody:
            stack.append((child, try_node, False))
        for child in try_node.orelse:
            stack.append((child, try_node, False))
        for child in try_node.handlers:
            stack.append((child, try_node, False))
        for child in try_node.body:
            stack.append((child, try_node, True))
    def _build_try_maps(self, tree: ast.AST) -> tuple[dict, dict]:
        node_map = {}
        handler_map = {}
        stack = [(tree, None, False)]
        while stack:
            t, parent_try, in_body = stack.pop()
            node_map[id(t)] = (parent_try, in_body)
            if isinstance(t, (ast.Try, TRY_STAR)):
                handler_map[id(t)] = [self._handler_info(h) for h in t.handlers]
                self._push_try_scope(stack, t)
            elif isinstance(t, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
                for child in ast.iter_child_nodes(t):
                    stack.append((child, None, False))
            else:
                for child in ast.iter_child_nodes(t):
                    stack.append((child, parent_try, in_body))
        return node_map, handler_map
    def _handler_catches(self, handler_info: dict, raise_type: str,
                         exc_bases: dict) -> bool:
        names = handler_info.get("exc_names") or set()
        if _is_broad_catch(names, handler_info.get("bare", False)):
            return True
        if _is_unknown_raise_type(raise_type):
            return False
        handler_types = {_canonical_exc_name(n) for n in names}
        return _lineage_catches(
            exception_type_lineage(raise_type, exc_bases), handler_types)
    def _handler_catches_reraise(self, handler_info: dict,
                                 active_types: frozenset,
                                 exc_bases: dict) -> bool:
        names = handler_info.get("exc_names") or set()
        if _is_broad_catch(names, handler_info.get("bare", False)):
            return True
        if not active_types:
            return False
        handler_types = {_canonical_exc_name(n) for n in names}
        return all(
            _lineage_catches(
                exception_type_lineage(active_type, exc_bases), handler_types)
            for active_type in active_types)
def log_swallowed_entries(entries) -> None:
    _warned = False
    for entry in entries:
        if not entry.is_swallowed:
            continue
        _exc_name = entry.except_type or "Exception"
        try:
            log_swallowed(
                __name__,
                RuntimeError(
                    f"{_exc_name} at {entry.filepath}:{entry.except_line}"),
                context=f"swallowed_except:{_exc_name}",
            )
        except Exception:
            if not _warned:
                logger.warning("log_swallowed integration failed",
                               exc_info=True)
                _warned = True
def _exc_scan_skip_dirs(root: str) -> frozenset:
    return (frozenset(scan_exclude_dirs(root or None))
            - TEST_DIR_CANDIDATES_LOWER)
def _iter_dir_py_files(directory: str):
    skip = _exc_scan_skip_dirs(directory)
    for root, dirs, fnames in os.walk(directory):
        dirs[:] = sorted(d for d in dirs
                         if not is_pruned_scan_dir(d, skip))
        for fn in sorted(fnames):
            if is_scan_py_name(fn):
                yield os.path.join(root, fn)
def _expand_single_source(p, add) -> None:
    p = os.fsdecode(os.fspath(p))
    if os.path.isfile(p):
        if is_scan_py_name(p):
            add(p)
        else:
            logger.debug("%s: 跳过非 Python 源文件: %s", _LOG_TAG, p)
        return
    if os.path.isdir(p):
        for filepath in _iter_dir_py_files(p):
            add(filepath)
        return
    logger.warning("%s: 异常扫描入口不存在或既非文件也非目录: %r",
                   _LOG_TAG, p)
def collect_exception_scan_files(source_paths=None) -> list:
    if source_paths is None:
        logger.debug("%s: 未提供异常扫描路径, 返回空清单", _LOG_TAG)
        return []
    if isinstance(source_paths, (str, bytes, os.PathLike)):
        source_paths = [source_paths]
    files: list[str] = []
    seen: set[str] = set()
    def _add(fp: str) -> None:
        key = os.path.normcase(os.path.normpath(os.path.abspath(fp)))
        if key not in seen:
            seen.add(key)
            files.append(fp)
    for p in source_paths:
        _expand_single_source(p, _add)
    return files
def _def_annotation_site_ids(node) -> frozenset[int]:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return frozenset()
    annotations = [arg.annotation for arg in _iter_params(node)]
    annotations.append(node.returns)
    return frozenset(id(annotation) for annotation in annotations
                     if annotation is not None)
class _ExceptionScopeVisitor(ast.NodeVisitor):
    # 行内抑制表（``# noqa: TRY004`` → {行号: {类别}}）。默认空表，
    # 由 _run_exception_detector 在读源码时填充。
    suppressions: dict = {}
    _in_except = False
    _except_var_name = None
    _handler_reraises = False
    _handler_traceback_covered_calls: frozenset[int] = frozenset()
    _annotations_postponed = False
    def visit_Module(self, node: ast.Module) -> None:
        was_postponed = self._annotations_postponed
        self._annotations_postponed = module_postpones_annotations(node)
        self.generic_visit(node)
        self._annotations_postponed = was_postponed
    def _visit_deferred_scope(self, node) -> None:
        was_in_except = self._in_except
        was_var = self._except_var_name
        postponed_sites = (_def_annotation_site_ids(node)
                           if self._annotations_postponed else frozenset())
        for _site in iter_def_site_nodes(node):
            if id(_site) not in postponed_sites:
                self.visit(_site)
        self._in_except = False
        self._except_var_name = None
        body = getattr(node, 'body', None)
        if isinstance(body, list):
            _visit_groups(self, body)
        elif body is not None:
            self.visit(body)
        self._in_except = was_in_except
        self._except_var_name = was_var
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_deferred_scope(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    visit_Lambda = visit_FunctionDef
    def visit_Try(self, node) -> None:
        self._visit_try_children(node)
    def visit_TryStar(self, node) -> None:
        self.visit_Try(node)
    def _visit_try_children(self, node) -> None:
        was_in_except = self._in_except
        was_var = self._except_var_name
        for handler in node.handlers:
            self._visit_handler(node, handler)
        self._in_except = was_in_except
        self._except_var_name = was_var
        _visit_groups(self, node.body, node.orelse, node.finalbody)
        self._in_except = was_in_except
        self._except_var_name = was_var
    def _visit_handler(self, node, handler) -> None:
        was_in_except = self._in_except
        was_var = self._except_var_name
        was_reraises = self._handler_reraises
        was_covered_calls = self._handler_traceback_covered_calls
        self._in_except = True
        self._except_var_name = handler.name or None
        self._handler_reraises = _handler_guarantees_reraise(handler)
        self._handler_traceback_covered_calls = _handler_traceback_coverage(
            handler)
        _visit_groups(self, handler.body)
        self._in_except = was_in_except
        self._except_var_name = was_var
        self._handler_reraises = was_reraises
        self._handler_traceback_covered_calls = was_covered_calls
class _TryceratopsVisitor(_ExceptionScopeVisitor):
    def __init__(self):
        self.findings = []
        self._in_except = False
        self._except_var_name = None
        self._func_stack: list[str] = []
        self.protocol_exempt = 0
        self.selective_reraise_exempt = 0
        self._exc_bases: dict = {}
        self._rebound_try201_raises: frozenset[int] = frozenset()
    def visit_Module(self, node: ast.Module) -> None:
        self._exc_bases = _class_exc_bases(node)
        self._rebound_try201_raises = _rebound_try201_raise_ids(node)
        super().visit_Module(node)
    def _visit_deferred_scope(self, node) -> None:
        _name = getattr(node, "name", None)
        if _name is None:
            super()._visit_deferred_scope(node)
            return
        self._func_stack.append(_name)
        try:
            super()._visit_deferred_scope(node)
        finally:
            self._func_stack.pop()
    def _report_try002_try003_call(self, node: ast.Raise) -> None:
        exc = _unwrap_with_traceback(node.exc)
        if not isinstance(exc, ast.Call):
            return
        exc_name = _raise_target_name(node)
        if exc_name in ('Exception', 'BaseException'):
            self.findings.append(_finding(
                node.lineno,
                'try002_raise_vanilla_class',
                'high',
                exc_name,
                f'Direct raise {exc_name}(): too generic (tryceratops TRY002)',
            ))
        if exc.args:
            for arg in exc.args:
                msg_len = _try003_msg_len(arg)
                if msg_len > 50:
                    self.findings.append(_finding(
                        node.lineno,
                        'try003_raise_vanilla_args',
                        'medium',
                        exc_name or 'unknown',
                        f'Long message ({msg_len} chars) outside exception class (tryceratops TRY003)',
                    ))
                    break
    def _report_try002_bare_name(self, node: ast.Raise) -> None:
        if (isinstance(node.exc, ast.Name)
                and node.exc.id in ('Exception', 'BaseException')):
            self.findings.append(_finding(
                node.lineno,
                'try002_raise_vanilla_class',
                'high',
                node.exc.id,
                f'Direct raise {node.exc.id}: too generic (tryceratops TRY002)',
            ))
    def _report_try201(self, node: ast.Raise) -> None:
        if node.exc is None or not self._except_var_name:
            return
        raised_name = _try201_raised_name(node.exc)
        if (raised_name and raised_name == self._except_var_name
                and id(node) not in self._rebound_try201_raises):
            self.findings.append(_finding(
                node.lineno,
                'try201_verbose_raise',
                'medium',
                raised_name,
                f'Verbose raise: use bare "raise" instead of "raise {raised_name}" (tryceratops TRY201)',
            ))
    def visit_Raise(self, node: ast.Raise) -> None:
        self._report_try002_try003_call(node)
        self._report_try002_bare_name(node)
        self._report_try201(node)
        self.generic_visit(node)
    def _report_try301(self, node: ast.Try) -> None:
        if any(_handler_is_substantive(h) for h in node.handlers):
            return
        for stmt, guarded in _iter_try_body_raises(node):
            if guarded or not _raise_caught_by_try(
                    node, stmt, self._exc_bases):
                continue
            self.findings.append(_finding(
                stmt.lineno,
                'try301_raise_within_try',
                'medium',
                'raise in try',
                'Raise within try: consider abstracting to inner function (tryceratops TRY301)',
            ))
    def _report_try300(self, node: ast.Try) -> None:
        # 与 Ruff TRY300 对齐：只对「try 体不止一条语句」报。单语句 try 体
        # （``try: return f()``）移到 else 是纯仪式——异常分支本来就会接管，
        # 加 else 只多一层缩进，反而降低可读性。
        if len(node.body) == 1:
            return
        for stmt in _iter_try_body_returns(node):
            self.findings.append(_finding(
                stmt.lineno,
                'try300_try_consider_else',
                'low',
                'return in try',
                'Return in try: consider moving to else block (tryceratops TRY300)',
            ))
    def _report_try203(self, node: ast.Try) -> None:
        _bare_reraise = sum(
            1 for handler in node.handlers
            if (handler.body and len(handler.body) == 1
                and isinstance(handler.body[0], ast.Raise)
                and handler.body[0].exc is None)
        )
        if node.handlers and _bare_reraise == len(node.handlers):
            self.findings.append(_finding(
                node.handlers[0].lineno,
                'try203_useless_try_except',
                'high',
                'bare raise',
                'Useless try-except: immediately re-raises (tryceratops TRY203)',
            ))
        elif _bare_reraise:
            self.selective_reraise_exempt += _bare_reraise
    def visit_Try(self, node: ast.Try) -> None:
        self._report_try301(node)
        self._report_try300(node)
        self._report_try203(node)
        super().visit_Try(node)
    def _report_try400(self, node: ast.Call) -> None:
        if not _is_logging_call(node, 'error'):
            return
        if (_logging_call_carries_traceback(node) or self._handler_reraises
                or id(node) in self._handler_traceback_covered_calls):
            return
        self.findings.append(_finding(
            node.lineno,
            'try400_error_instead_of_exception',
            'high',
            'logging.error',
            'Use logging.exception not logging.error in except block (tryceratops TRY400)',
        ))
    def _report_try401(self, node: ast.Call) -> None:
        if (_is_logging_call(node, 'exception')
                and self._except_var_name and node.args
                and _try401_arg_hit(node.args, self._except_var_name)):
            self.findings.append(_finding(
                node.lineno,
                'try401_verbose_log_message',
                'low',
                'logging.exception',
                'Redundant exception object in logging.exception (tryceratops TRY401)',
            ))
    def visit_Call(self, node: ast.Call) -> None:
        if self._in_except:
            self._report_try400(node)
            self._report_try401(node)
        self.generic_visit(node)
    def _report_try004(self, stmt) -> None:
        # 行内 ``# noqa: TRY004`` 是作者对「此处 ValueError 属契约」的显式声明：
        # 校验外部数据（JSON/文件内容）时抛 ValueError 才符合 Python 惯例，
        # 只有「函数参数类型错了」才该是 TypeError。
        if is_suppressed(self.suppressions, stmt.lineno, 'TRY004'):
            return
        raised_name = _raise_target_name(stmt)
        if not raised_name or raised_name in ('TypeError', 'type'):
            return
        if is_protocol_exc_site(
                self._func_stack[-1] if self._func_stack else "", raised_name):
            self.protocol_exempt += 1
            return
        self.findings.append(_finding(
            stmt.lineno,
            'try004_type_check_without_type_error',
            'medium',
            raised_name,
            f'Type check raises {raised_name} instead of TypeError (tryceratops TRY004)',
        ))
    def visit_If(self, node: ast.If) -> None:
        if _is_type_check_test(node.test):
            for stmt in list(node.body) + list(node.orelse or []):
                if isinstance(stmt, ast.Raise):
                    self._report_try004(stmt)
        self.generic_visit(node)
def _attr_owner_name(receiver) -> str:
    if isinstance(receiver, ast.Name):
        return receiver.id
    if isinstance(receiver, ast.Attribute):
        return receiver.attr
    return ""
def _is_logger_like_receiver(receiver) -> bool:
    if (isinstance(receiver, ast.Call)
            and isinstance(receiver.func, ast.Attribute)
            and receiver.func.attr == 'getLogger'):
        return _is_logger_like_receiver(receiver.func.value)
    name = _attr_owner_name(receiver)
    if not name:
        return False
    core = name.strip('_').lower()
    return (core in ('logging', 'logger', 'log')
            or core.endswith(('logger', '_log')))
def _is_logging_call(node: ast.Call, attr: str) -> bool:
    return (isinstance(node.func, ast.Attribute)
            and node.func.attr == attr
            and _is_logger_like_receiver(node.func.value))
_DEFERRED_SCOPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                    ast.ClassDef)
def _is_traceback_log_call(node) -> bool:
    if not isinstance(node, ast.Call):
        return False
    return (
        _is_logging_call(node, 'exception')
        or (_is_logging_call(node, 'error')
            and _logging_call_carries_traceback(node))
        or (isinstance(node.func, ast.Name)
            and node.func.id == 'log_swallowed'))
def _handler_traceback_coverage(handler: ast.ExceptHandler) -> frozenset[int]:
    covered: set[int] = set()
    def visit_expression(node, logged: bool) -> None:
        if node is None or isinstance(node, _DEFERRED_SCOPES):
            return
        if logged and isinstance(node, ast.Call):
            covered.add(id(node))
        for child in ast.iter_child_nodes(node):
            if not isinstance(child, ast.stmt):
                visit_expression(child, logged)
    def visit_block(statements, logged: bool) -> bool:
        for statement in statements or ():
            logged = visit_statement(statement, logged)
        return logged
    def visit_statement(stmt, logged: bool) -> bool:
        if isinstance(stmt, _DEFERRED_SCOPES):
            return logged
        if isinstance(stmt, ast.If):
            visit_expression(stmt.test, logged)
            body_logged = visit_block(stmt.body, logged)
            else_logged = visit_block(stmt.orelse, logged)
            return body_logged and else_logged
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            for child in ast.iter_child_nodes(stmt):
                if isinstance(child, ast.expr):
                    visit_expression(child, logged)
            visit_block(stmt.body, logged)
            visit_block(stmt.orelse, logged)
            return logged
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            for item in stmt.items:
                visit_expression(item.context_expr, logged)
            visit_block(stmt.body, logged)
            return logged
        if isinstance(stmt, (ast.Try, TRY_STAR)):
            normal_logged = visit_block(stmt.body, logged)
            normal_logged = visit_block(stmt.orelse, normal_logged)
            outcomes = [normal_logged]
            outcomes.extend(visit_block(nested.body, logged)
                            for nested in stmt.handlers)
            final_logged = visit_block(stmt.finalbody, logged)
            return all(outcomes) or final_logged
        if isinstance(stmt, ast.Match):
            visit_expression(stmt.subject, logged)
            outcomes = []
            exhaustive = False
            for case in stmt.cases:
                visit_expression(case.guard, logged)
                outcomes.append(visit_block(case.body, logged))
                if case.guard is None and is_irrefutable_pattern(case.pattern):
                    exhaustive = True
            if not exhaustive:
                outcomes.append(logged)
            return all(outcomes) if outcomes else logged
        for child in ast.iter_child_nodes(stmt):
            if isinstance(child, ast.expr):
                visit_expression(child, logged)
        if isinstance(stmt, ast.Expr) and _is_traceback_log_call(stmt.value):
            return True
        return logged
    visit_block(handler.body, False)
    return frozenset(covered)
def _logging_call_carries_traceback(node: ast.Call) -> bool:
    for keyword in node.keywords:
        if keyword.arg != "exc_info":
            continue
        value = keyword.value
        return bool(value.value) if isinstance(value, ast.Constant) else True
    return False
def _literal_nonempty_iter(node) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return bool(node.elts) and all(
            not isinstance(element, ast.Starred) for element in node.elts)
    if isinstance(node, ast.Dict):
        return bool(node.keys) and all(key is not None for key in node.keys)
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))
def _loop_statement_outcomes(stmt, body: set[str], loop_depth: int,
                             *, may_skip: bool, can_exhaust: bool) -> set[str]:
    current = body - {'continue', 'break', 'loop_continue'}
    if 'break' in body:
        current.add('continue')
    iteration_completes = bool(body & {'continue', 'loop_continue'})
    exhausts = can_exhaust and (may_skip or iteration_completes)
    if exhausts:
        current |= (_statement_outcomes(stmt.orelse, loop_depth)
                    if stmt.orelse else {'continue'})
    return current
def _match_statement_outcomes(stmt: ast.Match, loop_depth: int) -> set[str]:
    outcomes: set[str] = set()
    exhaustive = False
    for case in stmt.cases:
        outcomes |= _statement_outcomes(case.body, loop_depth)
        if case.guard is None and is_irrefutable_pattern(case.pattern):
            exhaustive = True
    if not exhaustive:
        outcomes.add('continue')
    return outcomes
def _statement_outcomes(statements, loop_depth: int = 0) -> set[str]:
    outcomes = {'continue'}
    for stmt in statements:
        if 'continue' not in outcomes:
            break
        terminal = outcomes - {'continue'}
        if isinstance(stmt, ast.Raise):
            current = {'reraise'}
        elif isinstance(stmt, ast.Return):
            current = {'exit'}
        elif isinstance(stmt, ast.Break):
            current = {'break' if loop_depth else 'exit'}
        elif isinstance(stmt, ast.Continue):
            current = {'loop_continue' if loop_depth else 'exit'}
        elif isinstance(stmt, ast.If):
            alternate = (_statement_outcomes(stmt.orelse, loop_depth)
                         if stmt.orelse else {'continue'})
            current = (_statement_outcomes(stmt.body, loop_depth)
                       | alternate)
        elif isinstance(stmt, (ast.With, ast.AsyncWith)):
            current = _statement_outcomes(stmt.body, loop_depth)
        elif isinstance(stmt, (ast.For, ast.AsyncFor)):
            body = _statement_outcomes(stmt.body, loop_depth + 1)
            nonempty = _literal_nonempty_iter(stmt.iter)
            current = _loop_statement_outcomes(
                stmt, body, loop_depth,
                may_skip=not nonempty, can_exhaust=True)
        elif isinstance(stmt, ast.While):
            body = _statement_outcomes(stmt.body, loop_depth + 1)
            constant_true = (isinstance(stmt.test, ast.Constant)
                             and bool(stmt.test.value))
            current = _loop_statement_outcomes(
                stmt, body, loop_depth,
                may_skip=not constant_true, can_exhaust=not constant_true)
        elif isinstance(stmt, ast.Match):
            current = _match_statement_outcomes(stmt, loop_depth)
        elif isinstance(stmt, (ast.Try, TRY_STAR)):
            body = _statement_outcomes(stmt.body, loop_depth)
            current = body - {'continue'}
            if 'continue' in body:
                current |= (_statement_outcomes(stmt.orelse, loop_depth)
                            if stmt.orelse else {'continue'})
            for handler in stmt.handlers:
                current |= _statement_outcomes(handler.body, loop_depth)
            final = _statement_outcomes(stmt.finalbody, loop_depth)
            if 'continue' not in final:
                current = final
            else:
                current |= final - {'continue'}
        else:
            current = {'continue'}
        outcomes = terminal | current
    return outcomes
def _handler_guarantees_reraise(handler: ast.ExceptHandler) -> bool:
    return _statement_outcomes(handler.body) == {'reraise'}
def _try003_msg_len(arg) -> int:
    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        return len(arg.value)
    if isinstance(arg, ast.JoinedStr):
        return sum(
            len(v.value) if isinstance(v, ast.Constant) and isinstance(v.value, str) else 10
            for v in arg.values
        )
    return 0
def _try201_raised_name(exc) -> str | None:
    return exc.id if isinstance(exc, ast.Name) else None
def _rebound_try201_raise_ids(tree: ast.AST) -> frozenset[int]:
    rebound_raises: set[int] = set()
    for handler in walk_nodes(tree):
        if not isinstance(handler, ast.ExceptHandler) or not handler.name:
            continue
        rebound = False
        for stmt in _iter_handler_scope_stmts(handler.body):
            if (rebound and isinstance(stmt, ast.Raise)
                    and isinstance(stmt.exc, ast.Name)
                    and stmt.exc.id == handler.name):
                rebound_raises.add(id(stmt))
            rebound_names = _statement_bound_names(stmt)
            rebound_names.extend(
                target.id for target, _value
                in _iter_named_expr_assignments(stmt))
            if handler.name in rebound_names:
                rebound = True
    return frozenset(rebound_raises)
def _try401_arg_hit(args, var: str) -> bool:
    return any(
        (isinstance(arg, ast.Name) and arg.id == var)
        or (isinstance(arg, ast.JoinedStr) and any(
            isinstance(v, ast.FormattedValue)
            and isinstance(v.value, ast.Name)
            and v.value.id == var
            for v in arg.values))
        for arg in args)
def _raise_target_name(stmt: ast.Raise) -> str | None:
    if not stmt.exc:
        return None
    exc = _unwrap_with_traceback(stmt.exc)
    if isinstance(exc, ast.Call):
        if isinstance(exc.func, ast.Name):
            return exc.func.id
        if isinstance(exc.func, ast.Attribute):
            return exc.func.attr
        return None
    if isinstance(exc, ast.Name):
        return exc.id
    if isinstance(exc, ast.Attribute):
        return exc.attr
    return None
_HANDLER_TRIVIAL_STMTS = (ast.Pass, ast.Raise, ast.Continue, ast.Break)
def _handler_is_substantive(handler: ast.ExceptHandler) -> bool:
    for stmt in handler.body:
        if isinstance(stmt, _HANDLER_TRIVIAL_STMTS):
            continue
        if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Attribute)
                and stmt.value.func.attr in _HANDLER_LOG_METHODS):
            continue
        return True
    return False
def _raise_caught_by_try(node: ast.Try, stmt: ast.Raise,
                          exc_bases: dict) -> bool:
    if not node.handlers:
        return False
    raise_type = _raise_target_name(stmt)
    if not raise_type or _is_unknown_raise_type(raise_type):
        return False
    lineage = exception_type_lineage(raise_type, exc_bases)
    for handler in node.handlers:
        names = handler_exc_names(handler)
        if _is_broad_catch(names, handler.type is None):
            return True
        if _lineage_catches(
                lineage, {_canonical_exc_name(n) for n in names}):
            return True
    return False
_GUARD_BRANCH_TYPES = (ast.If, ast.IfExp)
def _iter_try_body_raises(node: ast.Try):
    stack = [(child, False) for child in reversed(node.body)]
    while stack:
        cur, guarded = stack.pop()
        if isinstance(cur, ast.Raise):
            yield cur, guarded
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef, ast.Try, TRY_STAR)):
            continue
        if isinstance(cur, _GUARD_BRANCH_TYPES):
            guarded = True
        for child in reversed(list(ast.iter_child_nodes(cur))):
            stack.append((child, guarded))
def _iter_try_body_returns(node: ast.Try):
    stack = list(reversed(node.body))
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Return):
            yield cur
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef, ast.Try, TRY_STAR)):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
def _is_type_check_test(test) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        test = test.operand
    return (isinstance(test, ast.Call)
            and isinstance(test.func, ast.Name)
            and test.func.id == 'isinstance' and len(test.args) == 2)
def _carries_caught_object(value, carriers: set) -> bool:
    if isinstance(value, ast.Name):
        return value.id in carriers
    if (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Attribute)
            and value.func.attr == 'with_traceback'
            and isinstance(value.func.value, ast.Name)):
        return value.func.value.id in carriers
    return False
def _update_caught_aliases(reraise_names: set, targets, value) -> None:
    updates = []
    for target in targets:
        for leaf, bound in _iter_assignment_target_values(target, value):
            if isinstance(leaf, ast.Name):
                updates.append((
                    leaf.id, _carries_caught_object(bound, reraise_names)))
    for name, carried in updates:
        if carried:
            reraise_names.add(name)
        else:
            reraise_names.discard(name)
def _resolve_traceback_carrier(carrier):
    if isinstance(carrier, ast.Name):
        return None, carrier.id
    if isinstance(carrier, ast.Call):
        inner = carrier.func
        if isinstance(inner, ast.Name):
            return inner.id, None
        if isinstance(inner, ast.Attribute):
            return inner.attr, None
    return None, None
_HANDLER_SCOPE_SKIP = (ast.FunctionDef, ast.AsyncFunctionDef,
                       ast.Lambda, ast.ClassDef)
def _iter_handler_scope_stmts(stmts):
    for stmt in stmts:
        yield stmt
        if isinstance(stmt, _HANDLER_SCOPE_SKIP):
            continue
        if isinstance(stmt, (ast.Try, TRY_STAR)):
            yield from _iter_handler_scope_stmts(stmt.body)
            yield from stmt.handlers
            yield from _iter_handler_scope_stmts(stmt.orelse)
            yield from _iter_handler_scope_stmts(stmt.finalbody)
            continue
        for field_name in ("body", "orelse", "finalbody"):
            group = getattr(stmt, field_name, None)
            if isinstance(group, list):
                yield from _iter_handler_scope_stmts(group)
        for case in getattr(stmt, "cases", None) or ():
            body = getattr(case, "body", None)
            if isinstance(body, list):
                yield from _iter_handler_scope_stmts(body)
def _is_empty_handler_stmt(stmt) -> bool:
    if isinstance(stmt, ast.Pass):
        return True
    return isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
class _ExceptionMinerVisitor(_ExceptionScopeVisitor):
    def __init__(self):
        self.findings = []
        self._in_except = False
    def _report_em003(self, handler) -> None:
        if not handler.body:
            return
        if any(not _is_empty_handler_stmt(stmt) for stmt in handler.body):
            return
        self.findings.append(_finding(
            handler.lineno,
            'em003_empty_catch_with_comment',
            'high',
            handler_exc_name(handler, "bare"),
            'Empty except handler with only comment: exception silently swallowed (Exception Miner EM003)',
        ))
    def _report_em002(self, handler) -> None:
        caught_type = handler_exc_name(handler, "bare") or 'unknown'
        caught_names = handler_exc_names(handler)
        reraise_names: set[str] = {handler.name} if handler.name else set()
        for stmt in _iter_handler_scope_stmts(handler.body):
            if isinstance(stmt, ast.Raise) and stmt.exc is not None:
                raised_type = self._unchecked_cross_reraise_type(
                    stmt, reraise_names, caught_names)
                if raised_type is not None and stmt.cause is None:
                    self.findings.append(_finding(
                        stmt.lineno,
                        'em002_catch_throw_different',
                        'medium',
                        f'{caught_type} -> {raised_type}',
                        f'Catch {caught_type} then throw {raised_type} without "from": original context lost (Exception Miner EM002)',
                    ))
            for _target, _value in _iter_named_expr_assignments(stmt):
                _update_caught_aliases(
                    reraise_names, [_target], _value)
            _pair = assign_targets_value(stmt)
            if _pair is None:
                for _name in _statement_bound_names(stmt):
                    reraise_names.discard(_name)
                continue
            _targets, _v = _pair
            _update_caught_aliases(reraise_names, _targets, _v)
    def _report_em004(self, node: ast.Try, handler) -> None:
        if len(node.handlers) != 1 or node.orelse:
            return
        em004_names = self._em004_control_flow_names(handler)
        if not em004_names:
            return
        # handler 所有路径都以 raise 收束（如 err = str(exc); raise ... from exc）
        # 时异常并未被当作分支，而是被包装后继续传播：这不是控制流用法。
        # 漏掉这一判定会把「赋值 + 重抛」的包装型 handler 误报成 EM004。
        if _handler_guarantees_reraise(handler):
            return
        for stmt in handler.body:
            if isinstance(stmt, (ast.Assign, ast.AugAssign, ast.Return, ast.Continue, ast.Break)):
                self.findings.append(_finding(
                    node.lineno,
                    'em004_exception_control_flow',
                    'low',
                    '/'.join(em004_names),
                    f'Using try-except for {" or ".join(em004_names)} '
                    'as control flow: consider explicit check '
                    '(Exception Miner EM004)',
                ))
                break
    def _visit_handler(self, node, handler) -> None:
        self._report_em003(handler)
        self._report_em002(handler)
        self._report_em004(node, handler)
        super()._visit_handler(node, handler)
    def visit_Try(self, node: ast.Try) -> None:
        if self._in_except:
            self.findings.append(_finding(
                node.lineno,
                'em001_nested_try_in_except',
                'medium',
                'nested try',
                'Nested try-except inside except handler: overly complex error handling (Exception Miner EM001)',
            ))
        super().visit_Try(node)
    @staticmethod
    def _split_raise_target(exc):
        if isinstance(exc, ast.Name):
            return exc.id, exc.id
        if not isinstance(exc, ast.Call):
            return None, None
        func = exc.func
        if isinstance(func, ast.Name):
            return func.id, None
        if not isinstance(func, ast.Attribute):
            return None, None
        if func.attr != 'with_traceback':
            return func.attr, None
        return _resolve_traceback_carrier(func.value)
    def _unchecked_cross_reraise_type(self, stmt, reraise_names: set,
                                      caught_names) -> str | None:
        raised_type, reraise_base = self._split_raise_target(stmt.exc)
        is_reraise_var = (reraise_base is not None
                          and reraise_base in reraise_names)
        if not raised_type or is_reraise_var:
            return None
        if not caught_names:
            return raised_type
        caught = {_canonical_exc_name(name) for name in caught_names}
        if _canonical_exc_name(raised_type) in caught:
            return None
        return raised_type
    def _em004_control_flow_names(self, handler) -> tuple[str, ...] | None:
        t = handler.type
        if isinstance(t, ast.Name):
            elts = (t,)
        elif (isinstance(t, ast.Tuple) and t.elts
                and all(isinstance(e, ast.Name) for e in t.elts)):
            elts = tuple(t.elts)
        else:
            return None
        names = tuple(e.id for e in elts)
        if all(n in _EM004_CONTROL_FLOW_TYPES for n in names):
            return names
        return None
class _OpenAssign(NamedTuple):
    line: int
    is_open: bool
    is_os_open: bool
    call: ast.Call | None
    precise: tuple[int, int]
def _scope_open_registry(scope, path_index: Any):
    assigns: dict[str, list[_OpenAssign]] = {}
    with_uses: dict[str, list[int]] = {}
    close_uses: dict[str, list[tuple[int, int]]] = {}
    scope_id = id(scope)
    for stmt, _ih in iter_scope_statements(scope, include_defs=True):
        _register_open_assigns(stmt, assigns, path_index, scope_id)
        _register_open_uses(stmt, with_uses, close_uses)
    return assigns, with_uses, close_uses
def _open_registry_for(evidence: _LeakEvidence, scope):
    scope_id = id(scope)
    registry = evidence.open_registries.get(scope_id)
    if registry is None:
        registry = _scope_open_registry(scope, evidence.path_index)
        evidence.open_registries[scope_id] = registry
    return registry
def _iter_assignment_target_values(target, value):
    if isinstance(target, ast.Starred):
        yield from _iter_assignment_target_values(target.value, None)
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        literal = value if isinstance(value, (ast.Tuple, ast.List)) else None
        can_pair = bool(
            literal is not None and len(target.elts) == len(literal.elts)
            and not any(isinstance(elt, ast.Starred) for elt in target.elts)
            and not any(isinstance(elt, ast.Starred) for elt in literal.elts))
        if can_pair:
            for sub_target, sub_value in zip(target.elts, literal.elts):
                yield from _iter_assignment_target_values(sub_target, sub_value)
        else:
            for sub_target in target.elts:
                yield from _iter_assignment_target_values(sub_target, None)
        return
    while isinstance(value, ast.NamedExpr):
        value = value.value
    yield target, value
def _register_open_assigns(stmt, assigns: dict, path_index: Any,
                           scope_id: int | None) -> None:
    pairs = []
    pair = assign_targets_value(stmt)
    if pair is not None:
        pairs.append(pair)
    pairs.extend((([target], value) for target, value
                  in _iter_named_expr_assignments(stmt)))
    if pair is None:
        for name in _statement_bound_names(stmt):
            assigns.setdefault(name, []).append(_OpenAssign(
                line=stmt.lineno,
                is_open=False,
                is_os_open=False,
                call=None,
                precise=(stmt.lineno, stmt.col_offset),
            ))
    for targets, value in pairs:
        for target in targets:
            for leaf, bound_value in _iter_assignment_target_values(target, value):
                is_open = _is_file_open_call(bound_value, path_index, scope_id)
                is_os_open = is_open and _is_os_fd_open_call(
                    bound_value, path_index)
                if isinstance(leaf, ast.Name):
                    assigns.setdefault(leaf.id, []).append(_OpenAssign(
                        line=bound_value.lineno if is_open else stmt.lineno,
                        is_open=is_open,
                        is_os_open=is_os_open,
                        call=bound_value if is_open else None,
                        precise=((bound_value.lineno, bound_value.col_offset)
                                 if is_open else (stmt.lineno, stmt.col_offset))))
def _register_open_uses(stmt, with_uses: dict, close_uses: dict) -> None:
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            ce = item.context_expr
            if isinstance(ce, ast.Name):
                with_uses.setdefault(ce.id, []).append(stmt.lineno)
    if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Attribute)
            and stmt.value.func.attr == "close"
            and isinstance(stmt.value.func.value, ast.Name)):
        close_uses.setdefault(stmt.value.func.value.id, []).append(
            (stmt.lineno, stmt.col_offset))
def _assign_key(record: _OpenAssign, precise: bool):
    return record.precise if precise else (record.line,)
def _collect_open_exemptions(tree, evidence) -> tuple[dict, dict]:
    with_managed: dict = {}
    close_managed: dict = {}
    for scope in scope_roots(tree):
        assigns, with_uses, close_uses = _open_registry_for(evidence, scope)
        with_managed.update(
            _pair_open_exemptions(assigns, with_uses, precise=False))
        close_managed.update(
            _pair_open_exemptions(assigns, close_uses, precise=True))
    return with_managed, close_managed
def _pair_open_exemptions(assigns: dict, uses: dict,
                          precise: bool) -> dict:
    managed: dict = {}
    for var, positions in uses.items():
        records = assigns.get(var, ())
        for raw_pos in positions:
            pos = raw_pos if precise else (raw_pos,)
            latest = latest_prior(records, pos,
                                   lambda record: _assign_key(record, precise))
            if latest is not None and latest.is_open:
                managed[id(latest.call)] = latest.line
    return managed
_OPEN_MODULE_NAMES = frozenset({"io", "codecs", "builtins", "os"})
_FILE_OPEN_MODULES = frozenset({"io", "codecs", "builtins"})
_FD_WRAPPER_MODULES = frozenset({"io", "builtins"})
_OS_OPEN_MODULES = frozenset({"os"})
_PATH_CTOR_LAST_NAMES = frozenset({"Path", "PosixPath", "WindowsPath",
                                   "PurePath", "PurePosixPath",
                                   "PureWindowsPath"})
_DEFAULT_OS_NAMES = frozenset({"os"})
_EMPTY_NAMES = frozenset()
def _imported_module_names(tree: Any, canonical_names) -> frozenset:
    names = set(canonical_names)
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in canonical_names:
                    names.add(alias.asname or alias.name)
    return frozenset(names)
def _imported_func_names(tree: Any, modules, func_name: str) -> frozenset:
    names: set = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom) or node.level:
            continue
        if node.module not in modules:
            continue
        names.update(alias.asname or alias.name
                     for alias in node.names if alias.name == func_name)
    return frozenset(names)
def _os_names_of(path_index: Any) -> frozenset:
    return getattr(path_index, "os_names", None) or _DEFAULT_OS_NAMES
def _open_names_of(path_index: Any) -> frozenset:
    return getattr(path_index, "open_module_names", None) or _OPEN_MODULE_NAMES
def _open_funcs_of(path_index: Any) -> frozenset:
    return getattr(path_index, "open_func_names", None) or _EMPTY_NAMES
def _os_open_funcs_of(path_index: Any) -> frozenset:
    return getattr(path_index, "os_open_func_names", None) or _EMPTY_NAMES
def _os_close_funcs_of(path_index: Any) -> frozenset:
    return getattr(path_index, "os_close_func_names", None) or _EMPTY_NAMES
def _os_fdopen_funcs_of(path_index: Any) -> frozenset:
    return getattr(path_index, "os_fdopen_func_names", None) or _EMPTY_NAMES
def _path_ctor_names(tree: Any) -> frozenset:
    names = set(_PATH_CTOR_LAST_NAMES)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ImportFrom) and not node.level
                and node.module == "pathlib"):
            for alias in node.names:
                if alias.name in _PATH_CTOR_LAST_NAMES and alias.asname:
                    names.add(alias.asname)
    return frozenset(names)
def _path_ctor_receiver(value: ast.expr, ctor_names: frozenset) -> bool:
    if not ctor_names or not isinstance(value, ast.Call):
        return False
    _name = dotted_name(value.func)
    if not _name:
        return False
    return _name.rsplit(".", 1)[-1] in ctor_names
class _PathBindingIndex:
    def __init__(self, tree: Any) -> None:
        self.ctor_names = _path_ctor_names(tree)
        self.os_names = _imported_module_names(tree, _DEFAULT_OS_NAMES)
        self.open_module_names = _imported_module_names(tree, _OPEN_MODULE_NAMES)
        self.open_func_names = _imported_func_names(
            tree, _FILE_OPEN_MODULES, "open")
        self.fd_wrapper_module_names = _imported_module_names(
            tree, _FD_WRAPPER_MODULES)
        self.fd_wrapper_func_names = _imported_func_names(
            tree, _FD_WRAPPER_MODULES, "open")
        self.os_open_func_names = _imported_func_names(
            tree, _OS_OPEN_MODULES, "open")
        self.os_close_func_names = _imported_func_names(
            tree, _OS_OPEN_MODULES, "close")
        self.os_fdopen_func_names = _imported_func_names(
            tree, _OS_OPEN_MODULES, "fdopen")
        self._records: dict[int, dict[str, list[tuple[tuple[int, int], bool]]]] = {}
        for scope in scope_roots(tree):
            self._records[id(scope)] = _scope_path_records(
                scope, self.ctor_names)
    def is_path(self, scope_id: int | None, name: str,
                pos: tuple[int, int]) -> bool:
        if scope_id is None:
            return False
        records = self._records.get(scope_id, {}).get(name)
        if not records:
            return False
        prior = [record for record in records if record[0] <= pos]
        return bool(prior) and prior[-1][1]
def _scope_path_records(scope,
                        ctor_names: Any
                        ) -> dict[str, list[tuple[tuple[int, int], bool]]]:
    records: dict[str, list[tuple[tuple[int, int], bool]]] = {}
    def record_assignment(targets, value, pos) -> None:
        while isinstance(value, ast.NamedExpr):
            value = value.value
        for target in targets:
            for leaf, bound_value in _iter_assignment_target_values(
                    target, value):
                if isinstance(leaf, ast.Name):
                    is_path = _path_ctor_receiver(bound_value, ctor_names)
                    records.setdefault(leaf.id, []).append((pos, is_path))
    for stmt, _ih in iter_scope_statements(scope, include_defs=True):
        pos = (stmt.lineno, stmt.col_offset)
        if isinstance(stmt, ast.ExceptHandler):
            if stmt.name:
                records.setdefault(stmt.name, []).append((pos, False))
            continue
        for target, value in _iter_named_expr_assignments(stmt):
            record_assignment(
                [target], value, (target.lineno, target.col_offset))
        pair = assign_targets_value(stmt)
        if pair is None:
            for name in _statement_bound_names(stmt):
                records.setdefault(name, []).append((pos, False))
            continue
        record_assignment(*pair, pos)
    for entries in records.values():
        entries.sort(key=lambda record: record[0])
    return records
def _is_file_open_call(node: ast.AST, path_index: Any,
                  scope_id: int | None) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Name):
        return (func.id == "open" or func.id in _open_funcs_of(path_index)
                or func.id in _os_open_funcs_of(path_index)
                or func.id in _os_fdopen_funcs_of(path_index))
    if not (isinstance(func, ast.Attribute)
            and func.attr in {"open", "fdopen"}):
        return False
    receiver = func.value
    if func.attr == "fdopen":
        return _attr_owner_name(receiver) in _os_names_of(path_index)
    ctor_names = getattr(path_index, "ctor_names", None) or _EMPTY_NAMES
    owner = _attr_owner_name(receiver)
    if owner in _open_names_of(path_index):
        return True
    if isinstance(receiver, ast.Name) and owner in ctor_names:
        return True
    if _path_ctor_receiver(receiver, ctor_names):
        return True
    return (isinstance(receiver, ast.Name)
            and path_index is not None
            and path_index.is_path(scope_id, receiver.id,
                                   (node.lineno, node.col_offset)))
def _is_os_fd_open_call(node: ast.AST, path_index: Any) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in _os_open_funcs_of(path_index)
    return (isinstance(func, ast.Attribute) and func.attr == "open"
            and _attr_owner_name(func.value) in _os_names_of(path_index))
def _collect_open_attr_targets(scope_id: int, targets, value,
                               evidence: _LeakEvidence) -> None:
    for target in targets:
        for leaf, bound_value in _iter_assignment_target_values(target, value):
            if isinstance(leaf, ast.Name):
                continue
            key = attr_chain_key(leaf)
            if key is None:
                continue
            is_open = _is_file_open_call(
                bound_value, evidence.path_index, scope_id)
            is_os_open = is_open and _is_os_fd_open_call(
                bound_value, evidence.path_index)
            position_node = bound_value if bound_value is not None else value
            precise = (position_node.lineno, position_node.col_offset)
            record = _OpenAssign(
                line=position_node.lineno,
                is_open=is_open,
                is_os_open=is_os_open,
                call=bound_value if is_open else None,
                precise=precise,
            )
            evidence.attr_assigns.setdefault((scope_id, key), []).append(record)
def _collect_rebound_attr_targets(scope_id: int, stmt,
                                  evidence: _LeakEvidence) -> None:
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        targets = [stmt.target]
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        targets = [item.optional_vars for item in stmt.items
                   if item.optional_vars is not None]
    elif isinstance(stmt, ast.AugAssign):
        targets = [stmt.target]
    elif isinstance(stmt, ast.Delete):
        targets = stmt.targets
    else:
        return
    for target in targets:
        for leaf, _bound in _iter_assignment_target_values(target, None):
            key = attr_chain_key(leaf)
            if key is None:
                continue
            evidence.attr_assigns.setdefault((scope_id, key), []).append(
                _OpenAssign(
                    line=stmt.lineno,
                    is_open=False,
                    is_os_open=False,
                    call=None,
                    precise=(stmt.lineno, stmt.col_offset),
                ))
def _is_os_module_call(node: ast.Call, attr_name: str, os_names) -> bool:
    _f = node.func
    return (isinstance(_f, ast.Attribute) and _f.attr == attr_name
            and _attr_owner_name(_f.value) in os_names)
def _is_imported_func_call(node: ast.Call, names) -> bool:
    return isinstance(node.func, ast.Name) and node.func.id in names
def _fdopen_fd_arg(node: ast.Call) -> ast.expr | None:
    if node.args:
        return node.args[0]
    return next((keyword.value for keyword in node.keywords
                 if keyword.arg == "fd"), None)
def _fdopen_takes_ownership(node: ast.Call) -> bool:
    closefd = next((keyword.value for keyword in node.keywords
                    if keyword.arg == "closefd"), None)
    return not (isinstance(closefd, ast.Constant) and not closefd.value)
def _register_os_name_use(sid: int, name: str, node: ast.Call,
                          evidence: _LeakEvidence) -> None:
    scopes = evidence.os_name_use_sites.setdefault(sid, {})
    scopes.setdefault(name, []).append((node.lineno, node.col_offset))
def _unwrap_walrus(value: ast.AST) -> ast.AST:
    # ``os.close(fd := os.open(p))`` / ``open(fd := os.open(p))`` / ``for l in (f := open(p))``
    # / ``return (f := open(p))``：被包裹的表达式才是真正的 fd/迭代源/交接对象。
    # 不解包会把海象节点当成非调用，漏掉「fd 已被接管」「文件已消费/已返回」。
    while isinstance(value, ast.NamedExpr):
        value = value.value
    return value
def _collect_os_close_targets(sid: int, arg: ast.expr, node: ast.Call,
                              evidence: _LeakEvidence) -> None:
    if isinstance(arg, ast.Name):
        _register_os_name_use(sid, arg.id, node, evidence)
    else:
        key = attr_chain_key(arg)
        if key is not None:
            evidence.os_attr_close_uses.setdefault((sid, key), []).append(
                (node.lineno, node.col_offset))
    if _is_os_fd_open_call(arg, evidence.path_index):
        evidence.os_close_direct_ids.add(id(arg))
def _collect_fdopen_targets(sid: int, arg0: ast.expr, node: ast.Call,
                            evidence: _LeakEvidence) -> None:
    if isinstance(arg0, ast.Name):
        _register_os_name_use(sid, arg0.id, node, evidence)
        return
    key = attr_chain_key(arg0)
    if key is not None:
        evidence.os_attr_close_uses.setdefault((sid, key), []).append(
            (node.lineno, node.col_offset))
    elif _is_os_fd_open_call(arg0, evidence.path_index):
        evidence.os_fdopen_direct_ids.add(id(arg0))
def _collect_close_or_fdopen_targets(node: ast.Call, scope_id: int,
                                     evidence: _LeakEvidence) -> None:
    _os_names = _os_names_of(evidence.path_index)
    _path_index = evidence.path_index
    if (node.args
            and (_is_os_module_call(node, "close", _os_names)
                 or _is_imported_func_call(
                     node, _os_close_funcs_of(_path_index)))):
        _collect_os_close_targets(
            scope_id, _unwrap_walrus(node.args[0]), node, evidence)
    wrapper_modules = getattr(
        _path_index, "fd_wrapper_module_names", _FD_WRAPPER_MODULES)
    wrapper_funcs = getattr(_path_index, "fd_wrapper_func_names", _EMPTY_NAMES)
    is_file_fd_wrapper = (
        (isinstance(node.func, ast.Name)
         and (node.func.id == "open" or node.func.id in wrapper_funcs))
        or (isinstance(node.func, ast.Attribute)
            and node.func.attr == "open"
            and _attr_owner_name(node.func.value) in wrapper_modules))
    if (_is_os_module_call(node, "fdopen", _os_names)
            or _is_imported_func_call(
                node, _os_fdopen_funcs_of(_path_index))
            or is_file_fd_wrapper):
        arg0 = _fdopen_fd_arg(node)
        if arg0 is not None and _fdopen_takes_ownership(node):
            _collect_fdopen_targets(
                scope_id, _unwrap_walrus(arg0), node, evidence)
def _collect_file_close_target(node: ast.Call, scope_id: int,
                               evidence: _LeakEvidence) -> None:
    if not (isinstance(node.func, ast.Attribute)
            and node.func.attr == "close"):
        return
    if _is_os_module_call(node, "close", _os_names_of(evidence.path_index)):
        return
    if isinstance(node.func.value, ast.Name):
        uses = evidence.file_name_close_uses.setdefault(scope_id, {})
        uses.setdefault(node.func.value.id, []).append(
            (node.lineno, node.col_offset))
        return
    key = attr_chain_key(node.func.value)
    if key is None:
        return
    evidence.file_attr_close_uses.setdefault((scope_id, key), []).append(
        (node.lineno, node.col_offset))
@dataclass
class _LeakEvidence:
    inline_consumed: set = field(default_factory=set)
    with_direct_ids: set = field(default_factory=set)
    os_name_use_sites: dict = field(default_factory=dict)
    os_name_managed_call_ids: set = field(default_factory=set)
    os_close_direct_ids: set = field(default_factory=set)
    os_fdopen_direct_ids: set = field(default_factory=set)
    attr_assigns: dict = field(default_factory=dict)
    os_attr_close_uses: dict = field(default_factory=dict)
    file_attr_close_uses: dict = field(default_factory=dict)
    file_name_close_uses: dict = field(default_factory=dict)
    attr_scope_classes: dict = field(default_factory=dict)
    with_open_call_ids: set = field(default_factory=set)
    close_managed_call_ids: set = field(default_factory=set)
    open_call_ids: set = field(default_factory=set)
    open_registries: dict = field(default_factory=dict)
    path_index: Any = None
def _collect_node_evidence(node, scope, evidence: _LeakEvidence) -> None:
    if isinstance(node, (ast.Call, ast.For, ast.AsyncFor,
                         ast.comprehension)):
        _register_inline_consumed(node, evidence)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        _register_with_direct_ids(node, evidence, scope)
    if (isinstance(node, (ast.Return, ast.Yield, ast.YieldFrom))
            and node.value is not None):
        _register_ownership_transfer(node, evidence, scope)
    scope_id = id(scope)
    _collect_rebound_attr_targets(scope_id, node, evidence)
    if isinstance(node, ast.Assign):
        _collect_open_attr_targets(scope_id, node.targets, node.value, evidence)
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        _collect_open_attr_targets(scope_id, [node.target], node.value, evidence)
    elif isinstance(node, ast.Call):
        _collect_close_or_fdopen_targets(node, scope_id, evidence)
        _collect_file_close_target(node, scope_id, evidence)
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr == "enter_context"):
            _register_wrapped_with_open(node, evidence, scope)
        if _is_file_open_call(node, evidence.path_index, scope_id):
            evidence.open_call_ids.add(id(node))
def _push_leak_children(stack, node, scope, class_scope) -> None:
    body = getattr(node, "body", None)
    body_ids = {id(stmt) for stmt in body} if isinstance(body, list) else set()
    for child in ast.iter_child_nodes(node):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            in_body = id(child) in body_ids
            child_scope = node if in_body else scope
            child_class_scope = class_scope
        elif isinstance(node, ast.Lambda):
            child_scope = node if child is node.body else scope
            child_class_scope = class_scope
        elif isinstance(node, ast.ClassDef):
            in_body = id(child) in body_ids
            child_scope = node if in_body else scope
            child_class_scope = node if in_body else class_scope
        else:
            child_scope = scope
            child_class_scope = class_scope
        stack.append((child, child_scope, child_class_scope))
def _collect_leak_evidence(tree) -> _LeakEvidence:
    evidence = _LeakEvidence(path_index=_PathBindingIndex(tree))
    stack = [(tree, tree, None)]
    while stack:
        node, scope, class_scope = stack.pop()
        evidence.attr_scope_classes[id(scope)] = (
            id(class_scope) if class_scope is not None else None)
        _collect_node_evidence(node, scope, evidence)
        _push_leak_children(stack, node, scope, class_scope)
    with_managed, close_managed = _collect_open_exemptions(tree, evidence)
    evidence.with_open_call_ids = (
            set(with_managed) | evidence.with_direct_ids)
    evidence.close_managed_call_ids |= set(close_managed)
    for scope in scope_roots(tree):
        assigns, _with_uses, _close_uses = _open_registry_for(evidence, scope)
        uses = evidence.os_name_use_sites.get(id(scope), {})
        for var, positions in uses.items():
            evidence.os_name_managed_call_ids.update(
                _pair_attr_close_records(assigns.get(var, ()), positions, True))
        name_close_uses = evidence.file_name_close_uses.get(id(scope), {})
        evidence.close_managed_call_ids.update(
            _pair_open_exemptions(assigns, name_close_uses, precise=True))
    evidence.close_managed_call_ids.update(
        _pair_attr_exemptions(evidence))
    return evidence
def _register_inline_consumed(node: ast.AST, evidence: _LeakEvidence) -> None:
    if isinstance(node, ast.Call):
        if (isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Call)):
            if node.func.attr in {"__enter__", "__aenter__"}:
                return
            inner = node.func.value
            while (isinstance(inner, ast.Call)
                   and isinstance(inner.func, ast.Attribute)
                   and inner.func.attr in {"__enter__", "__aenter__"}
                   and isinstance(inner.func.value, ast.Call)):
                inner = inner.func.value
            if not _is_os_fd_open_call(inner, evidence.path_index):
                evidence.inline_consumed.add(id(inner))
    elif isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        _iter = _unwrap_walrus(node.iter)
        if isinstance(_iter, ast.Call):
            evidence.inline_consumed.add(id(_iter))
def _handoff_leaves(value: ast.AST) -> list[ast.expr]:
    if isinstance(value, ast.NamedExpr):
        return _handoff_leaves(value.value)
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        return [leaf for elt in value.elts for leaf in _handoff_leaves(elt)]
    if isinstance(value, ast.Starred):
        return _handoff_leaves(value.value)
    if isinstance(value, ast.Dict):
        return [leaf
                for key, val in zip(value.keys, value.values)
                for item in (key, val) if item is not None
                for leaf in _handoff_leaves(item)]
    return [value]
def _yieldfrom_handoff_leaves(value: ast.AST) -> list[ast.expr]:
    if isinstance(value, ast.Dict):
        return [leaf for key in value.keys if key is not None
                for leaf in _handoff_leaves(key)]
    if isinstance(value, ast.DictComp):
        return _handoff_leaves(value.key)
    if isinstance(value, (ast.GeneratorExp, ast.ListComp, ast.SetComp)):
        return _handoff_leaves(value.elt)
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        return _handoff_leaves(value)
    return []
def _register_ownership_transfer(node: ast.Return | ast.Yield | ast.YieldFrom,
                                  evidence: _LeakEvidence, scope) -> None:
    leaves = (_yieldfrom_handoff_leaves(node.value)
              if isinstance(node, ast.YieldFrom)
              else _handoff_leaves(node.value))
    scope_id = id(scope)
    for leaf in leaves:
        if (isinstance(leaf, ast.Call)
                and _is_file_open_call(leaf, evidence.path_index, scope_id)):
            evidence.inline_consumed.add(id(leaf))
    returned = {leaf.id for leaf in leaves
                if isinstance(leaf, ast.Name) and isinstance(leaf.ctx, ast.Load)}
    if not returned:
        return
    assigns, _with_uses, _close_uses = _open_registry_for(evidence, scope)
    return_pos = (node.lineno, node.col_offset)
    for name in returned:
        record = latest_prior(
            assigns.get(name, ()), return_pos,
            lambda candidate: candidate.precise)
        if (record is not None and record.is_open
                and record.call is not None):
            evidence.inline_consumed.add(id(record.call))
_WITH_OPEN_MANAGER_NAMES = frozenset({'closing', 'enter_context'})
def _is_with_open_manager(context_expr) -> bool:
    if not isinstance(context_expr, ast.Call):
        return False
    name = dotted_name(context_expr.func)
    return bool(name) and name.rsplit('.', 1)[-1] in _WITH_OPEN_MANAGER_NAMES
def _register_wrapped_with_open(context_expr, evidence: _LeakEvidence,
                                scope) -> None:
    for sub in walk_nodes(context_expr):
        if not _is_file_open_call(sub, evidence.path_index, id(scope)):
            continue
        if _is_os_fd_open_call(sub, evidence.path_index):
            evidence.close_managed_call_ids.add(id(sub))
        else:
            evidence.with_direct_ids.add(id(sub))
def _register_with_direct_ids(node: ast.With, evidence: _LeakEvidence,
                              scope) -> None:
    for item in node.items:
        call = item.context_expr
        while isinstance(call, ast.NamedExpr):
            call = call.value
        if _is_file_open_call(call, evidence.path_index, id(scope)):
            evidence.with_direct_ids.add(id(call))
            continue
        if _is_with_open_manager(call):
            _register_wrapped_with_open(call, evidence, scope)
def _pair_attr_close_records(records, uses, os_only: bool) -> set:
    managed: set = set()
    for pos in uses:
        latest = latest_prior(records, pos, lambda record: record.precise)
        if (latest is not None and latest.is_open and latest.call is not None
                and (not os_only or latest.is_os_open)):
            managed.add(id(latest.call))
    return managed
def _pair_attr_exemptions(evidence: _LeakEvidence) -> set:
    managed: set = set()
    close_maps = ((evidence.os_attr_close_uses, True),
                  (evidence.file_attr_close_uses, False))
    for close_map, os_only in close_maps:
        for (scope_id, key), uses in close_map.items():
            managed |= _pair_attr_close_records(
                evidence.attr_assigns.get((scope_id, key), ()), uses, os_only)
    for close_map, os_only in close_maps:
        managed |= _pair_cross_method_attr_exemptions(
            evidence, close_map, os_only)
    return managed
def _pair_cross_method_attr_exemptions(evidence: _LeakEvidence, close_map: dict,
                                       os_only: bool) -> set:
    managed: set = set()
    for (close_scope, key), uses in close_map.items():
        class_id = evidence.attr_scope_classes.get(close_scope)
        if class_id is None:
            continue
        local_records = evidence.attr_assigns.get((close_scope, key), ())
        if not any(latest_prior(
                local_records, pos, lambda record: record.precise) is None
                for pos in uses):
            continue
        latest_by_scope: dict[int, _OpenAssign] = {}
        for (scope_id, record_key), scoped in evidence.attr_assigns.items():
            if (record_key != key or scope_id == close_scope
                    or evidence.attr_scope_classes.get(scope_id) != class_id):
                continue
            for record in scoped:
                current = latest_by_scope.get(scope_id)
                if current is None or record.precise > current.precise:
                    latest_by_scope[scope_id] = record
        for record in latest_by_scope.values():
            if (record.is_open and record.call is not None
                    and (not os_only or record.is_os_open)):
                managed.add(id(record.call))
    return managed
def _os_open_fd_closed(call: ast.Call, evidence: _LeakEvidence) -> bool:
    if id(call) in evidence.os_name_managed_call_ids:
        return True
    if id(call) in evidence.os_close_direct_ids:
        return True
    return id(call) in evidence.os_fdopen_direct_ids
def _classify_open_call(node: ast.Call, is_test: bool,
                        evidence: _LeakEvidence) -> str | None:
    if id(node) in evidence.with_open_call_ids:
        return "safe_with"
    if id(node) in evidence.inline_consumed:
        return "exempt_inline"
    if is_test:
        return "exempt_test"
    if (_is_os_fd_open_call(node, evidence.path_index)
            and _os_open_fd_closed(node, evidence)):
        return "exempt_fd_closed"
    if id(node) in evidence.close_managed_call_ids:
        return "exempt_fd_closed"
    return None
def _leak_entry(node: ast.Call, rel: str, is_os_open: bool) -> dict:
    line = node.lineno
    if is_os_open:
        return {
            "file": rel,
            "line": line,
            "severity": "medium",
            "message": f"os.open() fd at {rel}:{line} never closed",
            "suggestion": "fd = os.open(...) 后在 finally 中 os.close(fd)",
        }
    return {
        "file": rel,
        "line": line,
        "severity": "medium",
        "message": f"open() at {rel}:{line} not in with-statement",
        "suggestion": "使用 with open(...) 或确保显式 close()",
    }
def detect_resource_leaks_inline(tree, rel: str) -> dict:
    if tree is None:
        return {}
    is_test = is_test_file_path(rel)
    evidence = _collect_leak_evidence(tree)
    open_calls = 0
    buckets = {"safe_with": 0, "exempt_inline": 0, "exempt_test": 0,
               "exempt_fd_closed": 0}
    leaks = []
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call) or id(node) not in evidence.open_call_ids:
            continue
        is_os_open = _is_os_fd_open_call(node, evidence.path_index)
        open_calls += 1
        bucket = _classify_open_call(node, is_test, evidence)
        if bucket is None:
            leaks.append(_leak_entry(node, rel, is_os_open))
        else:
            buckets[bucket] += 1
    return {
        "open_calls": open_calls,
        "safe_with": buckets["safe_with"],
        "exempt_inline": buckets["exempt_inline"],
        "exempt_test": buckets["exempt_test"],
        "exempt_fd_closed": buckets["exempt_fd_closed"],
        "leaks": leaks,
    }
def _entry_counts(entries) -> dict:
    return {
        "total_raises": len(entries),
        "total_caught": sum(1 for e in entries if e.except_line > 0),
        "total_uncaught": sum(1 for e in entries if e.except_line == 0),
        "swallowed_exceptions": sum(1 for e in entries if e.is_swallowed),
    }
def summarize_type_flow(entries) -> dict:
    by_severity = defaultdict(int)
    for entry in entries:
        by_severity[entry.severity] += 1
    return {
        **_entry_counts(entries),
        "entries": [asdict(entry) for entry in entries],
        "by_severity": dict(by_severity),
    }
def load_source_and_tree(filepath, ctx):
    source = tree = None
    if ctx is not None:
        try:
            source = ctx.get_source(filepath)
            tree = ctx.get_ast(filepath)
        except CONTEXT_ACCESS_ERRORS as _e:
            log_swallowed(
                __name__, _e,
                context=f'load_source_and_tree:{type(_e).__name__}')
            source = None
    if source is None or tree is None:
        source, tree = _parse_py_file(filepath, quiet=True)
        if source is None or tree is None:
            logger.debug("%s: skipped file in unified exception scan: %s",
                         _LOG_TAG, filepath)
            return None, None
    return source, tree
def _read_suppressions(filepath: str) -> dict:
    """读取源码的行内抑制表；不可读时按「无抑制」处理，不阻断检测。"""
    try:
        with open(filepath, encoding='utf-8', errors='replace') as _fh:
            return parse_suppressions(_fh.read())
    except OSError:
        return {}


def _run_exception_detector(detector_cls, label: str, tree, filepath: str,
                            rel: str, is_test_file: bool):
    try:
        visitor = detector_cls()
        visitor.suppressions = _read_suppressions(filepath)
        visitor.visit(tree)
        if is_test_file:
            return visitor, [], len(visitor.findings)
        new_findings: list = []
        for f_ in visitor.findings:
            f_['file'] = rel
            new_findings.append(f_)
        return visitor, new_findings, 0
    except Exception:
        logger.warning("%s: %s analysis failed for %s", _LOG_TAG, label, filepath,
                       exc_info=True)
        raise
def run_tryceratops_detector(tree, filepath: str, rel: str,
                             is_test_file: bool):
    visitor, findings, exempt_test = _run_exception_detector(
        _TryceratopsVisitor, "tryceratops", tree, filepath, rel, is_test_file)
    if visitor is None:
        return [], 0, 0, 0
    return (findings, exempt_test, visitor.protocol_exempt,
            visitor.selective_reraise_exempt)
def run_exception_miner_detector(tree, filepath: str, rel: str,
                                 is_test_file: bool):
    _visitor, findings, exempt_test = _run_exception_detector(
        _ExceptionMinerVisitor, "exception-miner", tree, filepath, rel,
        is_test_file)
    return findings, exempt_test

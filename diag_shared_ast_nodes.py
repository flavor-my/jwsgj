from __future__ import annotations

import ast
import builtins
import contextlib
import copy
import logging
import os
import re
import sys
from collections import deque
from collections.abc import Callable, Iterable, Iterator
from pathlib import Path
from typing import Any
from weakref import WeakKeyDictionary

from jwsgj.diag_types_vocab import (
    DEFAULT_VIRTUAL_FILENAME,
    YAML_SAFE_LOADERS,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC as _PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
BUILTIN_NAMES: frozenset[str] = frozenset(
    name for name in dir(builtins) if name != "__builtins__")
BUILTIN_CALLABLES: frozenset[str] = BUILTIN_NAMES
_RUNTIME_NOISE_TOP_MODULES = frozenset({"pytest", "typing_extensions"})
_LEGACY_STDLIB_TOP_MODULES = frozenset({
    "os", "sys", "time", "datetime", "json", "re", "math", "random",
    "pathlib", "shutil", "tempfile", "io", "hashlib", "base64",
    "collections", "itertools", "functools", "operator",
    "typing", "abc", "dataclasses", "enum",
    "logging", "warnings", "traceback", "inspect", "textwrap",
    "subprocess", "argparse", "configparser", "csv",
    "threading", "multiprocessing", "queue", "asyncio",
    "unittest", "doctest",
    "copy", "pprint", "uuid", "atexit", "signal",
    "ast", "tokenize", "dis", "code", "codeop",
    "socket", "http", "urllib", "xml", "html", "email",
    "sqlite3", "pickle", "struct", "zlib", "gzip", "tarfile", "zipfile",
    "decimal", "fractions", "statistics",
    "platform", "locale", "gettext", "getpass",
    "cmd", "shlex", "readline", "rlcompleter",
    "cProfile", "profile", "pstats", "timeit",
    "importlib", "pkgutil", "runpy",
    "__future__", "builtins", "gc", "weakref", "types",
    "concurrent", "contextlib", "contextvars",
})
PY_STDLIB_HINTS = (
    frozenset(getattr(sys, "stdlib_module_names", frozenset()))
    | _LEGACY_STDLIB_TOP_MODULES
)
NON_PROJECT_TOP_MODULES = PY_STDLIB_HINTS | _RUNTIME_NOISE_TOP_MODULES
FUNC_NODE_TYPES: tuple[type, ...] = (ast.FunctionDef, ast.AsyncFunctionDef)
TRY_NODE_TYPES: tuple[type, ...] = (
    (ast.Try, ast.TryStar) if hasattr(ast, 'TryStar') else (ast.Try,)
)
MATCH_NODE_TYPES: tuple[type, ...] = (
    (ast.Match,) if hasattr(ast, 'Match') else ()
)
_CLASS_BODY_CONTAINERS: tuple[type, ...] = (
    ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith,
    *TRY_NODE_TYPES, ast.ExceptHandler, *MATCH_NODE_TYPES,
    *((ast.match_case,) if hasattr(ast, "match_case") else ()),
)
def _virtual_filename(filename: Any) -> str:
    return coerce_str(filename) or DEFAULT_VIRTUAL_FILENAME
def _parse_via_shared_channel(
        code: str, filename: Any = DEFAULT_VIRTUAL_FILENAME):
    # 硬环：diag_shared_source_core 复用本模块的 AST 节点工具。
    from jwsgj.diag_shared_source_core import (
        parse_cached,  # lazy-by-design — 硬环断路器
    )
    return parse_cached(code, _virtual_filename(filename))
def parse_py_source(code: str) -> ast.Module | None:
    try:
        return _parse_via_shared_channel(code)
    except _PARSE_DEGRADE_EXC as e:
        logger.warning("parse_py_source: 代码解析失败，返回空结果: %s", e)
        return None
def parse_ast_safely(code: str) -> tuple[ast.Module | None, Exception | None]:
    try:
        return _parse_via_shared_channel(code), None
    except _PARSE_DEGRADE_EXC as e:
        logger.debug("parse_ast_safely 解析失败: %s", e)
        return None, e
def parse_source_tree(source: str, filepath: str) -> ast.Module | None:
    try:
        return _parse_via_shared_channel(source, filepath)
    except _PARSE_DEGRADE_EXC as exc:
        logger.warning("无法解析 %s: %s", filepath, exc)
        return None
def _iter_chain_nodes(node: Any):
    cur: Any = node
    while isinstance(cur, (ast.Attribute, ast.Call)):
        yield cur
        cur = cur.value if isinstance(cur, ast.Attribute) else cur.func
def chain_depth(node: Any) -> int:
    return sum(isinstance(part, ast.Attribute)
               for part in _iter_chain_nodes(node))
def chain_spine_calls(func_expr: Any) -> list:
    return [part for part in _iter_chain_nodes(func_expr)
            if isinstance(part, ast.Call)]
def iter_params(args: ast.arguments) -> list:
    return list(args.posonlyargs) + list(args.args) + list(args.kwonlyargs)
def iter_arg_nodes(args: ast.arguments) -> list:
    nodes = [*args.posonlyargs, *args.args]
    if args.vararg:
        nodes.append(args.vararg)
    nodes.extend(args.kwonlyargs)
    if args.kwarg:
        nodes.append(args.kwarg)
    return nodes
def has_type_hints(func: Any) -> bool:
    return bool(func.returns) or any(
        arg.annotation for arg in iter_arg_nodes(func.args))
def argument_param_names(args: ast.arguments) -> list[str]:
    def _names(items: list) -> list[str]:
        return [item.arg for item in items if isinstance(item, ast.arg)]
    names = _names(args.posonlyargs)
    names += _names(args.args)
    if isinstance(args.vararg, ast.arg):
        names.append(args.vararg.arg)
    names += _names(args.kwonlyargs)
    if isinstance(args.kwarg, ast.arg):
        names.append(args.kwarg.arg)
    return names
_CLI_ARGV_PARAM_NAMES = frozenset({"argv", "args", "args_list", "arguments", "cli_args"})
_ENTRY_REQUIRES_ARGS = "entry_requires_arguments"
def main_block_entry_args(node, *,
                          program_name: str = "program") -> tuple[tuple, str]:
    if node is None:
        return (), ""
    _a = node.args
    _pos = [*_a.posonlyargs, *_a.args]
    _required_positional = [x.arg for x in _pos[:len(_pos) - len(_a.defaults)]]
    if any(default is None for default in _a.kw_defaults):
        return (), _ENTRY_REQUIRES_ARGS
    if not _required_positional:
        return (), ""
    if (len(_required_positional) == 1
            and _required_positional[0].lower() in _CLI_ARGV_PARAM_NAMES):
        return ([program_name],), ""
    return (), _ENTRY_REQUIRES_ARGS
def is_dataclass_decorator(dec: str) -> bool:
    return isinstance(dec, str) and (
        dec in ("dataclass", "dataclasses.dataclass")
        or dec.startswith(("dataclass(", "dataclasses.dataclass("))
    )
def decorator_name(decorator: ast.AST) -> str:
    target = decorator.func if isinstance(decorator, ast.Call) else decorator
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        return target.attr
    return ""
def is_static_method(node: ast.AST) -> bool:
    return any(decorator_name(dec) == "staticmethod"
               for dec in getattr(node, "decorator_list", ()) or ())
def is_broad_except(node: ast.ExceptHandler) -> bool:
    return node.type is None or _is_broad_exception_type(node.type)
def _is_broad_exception_type(t: ast.expr) -> bool:
    if isinstance(t, ast.Name):
        return t.id in ("Exception", "BaseException")
    if (isinstance(t, ast.Attribute)
            and isinstance(t.value, ast.Name)
            and t.value.id == "builtins"):
        return t.attr in ("Exception", "BaseException")
    if isinstance(t, ast.Tuple):
        return any(_is_broad_exception_type(e) for e in t.elts)
    if isinstance(t, ast.BinOp) and isinstance(t.op, ast.BitOr):
        return any(_is_broad_exception_type(e) for e in (t.left, t.right))
    return False
def class_body_owner(node: Any, parents: dict) -> Any:
    parent = parents.get(node)
    while isinstance(parent, _CLASS_BODY_CONTAINERS):
        parent = parents.get(parent)
    return parent if isinstance(parent, ast.ClassDef) else None
def is_overload_stub(node: ast.AST) -> bool:
    return any(decorator_name(dec) == "overload"
               for dec in getattr(node, "decorator_list", ()) or ())
def find_runtime_function(node: ast.AST,
                          function_name: str | None = None) -> ast.AST | None:
    for child in walk_nodes(node):
        if not isinstance(child, FUNC_NODE_TYPES) or is_overload_stub(child):
            continue
        if not function_name or child.name == function_name:
            return child
    return None
def count_params(node: ast.AST, is_method: bool = False) -> int:
    args = getattr(node, "args", None)
    if not isinstance(args, ast.arguments):
        return 0
    total = len(iter_arg_nodes(args))
    positional = (*args.posonlyargs, *args.args)
    if (is_method and total > 0 and not is_static_method(node)
            and positional and isinstance(positional[0], ast.arg)
            and positional[0].arg in ("self", "cls")):
        return total - 1
    return total
def is_none_literal(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and node.value is None
def definition_time_exprs(node: ast.AST) -> list:
    exprs = list(getattr(node, "decorator_list", ()) or ())
    args = getattr(node, "args", None)
    if args is not None:
        exprs.extend(iter_arg_defaults(args))
    return exprs
_IDENT_SEG_RE = re.compile(r'[A-Z]+(?![a-z])|[A-Z][a-z0-9]*|[a-z0-9]+')
def split_identifier(name: str) -> tuple[str, ...]:
    return tuple(part.lower() for part in _IDENT_SEG_RE.findall(name))
def segments_equal(left: str, right: str) -> bool:
    if left == right:
        return True
    if len(left) <= 3 or len(right) <= 3:
        return False
    return left.removesuffix("s") == right.removesuffix("s")
def first_segment(dotted: str) -> str:
    return dotted.split(".", 1)[0]
def collect_param_names(node: ast.AST) -> set[str]:
    args = getattr(node, "args", None)
    if not isinstance(args, ast.arguments):
        return set()
    return set(argument_param_names(args))
def extract_loop_target_names(node: ast.AST) -> set[str]:
    if not isinstance(node, (ast.For, ast.AsyncFor)):
        return set()
    return set(iter_unpack_target_names(node.target))
def flatten_unpack_targets(
        targets: ast.AST | Iterable[ast.AST]) -> Iterator[ast.AST]:
    roots = (() if targets is None
             else ((targets,) if isinstance(targets, ast.AST) else targets))
    stack = list(reversed(list(roots)))
    while stack:
        target = stack.pop()
        if isinstance(target, (ast.Tuple, ast.List)):
            stack.extend(reversed(target.elts))
        elif isinstance(target, ast.Starred):
            stack.append(target.value)
        else:
            yield target
def iter_target_bindings(target: ast.AST) -> Iterator[tuple[str, int, int]]:
    for leaf in flatten_unpack_targets(target):
        if isinstance(leaf, ast.Name):
            yield (leaf.id, getattr(leaf, "lineno", 0),
                   getattr(leaf, "col_offset", 0))
def iter_unpack_target_names(targets: ast.AST | Iterable[ast.AST]) -> Iterator[str]:
    roots = ((targets,) if isinstance(targets, ast.AST)
             else (targets or ()))
    for target in roots:
        for name, _line, _col in iter_target_bindings(target):
            yield name
def iter_pattern_capture_names(pattern: ast.AST) -> list[str]:
    names: list[str] = []
    for sub in walk_nodes(pattern):
        capture = None
        if isinstance(sub, (ast.MatchAs, ast.MatchStar)):
            capture = sub.name
        elif isinstance(sub, ast.MatchMapping):
            capture = sub.rest
        if capture:
            names.append(capture)
    return names
def pattern_capture_name(node: ast.AST) -> str | None:
    if isinstance(node, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar)) and node.name:
        return node.name
    if isinstance(node, ast.MatchMapping) and node.rest:
        return node.rest
    return None
def _annassign_binding_name(node: ast.AST) -> str | None:
    if not isinstance(node, ast.AnnAssign) or node.value is None:
        return None
    return node.target.id if isinstance(node.target, ast.Name) else None
def _assigned_binding_names(node: ast.AST) -> set:
    if isinstance(node, ast.Assign):
        return set(iter_unpack_target_names(node.targets))
    name = _annassign_binding_name(node)
    return {name} if name is not None else set()
def _control_flow_binding_names(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return set(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return {
            name
            for item in node.items
            if item.optional_vars is not None
            for name in iter_unpack_target_names(item.optional_vars)
        }
    if isinstance(node, TRY_NODE_TYPES):
        return {handler.name for handler in node.handlers if handler.name}
    if isinstance(node, ast.AugAssign):
        return set(iter_unpack_target_names(node.target))
    if MATCH_NODE_TYPES and isinstance(node, MATCH_NODE_TYPES):
        return {
            name
            for case in node.cases
            for name in iter_pattern_capture_names(case.pattern)
        }
    return set()
def _stmt_binding_names(node: ast.AST,
                       annotations_evaluated: bool) -> set:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name} | definition_site_walrus_names(
            node, annotations_evaluated)
    if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
        return {node.name.id} if isinstance(node.name, ast.Name) else set()
    names = _assigned_binding_names(node)
    names.update(_control_flow_binding_names(node))
    names.update(_walrus_target_names(node))
    return names
def module_level_binding_names(tree: ast.AST) -> set:
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    return {name for node in iter_module_level_stmts(tree)
            for name in _stmt_binding_names(node, annotations_evaluated)}
def ast_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Call):
        return ast_name(node.func)
    return ''
def is_dunder_name(name: str) -> bool:
    return name.startswith('__') and name.endswith('__')
def is_public_name(name: str) -> bool:
    return bool(name) and not name.startswith('_')
def matches_any(name: str, patterns: list) -> bool:
    return any(p.search(name) for p in patterns)
def as_format_call(node: ast.AST) -> ast.Call | None:
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "format"):
        return node
    return None
_NODE_SCOPE_TYPES = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.Lambda)
def nearest_scope_node(node: ast.AST | None,
                       parent_map: dict[int, ast.AST]) -> ast.AST | None:
    while node is not None and not isinstance(node, _NODE_SCOPE_TYPES):
        node = parent_map.get(id(node))
    return node
def dotted_name(node: ast.AST, *, constant_base: bool = False) -> str:
    parts: list[str] = []
    cur = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        parts.append(cur.id)
    elif not (constant_base and isinstance(cur, ast.Constant)):
        return ""
    return ".".join(reversed(parts))
def attr_chain_key(node: ast.AST) -> str | None:
    return dotted_name(node) or None
def type_last_name(t: ast.expr) -> str:
    dotted = dotted_name(t) if isinstance(t, (ast.Name, ast.Attribute)) else ""
    return dotted.rsplit(".", 1)[-1] if dotted else ""
def type_last_names(ty: ast.expr) -> list[str]:
    if isinstance(ty, ast.Tuple):
        return [type_last_name(e) for e in ty.elts]
    return [type_last_name(ty)]
ABSTRACT_NAME_PREFIXES = ("Abstract", "Base")
def expr_target_name(expr: ast.expr) -> str:
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Attribute):
        return expr.attr
    return ""
def _iter_parent_edges(tree: ast.AST) -> Iterator[tuple[ast.AST, ast.AST]]:
    for parent in walk_nodes(tree):
        for child in ast.iter_child_nodes(parent):
            yield child, parent
_PARENT_MAP_CACHE: WeakKeyDictionary[Any, dict[int, ast.AST]] = WeakKeyDictionary()
_PARENT_MAP_CACHE_MAX = 256


def build_parent_map(tree: ast.AST) -> dict[int, ast.AST]:
    """返回 ``{id(child): parent}`` 父图（按树缓存、只读共享）。

    父图只与树结构相关，而诊断轮次内同一棵树会被数十个检测器请求
    （实测单轮 418 次调用）；每次重新 ``ast.walk`` 整树是纯粹的重复劳动。
    缓存后返回同一映射，调用方**不得原地修改**（需变更请自行 ``dict(...)`` 拷贝）。
    """
    if tree is None:
        return {}
    try:
        cached = _PARENT_MAP_CACHE.get(tree)
    except TypeError:  # 非弱引用可缓存对象，退回无缓存计算
        return {id(child): parent for child, parent in _iter_parent_edges(tree)}
    if cached is not None:
        return cached
    built = {id(child): parent for child, parent in _iter_parent_edges(tree)}
    try:
        _PARENT_MAP_CACHE[tree] = built
        while len(_PARENT_MAP_CACHE) > _PARENT_MAP_CACHE_MAX:
            del _PARENT_MAP_CACHE[next(iter(_PARENT_MAP_CACHE))]
    except TypeError:
        pass
    return built
def build_node_parent_map(tree: ast.AST) -> dict[ast.AST, ast.AST]:
    return dict(_iter_parent_edges(tree))
def _has_abc_base(node: ast.ClassDef) -> bool:
    return any(expr_target_name(base) == "ABC" for base in node.bases)
def _has_abstractmeta_keyword(node: ast.ClassDef) -> bool:
    return any(kw.arg == "metaclass" and expr_target_name(kw.value) == "ABCMeta"
               for kw in node.keywords)
def has_abstractmethod_decorator(node: ast.AST) -> bool:
    return any(expr_target_name(dec) == "abstractmethod"
               for dec in getattr(node, "decorator_list", ()))
def _iter_class_body_members(stmts: Iterable[ast.AST]) -> Iterator[ast.AST]:
    for node in stmts:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node
            continue
        if isinstance(node, (ast.ClassDef, ast.Lambda)):
            continue
        for block in iter_module_stmt_blocks(node):
            yield from _iter_class_body_members(block)
def _has_abstract_method(node: ast.ClassDef) -> bool:
    return any(has_abstractmethod_decorator(item)
               for item in _iter_class_body_members(node.body))
def is_abstract_class_def(node: ast.ClassDef) -> bool:
    return (node.name.startswith(ABSTRACT_NAME_PREFIXES)
            or _has_abc_base(node)
            or _has_abstractmeta_keyword(node)
            or _has_abstract_method(node))
def _is_isinstance_call(test: ast.expr) -> bool:
    return (isinstance(test, ast.Call)
            and isinstance(test.func, ast.Name)
            and test.func.id == "isinstance")
def _is_none_identity_compare(test: ast.expr) -> bool:
    if not isinstance(test, ast.Compare):
        return False
    if (len(test.ops) != 1 or len(test.comparators) != 1
            or not isinstance(test.ops[0], (ast.Is, ast.IsNot))):
        return False
    return (is_none_literal(test.left)
            or is_none_literal(test.comparators[0]))
def is_invariant_assert(node: ast.AST) -> bool:
    if not isinstance(node, ast.Assert):
        return False
    return (_is_isinstance_call(node.test)
            or _is_none_identity_compare(node.test))
def recv_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    return dotted_name(node)
def is_subscript_of(node: ast.AST, seq_name: str) -> bool:
    if not isinstance(node, ast.Subscript):
        return False
    return recv_name(node.value) == seq_name
def iter_handler_scope(handler: ast.ExceptHandler):
    stack = list(reversed(handler.body))
    while stack:
        node = stack.pop()
        if isinstance(node, _SCOPE_STOP_NODES):
            continue
        yield node
        if isinstance(node, ast.ExceptHandler):
            stack.extend(reversed(node.body))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def iter_loop_frame_nodes(stmts: list) -> list:
    out: list[ast.AST] = []
    for stmt in stmts or ():
        if isinstance(stmt, _SCOPE_STOP_NODES):
            continue
        out.append(stmt)
        out.extend(_iter_frame_nodes(stmt, _SCOPE_STOP_NODES))
    return out
COMP_SCOPE_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                     ast.GeneratorExp)
SHADOW_SCOPE_STOP = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_SCOPE_STOP_NODES = (*SHADOW_SCOPE_STOP, ast.Lambda)
FRAME_BOUNDARY_NODES = _SCOPE_STOP_NODES
def _iter_frame_raw(
    scope: ast.AST,
    stop_types: tuple[type, ...],
    *,
    yield_stop: bool = False,
    state: Any = None,
    enter: Callable[[ast.AST, ast.AST, Any], Any] | None = None,
) -> Iterator[tuple[ast.AST, Any]]:
    stack: list[tuple[Iterator[ast.AST], Any, ast.AST]] = [
        (iter(ast.iter_child_nodes(scope)), state, scope)]
    while stack:
        try:
            child = next(stack[-1][0])
        except StopIteration:
            stack.pop()
            continue
        cur = stack[-1][1]
        parent = stack[-1][2]
        child_state = enter(parent, child, cur) if enter is not None else cur
        if isinstance(child, stop_types):
            if yield_stop:
                yield child, child_state
            continue
        yield child, child_state
        stack.append(
            (iter(ast.iter_child_nodes(child)), child_state, child))
def _iter_frame_nodes(scope: ast.AST, stop_types: tuple[type, ...],
                      yield_stop: bool = False) -> Iterator[ast.AST]:
    for node, _state in _iter_frame_raw(
            scope, stop_types, yield_stop=yield_stop):
        yield node
#: 所有以 **AST 对象身份** 为键的派生缓存的统一释放入口。
#:
#: 关键认识（L0-3 内存画像）：这些缓存按 ``id(节点)`` / 弱引用键存放，
#: **跨文件永远不可能命中**——上一个文件的 AST 对象与下一个文件不共享身份。
#: 因此把它们保留到下一次 GC 是纯内存浪费：实测 4 个文件后
#: ``_PARENT_MAP_CACHE``(256) + ``_WALK_NODES_CACHE``(1024) +
#: ``_NAMEDEXPR_PRESENCE``(2048) + ``_SCOPE_NODES_LIST_CACHE``(751)
#: 全部占满，RSS 139 MB → 1757 MB，且弱引用字典的 **值里又持有键的后代节点**
#: （父子映射、节点列表），形成「弱键 → 强值 → 键的后代」的引用环，
#: 弱引用字典无法回收，整棵文件 AST 被钉在内存里。
#:
#: 释放是**零代价**的：文件内的复用（实测 77.6×）在文件结束前已全部发生。
def release_ast_identity_caches() -> dict[str, int]:
    """清空全部「按 AST 对象身份作键」的派生缓存，返回各域清掉的条目数。"""
    out: dict[str, int] = {}
    for name, cache in (
        ("parent_map", _PARENT_MAP_CACHE),
        ("scope_nodes_list", _SCOPE_NODES_LIST_CACHE),
        ("tc_guard_polarity", _TC_GUARD_POLARITY_CACHE),
        ("tc_body_ids", _TC_BODY_IDS_CACHE),
    ):
        try:
            out[name] = len(cache)
            cache.clear()
        except Exception:  # 释放失败不阻断诊断
            out[name] = -1
    return out


#: ``scope_nodes_list`` 的作用域级缓存。
#:
#: ``iter_scope_nodes`` 每次调用都要把作用域子树完整走一遍。实测 ``check_PY07``
#: 单文件为 971 个调用点各自调用一次（合计 1,929 次，累计 8.7 s），而作用域只有
#: 数百个——同一份「作用域内节点列表」被反复重建。此缓存把它降为一次遍历。
#: 用弱引用字典保证不阻止 AST 回收；返回元组，调用方只读。
_SCOPE_NODES_LIST_CACHE: WeakKeyDictionary[Any, tuple] = WeakKeyDictionary()
_SCOPE_NODES_LIST_MAX = 4096


def scope_nodes_list(scope: ast.AST) -> tuple:
    """``tuple(iter_scope_nodes(scope))`` 的缓存版本（作用域的纯函数）。"""
    try:
        cached = _SCOPE_NODES_LIST_CACHE.get(scope)
    except TypeError:  # 非弱引用可缓存对象，退回无缓存计算
        return tuple(iter_scope_nodes(scope))
    if cached is not None:
        return cached
    built = tuple(iter_scope_nodes(scope))
    try:
        _SCOPE_NODES_LIST_CACHE[scope] = built
        while len(_SCOPE_NODES_LIST_CACHE) > _SCOPE_NODES_LIST_MAX:
            del _SCOPE_NODES_LIST_CACHE[next(iter(_SCOPE_NODES_LIST_CACHE))]
    except TypeError:
        pass
    return built


def iter_scope_nodes(scope: ast.AST) -> Iterator[ast.AST]:
    yield from _iter_frame_nodes(scope, _SCOPE_STOP_NODES, yield_stop=True)
def iter_own_nodes(scope: ast.AST) -> Iterator[ast.AST]:
    yield from _iter_frame_nodes(scope, _SCOPE_STOP_NODES)
def scope_roots(tree: ast.AST) -> list[ast.AST]:
    roots: list[ast.AST] = [tree]
    roots.extend(n for n in walk_nodes(tree)
                 if n is not tree and isinstance(n, _SCOPE_STOP_NODES))
    return roots
_SCOPE_CHAIN_NODES = (ast.Module, *_SCOPE_STOP_NODES)
def _iter_lexical_scope_chain(
    node: ast.AST,
    parent_of: Callable[[ast.AST], ast.AST | None],
) -> Iterator[ast.AST]:
    innermost: ast.AST | None = None
    cur = parent_of(node)
    while cur is not None:
        if isinstance(cur, _SCOPE_CHAIN_NODES):
            if isinstance(cur, ast.ClassDef) and innermost is not None:
                cur = parent_of(cur)
                continue
            yield cur
            innermost = cur
        cur = parent_of(cur)
def scope_chain(node: ast.AST, parents: dict) -> list[ast.AST]:
    return list(_iter_lexical_scope_chain(
        node, lambda cur: parents.get(id(cur))))
def subscript_base_node(t: ast.AST) -> ast.AST:
    while isinstance(t, ast.Subscript):
        t = t.value
    return t
def subscript_base_name(t: ast.AST) -> str | None:
    base = subscript_base_node(t)
    return base.id if isinstance(base, ast.Name) else None
def kw_arg(node: ast.Call, arg_name: str) -> ast.keyword | None:
    return next((kw for kw in node.keywords if kw.arg == arg_name), None)
def _loop_try_has_break(node: ast.AST) -> bool:
    if (node.finalbody
            and not block_may_fall_through(node.finalbody)):
        return loop_body_has_break(node.finalbody)
    if loop_body_has_break(node.body):
        return True
    if (block_may_fall_through(node.body)
            and loop_body_has_break(node.orelse)):
        return True
    if any(loop_body_has_break(handler.body)
           for handler in node.handlers):
        return True
    return loop_body_has_break(node.finalbody)
def _loop_stmt_has_break(node: ast.AST) -> bool:
    if isinstance(node, ast.Break):
        return True
    if isinstance(node, _SCOPE_STOP_NODES):
        return False
    if isinstance(node, ast.If):
        if isinstance(node.test, ast.Constant):
            branch = node.body if bool(node.test.value) else node.orelse
            return loop_body_has_break(branch)
        return (loop_body_has_break(node.body)
                or loop_body_has_break(node.orelse))
    if isinstance(node, ast.While):
        if (isinstance(node.test, ast.Constant)
                and bool(node.test.value)):
            return False
        return loop_body_has_break(node.orelse)
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return loop_body_has_break(node.orelse)
    if isinstance(node, TRY_NODE_TYPES):
        return _loop_try_has_break(node)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return loop_body_has_break(node.body)
    if isinstance(node, ast.Match):
        return any(loop_body_has_break(case.body)
                   for case in _reachable_match_cases(node))
    return False
def loop_body_has_break(stmts: Iterable[ast.AST]) -> bool:
    for stmt in stmts:
        if _loop_stmt_has_break(stmt):
            return True
        if not _stmt_may_fall_through(stmt):
            return False
    return False
def _irrefutable_pattern(pattern: ast.AST) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return pattern.pattern is None
    return (isinstance(pattern, ast.MatchOr)
            and any(_irrefutable_pattern(sub) for sub in pattern.patterns))
def _irrefutable_case(case: ast.match_case) -> bool:
    return case.guard is None and _irrefutable_pattern(case.pattern)
def _reachable_match_cases(node: ast.Match) -> Iterator[ast.AST]:
    for case in node.cases:
        yield case
        if _irrefutable_case(case):
            break
def _last_stmt_or_fallthrough(body: list[ast.stmt]) -> ast.stmt | bool:
    if not body:
        return True
    if not block_may_fall_through(body[:-1]):
        return False
    return body[-1]
def _loop_fallthrough_kids(stmt: ast.stmt, stack: list) -> list | None:
    if isinstance(stmt, ast.While) and isinstance(stmt.test, ast.Constant):
        if bool(stmt.test.value):
            stack.append(('val', loop_body_has_break(stmt.body)))
            return None
        return [_last_stmt_or_fallthrough(stmt.orelse)]
    if loop_body_has_break(stmt.body) or not stmt.orelse:
        stack.append(('val', True))
        return None
    return [_last_stmt_or_fallthrough(stmt.orelse)]
def _try_fallthrough_kids(stmt: ast.stmt) -> list:
    kids = [_last_stmt_or_fallthrough(stmt.body),
            _last_stmt_or_fallthrough(stmt.orelse)]
    kids.extend(_last_stmt_or_fallthrough(handler.body)
                for handler in stmt.handlers)
    if stmt.finalbody:
        kids.append(_last_stmt_or_fallthrough(stmt.finalbody))
    return kids
def _fallthrough_kids(stmt: ast.stmt, stack: list) -> list | None:
    if isinstance(stmt, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
        stack.append(('val', False))
        return None
    if isinstance(stmt, TRY_NODE_TYPES):
        return _try_fallthrough_kids(stmt)
    if isinstance(stmt, ast.If):
        if isinstance(stmt.test, ast.Constant):
            branch = stmt.body if bool(stmt.test.value) else stmt.orelse
            return [_last_stmt_or_fallthrough(branch)]
        if not stmt.orelse:
            stack.append(('val', True))
            return None
        return [_last_stmt_or_fallthrough(stmt.body),
                _last_stmt_or_fallthrough(stmt.orelse)]
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return [_last_stmt_or_fallthrough(stmt.body)]
    if isinstance(stmt, ast.Match):
        cases = list(_reachable_match_cases(stmt))
        if not cases:
            stack.append(('val', True))
            return None
        return [_last_stmt_or_fallthrough(case.body) for case in cases]
    if isinstance(stmt, (ast.While, ast.For, ast.AsyncFor)):
        return _loop_fallthrough_kids(stmt, stack)
    stack.append(('val', True))
    return None
def _combine_fallthrough(stmt: ast.stmt, results: list[bool]) -> bool:
    if isinstance(stmt, ast.If):
        return any(results)
    if isinstance(stmt, (ast.With, ast.AsyncWith,
                         ast.While, ast.For, ast.AsyncFor)):
        return results[0]
    if isinstance(stmt, TRY_NODE_TYPES):
        if stmt.finalbody and not results[-1]:
            return False
        normal_path = results[0] and results[1]
        handler_path = any(results[2:2 + len(stmt.handlers)])
        return normal_path or handler_path
    if isinstance(stmt, ast.Match):
        if any(results):
            return True
        return not any(_irrefutable_case(case) for case in stmt.cases)
    return True
def _expand_fallthrough(stmt: ast.stmt, stack: list) -> None:
    kids = _fallthrough_kids(stmt, stack)
    if kids is None:
        return
    stack.append(('combine', stmt, len(kids)))
    for kid in reversed(kids):
        stack.append(
            ('val', kid) if isinstance(kid, bool) else ('eval', kid))
def _stmt_may_fall_through(stmt: ast.stmt) -> bool:
    stack: list[tuple] = [('eval', stmt)]
    values: list[bool] = []
    while stack:
        task = stack.pop()
        op = task[0]
        if op == 'val':
            values.append(task[1])
        elif op == 'combine':
            n = task[2]
            results = values[-n:] if n else []
            if n:
                del values[-n:]
            values.append(_combine_fallthrough(task[1], results))
        else:
            _expand_fallthrough(task[1], stack)
    return values[-1]
def block_may_fall_through(stmts: list[ast.stmt]) -> bool:
    for stmt in stmts:
        if not _stmt_may_fall_through(stmt):
            return False
    return True
def comp_target_names(node: ast.AST) -> set[str]:
    return {name for gen in node.generators
            for name in iter_unpack_target_names(gen.target)}
def comp_element_roots(comp: ast.AST) -> list[ast.AST]:
    if isinstance(comp, ast.DictComp):
        return [comp.key, comp.value]
    return [comp.elt]
def _shadow_bindings(node: ast.AST) -> frozenset[str]:
    if isinstance(node, COMP_SCOPE_NODES):
        return frozenset(comp_target_names(node))
    if isinstance(node, ast.Lambda):
        return frozenset(collect_param_names(node))
    return frozenset()
def root_binding_shadow(root: ast.AST,
                         shadowed: frozenset[str]) -> frozenset[str]:
    extra = _shadow_bindings(root)
    return shadowed | extra if extra else shadowed
def iter_scope_nodes_with_shadow(
    scope: ast.AST,
    shadowed: frozenset[str] = frozenset(),
) -> Iterator[tuple[ast.AST, frozenset[str]]]:
    frames = (frozenset(shadowed),)
    initial = _shadow_bindings(scope)
    if initial:
        frames += (initial,)
    for node, node_frames in _iter_frame_raw(
            scope, SHADOW_SCOPE_STOP, yield_stop=True,
            state=frames, enter=_shadow_child_state):
        yield node, _shadow_visible_names(node_frames)
def _shadow_visible_names(
    frames: tuple[frozenset[str], ...],
) -> frozenset[str]:
    return frozenset(name for frame in frames for name in frame)
def _push_shadow_frame(
    frames: tuple[frozenset[str], ...], node: ast.AST,
) -> tuple[frozenset[str], ...]:
    bindings = _shadow_bindings(node)
    return (*frames, bindings) if bindings else frames
def _shadow_child_state(
    parent: ast.AST, child: ast.AST,
    frames: tuple[frozenset[str], ...],
) -> tuple[frozenset[str], ...]:
    if isinstance(parent, COMP_SCOPE_NODES) and isinstance(
            child, ast.comprehension):
        targets = frozenset()
        for generator in parent.generators:
            targets |= frozenset(iter_unpack_target_names(generator.target))
            if generator is child:
                return (*frames[:-1], targets)
    if isinstance(parent, ast.comprehension) and child is parent.iter:
        current = frozenset(iter_unpack_target_names(parent.target))
        frames = (*frames[:-1], frames[-1] - current)
    elif isinstance(parent, ast.Lambda) and child is parent.args:
        current = frozenset(collect_param_names(parent))
        frames = (*frames[:-1], frames[-1] - current)
    return _push_shadow_frame(frames, child)
def in_subtree(node: ast.AST, root: ast.AST) -> bool:
    return any(node is n for n in walk_nodes(root))
def subtree_node_ids(roots: Iterable[ast.AST]) -> set[int]:
    ids: set[int] = set()
    for root in roots:
        ids.update(id(sub) for sub in walk_nodes(root))
    return ids
def _inside_function_body(scope: ast.AST, child: ast.AST) -> bool:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return child in scope.body
    return child is scope.body
def _is_outer_comprehension_iter(scope: ast.AST, child: ast.AST,
                                 below: ast.AST | None) -> bool:
    return bool(
        isinstance(child, ast.comprehension)
        and scope.generators
        and child is scope.generators[0]
        and below is child.iter
    )
def _crossed_evaluation_scope(scope: ast.AST, child: ast.AST,
                              below: ast.AST | None, chain: list,
                              crossed_class_barrier: bool) -> bool:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        if not _inside_function_body(scope, child):
            return crossed_class_barrier
        chain.append(scope)
        return True
    if isinstance(scope, COMP_SCOPE_NODES):
        return (crossed_class_barrier
                or not _is_outer_comprehension_iter(scope, child, below))
    if isinstance(scope, ast.ClassDef):
        if child in scope.body:
            if not crossed_class_barrier:
                chain.append(scope)
            return True
        return crossed_class_barrier
    if isinstance(scope, ast.Module):
        chain.append(scope)
    return crossed_class_barrier
def _evaluation_scope_chain(
    node: ast.AST,
    parent_of: Callable[[ast.AST], ast.AST | None],
) -> list:
    chain: list = []
    crossed_class_barrier = False
    current = parent_of(node)
    child = node
    below = None
    while current is not None:
        crossed_class_barrier = _crossed_evaluation_scope(
            current, child, below, chain, crossed_class_barrier)
        below = child
        child = current
        current = parent_of(current)
    return chain
def iter_evaluation_scope_chain(node: ast.AST, parents: dict) -> list:
    return _evaluation_scope_chain(node, lambda cur: parents.get(id(cur)))
def walk_stmts(stmts: Iterable[ast.AST]) -> Iterator[ast.AST]:
    _dq = deque(stmts)
    while _dq:
        _n = _dq.popleft()
        if isinstance(_n, _SCOPE_STOP_NODES):
            continue
        yield _n
        _dq.extend(ast.iter_child_nodes(_n))
def iter_module_stmt_blocks(stmt: ast.AST) -> Iterator[list]:
    body = getattr(stmt, "body", None)
    if body is not None:
        yield body
    for handler in getattr(stmt, "handlers", ()) or ():
        yield handler.body
    for attr in ("orelse", "finalbody"):
        block = getattr(stmt, attr, None)
        if block is not None:
            yield block
    for case in getattr(stmt, "cases", ()) or ():
        yield case.body
def iter_module_level_stmts(tree: ast.AST) -> Iterator[ast.AST]:
    queue = deque(getattr(tree, "body", ()))
    while queue:
        node = queue.popleft()
        yield node
        if isinstance(node, _SCOPE_STOP_NODES):
            continue
        for block in iter_module_stmt_blocks(node):
            queue.extend(block)
def _push_stmts(stack, stmts, in_handler: bool) -> None:
    for s in reversed(stmts or []):
        stack.append((s, in_handler))
def _push_try_children(stack, node, in_handler: bool) -> None:
    _push_stmts(stack, getattr(node, "finalbody", None), in_handler)
    _push_stmts(stack, getattr(node, "orelse", None), in_handler)
    _push_stmts(stack, node.handlers, in_handler)
    _push_stmts(stack, getattr(node, "body", None), in_handler)
def _push_composite_children(stack, node, in_handler: bool) -> None:
    for attr in ("finalbody", "orelse", "body"):
        _push_stmts(stack, getattr(node, attr, None), in_handler)
def _push_case_bodies(stack, node, in_handler: bool) -> None:
    for case in reversed(getattr(node, "cases", None) or ()):
        _push_stmts(stack, getattr(case, "body", None), in_handler)
def iter_scope_statements(scope_node: Any, *,
                          include_defs: bool = False
                          ) -> Iterator[tuple[ast.AST, bool]]:
    body = getattr(scope_node, "body", None)
    if not isinstance(body, list):
        return
    stack = [(n, False) for n in reversed(body)]
    while stack:
        node, in_handler = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            if include_defs and not isinstance(node, ast.Lambda):
                yield node, in_handler
            continue
        if isinstance(node, ast.ExceptHandler):
            yield node, in_handler
            _push_stmts(stack, node.body, True)
            continue
        yield node, in_handler
        if isinstance(node, TRY_NODE_TYPES):
            _push_try_children(stack, node, in_handler)
        else:
            _push_composite_children(stack, node, in_handler)
        _push_case_bodies(stack, node, in_handler)
def _dispatch_visit_methods(klass: type, table: dict) -> None:
    for name, fn in vars(klass).items():
        if not name.startswith("visit_") or not callable(fn):
            continue
        node_type = getattr(ast, name[len("visit_"):], None)
        if isinstance(node_type, type):
            table[node_type] = fn
def build_node_dispatch(visitor_cls: type) -> dict:
    table: dict = {}
    for klass in reversed(visitor_cls.__mro__):
        if klass is ast.NodeVisitor or klass is object:
            continue
        _dispatch_visit_methods(klass, table)
    return table
@contextlib.contextmanager
def class_scope(visitor: ast.NodeVisitor, node: ast.ClassDef,
                attr: str = "_current_class") -> Iterator[None]:
    previous = getattr(visitor, attr, None)
    setattr(visitor, attr, node.name)
    try:
        yield
    finally:
        setattr(visitor, attr, previous)
class FastDispatchNodeVisitor(ast.NodeVisitor):
    def visit(self, node):
        cls = type(self)
        table = cls.__dict__.get("_NODE_DISPATCH")
        if table is None:
            table = build_node_dispatch(cls)
            cls._NODE_DISPATCH = table
        h = table.get(node.__class__)
        if h is None:
            return self.generic_visit(node)
        return h(self, node)
TRY_STAR: type = TRY_NODE_TYPES[-1]
def is_shell_true_keyword(kw: Any) -> bool:
    if getattr(kw, "arg", None) != "shell":
        return False
    value = kw.value
    if isinstance(value, ast.Constant):
        return bool(value.value)
    if isinstance(value, ast.UnaryOp) and isinstance(
            value.op, (ast.USub, ast.UAdd)):
        operand = value.operand
        if (isinstance(operand, ast.Constant)
                and isinstance(operand.value, (int, float))):
            return bool(-operand.value if isinstance(value.op, ast.USub)
                        else operand.value)
    return False
def is_static_literal_expr(node: ast.AST) -> bool:
    stack: list[ast.AST] = [node]
    while stack:
        sub = stack.pop()
        if isinstance(sub, ast.Constant):
            continue
        if isinstance(sub, ast.BinOp):
            stack.append(sub.left)
            stack.append(sub.right)
            continue
        if isinstance(sub, ast.UnaryOp):
            stack.append(sub.operand)
            continue
        if isinstance(sub, ast.JoinedStr):
            for value in sub.values:
                if isinstance(value, ast.Constant):
                    continue
                if not isinstance(value, ast.FormattedValue):
                    return False
                stack.append(value.value)
                if value.format_spec is not None:
                    stack.append(value.format_spec)
            continue
        return False
    return True
_MATCH = getattr(ast, "Match", None)
_MATCH_CASE = getattr(ast, "match_case", None)
_COGNITIVE_BREAK_FLOW = {
    ast.Break, ast.Continue, ast.Raise,
    ast.Return,
}
_COGNITIVE_INCREMENT_NODES = {
    ast.If, ast.While, ast.For, ast.AsyncFor,
    ast.ExceptHandler, ast.With, ast.AsyncWith,
    ast.BoolOp,
    ast.IfExp,
}
if _MATCH_CASE is not None:
    _COGNITIVE_INCREMENT_NODES.add(_MATCH_CASE)
_COGNITIVE_INCREMENT_TUPLE = tuple(_COGNITIVE_INCREMENT_NODES)
_COGNITIVE_BREAK_TUPLE = tuple(_COGNITIVE_BREAK_FLOW)
_COGNITIVE_NESTING_TUPLE = (
    ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
    ast.Try, TRY_STAR, ast.ExceptHandler,
) + ((_MATCH_CASE,) if _MATCH_CASE is not None else ())
def _cognitive_child_frame(child: ast.AST, nest: int) -> tuple[int, int]:
    child_inc = 0
    if isinstance(child, _COGNITIVE_INCREMENT_TUPLE):
        child_inc = 1 + nest
    if isinstance(child, _COGNITIVE_BREAK_TUPLE) and nest > 0:
        child_inc += 1
    child_nest = nest + 1 if isinstance(
        child, _COGNITIVE_NESTING_TUPLE) else nest
    return child_inc, child_nest
def _metric_skips_child(root: ast.AST, child: ast.AST) -> bool:
    return (isinstance(root, (*FUNC_NODE_TYPES, ast.Lambda))
            and isinstance(child, _SCOPE_STOP_NODES))
def _iter_metric_nodes(root: ast.AST):
    stack: list[ast.AST] = [root]
    while stack:
        cur = stack.pop()
        yield cur
        for child in ast.iter_child_nodes(cur):
            if _metric_skips_child(root, child):
                continue
            stack.append(child)
def cognitive_complexity(node: ast.AST, nesting: int = 0) -> int:
    result = 0
    stack: list[tuple[ast.AST, int]] = [(node, nesting)]
    while stack:
        cur, nest = stack.pop()
        for child in ast.iter_child_nodes(cur):
            if _metric_skips_child(node, child):
                continue
            child_inc, child_nest = _cognitive_child_frame(child, nest)
            result += child_inc
            stack.append((child, child_nest))
    return result
_CYCLOMATIC_BRANCH_TUPLE = (
    ast.If, ast.For, ast.While, ast.AsyncFor, ast.ExceptHandler,
) + ((_MATCH_CASE,) if _MATCH_CASE is not None else ())
def _cyclomatic_increment(child: ast.AST) -> int:
    if isinstance(child, _CYCLOMATIC_BRANCH_TUPLE):
        return 1
    if isinstance(child, ast.BoolOp):
        return len(child.values) - 1
    if isinstance(child, COMP_SCOPE_NODES):
        return len(child.generators) + sum(
            len(gen.ifs) for gen in child.generators)
    return 0
def cyclomatic_complexity(node: ast.AST, node_iter=None) -> int:
    iterator = _iter_metric_nodes(node) if node_iter is None else node_iter(node)
    return 1 + sum(_cyclomatic_increment(child) for child in iterator)
_PROFILE_DECISION_TUPLE = (
    ast.If, ast.For, ast.AsyncFor, ast.While, ast.ExceptHandler, ast.IfExp,
)
def _profile_decision_increment(child: ast.AST) -> int:
    if isinstance(child, _PROFILE_DECISION_TUPLE):
        return 1
    if isinstance(child, ast.BoolOp):
        return len(child.values) - 1
    if isinstance(child, ast.comprehension):
        return 1 + len(child.ifs)
    if _MATCH_CASE is not None and isinstance(child, _MATCH_CASE):
        return 1
    return 0
def decision_points(node: ast.AST, node_iter=None) -> int:
    iterator = _iter_metric_nodes(node) if node_iter is None else node_iter(node)
    return sum(_profile_decision_increment(child) for child in iterator)
_NO_CLASS_DEFAULT = object()
def dump_len(node, limit: int) -> int:
    try:
        return _dump_len_recur(node, limit)
    except RecursionError as _e:
        logger.debug('静默降级[dump_len:RecursionError]: %s: %s', type(_e).__name__, _e)
        return -1
def _dump_len_add(item, total: int, limit: int) -> int:
    sub = dump_len(item, limit)
    if sub < 0:
        return -1
    total += sub
    return total if total <= limit else -1
def _dump_len_ast_fields(node: ast.AST, total: int, limit: int) -> int:
    cls = type(node)
    fields = [fv for fv in ast.iter_fields(node)
              if fv[1] is not None
              or getattr(cls, fv[0], _NO_CLASS_DEFAULT) is _NO_CLASS_DEFAULT]
    if not fields:
        return total
    total += 2 * (len(fields) - 1)
    for name, value in fields:
        total += len(name) + 1
        total = _dump_len_add(value, total, limit)
        if total < 0:
            return -1
    return total
def _dump_len_recur(node, limit) -> int:
    if isinstance(node, ast.AST):
        head = len(node.__class__.__name__) + 2
        total = _dump_len_ast_fields(node, head, limit)
        if total < 0 or total > limit:
            return -1
        return total
    if isinstance(node, list):
        return _dump_len_list_sum(node, limit)
    length = len(repr(node))
    return length if length <= limit else -1
def _dump_len_list_sum(node: list, limit: int) -> int:
    if not node:
        return 2 if limit >= 2 else -1
    total = 2 + 2 * (len(node) - 1)
    for item in node:
        total = _dump_len_add(item, total, limit)
        if total < 0:
            return -1
    return total
_NESTING_INCREMENT_NODES = {
    ast.If, ast.For, ast.While, ast.Try, TRY_STAR, ast.With,
    ast.AsyncFor, ast.AsyncWith, ast.ExceptHandler,
}
if _MATCH is not None:
    _NESTING_INCREMENT_NODES.add(_MATCH)
_NESTING_INCREMENT_TUPLE = tuple(_NESTING_INCREMENT_NODES)
def calc_nesting(node: ast.AST) -> int:
    max_depth = 0
    stack = [(node, 0)]
    while stack:
        cur, depth = stack.pop()
        if cur is not node and isinstance(cur, _SCOPE_STOP_NODES):
            continue
        if isinstance(cur, _NESTING_INCREMENT_TUPLE):
            depth += 1
            max_depth = max(max_depth, depth)
        for child in ast.iter_child_nodes(cur):
            stack.append((child, depth))
    return max_depth
_MATCH_METHODS = ('group', 'groups', 'groupdict', 'start', 'end', 'span')
def _is_dunder_name_node(node: ast.AST) -> bool:
    return isinstance(node, ast.Name) and node.id == '__name__'
def _is_main_module_const(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and node.value == '__main__'
def _main_compare_parts(
    test: ast.AST,
) -> tuple[ast.AST, ast.cmpop, ast.AST] | None:
    if (not isinstance(test, ast.Compare) or len(test.ops) != 1
            or len(test.comparators) != 1):
        return None
    return test.left, test.ops[0], test.comparators[0]
def _is_main_equality(left: ast.AST, right: ast.AST) -> bool:
    return ((_is_dunder_name_node(left) and _is_main_module_const(right))
            or (_is_main_module_const(left) and _is_dunder_name_node(right)))
def is_main_check(test: ast.AST) -> bool:
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        return any(is_main_check(value) for value in test.values)
    parts = _main_compare_parts(test)
    if parts is None:
        return False
    left, op, right = parts
    if isinstance(op, ast.In):
        return (_is_dunder_name_node(left)
                and isinstance(right, (ast.Tuple, ast.List, ast.Set))
                and any(_is_main_module_const(node) for node in right.elts))
    return isinstance(op, ast.Eq) and _is_main_equality(left, right)
def main_guard_branch(test: ast.AST) -> bool | None:
    parts = _main_compare_parts(test)
    if parts is None:
        return None
    left, op, right = parts
    if not _is_main_equality(left, right):
        return None
    if isinstance(op, ast.Eq):
        return True
    if isinstance(op, ast.NotEq):
        return False
    return None
def main_guard_node_ids(tree: ast.AST) -> frozenset[int]:
    """``if __name__ == "__main__":`` 守卫体内全部节点的 id 集合。

    守卫体是「进程入口」而不是「模块导入副作用」：其中的 ``sys.exit(...)``、
    ``main()`` 等调用只在直接执行脚本时发生，``import`` 该模块不会触发。
    任何以「模块级调用」为判据的规则都应先扣除这部分节点。
    """
    ids: set[int] = set()
    for node in getattr(tree, "body", ()):
        if (not isinstance(node, ast.If)
                or main_guard_branch(node.test) is not True):
            continue
        for stmt in node.body:
            for sub in walk_nodes(stmt):
                ids.add(id(sub))
    return frozenset(ids)


def is_match_method(attr: str) -> bool:
    return attr in _MATCH_METHODS
def collect_import_bindings(
        content: str,
        tree: ast.Module | None = None,
) -> tuple[dict[str, str], dict[str, str], set[str]]:
    module_aliases: dict[str, str] = {}
    from_imports: dict[str, str] = {}
    star_modules: set[str] = set()
    if tree is None:
        tree, failure = parse_ast_safely(content)
        if tree is None:
            log_swallowed(__name__, failure or ValueError("unparseable"),
                          context='import_bindings:parse')
            return module_aliases, from_imports, star_modules
    # 只收集模块级绑定：函数/类体 import 在模块作用域不可见，若按
    # walk_nodes 全树合并会让内层别名覆盖模块级别名（如类体内
    # ``import subprocess as os`` 覆盖模块级 ``import os``），导致
    # 危险调用解析漏报。iter_module_level_stmts 会保留 if/try/with
    # 等模块级块，只跳过 FunctionDef/AsyncFunctionDef/ClassDef/Lambda。
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.Import):
            _bindings_from_import(node, module_aliases)
        elif isinstance(node, ast.ImportFrom):
            _bindings_from_import_from(node, from_imports, star_modules)
    return module_aliases, from_imports, star_modules
def _bindings_from_import(node: ast.Import,
                           module_aliases: dict[str, str]) -> None:
    for alias in node.names:
        if alias.asname:
            module_aliases[alias.asname] = alias.name
            continue
        root = alias.name.split('.', 1)[0]
        module_aliases[root] = root
def _bindings_from_import_from(node: ast.ImportFrom,
                                from_imports: dict[str, str],
                                star_modules: set[str]) -> None:
    if not node.module or node.level:
        return
    for alias in node.names:
        if alias.name == "*":
            star_modules.add(node.module)
        else:
            from_imports[alias.asname or alias.name] = (
                f"{node.module}.{alias.name}")
def resolve_import_binding(tables: dict, pm: dict, query_node: ast.AST,
                           name: str):
    for scope in _evaluation_scope_chain(query_node, pm.get):
        rec = tables.get(scope, {}).get(name)
        if rec is not None:
            return rec
    return None
def is_docstring_stmt(node: ast.AST) -> bool:
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str))
def _except_type_tail(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None
def handler_exc_names(handler: ast.ExceptHandler) -> list[str]:
    if handler.type is None:
        return ['BaseException']
    tails: list[str] = []
    stack: list[ast.AST] = [handler.type]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Tuple):
            stack.extend(reversed(node.elts))
            continue
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            stack.extend((node.right, node.left))
            continue
        tail = _except_type_tail(node)
        if tail and tail not in tails:
            tails.append(tail)
    return tails
def is_safe_yaml_loader(value: ast.AST) -> bool:
    if isinstance(value, ast.Attribute):
        return value.attr in YAML_SAFE_LOADERS
    if isinstance(value, ast.Name):
        return value.id in YAML_SAFE_LOADERS
    return False
def is_star_import(node: ast.AST) -> bool:
    return (isinstance(node, ast.ImportFrom)
            and any(alias.name == "*" for alias in node.names))
def import_alias_bound_name(alias: ast.alias, *,
                            from_import: bool) -> str | None:
    if from_import and alias.name == '*':
        return None
    if alias.asname:
        return alias.asname
    return alias.name if from_import else alias.name.split('.')[0]
def import_alias_bound_names(node: ast.Import | ast.ImportFrom) -> list[str]:
    from_import = isinstance(node, ast.ImportFrom)
    out: list[str] = []
    for alias in node.names:
        bound = import_alias_bound_name(alias, from_import=from_import)
        if bound is not None:
            out.append(bound)
    return out
_IMPORT_ERROR_NAMES = frozenset({"ImportError", "ModuleNotFoundError"})

def _handler_catches_import_error(handler: ast.ExceptHandler) -> bool:
    if handler.type is None:
        return False
    return bool(_IMPORT_ERROR_NAMES.intersection(handler_exc_names(handler)))

def _stmt_import_heads(stmt: ast.AST) -> tuple[bool, list[str]]:
    if isinstance(stmt, ast.ImportFrom):
        return stmt.level > 0, ([stmt.module.split(".")[0]] if stmt.module else [])
    if isinstance(stmt, ast.Import):
        return False, [alias.name.split(".")[0] for alias in stmt.names]
    return False, []

def import_fallback_import_lines(tree: ast.AST) -> dict[int, str]:
    """``try: from .x import A / except ImportError: from x import A`` 的兜底导入行。

    双模式技能（既能 ``python -m pkg.mod`` 也能 ``python scripts/mod.py``）
    的标准写法：相对导入失败时回退到裸模块名。回退分支里的裸导入是**有意
    为之**——它既不是「绕过包边界」（GF-16）也不是「未指定包前缀」（IA-01）。
    不识别这一形态时，每个双模式模块的每一处回退导入都会被报成缺陷。

    返回 ``{行号: 模块头段名}``；没有 ``try`` 内相对导入作前提的回退不算。
    """
    lines: dict[int, str] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, TRY_NODE_TYPES):
            continue
        has_relative = False
        for stmt in node.body:
            for sub in walk_stmts((stmt,)):
                if _stmt_import_heads(sub)[0]:
                    has_relative = True
                    break
            if has_relative:
                break
        if not has_relative:
            continue
        for handler in node.handlers:
            if not _handler_catches_import_error(handler):
                continue
            for stmt in handler.body:
                for sub in walk_stmts((stmt,)):
                    _rel, heads = _stmt_import_heads(sub)
                    if heads and isinstance(sub, (ast.Import, ast.ImportFrom)):
                        lines.setdefault(sub.lineno, heads[0])
    return lines

_MUTABLE_DEFAULT_NODES = (ast.List, ast.Dict, ast.Set,
                          ast.ListComp, ast.DictComp, ast.SetComp)
_MUTABLE_DEFAULT_CTORS = frozenset({"list", "dict", "set", "bytearray"})
def is_mutable_default(node: ast.AST | None) -> bool:
    if isinstance(node, _MUTABLE_DEFAULT_NODES):
        return True
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in _MUTABLE_DEFAULT_CTORS):
        return True
    if isinstance(node, ast.Tuple):
        return any(is_mutable_default(elt) for elt in node.elts)
    if isinstance(node, ast.BinOp) and isinstance(
            node.op, (ast.Add, ast.Mult, ast.BitOr,
                      ast.BitAnd, ast.Sub, ast.BitXor)):
        return (is_mutable_default(node.left)
                or is_mutable_default(node.right))
    return False
def empty_container_ctor_name(node: ast.AST | None) -> str | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)):
        return None
    if node.func.id not in _MUTABLE_DEFAULT_CTORS:
        return None
    if node.args or node.keywords:
        return None
    return node.func.id
_RCN_MISSING = object()
def resolve_call_name(node: ast.AST) -> str:
    _cached = getattr(node, "_jwsgj_rcn", _RCN_MISSING)
    if _cached is not _RCN_MISSING:
        return _cached
    _func = getattr(node, "func", None)
    if isinstance(_func, ast.Attribute):
        _name = dotted_name(_func, constant_base=True)
    elif isinstance(_func, ast.Name):
        _name = _func.id
    else:
        _name = ""
    with contextlib.suppress(AttributeError, TypeError):
        node._jwsgj_rcn = _name
    return _name
def get_call_name(call: ast.Call) -> str | None:
    return resolve_call_name(call) or None
def call_tail_name(call: ast.Call) -> str:
    func = getattr(call, "func", None)
    if isinstance(func, ast.Attribute):
        return func.attr
    if isinstance(func, ast.Name):
        return func.id
    return ""
def call_arg_values(call: ast.Call) -> list[ast.expr]:
    return list(call.args) + [
        kw.value for kw in call.keywords if kw.value is not None]
def resolve_module_member_call(node: ast.AST, receivers: set, allowed: tuple,
                               from_map: dict) -> str | None:
    func = getattr(node, "func", None)
    if isinstance(func, ast.Attribute):
        if (isinstance(func.value, ast.Name)
                and func.value.id in receivers
                and func.attr in allowed):
            return func.attr
        return None
    if isinstance(func, ast.Name):
        member = from_map.get(func.id)
        if not isinstance(member, str) or not member:
            return None
        tail = member.rsplit(".", 1)[-1]
        return tail if tail in allowed else None
    return None
def _is_mod_format_concat(node: ast.BinOp) -> bool:
    if isinstance(node.left, ast.Constant):
        return isinstance(node.left.value, str)
    return True
def _fstring_is_unsafe_concat(node: ast.JoinedStr) -> bool:
    if not any(isinstance(v, ast.FormattedValue) for v in node.values):
        return False
    return not is_static_literal_expr(node)
def _is_format_call_concat(node: ast.Call) -> bool:
    name = resolve_call_name(node)
    return name == 'format' or name.endswith('.format')
def _add_chain_is_concat(node: ast.BinOp) -> bool:
    has_str_leaf = False
    has_dynamic_leaf = False
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Add):
            stack.append(cur.left)
            stack.append(cur.right)
            continue
        if isinstance(cur, ast.Constant):
            if isinstance(cur.value, str):
                has_str_leaf = True
            continue
        if isinstance(cur, ast.JoinedStr):
            has_str_leaf = True
            if _fstring_is_unsafe_concat(cur):
                has_dynamic_leaf = True
            continue
        has_dynamic_leaf = True
    return has_str_leaf and has_dynamic_leaf
def _open_call_has_encoding(node: ast.Call) -> bool:
    if len(node.args) >= 4 and not is_none_literal(node.args[3]):
        return True
    return any(kw.arg == "encoding" and not is_none_literal(kw.value)
               for kw in node.keywords)
def _open_call_is_binary_mode(node: ast.Call) -> bool:
    if len(node.args) >= 2:
        mode = str_constant_value(node.args[1])
        if mode is not None and 'b' in mode:
            return True
    return any(kw.arg == "mode" and 'b' in (str_constant_value(kw.value) or '')
               for kw in node.keywords)
def _is_open_call(node: ast.Call) -> bool:
    fn = node.func
    if isinstance(fn, ast.Name):
        return fn.id == "open"
    if isinstance(fn, ast.Attribute):
        return (isinstance(fn.value, ast.Name)
                and fn.value.id in ("builtins", "io")
                and fn.attr == "open")
    return False
def _open_call_has_file_arg(node: ast.Call) -> bool:
    return bool(node.args) or any(kw.arg == "file" for kw in node.keywords)
def _open_call_has_dynamic_args(node: ast.Call) -> bool:
    return (any(isinstance(a, ast.Starred) for a in node.args)
            or any(kw.arg is None for kw in node.keywords))
def _open_call_needs_encoding(node: ast.Call) -> bool:
    return (_is_open_call(node)
            and _open_call_has_file_arg(node)
            and not _open_call_has_dynamic_args(node)
            and not _open_call_has_encoding(node)
            and not _open_call_is_binary_mode(node))
def open_calls_missing_encoding(tree: ast.AST) -> list:
    return [node for node in walk_nodes(tree)
            if isinstance(node, ast.Call)
            and _open_call_needs_encoding(node)]
class ASTPreciseParser:
    @staticmethod
    def parse(code: str, filepath: str = "") -> ast.Module | None:
        if filepath:
            return parse_source_tree(code, filepath)
        return parse_py_source(code)
    @staticmethod
    def is_string_concatenation(node: ast.AST) -> bool:
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
            return _is_mod_format_concat(node)
        if isinstance(node, ast.JoinedStr):
            return _fstring_is_unsafe_concat(node)
        if isinstance(node, ast.Call):
            return _is_format_call_concat(node)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return _add_chain_is_concat(node)
        return False
def is_constant_expr_stmt(stmt: ast.AST) -> bool:
    return isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
def is_type_checking_guard(
    test: ast.expr,
    typing_aliases: set[str] | None = None,
    type_checking_names: set[str] | None = None,
) -> bool:
    if isinstance(test, ast.Name):
        names = ({"TYPE_CHECKING"} if type_checking_names is None
                 else type_checking_names)
        return test.id in names
    if not (isinstance(test, ast.Attribute) and test.attr == "TYPE_CHECKING"):
        return False
    if typing_aliases is None:
        return True
    return isinstance(test.value, ast.Name) and test.value.id in typing_aliases
def _type_checking_guard_polarity(
    test: ast.expr,
    typing_aliases: set[str] | None = None,
    type_checking_names: set[str] | None = None,
) -> bool | None:
    negated = False
    while isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        negated = not negated
        test = test.operand
    if is_type_checking_guard(test, typing_aliases, type_checking_names):
        return negated
    return None
_OWN_SCOPE_MEMO_ATTR = "_jwsgj_own_scope_memo"
def iter_own_scope(node: ast.AST, *, skip_lambda: bool = False,
                    skip_type_checking_body: bool = False,
                    include_self: bool = False,
                    tc_polarities: dict[int, bool] | None = None):
    """自身作用域节点（不进入嵌套函数/类体）。

    ``tc_polarities`` 为可选的 ``{id(If): polarity}``（来自
    ``_type_checking_guard_node_polarities(tree)``）：传入后
    ``skip_type_checking_body`` 能识别 ``from typing import TYPE_CHECKING as TC``
    这类裸名别名；不传则沿用无极性回退（仅认裸名 TYPE_CHECKING 与任意
    ``X.TYPE_CHECKING`` 属性）。无极性时作用于 Module 的调用方应传入。
    """
    memo = getattr(node, _OWN_SCOPE_MEMO_ATTR, None)
    if memo is None:
        try:
            memo = {}
            setattr(node, _OWN_SCOPE_MEMO_ATTR, memo)
        except (AttributeError, TypeError) as _memo_err:
            logger.debug("自身作用域 memo setattr 失败，降级直算（无 memo）: %s", _memo_err)
            memo = None
    polarity_key = (None if tc_polarities is None
                    else frozenset(tc_polarities.items()))
    key = (bool(skip_lambda), bool(skip_type_checking_body),
           bool(include_self), polarity_key)
    if memo is not None:
        cached = memo.get(key)
        if cached is not None:
            yield from cached
            return
    out: list[ast.AST] = []
    for n in _iter_own_scope_uncached(
            node, skip_lambda=skip_lambda,
            skip_type_checking_body=skip_type_checking_body,
            include_self=include_self, tc_polarities=tc_polarities):
        out.append(n)
        yield n
    if memo is not None:
        memo[key] = tuple(out)
def _iter_own_scope_uncached(node: ast.AST, *, skip_lambda: bool,
                             skip_type_checking_body: bool,
                             include_self: bool,
                             tc_polarities: dict[int, bool] | None = None):
    if include_self:
        yield node
    stack: list[tuple[ast.AST, bool]] = [(node, True)]
    while stack:
        cur, descend = stack.pop()
        if not descend:
            continue
        for sub in ast.iter_child_nodes(cur):
            if skip_lambda and isinstance(sub, ast.Lambda):
                continue
            if (_tc_guard_polarity(sub, skip_type_checking_body, tc_polarities)
                    is not None):
                for stmt in _visible_tc_runtime_stmts(sub, tc_polarities):
                    yield stmt
                    stack.append((stmt, _scope_descend_flag(stmt)))
                continue
            stack.append((sub, _scope_descend_flag(sub)))
            yield sub
            if isinstance(sub, ast.Lambda) and not skip_lambda:
                stack.append((sub.args, True))
def _tc_guard_polarity(node: ast.AST, enabled: bool,
                      tc_polarities: dict[int, bool] | None = None) -> bool | None:
    if not enabled or not isinstance(node, ast.If):
        return None
    if tc_polarities is not None:
        return tc_polarities.get(id(node))
    return _type_checking_guard_polarity(node.test)
def _scope_descend_flag(node: ast.AST) -> bool:
    return not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef, ast.Lambda))
def _visible_tc_runtime_stmts(node: ast.If,
                              tc_polarities: dict[int, bool] | None = None) -> list:
    polarity = _tc_guard_polarity(node, True, tc_polarities)
    if polarity is None:
        return []
    visible: list = []
    pending = list(node.orelse if not polarity else node.body)
    while pending:
        stmt = pending.pop(0)
        nested = _tc_guard_polarity(stmt, True, tc_polarities)
        if nested is not None:
            pending[0:0] = stmt.orelse if not nested else stmt.body
            continue
        visible.append(stmt)
    return visible
_TYPING_MODULE_NAMES = ("typing", "typing_extensions")
def typing_guard_aliases(tree: ast.Module) -> set[str]:
    aliases = set(_TYPING_MODULE_NAMES)
    for stmt in iter_module_level_stmts(tree):
        if not isinstance(stmt, ast.Import):
            continue
        for alias in stmt.names:
            if alias.name in _TYPING_MODULE_NAMES:
                aliases.add(alias.asname or alias.name.split(".", 1)[0])
    return aliases
def typing_type_checking_names(tree: ast.Module) -> set[str]:
    return {
        alias.asname or alias.name
        for stmt in iter_module_level_stmts(tree)
        if isinstance(stmt, ast.ImportFrom)
        and stmt.level == 0 and stmt.module in _TYPING_MODULE_NAMES
        for alias in stmt.names if alias.name == "TYPE_CHECKING"
    }
def _tc_guard_root(test: ast.expr) -> tuple[str, bool]:
    if isinstance(test, ast.Name):
        return test.id, False
    if (isinstance(test, ast.Attribute)
            and isinstance(test.value, ast.Name)):
        return test.value.id, True
    return "", False

def _tc_is_typing_import(stmt: ast.AST, name: str,
                         attribute: bool) -> bool:
    if attribute and isinstance(stmt, ast.Import):
        return any(
            alias.name in _TYPING_MODULE_NAMES
            and (alias.asname or alias.name.split(".", 1)[0]) == name
            for alias in stmt.names)
    return bool(
        not attribute and isinstance(stmt, ast.ImportFrom)
        and stmt.level == 0 and stmt.module in _TYPING_MODULE_NAMES
        and any(alias.name == "TYPE_CHECKING"
                and (alias.asname or alias.name) == name
                for alias in stmt.names))

def _tc_write_targets(stmt: ast.AST) -> list[ast.AST]:
    if isinstance(stmt, ast.Assign):
        return list(stmt.targets)
    if isinstance(stmt, (ast.AnnAssign, ast.AugAssign)):
        return [stmt.target]
    if isinstance(stmt, ast.Delete):
        return list(stmt.targets)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return [stmt.target]
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in stmt.items
                if item.optional_vars is not None]
    return []

def _tc_attribute_write(target: ast.AST, name: str) -> bool:
    return any(
        isinstance(leaf, ast.Attribute) and leaf.attr == "TYPE_CHECKING"
        and isinstance(leaf.value, ast.Name) and leaf.value.id == name
        for leaf in flatten_unpack_targets(target))

def _tc_false_literal_assignment(stmt: ast.AST, name: str,
                                 attribute: bool) -> bool:
    parts = assign_targets_value(stmt)
    if parts is None:
        return False
    targets, value = parts
    matches = any(
        (_tc_attribute_write(target, name) if attribute
         else name in iter_unpack_target_names(target))
        for target in targets)
    return bool(isinstance(value, ast.Constant) and not value.value and matches)

def _tc_header_walrus_binds(stmt: ast.AST, name: str) -> bool:
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        expressions = iter_def_site_nodes(stmt)
    elif isinstance(stmt, (ast.If, ast.While)):
        expressions = (stmt.test,)
    elif isinstance(stmt, (ast.For, ast.AsyncFor)):
        expressions = (stmt.iter,)
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        expressions = (item.context_expr for item in stmt.items)
    elif isinstance(stmt, TRY_NODE_TYPES):
        expressions = ()
    elif MATCH_NODE_TYPES and isinstance(stmt, MATCH_NODE_TYPES):
        expressions = (stmt.subject,)
    else:
        expressions = (stmt,)
    return any(name in _walrus_target_names(expr) for expr in expressions)

def _tc_branch_binding_events(stmt: ast.AST, name: str):
    if isinstance(stmt, TRY_NODE_TYPES):
        bound = {handler.name for handler in stmt.handlers if handler.name}
        events = [
            (node_position(handler), False)
            for handler in stmt.handlers if handler.name == name
        ]
        return bound, events
    if MATCH_NODE_TYPES and isinstance(stmt, MATCH_NODE_TYPES):
        bound = {
            capture
            for case in stmt.cases
            for capture in iter_pattern_capture_names(case.pattern)
        }
        events = [
            (node_position(case.pattern), False)
            for case in stmt.cases
            if name in iter_pattern_capture_names(case.pattern)
        ]
        events.extend(
            (node_position(case.guard), False)
            for case in stmt.cases
            if case.guard is not None
            and name in _walrus_target_names(case.guard)
        )
        return bound, events
    return set(), []

def _tc_scope_binding_events(scope: ast.AST, name: str,
                             attribute: bool) -> list[tuple[tuple[int, int], bool]]:
    events: list[tuple[tuple[int, int], bool]] = []
    if name in collect_param_names(scope):
        events.append((node_position(scope), False))
    for stmt in iter_module_level_stmts(scope):
        pos = node_position(stmt)
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            if name in import_alias_bound_names(stmt):
                events.append((pos, _tc_is_typing_import(
                    stmt, name, attribute)))
            continue
        bound = _assigned_binding_names(stmt) | _control_flow_binding_names(stmt)
        branch_bound, branch_events = _tc_branch_binding_events(stmt, name)
        bound.difference_update(branch_bound)
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(stmt.name)
        if TYPE_ALIAS_NODES and isinstance(stmt, TYPE_ALIAS_NODES):
            bound.update(iter_unpack_target_names(stmt.name))
        if isinstance(stmt, ast.Delete):
            bound.update(iter_unpack_target_names(stmt.targets))
        if (isinstance(scope, FUNC_NODE_TYPES)
                and isinstance(stmt, ast.AnnAssign) and stmt.value is None):
            bound.update(iter_unpack_target_names(stmt.target))
        if attribute and any(_tc_attribute_write(target, name)
                             for target in _tc_write_targets(stmt)):
            bound.add(name)
        if name in bound:
            events.append((pos, _tc_false_literal_assignment(
                stmt, name, attribute)))
        if _tc_header_walrus_binds(stmt, name):
            events.append((pos, False))
        events.extend(branch_events)
    events.sort(key=lambda event: event[0])
    return events

def _tc_name_redirected(scope: ast.AST, name: str) -> bool:
    return any(isinstance(stmt, (ast.Global, ast.Nonlocal))
               and name in stmt.names
               for stmt in iter_module_level_stmts(scope))

def _type_checking_guard_is_shadowed(node: ast.If,
                                     parent_map: dict) -> bool:
    test = node.test
    while isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        test = test.operand
    name, attribute = _tc_guard_root(test)
    if not name:
        return False
    if name in _walrus_target_names(test):
        return True
    guard_pos = node_position(node)
    deferred_outer = False
    for scope in iter_evaluation_scope_chain(node, parent_map):
        if isinstance(scope, COMP_SCOPE_NODES):
            if name in comp_target_names(scope):
                return True
            continue
        events = _tc_scope_binding_events(scope, name, attribute)
        if deferred_outer and events:
            return not events[-1][1]
        prior = [event for event in events if event[0] < guard_pos]
        if prior:
            return not prior[-1][1]
        if isinstance(scope, FUNC_NODE_TYPES):
            if events and not _tc_name_redirected(scope, name):
                return True
            deferred_outer = True
        elif isinstance(scope, ast.Module) and events:
            return True
    return False

#: ``_type_checking_guard_node_polarities`` / ``type_checking_body_node_ids``
#: 的树级缓存。两者都是树的纯函数（只读遍历），却各自做一次全树 ``ast.walk``；
#: 实测单文件被 349 个检测器各调一次，单次 54ms。用弱引用字典保证不阻止 AST
#: 回收（与 ``_PARENT_MAP_CACHE`` 同一套约定），容量上限仍为 256。
_TC_GUARD_POLARITY_CACHE: WeakKeyDictionary[Any, dict[int, bool]] = (
    WeakKeyDictionary())
_TC_BODY_IDS_CACHE: WeakKeyDictionary[Any, frozenset] = WeakKeyDictionary()
_TC_GUARD_CACHE_MAX = 256


def _cache_evict_oldest(cache: WeakKeyDictionary) -> None:
    while len(cache) > _TC_GUARD_CACHE_MAX:
        del cache[next(iter(cache))]


def _type_checking_guard_node_polarities(tree: ast.AST) -> dict[int, bool]:
    if tree is None:
        return {}
    try:
        cached = _TC_GUARD_POLARITY_CACHE.get(tree)
    except TypeError:
        cached = None
    if cached is not None:
        return cached
    typing_aliases = (
        typing_guard_aliases(tree) if isinstance(tree, ast.Module) else None)
    type_checking_names = (
        typing_type_checking_names(tree)
        if isinstance(tree, ast.Module) else None)
    parent_map = build_parent_map(tree)
    polarities: dict[int, bool] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        polarity = _type_checking_guard_polarity(
            node.test, typing_aliases, type_checking_names)
        if (polarity is not None
                and not _type_checking_guard_is_shadowed(node, parent_map)):
            polarities[id(node)] = polarity
    try:
        _TC_GUARD_POLARITY_CACHE[tree] = polarities
        _cache_evict_oldest(_TC_GUARD_POLARITY_CACHE)
    except TypeError:
        pass
    return polarities

def type_checking_body_node_ids(tree: ast.AST) -> set[int]:
    if tree is None:
        return set()
    try:
        cached = _TC_BODY_IDS_CACHE.get(tree)
    except TypeError:
        cached = None
    if cached is not None:
        return set(cached)
    polarities = _type_checking_guard_node_polarities(tree)
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        polarity = polarities.get(id(node))
        if polarity is None:
            continue
        for stmt in (node.orelse if polarity else node.body):
            ids.update(id(sub) for sub in walk_nodes(stmt))
    try:
        _TC_BODY_IDS_CACHE[tree] = frozenset(ids)
        _cache_evict_oldest(_TC_BODY_IDS_CACHE)
    except TypeError:
        pass
    return ids
def _annotation_is_literal_subscript(node: ast.AST) -> bool:
    if not isinstance(node, ast.Subscript):
        return False
    value = node.value
    if isinstance(value, ast.Name):
        return value.id == "Literal"
    if isinstance(value, ast.Attribute):
        return value.attr == "Literal"
    return False
def collect_annotation_names(annotation: ast.expr | None, used: set[str]) -> None:
    if annotation is None:
        return
    _collect_annotation_names_node(annotation, used)
def _collect_annotation_names_node(node: ast.AST, used: set[str]) -> None:
    if isinstance(node, ast.Name):
        used.add(node.id)
        return
    if isinstance(node, ast.Constant):
        if isinstance(node.value, str) and node.value.strip():
            parse_forward_ref_names(node.value, used)
        return
    if _annotation_is_literal_subscript(node):
        _collect_annotation_names_node(node.value, used)
        _collect_literal_value_names(node.slice, used)
        return
    for child in ast.iter_child_nodes(node):
        _collect_annotation_names_node(child, used)
def _collect_literal_value_names(node: ast.AST, used: set[str]) -> None:
    if isinstance(node, ast.Constant):
        return
    if isinstance(node, ast.Name):
        used.add(node.id)
        return
    if isinstance(node, ast.Tuple):
        for element in node.elts:
            _collect_literal_value_names(element, used)
        return
    for child in ast.iter_child_nodes(node):
        _collect_literal_value_names(child, used)
def parse_forward_ref_names(annotation_str: str, used: set[str]) -> None:
    s = annotation_str.strip()
    if not s:
        return
    try:
        parsed = ast.parse(s, mode="eval")
    except _PARSE_DEGRADE_EXC as _e:
        logger.debug(
            '静默降级[parse_forward_ref_names:%s]: %s', type(_e).__name__, _e)
        return
    collect_annotation_names(parsed.body, used)
def coerce_str(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, (bytes, bytearray)):
        return value.decode("utf-8", errors="replace")
    if isinstance(value, os.PathLike):
        try:
            return os.fsdecode(value)
        except (TypeError, ValueError) as exc:
            log_swallowed(__name__, exc, context="coerce_str:PathLike")
            return ""
    return ""
def normalize_node_str(value: Any) -> str:
    return value if isinstance(value, str) else str(value)
normalize_torn_name = normalize_node_str
def is_self_caller_name(caller, callee_key) -> bool:
    if caller is None or callee_key is None:
        return False
    caller_text = normalize_torn_name(caller)
    callee_text = normalize_torn_name(callee_key)
    if not caller_text or not callee_text:
        return False
    return (caller_text == callee_text
            or caller_text.startswith(callee_text + ":"))
def torn_list(value: Any) -> tuple | list | set | frozenset:
    return value if isinstance(value, (list, tuple, set, frozenset)) else ()
def module_postpones_annotations(tree: Any, *, require_absolute: bool = False) -> bool:
    for stmt in getattr(tree, "body", None) or ():
        if not isinstance(stmt, ast.ImportFrom) or stmt.module != "__future__":
            continue
        if require_absolute and stmt.level:
            continue
        if any(alias.name == "annotations" for alias in stmt.names):
            return True
    return False
def path_to_dotted_module(rel_path: str) -> str:
    rel = rel_path.replace("\\", "/").strip("/")
    while rel.startswith("./"):
        rel = rel[2:]
    if not rel:
        return ""
    if rel.lower().endswith(".py"):
        rel = rel[:-3]
    parts = [part for part in rel.split("/") if part]
    if parts and parts[-1].lower() == "__init__":
        parts = parts[:-1]
    return ".".join(parts)
def relative_import_targets(pkg_segs: list[str], node: ast.ImportFrom) -> list[str]:
    if not pkg_segs or node.level <= 0 or node.level > len(pkg_segs):
        return []
    keep = len(pkg_segs) - (node.level - 1)
    if keep < 0:
        return []
    base = pkg_segs[:keep]
    if node.module:
        return [".".join([*base, node.module])]
    return [".".join([*base, a.name]) for a in node.names]
def pkg_root_name(project_root: str) -> str:
    return os.path.basename(os.path.abspath(project_root))
def strip_pkg_root(name: Any, pkg_root: str) -> str:
    text = normalize_torn_name(name)
    if not pkg_root:
        return text
    prefix = pkg_root + "."
    if text.startswith(prefix):
        return text[len(prefix):]
    return text
def is_placeholder_stmt(stmt: ast.AST) -> bool:
    if isinstance(stmt, ast.Pass):
        return True
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and stmt.value.value is ...)
def iter_module_scope_entities(
    tree: ast.AST,
) -> Iterator[ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef]:
    stack: list[ast.AST] = list(reversed(getattr(tree, "body", None) or ()))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            yield node
            continue
        if isinstance(node, ast.Lambda):
            continue
        for block in reversed(list(iter_module_stmt_blocks(node))):
            stack.extend(reversed(block))
def iter_module_scope_funcdefs(tree: ast.Module):
    for node in iter_module_scope_entities(tree):
        if isinstance(node, FUNC_NODE_TYPES):
            yield node
def iter_class_scope_methods(node: ast.ClassDef) -> Iterator[ast.AST]:
    yield from _iter_class_body_members(getattr(node, "body", None) or ())
def definition_start_line(node: ast.AST) -> int:
    decorator_lines = [
        int(deco.lineno) for deco in (getattr(node, "decorator_list", None) or ())
        if getattr(deco, "lineno", None) is not None
    ]
    lineno = int(getattr(node, "lineno", 0) or 0)
    return min(decorator_lines + [lineno]) if decorator_lines else lineno
def own_scope_line_span(node: ast.AST) -> int:
    start = definition_start_line(node)
    end = getattr(node, "end_lineno", start) or start
    total = max(end - start + 1, 1)
    nested = 0
    stack = list(ast.iter_child_nodes(node))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            nested_start = definition_start_line(current)
            nested_end = getattr(current, "end_lineno", nested_start) or nested_start
            nested += max(nested_end - nested_start + 1, 1)
            continue
        stack.extend(ast.iter_child_nodes(current))
    return max(total - nested, 1)
def node_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
def definition_binding_name(node: ast.AST) -> set[str]:
    return {node.name}
_HEADER_CODING_RE = re.compile(r"^[ \t\f]*#.*coding[:=][ \t]*([-\w.]+)")
def innermost_span(spans: list[tuple[int, int, str]], line: int) -> str:
    best: tuple[int, int, str] | None = None
    for index, (start, end, name) in enumerate(spans):
        if not start <= line <= end:
            continue
        candidate = (end - start, index, name)
        if best is None or candidate[:2] < best[:2]:
            best = candidate
    return best[2] if best is not None else ""
def _is_coding_header_line(lines: list[str], idx: int) -> bool:
    if idx > 1:
        return False
    if idx == 0 and lines[idx].strip().startswith("#!"):
        return True
    return bool(_HEADER_CODING_RE.match(lines[idx]))
def symbol_start_line(lines: list[str], node: ast.AST) -> int:
    start = definition_start_line(node)
    while (start - 2 >= 0
           and lines[start - 2].strip().startswith("#")
           and not _is_coding_header_line(lines, start - 2)):
        start -= 1
    return start
def multiline_string_spans(
    tree: ast.AST, *, include_joined: bool = False,
) -> Iterator[tuple[int, int]]:
    for node in walk_nodes(tree):
        is_string = (
            (isinstance(node, ast.Constant) and isinstance(node.value, str))
            or (include_joined and isinstance(node, ast.JoinedStr))
        )
        if not is_string:
            continue
        end_lineno = getattr(node, "end_lineno", None)
        lineno = getattr(node, "lineno", None)
        if lineno is None or end_lineno is None or end_lineno <= lineno:
            continue
        yield lineno, end_lineno
NESTED_CTRL_TYPES = (
    ast.If, ast.For, ast.While, ast.AsyncFor,
    ast.With, ast.AsyncWith, *TRY_NODE_TYPES, *MATCH_NODE_TYPES,
)
def _is_executable_line(line: str) -> bool:
    stripped = line.strip()
    return bool(stripped) and not stripped.startswith('#')
def executable_line_numbers(lines) -> frozenset[int]:
    return frozenset(
        lineno for lineno, line in enumerate(lines, 1)
        if _is_executable_line(line))
def class_base_names(cls_node: ast.ClassDef) -> tuple[str, ...]:
    names = []
    for base in cls_node.bases:
        node = base
        while isinstance(node, ast.Subscript):
            node = node.value
        if isinstance(node, ast.Name):
            names.append(node.id)
        elif isinstance(node, ast.Attribute):
            names.append(node.attr)
    return tuple(names)
def iter_import_time_nodes(
    node: ast.AST, *, annotations_evaluated: bool | None = None,
) -> Iterator[ast.AST]:
    if annotations_evaluated is None:
        annotations_evaluated = not (
            isinstance(node, ast.Module)
            and module_postpones_annotations(node, require_absolute=True))
    stack: list[ast.AST] = [node]
    while stack:
        current = stack.pop()
        yield current
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            children = [*current.decorator_list]
            if annotations_evaluated:
                children.append(current.args)
                if current.returns is not None:
                    children.append(current.returns)
            else:
                children.extend(iter_arg_defaults(current.args))
            stack.extend(reversed(children))
            continue
        if TYPE_ALIAS_NODES and isinstance(current, TYPE_ALIAS_NODES):
            stack.append(current.name)
            continue
        if isinstance(current, ast.AnnAssign) and not annotations_evaluated:
            children = [current.target]
            if current.value is not None:
                children.append(current.value)
            stack.extend(reversed(children))
            continue
        if isinstance(current, ast.ClassDef):
            type_params = getattr(current, "type_params", ())
            children = [child for child in ast.iter_child_nodes(current)
                        if child not in type_params]
            stack.extend(reversed(children))
            continue
        if isinstance(current, ast.Lambda):
            stack.append(current.args)
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(current))))
def iter_module_scope_nodes(tree: ast.Module, *, descend_classes: bool = True):
    stack = list(ast.iter_child_nodes(tree))
    stack.reverse()
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        yield cur
        if isinstance(cur, ast.ClassDef) and not descend_classes:
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
def parse_import_name_list(raw: str, *, bound_names: bool = False) -> list[str]:
    names: list[str] = []
    normalized = " ".join(
        line.split("#", 1)[0] for line in raw.splitlines())
    for part in normalized.split(","):
        pieces = re.split(r"\s+as\s+", part.strip(), maxsplit=1)
        name = (pieces[-1] if bound_names else pieces[0]).strip()
        if name:
            names.append(name)
    return names
TYPE_ALIAS_NODES = ((ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ())
MATCH_CAPTURE_NODES = ((ast.MatchAs, ast.MatchStar)
                        if hasattr(ast, "MatchAs") else ())
MATCH_REST_NODES = ((ast.MatchMapping,)
                     if hasattr(ast, "MatchMapping") else ())
def iter_def_site_nodes(node: ast.AST):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        yield from _iter_function_def_sites(node)
    elif isinstance(node, ast.ClassDef):
        yield from _iter_class_def_sites(node)
    elif isinstance(node, ast.Lambda):
        yield from _iter_lambda_sites(node)
def _iter_function_def_sites(node: ast.AST) -> Iterator[ast.AST]:
    yield from (getattr(node, 'decorator_list', None) or [])
    _a = getattr(node, 'args', None)
    if _a is not None:
        yield from iter_arg_defaults(_a)
        yield from _iter_param_annotations(_a)
    _ret = getattr(node, 'returns', None)
    if _ret is not None:
        yield _ret
def _iter_class_def_sites(node: ast.AST) -> Iterator[ast.AST]:
    yield from (getattr(node, 'decorator_list', None) or [])
    yield from (getattr(node, 'bases', None) or [])
    for _kw in (getattr(node, 'keywords', None) or []):
        _kv = getattr(_kw, 'value', None)
        if _kv is not None:
            yield _kv
def _iter_lambda_sites(node: ast.AST) -> Iterator[ast.AST]:
    _a = getattr(node, 'args', None)
    if _a is not None:
        yield from iter_arg_defaults(_a)
def _walrus_target_names(expr: ast.expr) -> set[str]:
    names: set[str] = set()
    stack: list[ast.AST] = [expr]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.ClassDef):
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            stack.extend(cur.args.defaults)
            stack.extend(d for d in cur.args.kw_defaults
                         if d is not None)
            continue
        if isinstance(cur, ast.NamedExpr):
            names.add(cur.target.id)
        stack.extend(ast.iter_child_nodes(cur))
    return names
def definition_site_walrus_names(
        node: ast.AST, annotations_evaluated: bool) -> set[str]:
    expressions = (iter_def_site_nodes(node)
                   if annotations_evaluated or isinstance(node, ast.ClassDef)
                   else definition_time_exprs(node))
    names: set[str] = set()
    for expression in expressions:
        names.update(_walrus_target_names(expression))
    return names
def iter_arg_defaults(args: Any) -> Any:
    yield from (getattr(args, 'defaults', None) or [])
    for _d in (getattr(args, 'kw_defaults', None) or []):
        if _d is not None:
            yield _d
def _iter_param_annotations(args):
    for _p in iter_arg_nodes(args):
        _ann = getattr(_p, 'annotation', None)
        if _ann is not None:
            yield _ann
def str_constant_value(node) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None
def assign_targets_value(node: ast.AST) -> tuple[list[ast.AST], ast.AST] | None:
    if isinstance(node, ast.Assign):
        return node.targets, node.value
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return [node.target], node.value
    return None
def annassign_target_names(
    node: ast.AnnAssign, *, include_unassigned: bool = False,
) -> set[str]:
    if node.value is None and not include_unassigned:
        return set()
    return {node.target.id} if isinstance(node.target, ast.Name) else set()
def augassign_target_names(node: ast.AugAssign) -> set[str]:
    return {node.target.id} if isinstance(node.target, ast.Name) else set()
def is_module_call(node: ast.AST, module: str, attr: str | None = None) -> bool:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == module):
        return False
    return attr is None or node.func.attr == attr
def first_symbol_field(f: dict, keys, *, skip_builtins: bool = False) -> str:
    for key in keys:
        v = f.get(key)
        if not isinstance(v, str):
            continue
        name = v.strip()
        if not name:
            continue
        if skip_builtins and name in BUILTIN_NAMES:
            continue
        return name
    return ""
def is_class_shaped_exc_name(raise_type: str) -> bool:
    name = raise_type.strip()
    if not name or name == "bare re-raise":
        return False
    tail = name.rsplit(".", 1)[-1]
    return bool(tail) and tail[0].isupper() and (
        len(tail) == 1 or not tail.isupper())
def extract_all_declarations(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    collect_all_export_names(getattr(tree, "body", None) or (), names,
                             require_str=True)
    return names
def direct_class_methods(
    node: ast.ClassDef,
) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
    return [
        child for child in ast.iter_child_nodes(node)
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
def _collect_import_entries(
    nodes: list[ast.AST],
) -> list[tuple[str, int, str]]:
    import_entries: list[tuple[str, int, str]] = []
    for node in nodes:
        if isinstance(node, ast.Import):
            import_entries.extend(
                _import_alias_entry(alias, node.lineno) for alias in node.names)
            continue
        if isinstance(node, ast.ImportFrom) and node.module != "__future__":
            import_entries.extend(_importfrom_alias_entries(node))
    return import_entries
def _import_alias_entry(alias: ast.alias, lineno: int) -> tuple[str, int, str]:
    name = alias.asname or alias.name.split(".")[0]
    desc = f"import {alias.name}" + (
        f" as {alias.asname}" if alias.asname else "")
    return name, lineno, desc
def _importfrom_alias_entries(
    node: ast.ImportFrom,
) -> list[tuple[str, int, str]]:
    module_disp = "." * node.level + (node.module or "")
    entries: list[tuple[str, int, str]] = []
    for alias in node.names:
        if alias.name == "*":
            continue
        name = alias.asname or alias.name
        desc = f"from {module_disp} import {alias.name}" + (
            f" as {alias.asname}" if alias.asname else "")
        entries.append((name, node.lineno, desc))
    return entries
def is_package_init_path(filepath: object) -> bool:
    if not filepath:
        return False
    try:
        return Path(os.fsdecode(filepath)).name == "__init__.py"
    except TypeError as exc:
        log_swallowed(__name__, exc, context="is_package_init_path:TypeError")
        return False
def collect_import_usage(
    tree: ast.AST,
    nodes: Iterable[ast.AST] | None = None,
) -> tuple[list[tuple[str, int, str]], set[str], set[str]]:
    all_nodes = list(nodes) if nodes is not None else list(walk_nodes(tree))
    used_names = _collect_used_names(all_nodes)
    used_names.update(_collect_string_annotation_names(tree))
    return (_collect_import_entries(all_nodes), used_names,
            extract_all_declarations(tree))
def _collect_used_names(nodes: Iterable[ast.AST]) -> set[str]:
    return {node.id for node in nodes if _is_load_name(node)}
def _is_load_name(node: ast.AST) -> bool:
    return (isinstance(node, ast.Name)
            and isinstance(getattr(node, 'ctx', None), ast.Load))
def classify_import_usage(
    name: str, line: int, desc: str,
    used_names: set[str], exported_names: set[str],
) -> tuple[str | None, str | None]:
    if name in used_names:
        return None, None
    if name in exported_names:
        return None, f"L{line}: {desc} (在 __all__ 中，可能为重导出)"
    return f"L{line}: {desc}", None
def _iter_annotation_expressions(tree: ast.AST) -> Iterator[ast.AST]:
    for node in walk_nodes(tree):
        annotation = _annotation_of_node(node)
        if annotation is not None:
            yield annotation
        if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
            yield node.value
        for param in getattr(node, "type_params", None) or ():
            for attr in ("bound", "default_value", "default"):
                expression = getattr(param, attr, None)
                if expression is not None:
                    yield expression
def _collect_string_annotation_names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for annotation in _iter_annotation_expressions(tree):
        collect_annotation_names(annotation, names)
    return names
def _annotation_of_node(node: ast.AST) -> ast.AST | None:
    if isinstance(node, ast.arg):
        return node.annotation
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return node.returns
    if isinstance(node, ast.AnnAssign):
        return node.annotation
    return None
_TEST_FRAMEWORK_ROOTS = frozenset({
    'unittest', 'pytest', 'nose', 'nose2', 'ward',
})
def module_imports_test_framework(
        tree, framework_roots: Iterable[str] | None = None) -> bool:
    roots = (_TEST_FRAMEWORK_ROOTS if framework_roots is None
             else frozenset(framework_roots))
    return any(_import_node_is_test_framework(node, roots)
               for node in iter_module_level_stmts(tree))
def _import_node_is_test_framework(node, roots: frozenset[str]) -> bool:
    if isinstance(node, ast.Import):
        return any(a.name.split('.')[0] in roots for a in node.names)
    if isinstance(node, ast.ImportFrom) and node.module and not node.level:
        return node.module.split('.')[0] in roots
    return False
def latest_prior(records: Any, pos: Any,
                  key: Callable[[Any], Any] | None = None) -> Any | None:
    if key is None:
        prior = sorted(record for record in records if record <= pos)
    else:
        prior = sorted((record for record in records if key(record) <= pos),
                       key=key)
    return prior[-1] if prior else None
AST_MATCH_TYPES: tuple[type, ...] = MATCH_NODE_TYPES
def _docstring_first_expr(node: Any) -> ast.Expr | None:
    body = getattr(node, "body", None)
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[0]
    return None
_DOCSTRING_HOLDER_TYPES = (ast.Module, ast.FunctionDef,
                           ast.AsyncFunctionDef, ast.ClassDef)
def iter_docstring_nodes(tree: ast.AST):
    for node in walk_nodes(tree):
        if not isinstance(node, _DOCSTRING_HOLDER_TYPES):
            continue
        first = _docstring_first_expr(node)
        if first is not None:
            yield node, first
def collect_docstring_node_ids(tree: ast.AST) -> set[int]:
    return {id(first.value) for _node, first in iter_docstring_nodes(tree)}
def _sorted_export_scope_stmts(tree: ast.AST):
    nodes = list(iter_module_level_stmts(tree))
    return iter(sorted(nodes, key=lambda node: (
        getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0))))
def import_binds_of(node: ast.AST) -> set[str]:
    return set(import_alias_bound_names(node))
def _is_all_name_node(node: ast.AST) -> bool:
    return isinstance(node, ast.Name) and node.id == '__all__'
def _all_method_call(call: ast.Call) -> tuple[str, list[ast.expr]] | None:
    func = call.func
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id == '__all__'):
        return None
    if func.attr == 'clear':
        return ('clear', []) if not call.args and not call.keywords else None
    if func.attr not in ("extend", "append", "insert", "remove", "discard"):
        return None
    return (func.attr, call.args) if call.args else None
def collect_all_export_names(nodes, sink: set[str],
                             require_str: bool = False) -> None:
    stmts = [node for node in nodes if isinstance(node, ast.stmt)]
    if not stmts:
        return
    # 硬环：diag_shared_ast_surface 反向复用本模块的节点工具。
    from jwsgj.diag_shared_ast_surface import (
        collect_module_exports_state,  # lazy-by-design — 硬环断路器
    )
    names, _exact = collect_module_exports_state(
        ast.Module(body=stmts, type_ignores=[]))
    if require_str:
        names = {name for name in names if isinstance(name, str)}
    sink.update(names)
_EXPORT_DECLARATION_METHODS = frozenset({"extend", "append", "insert"})
def _export_declaration_values(node: ast.stmt) -> list[ast.expr]:
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        if isinstance(node, ast.AugAssign):
            if not isinstance(node.op, (ast.Add, ast.BitOr)):
                return []
            targets, value = [node.target], node.value
        else:
            parts = assign_targets_value(node)
            if parts is None:
                return []
            targets, value = list(parts[0]), parts[1]
        declares = any(
            _is_all_name_node(target)
            or (isinstance(target, ast.Subscript)
                and _is_all_name_node(target.value))
            for target in targets)
        return [value] if declares else []
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        call = node.value
        mutation = _all_method_call(call)
        if mutation is None or mutation[0] not in _EXPORT_DECLARATION_METHODS:
            return []
        return list(call.args)
    return []
def all_export_string_node_ids(entry) -> set[int]:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return set()
    ids: set[int] = set()
    for stmt in _sorted_export_scope_stmts(tree):
        for value in _export_declaration_values(stmt):
            ids.update(
                id(sub) for sub in walk_nodes(value)
                if isinstance(sub, ast.Constant)
                and isinstance(sub.value, str))
    return ids
def all_export_declaration_lines(entry) -> dict[str, int]:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return {}
    # 硬环：diag_shared_ast_surface 反向复用本模块的节点工具。
    from jwsgj.diag_shared_ast_surface import (
        iter_all_export_entries,  # lazy-by-design — 硬环断路器
    )
    return dict(iter_all_export_entries(tree))
__all__ = [
    "ABSTRACT_NAME_PREFIXES",
    "AST_MATCH_TYPES",
    "BUILTIN_CALLABLES",
    "BUILTIN_NAMES",
    "COMP_SCOPE_NODES",
    "FRAME_BOUNDARY_NODES",
    "FUNC_NODE_TYPES",
    "MATCH_CAPTURE_NODES",
    "MATCH_NODE_TYPES",
    "MATCH_REST_NODES",
    "NESTED_CTRL_TYPES",
    "NON_PROJECT_TOP_MODULES",
    "PY_STDLIB_HINTS",
    "SHADOW_SCOPE_STOP",
    "TRY_NODE_TYPES",
    "TRY_STAR",
    "TYPE_ALIAS_NODES",
    "ASTPreciseParser",
    "FastDispatchNodeVisitor",
    "all_export_declaration_lines",
    "all_export_string_node_ids",
    "annassign_target_names",
    "argument_param_names",
    "as_format_call",
    "assign_targets_value",
    "ast_name",
    "attr_chain_key",
    "augassign_target_names",
    "block_may_fall_through",
    "build_node_dispatch",
    "build_node_parent_map",
    "build_parent_map",
    "calc_nesting",
    "call_arg_values",
    "call_tail_name",
    "chain_depth",
    "chain_spine_calls",
    "class_base_names",
    "class_body_owner",
    "class_scope",
    "classify_import_usage",
    "coerce_str",
    "cognitive_complexity",
    "collect_all_export_names",
    "collect_annotation_names",
    "collect_docstring_node_ids",
    "collect_import_bindings",
    "collect_import_usage",
    "collect_param_names",
    "comp_element_roots",
    "comp_target_names",
    "count_params",
    "cyclomatic_complexity",
    "decision_points",
    "decorator_name",
    "definition_binding_name",
    "definition_site_walrus_names",
    "definition_start_line",
    "definition_time_exprs",
    "direct_class_methods",
    "dotted_name",
    "dump_len",
    "empty_container_ctor_name",
    "executable_line_numbers",
    "expr_target_name",
    "extract_all_declarations",
    "extract_loop_target_names",
    "find_runtime_function",
    "first_segment",
    "first_symbol_field",
    "flatten_unpack_targets",
    "get_call_name",
    "handler_exc_names",
    "has_abstractmethod_decorator",
    "has_type_hints",
    "import_alias_bound_name",
    "import_alias_bound_names",
    "import_binds_of",
    "in_subtree",
    "innermost_span",
    "is_abstract_class_def",
    "is_broad_except",
    "is_class_shaped_exc_name",
    "is_constant_expr_stmt",
    "is_dataclass_decorator",
    "is_docstring_stmt",
    "is_dunder_name",
    "is_invariant_assert",
    "is_main_check",
    "is_match_method",
    "is_module_call",
    "import_fallback_import_lines",
    "main_guard_node_ids",
    "is_mutable_default",
    "is_none_literal",
    "is_overload_stub",
    "is_package_init_path",
    "is_placeholder_stmt",
    "is_public_name",
    "is_safe_yaml_loader",
    "is_self_caller_name",
    "is_shell_true_keyword",
    "is_star_import",
    "is_static_literal_expr",
    "is_static_method",
    "is_subscript_of",
    "is_type_checking_guard",
    "iter_arg_defaults",
    "iter_arg_nodes",
    "iter_class_scope_methods",
    "iter_def_site_nodes",
    "iter_docstring_nodes",
    "iter_evaluation_scope_chain",
    "iter_handler_scope",
    "iter_import_time_nodes",
    "iter_loop_frame_nodes",
    "iter_module_level_stmts",
    "iter_module_scope_entities",
    "iter_module_scope_funcdefs",
    "iter_module_scope_nodes",
    "iter_module_stmt_blocks",
    "iter_own_nodes",
    "iter_own_scope",
    "iter_params",
    "iter_pattern_capture_names",
    "iter_scope_nodes",
    "iter_scope_nodes_with_shadow",
    "iter_scope_statements",
    "iter_target_bindings",
    "iter_unpack_target_names",
    "kw_arg",
    "latest_prior",
    "loop_body_has_break",
    "main_block_entry_args",
    "main_guard_branch",
    "matches_any",
    "module_imports_test_framework",
    "module_level_binding_names",
    "module_postpones_annotations",
    "multiline_string_spans",
    "nearest_scope_node",
    "node_position",
    "normalize_node_str",
    "normalize_torn_name",
    "open_calls_missing_encoding",
    "own_scope_line_span",
    "parse_ast_safely",
    "parse_forward_ref_names",
    "parse_import_name_list",
    "parse_py_source",
    "parse_source_tree",
    "path_to_dotted_module",
    "pattern_capture_name",
    "pkg_root_name",
    "recv_name",
    "relative_import_targets",
    "resolve_call_name",
    "resolve_import_binding",
    "resolve_module_member_call",
    "root_binding_shadow",
    "scope_chain",
    "scope_roots",
    "segments_equal",
    "split_identifier",
    "str_constant_value",
    "strip_pkg_root",
    "subscript_base_name",
    "subscript_base_node",
    "subtree_node_ids",
    "symbol_start_line",
    "torn_list",
    "type_checking_body_node_ids",
    "type_last_name",
    "type_last_names",
    "typing_guard_aliases",
    "typing_type_checking_names",
    "walk_stmts",
]
def _prune_cases(cases: list, *, drop_imports: bool,
                 tc_polarities: dict[int, bool] | None = None) -> list:
    replaced: list = []
    is_changed = False
    for case in cases:
        # case guard 常量假（`case 1 if False:` / `if []`）时 body 不可达。
        # 只剪 body 不清 guard/pattern：pattern 捕获与匹配副作用仍在。
        if _constant_truth_value(getattr(case, "guard", None)) is False:
            if case.body:
                case = copy.copy(case)
                case.body = []
                is_changed = True
            replaced.append(case)
            continue
        block = _prune_stmt_block(
            case.body, drop_imports=drop_imports, tc_polarities=tc_polarities)
        if block is not case.body:
            is_changed = True
            case = copy.copy(case)
            case.body = block
        replaced.append(case)
    return replaced if is_changed else cases

def _prune_handlers(handlers: list, *, drop_imports: bool,
                    tc_polarities: dict[int, bool] | None = None) -> list:
    replaced: list = []
    is_changed = False
    for handler in handlers:
        block = _prune_stmt_block(
            handler.body, drop_imports=drop_imports,
            tc_polarities=tc_polarities)
        if block is not handler.body:
            is_changed = True
            handler = copy.copy(handler)
            handler.body = block
        replaced.append(handler)
    return replaced if is_changed else handlers


def _clone_with(stmt: ast.AST, changed: list) -> ast.AST:
    if not changed:
        return stmt
    clone = copy.copy(stmt)
    for field, value in changed:
        setattr(clone, field, value)
    return clone


def _is_constant_empty_iterable(node: ast.AST) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes))
            and not node.value)


def _constant_truth_value(node: ast.AST | None) -> bool | None:
    """字面量表达式的静态真值；无法确定返回 None。

    覆盖 ``ast.Constant`` 与**无展开/无 ``**``** 的容器显示：列表/元组/集合
    按元素数、字典按键数判真。含 ``*x`` 或 ``**x`` 的显示长度取决于运行时
    值，不能静态判定（``[*()]`` 为空、``{**{}}`` 为空）。
    """
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if any(isinstance(elt, ast.Starred) for elt in node.elts):
            return None
        return bool(node.elts)
    if isinstance(node, ast.Dict):
        if any(key is None for key in node.keys):
            return None
        return bool(node.keys)
    return None

def _constant_loop_non_import_branch(node: ast.AST) -> str | None:
    if isinstance(node, ast.While):
        truth = _constant_truth_value(node.test)
        if truth is not None:
            return 'body' if not truth else 'orelse'
        return None
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return 'body' if _is_constant_empty_iterable(node.iter) else None
    return None


def _non_import_time_branch(
        node: ast.AST, tc_polarities: dict[int, bool] | None = None) -> str | None:
    if isinstance(node, (ast.While, ast.For, ast.AsyncFor)):
        return _constant_loop_non_import_branch(node)
    if not isinstance(node, ast.If):
        return None
    truth = _constant_truth_value(node.test)
    if truth is not None:
        return 'body' if not truth else 'orelse'
    main_branch = main_guard_branch(node.test)
    if main_branch is not None:
        return 'body' if main_branch else 'orelse'
    polarity = (tc_polarities.get(id(node))
                if tc_polarities is not None
                else _type_checking_guard_polarity(node.test))
    if polarity is not None:
        return 'orelse' if polarity else 'body'
    if is_main_check(node.test):
        return 'body'
    return None

def _prune_non_import_time_branches(tree, *, drop_imports: bool = False):
    body = getattr(tree, "body", None)
    if not isinstance(body, list):
        return tree
    tc_polarities = _type_checking_guard_node_polarities(tree)
    new_body = _prune_stmt_block(
        body, drop_imports=drop_imports, tc_polarities=tc_polarities)
    if new_body is body:
        return tree
    clone = copy.copy(tree)
    clone.body = new_body
    return clone

def _prune_stmt_block(stmts: list, *, drop_imports: bool,
                      tc_polarities: dict[int, bool] | None = None) -> list:
    replaced: list = []
    is_changed = False
    for stmt in stmts:
        if drop_imports and isinstance(stmt, (ast.Import, ast.ImportFrom)):
            is_changed = True
            continue
        new_stmt = _prune_stmt(
            stmt, drop_imports=drop_imports, tc_polarities=tc_polarities)
        if new_stmt is not stmt:
            is_changed = True
        replaced.append(new_stmt)
    return replaced if is_changed else stmts

def _prune_stmt(stmt: ast.AST, *, drop_imports: bool,
                tc_polarities: dict[int, bool] | None = None) -> ast.AST:
    if isinstance(stmt, (ast.If, ast.While, ast.For, ast.AsyncFor)):
        _branch = _non_import_time_branch(stmt, tc_polarities)
        if _branch == 'body':
            clone = copy.copy(stmt)
            clone.body = []
            clone.orelse = _prune_stmt_block(
                stmt.orelse, drop_imports=drop_imports,
                tc_polarities=tc_polarities)
            return clone
        if _branch == 'orelse':
            clone = copy.copy(stmt)
            clone.orelse = []
            clone.body = _prune_stmt_block(
                stmt.body, drop_imports=drop_imports,
                tc_polarities=tc_polarities)
            return clone
    changed: list[tuple[str, object]] = []
    for field in ("body", "orelse", "finalbody"):
        block = getattr(stmt, field, None)
        if isinstance(block, list):
            replaced = _prune_stmt_block(
                block, drop_imports=drop_imports, tc_polarities=tc_polarities)
            if replaced is not block:
                changed.append((field, replaced))
    handlers = getattr(stmt, "handlers", None)
    if handlers:
        replaced_handlers = _prune_handlers(
            handlers, drop_imports=drop_imports, tc_polarities=tc_polarities)
        if replaced_handlers is not handlers:
            changed.append(("handlers", replaced_handlers))
    cases = getattr(stmt, "cases", None)
    if cases:
        replaced_cases = _prune_cases(
            cases, drop_imports=drop_imports, tc_polarities=tc_polarities)
        if replaced_cases is not cases:
            changed.append(("cases", replaced_cases))
    return _clone_with(stmt, changed)


_PROTOCOL_BASE_NAME = 'Protocol'

_TYPING_PROTOCOL_MODULES = frozenset({'typing', 'typing_extensions'})

def _protocol_base_names(tree: ast.Module) -> frozenset[str]:
    names = {_PROTOCOL_BASE_NAME}
    for stmt in iter_module_level_stmts(tree):
        if (isinstance(stmt, ast.ImportFrom)
                and stmt.module in _TYPING_PROTOCOL_MODULES):
            names.update(
                alias.asname or alias.name for alias in stmt.names
                if alias.name == _PROTOCOL_BASE_NAME)
    return frozenset(names)

def _base_is_protocol(base: ast.expr, protocol_names: frozenset[str]) -> bool:
    if isinstance(base, ast.Subscript):
        return _base_is_protocol(base.value, protocol_names)
    if isinstance(base, ast.Name):
        return base.id in protocol_names
    if isinstance(base, ast.Attribute):
        return base.attr == _PROTOCOL_BASE_NAME
    return False

def _protocol_member_ids(tree: ast.Module) -> set[int]:
    protocol_names = _protocol_base_names(tree)
    member_ids: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        if not any(_base_is_protocol(base, protocol_names)
                   for base in node.bases):
            continue
        member_ids.update(
            id(item) for item in node.body
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        )
    return member_ids


logger.info(
    "diag_shared_ast_nodes L0 AST 节点判定·遍历·调用形态与度量域已加载: %d 项导出",
    len(__all__))

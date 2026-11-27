from __future__ import annotations

import ast
import hashlib
import io
import logging
import os
import re
import time
import tokenize
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    _type_checking_guard_polarity,
    dotted_name,
)
from jwsgj.diag_shared_source_core import count_lines, decode_source_bytes
from jwsgj.diag_types_normalize import int_or, signal_bool
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_analysis import (
    DEFAULT_MAX_LOG_ENTRIES,
    load_json_logs,
    load_test_runs,
    summarize_test_runs,
)
from jwsgj.log_config import (
    ACTIVE_FILES,
    LOG_DIR_ENV_VAR,
    TEST_RUNS_FILE,
    TEST_RUNS_MAX_BYTES,
    get_log_dir,
    log_swallowed,
    setup_logging,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import SOURCE_LAYOUT_ROOT_NAMES
from jwsgj.runtime_scope import (
    PACKAGE_NAME,
    SKILL_LOG_DIR_NAME,
    TEST_ARTIFACT_DIRS,
    is_pruned_scan_dir,
    is_scan_py_name,
    is_test_dir_name,
    is_test_file_path,
    is_test_source_basename,
    scan_exclude_dirs,
)

__all__ = [
    'audit_log_coverage',
]
_LOGGER = logging.getLogger(__name__)
_LOGGER.info("diag_log_coverage 日志覆盖度审计域已加载（静态扫描+五层编排）: %d 项导出", len(__all__))
_LOG_METHODS = frozenset({
    "debug", "info", "warning", "warn", "error",
    "exception", "critical", "fatal", "log",
})
_LOGGER_FACTORY_FUNCS = ("getLogger", "get_module_logger")
_EMPTY_LOGGER_FACTORY_NAMES: frozenset[str] = frozenset()
_EMPTY_AST_NODES: frozenset[ast.AST] = frozenset()
_LOGGER_VAR_NAMES = frozenset({"logger", "_logger", "_LOGGER", "log", "_log", "_LOG"})
_LOGGER_ATTR_NAMES = frozenset({"logger", "_logger", "_log", "log"})
_SCAN_EXTRA_EXCLUDED_DIRS = frozenset({"references", "fixtures"})
_TEST_CHANNEL_WRITER = "log_config"
_TEST_CHANNEL_READER = "log_analysis"
_TEST_HOOK_APIS = ("install_test_logging", "record_test_outcome",
                   "finish_test_logging")
_TEST_RUNS_WINDOW_MB = TEST_RUNS_MAX_BYTES // (1024 * 1024)
_STRUCT_EVENT_FUNCS = frozenset({
    "write_audit", "safe_write_audit", "perf_trace",
    "timed_log", "perf_scope", "log_swallowed", "write_bug_intercept",
    "write_detector_liveness", "write_defense_feedback",
    "write_module_run",
})
_PERF_EVENT_FUNCS = frozenset({
    "perf_trace", "timed_log", "perf_scope",
})
_LOAD_EVENT_LOG_METHODS = frozenset({
    "info", "warning", "warn", "error", "exception", "critical", "fatal",
})
_LOAD_EVENT_LOG_LEVEL_NAMES = frozenset({
    "INFO", "WARNING", "WARN", "ERROR", "CRITICAL", "FATAL",
})
_ITERATION_END_EXC_NAMES = frozenset({"StopIteration", "StopAsyncIteration"})
_STDERR_WRITE_FUNCS = frozenset({"safe_stderr_write"})
def _relative_audit_path(path: str, root: str | None) -> str:
    if not root:
        return ""
    try:
        rel = os.path.relpath(path, root)
    except (OSError, ValueError) as e:
        log_swallowed(__name__, e,
                      context=f'_relative_audit_path:{type(e).__name__}')
        return ""
    if rel == os.pardir or rel.startswith(os.pardir + os.sep):
        return ""
    return rel.replace(os.sep, "/")
def _test_dirs_of(target_dir: str) -> list[str]:
    try:
        names = sorted(os.listdir(target_dir))
    except OSError as e:
        log_swallowed(__name__, e, context=f'_test_dirs_of:{type(e).__name__}')
        return []
    return [path for name in names
            if is_test_dir_name(name)
            and os.path.isdir(path := os.path.join(target_dir, name))]
def _tests_dir_of(target_dir: str) -> str:
    dirs = _test_dirs_of(target_dir)
    return dirs[0] if dirs else ""
def _scan_skip_dirs(root: str, include_tests: bool) -> frozenset[str]:
    skip = set(scan_exclude_dirs(root))
    if include_tests:
        skip -= TEST_ARTIFACT_DIRS - _SCAN_EXTRA_EXCLUDED_DIRS
    return frozenset(skip | _SCAN_EXTRA_EXCLUDED_DIRS)
def _walk_error_scan(root: str, exc: OSError) -> dict[str, Any]:
    path = os.fspath(getattr(exc, "filename", None) or root)
    rel_path = _relative_audit_path(path, root)
    module = (os.path.splitext(os.path.basename(path))[0]
              or os.path.basename(os.path.normpath(root)))
    return {
        "file": path,
        "rel_path": rel_path,
        "module": module,
        "module_key": _dotted_module_name(rel_path) or module,
        "error": f"walk failed: {type(exc).__name__}: {exc}",
    }
def _collect_py_files(
    root: str, include_tests: bool,
    walk_errors: list[dict[str, Any]] | None = None,
) -> list[str]:
    out: list[str] = []
    skip = _scan_skip_dirs(root, include_tests)
    def _on_walk_error(exc: OSError) -> None:
        log_swallowed(__name__, exc,
                      context=f'_collect_py_files:walk:{type(exc).__name__}')
        if walk_errors is not None:
            walk_errors.append(_walk_error_scan(root, exc))
    for dirpath, dirnames, filenames in os.walk(root, onerror=_on_walk_error):
        dirnames[:] = [d for d in dirnames if not is_pruned_scan_dir(d, skip)]
        for fn in filenames:
            if not is_scan_py_name(fn):
                continue
            path = os.path.join(dirpath, fn)
            if not include_tests:
                rel_path = _relative_audit_path(path, root)
                if rel_path and is_test_file_path(rel_path):
                    continue
            out.append(path)
    return sorted(out)
class _ScanBindings(NamedTuple):
    logger_vars: frozenset
    logging_names: frozenset
    logging_func_names: frozenset
    struct_alias: frozenset
    perf_alias: frozenset
    swallow_alias: frozenset
    logging_func_canonical: dict[str, str] | None = None
    logger_factory_names: frozenset = _EMPTY_LOGGER_FACTORY_NAMES
    logging_level_canonical: dict[str, str] | None = None
def _reference_name(node: ast.AST | None) -> str:
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Name):
        return node.id
    return ""
def _is_logger_factory_call(
        call: ast.Call, extra_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES) -> bool:
    name = _reference_name(call.func)
    return name in _LOGGER_FACTORY_FUNCS or name in extra_names
def _is_log_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        return func.id in bindings.logging_func_names
    if not (isinstance(func, ast.Attribute) and func.attr in _LOG_METHODS):
        return False
    base = func.value
    if isinstance(base, ast.Name) and base.id in bindings.logging_names:
        return True
    return _is_logger_receiver(
        base, bindings.logger_vars, bindings.logger_factory_names)
def _is_swallow_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        return func.attr == "log_swallowed"
    return isinstance(func, ast.Name) and (
        func.id == "log_swallowed" or func.id in bindings.swallow_alias
    )
def _is_stderr_write_call(call: ast.Call) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        if func.attr == "write":
            v = func.value
            return isinstance(v, ast.Attribute) and v.attr == "stderr"
        return func.attr in _STDERR_WRITE_FUNCS or func.attr == "handleError"
    return isinstance(func, ast.Name) and func.id in _STDERR_WRITE_FUNCS
def _is_struct_event_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        return func.attr in _STRUCT_EVENT_FUNCS
    return isinstance(func, ast.Name) and (
        func.id in _STRUCT_EVENT_FUNCS or func.id in bindings.struct_alias
    )
def _is_perf_event_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        return func.attr in _PERF_EVENT_FUNCS
    return isinstance(func, ast.Name) and (
        func.id in _PERF_EVENT_FUNCS or func.id in bindings.perf_alias
    )
def _is_log_proxy_call(call: ast.Call) -> bool:
    return _reference_name(call.func) in _LOG_PROXY_FUNCS
def _is_observability_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    return (_is_log_call(call, bindings)
            or _is_swallow_call(call, bindings)
            or _is_struct_event_call(call, bindings)
            or _is_stderr_write_call(call)
            or _is_log_proxy_call(call))
def _is_iteration_end_exc(node: ast.expr) -> bool:
    if isinstance(node, ast.Name):
        return node.id in _ITERATION_END_EXC_NAMES
    if isinstance(node, ast.Attribute):
        return node.attr in _ITERATION_END_EXC_NAMES
    return False
def _is_iteration_end_handler(handler: ast.ExceptHandler) -> bool:
    t = handler.type
    if t is None:
        return False
    if isinstance(t, ast.Tuple):
        return bool(t.elts) and all(_is_iteration_end_exc(e) for e in t.elts)
    return _is_iteration_end_exc(t)
_SILENT_OK_MARKER_RE = re.compile(
    r"#\s*[A-Za-z_][\w.\-]*:silent-ok\b")
def _marked_silent_lines(tree: ast.Module, src: str) -> frozenset[int]:
    handlers = [
        node for node in walk_nodes(tree)
        if isinstance(node, ast.ExceptHandler)
    ]
    marked: set[int] = set()
    for token in tokenize.generate_tokens(io.StringIO(src).readline):
        if (token.type != tokenize.COMMENT
                or not _SILENT_OK_MARKER_RE.search(token.string)):
            continue
        line = token.start[0]
        owners = [
            node for node in handlers
            if node.lineno <= line <= (node.end_lineno or node.lineno)
        ]
        if owners:
            marked.add(max(owners, key=lambda node: node.lineno).lineno)
    return frozenset(marked)
def _runtime_branch_of_static_if(node: ast.If) -> list[ast.stmt] | None:
    if isinstance(node.test, ast.Constant):
        return node.body if node.test.value else node.orelse
    polarity = _type_checking_guard_polarity(node.test)
    if polarity is None:
        return None
    return node.body if polarity else node.orelse


def _iter_handler_own_nodes(
    handler: ast.ExceptHandler, *, include_annotations: bool = False,
    excluded_nodes: frozenset[ast.AST] = _EMPTY_AST_NODES,
):
    stack = list(handler.body)
    deferred = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    while stack:
        node = stack.pop()
        if node in excluded_nodes:
            continue
        if isinstance(node, ast.ExceptHandler):
            continue
        if isinstance(node, ast.If):
            branch = _runtime_branch_of_static_if(node)
            if branch is not None:
                stack.extend(branch)
                continue
        if isinstance(node, deferred):
            yield node
            if not isinstance(node, ast.Lambda):
                stack.extend(node.decorator_list)
            stack.extend(node.args.defaults)
            stack.extend(
                default for default in node.args.kw_defaults
                if default is not None)
            if include_annotations and not isinstance(node, ast.Lambda):
                stack.extend(_function_annotation_exprs(node))
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _block_is_silent(
    handler: ast.ExceptHandler, bindings: _ScanBindings,
    include_annotations: bool = False,
    excluded_nodes: frozenset[ast.AST] = _EMPTY_AST_NODES,
) -> bool:
    if _is_iteration_end_handler(handler):
        return False
    for sub in _iter_handler_own_nodes(
            handler, include_annotations=include_annotations,
            excluded_nodes=excluded_nodes):
        if isinstance(sub, ast.Raise):
            return False
        if isinstance(sub, ast.Call) and _is_observability_call(sub, bindings):
            return False
    return True
def _is_main_guard(test: ast.expr) -> bool:
    if not isinstance(test, ast.Compare):
        return False
    if len(test.ops) != 1 or not isinstance(test.ops[0], ast.Eq):
        return False
    if len(test.comparators) != 1:
        return False
    def _is_name(node: ast.expr) -> bool:
        return isinstance(node, ast.Name) and node.id == "__name__"
    def _is_main(node: ast.expr) -> bool:
        return isinstance(node, ast.Constant) and node.value == "__main__"
    left, right = test.left, test.comparators[0]
    return ((_is_name(left) and _is_main(right))
            or (_is_main(left) and _is_name(right)))
def _is_load_level_log_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    level = (call.args[0] if call.args else next(
        (kw.value for kw in call.keywords if kw.arg == "level"), None))
    if level is None:
        return False
    if isinstance(level, ast.Constant):
        return isinstance(level.value, int) and level.value >= logging.INFO
    if isinstance(level, ast.Name):
        canonical = bindings.logging_level_canonical or {}
        return canonical.get(level.id) in _LOAD_EVENT_LOG_LEVEL_NAMES
    if isinstance(level, ast.Attribute):
        return (level.attr in _LOAD_EVENT_LOG_LEVEL_NAMES
                and isinstance(level.value, ast.Name)
                and level.value.id in bindings.logging_names)
    return False
def _is_load_event_call(call: ast.Call, bindings: _ScanBindings) -> bool:
    if not _is_observability_call(call, bindings):
        return False
    if not _is_log_call(call, bindings):
        return True
    func = call.func
    if isinstance(func, ast.Name) and func.id in bindings.logging_func_names:
        canonical = bindings.logging_func_canonical or {}
        name = canonical.get(func.id)
    else:
        name = _reference_name(func)
    if name == "log":
        return _is_load_level_log_call(call, bindings)
    return name in _LOAD_EVENT_LOG_METHODS
def _iter_logger_factory_assigns(
        tree: ast.Module, factory_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES):
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if (isinstance(node.value, ast.Call)
                and _is_logger_factory_call(node.value, factory_names)):
            yield node
def _collect_logger_vars(
        tree: ast.Module,
        factory_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES,
) -> tuple[set[str], bool]:
    logger_vars: set[str] = set()
    has_factory = False
    for node in _iter_logger_factory_assigns(tree, factory_names):
        has_factory = True
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            if isinstance(target, ast.Name):
                logger_vars.add(target.id)
    return logger_vars, has_factory
def _logging_import_names(stmt: ast.Import) -> set[str]:
    names: set[str] = set()
    for alias in stmt.names:
        if alias.name.split(".", 1)[0] == "logging":
            names.add(alias.asname or "logging")
    return names
def _collect_logging_names(tree: ast.Module) -> set[str]:
    logging_names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            logging_names |= _logging_import_names(node)
    return logging_names
def _logging_func_import_names(
    stmt: ast.ImportFrom,
    canonical: dict[str, str] | None = None,
) -> set[str]:
    names: set[str] = set()
    for alias in stmt.names:
        if alias.name in _LOG_METHODS:
            names.add(alias.asname or alias.name)
            if canonical is not None:
                canonical[alias.asname or alias.name] = alias.name
    return names
def _collect_logging_func_names(
    tree: ast.Module,
    canonical: dict[str, str] | None = None,
) -> set[str]:
    logging_func_names: set[str] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ImportFrom) and not node.level
                and node.module == "logging"):
            logging_func_names |= _logging_func_import_names(node, canonical)
    return logging_func_names
def _collect_logging_level_names(tree: ast.Module) -> dict[str, str]:
    canonical: dict[str, str] = {}
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.ImportFrom) and not node.level
                and node.module == "logging"):
            continue
        for alias in node.names:
            if alias.name in _LOAD_EVENT_LOG_LEVEL_NAMES:
                canonical[alias.asname or alias.name] = alias.name
    return canonical
class _EventAliases(NamedTuple):
    struct_alias: set[str]
    perf_alias: set[str]
    swallow_alias: set[str]
_EVENT_CHANNEL_MODULES = frozenset({"log_config", "log_analysis"})
def _is_event_channel_module(module: str | None) -> bool:
    return bool(module) and module.rsplit(".", 1)[-1] in _EVENT_CHANNEL_MODULES
def _collect_logger_factory_names(tree: ast.Module) -> frozenset[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        stdlib_factory = not node.level and node.module == "logging"
        product_factory = _is_event_channel_module(node.module)
        if not (stdlib_factory or product_factory):
            continue
        for alias in node.names:
            if ((stdlib_factory and alias.name == "getLogger")
                    or (product_factory and alias.name == "get_module_logger")):
                names.add(alias.asname or alias.name)
    return frozenset(names)
_EVENT_ALIAS_RULES = (
    ("struct_alias", _STRUCT_EVENT_FUNCS),
    ("perf_alias", _PERF_EVENT_FUNCS),
    ("swallow_alias", frozenset({"log_swallowed"})),
)
def _iter_function_own_calls(function: ast.AST):
    stack = list(getattr(function, "body", ()))
    nested = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Call):
            yield node
        for child in ast.iter_child_nodes(node):
            if not isinstance(child, nested):
                stack.append(child)
def _collect_event_aliases(tree: ast.Module) -> _EventAliases:
    aliases = {field: set() for field in _EventAliases._fields}
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.ImportFrom)
                and _is_event_channel_module(node.module)):
            continue
        for alias in node.names:
            local = alias.asname or alias.name
            for field, event_names in _EVENT_ALIAS_RULES:
                if alias.name in event_names:
                    aliases[field].add(local)
    emit_names = aliases["swallow_alias"] | {"log_swallowed"}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if any(_reference_name(call.func) in emit_names
               for call in _iter_function_own_calls(node)):
            aliases["swallow_alias"].add(node.name)
    return _EventAliases(**aliases)
def _collect_logger_bindings(tree: ast.Module) -> tuple[_ScanBindings, bool]:
    factory_names = _collect_logger_factory_names(tree)
    logger_vars, has_factory = _collect_logger_vars(tree, factory_names)
    aliases = _collect_event_aliases(tree)
    logging_func_canonical: dict[str, str] = {}
    return _ScanBindings(
        logger_vars=frozenset(logger_vars),
        logging_names=frozenset(_collect_logging_names(tree)),
        logging_func_names=frozenset(
            _collect_logging_func_names(tree, logging_func_canonical)),
        logging_func_canonical=logging_func_canonical,
        struct_alias=frozenset(aliases.struct_alias),
        perf_alias=frozenset(aliases.perf_alias),
        swallow_alias=frozenset(aliases.swallow_alias),
        logger_factory_names=factory_names,
        logging_level_canonical=_collect_logging_level_names(tree),
    ), has_factory
def _count_call_events(node: ast.Call, bindings: _ScanBindings,
                       result: dict[str, Any]) -> None:
    if _is_log_call(node, bindings) or _is_log_proxy_call(node):
        result["log_calls"] += 1
    if _is_swallow_call(node, bindings):
        result["swallow_calls"] += 1
    if _is_struct_event_call(node, bindings):
        result["struct_event_calls"] += 1
        if _is_perf_event_call(node, bindings):
            result["perf_calls"] += 1
def _collect_runtime_events(tree: ast.Module, bindings: _ScanBindings,
                            result: dict[str, Any],
                            marked: frozenset[int]) -> None:
    excluded_nodes = _unevaluated_annotation_nodes(tree)
    for node in walk_nodes(tree):
        if node in excluded_nodes:
            continue
        if isinstance(node, ast.Call):
            _count_call_events(node, bindings, result)
        elif (isinstance(node, ast.ExceptHandler)
              and _block_is_silent(
                  node, bindings,
                  include_annotations=not _has_future_annotations(tree),
                  excluded_nodes=excluded_nodes)):
            if node.lineno in marked:
                result["silent_exempts"].append(node.lineno)
            else:
                result["silent_excepts"].append(node.lineno)
    result["silent_excepts"].sort()
    result["silent_exempts"].sort()
def _has_future_annotations(tree: ast.Module) -> bool:
    return any(
        isinstance(node, ast.ImportFrom) and node.module == "__future__"
        and any(alias.name == "annotations" for alias in node.names)
        for node in tree.body
    )
def _function_annotation_exprs(function: ast.AST) -> list[ast.expr]:
    args = function.args
    params = [
        *args.posonlyargs, *args.args, *args.kwonlyargs,
        args.vararg, args.kwarg,
    ]
    annotations = [
        param.annotation for param in params
        if param is not None and param.annotation is not None
    ]
    if function.returns is not None:
        annotations.append(function.returns)
    return annotations
def _unevaluated_annotation_nodes(tree: ast.Module) -> frozenset[ast.AST]:
    future = _has_future_annotations(tree)
    roots: list[ast.expr] = []
    stack: list[tuple[ast.AST, bool]] = [(tree, False)]
    while stack:
        node, in_function = stack.pop()
        if future and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            roots.extend(_function_annotation_exprs(node))
        if isinstance(node, ast.AnnAssign) and (future or in_function):
            roots.append(node.annotation)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            in_function = True
        elif isinstance(node, ast.ClassDef):
            in_function = False
        stack.extend(
            (child, in_function) for child in ast.iter_child_nodes(node))
    return frozenset(
        child for root in roots for child in walk_nodes(root))
def _iter_import_time_nodes(
    stmts: list[ast.stmt], *, include_annotations: bool = False,
    excluded_nodes: frozenset[ast.AST] = _EMPTY_AST_NODES,
):
    stack = list(stmts)
    deferred_bodies = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    while stack:
        node = stack.pop()
        if node in excluded_nodes:
            continue
        if isinstance(node, ast.If):
            branch = _runtime_branch_of_static_if(node)
            if branch is not None:
                stack.extend(branch)
                continue
        if isinstance(node, deferred_bodies):
            yield node
            if not isinstance(node, ast.Lambda):
                stack.extend(node.decorator_list)
            stack.extend(node.args.defaults)
            stack.extend(
                default for default in node.args.kw_defaults
                if default is not None)
            if include_annotations and not isinstance(node, ast.Lambda):
                stack.extend(_function_annotation_exprs(node))
            continue
        if isinstance(node, ast.If) and _is_main_guard(node.test):
            stack.extend(node.orelse)
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _detect_load_event(tree: ast.Module, bindings: _ScanBindings) -> bool:
    return any(
        isinstance(node, ast.Call) and _is_load_event_call(node, bindings)
        for node in _iter_import_time_nodes(
            tree.body,
            include_annotations=not _has_future_annotations(tree),
            excluded_nodes=_unevaluated_annotation_nodes(tree),
        )
    )
_EXEC_SURFACE_NODE_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
    ast.ExceptHandler, ast.Call, ast.If, ast.For, ast.AsyncFor, ast.While,
    ast.With, ast.AsyncWith, ast.Try, ast.Raise, ast.Assert, ast.Delete,
    ast.NamedExpr,
)
if hasattr(ast, "Match"):
    _EXEC_SURFACE_NODE_TYPES += (ast.Match,)
def _has_exec_surface(tree: ast.Module) -> bool:
    return any(isinstance(node, _EXEC_SURFACE_NODE_TYPES)
               for node in walk_nodes(tree))
def _has_except_handlers(tree: ast.Module) -> bool:
    return any(isinstance(node, ast.ExceptHandler) for node in walk_nodes(tree))
class _SinkRefs(NamedTuple):
    module_refs: dict[str, str]
    direct_names: dict[str, str]
def _is_logging_module_path(path: str) -> bool:
    return path == _LOGGING_NAMESPACE or path.startswith(_LOGGING_NAMESPACE + ".")
def _resolve_logging_module(node: ast.AST | None,
                            module_refs: dict[str, str]) -> str | None:
    dotted = dotted_name(node)
    if not dotted:
        return None
    root, _, rest = dotted.partition(".")
    canonical = module_refs.get(root)
    if canonical is None:
        return None
    full = f"{canonical}.{rest}" if rest else canonical
    return full if _is_logging_module_path(full) else None
def _bind_logging_module_import(node: ast.Import, refs: _SinkRefs) -> None:
    for alias in node.names:
        if not _is_logging_module_path(alias.name):
            continue
        bound = alias.asname or alias.name.split(".", 1)[0]
        refs.module_refs[bound] = alias.name if alias.asname else bound
def _bind_logging_from_import(node: ast.ImportFrom, refs: _SinkRefs) -> None:
    if node.level or not _is_logging_module_path(node.module or ""):
        return
    for alias in node.names:
        bound = alias.asname or alias.name
        if alias.name == "handlers":
            refs.module_refs[bound] = _LOGGING_HANDLERS_MODULE
            continue
        kind = _DIRECT_SINK_KINDS.get(alias.name)
        if kind is not None:
            refs.direct_names[bound] = kind
def _collect_logging_sink_aliases(tree: ast.AST) -> _SinkRefs:
    refs = _SinkRefs({}, {})
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            _bind_logging_module_import(node, refs)
        elif isinstance(node, ast.ImportFrom):
            _bind_logging_from_import(node, refs)
    return refs
def _is_null_handler_call(node: ast.AST | None) -> bool:
    return isinstance(node, ast.Call) and _reference_name(node.func) == "NullHandler"
def _is_logger_receiver(
        node: ast.AST,
        logger_vars: frozenset,
        factory_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES,
) -> bool:
    if isinstance(node, ast.Name):
        return node.id in logger_vars or node.id in _LOGGER_VAR_NAMES
    if isinstance(node, ast.Attribute):
        return node.attr in _LOGGER_ATTR_NAMES
    if isinstance(node, ast.Call):
        if _is_logger_factory_call(node, factory_names):
            return True
        func = node.func
        return (isinstance(func, ast.Attribute) and func.attr == "getChild"
                and _is_logger_receiver(
                    func.value, logger_vars, factory_names))
    return False
def _attr_sink_kind(
        func: ast.Attribute,
        refs: _SinkRefs,
        logger_vars: frozenset,
        factory_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES,
) -> str | None:
    base = func.value
    if _resolve_logging_module(base, refs.module_refs) is not None:
        return _MODULE_SINK_KINDS.get(func.attr)
    if (func.attr == "addHandler"
            and _is_logger_receiver(base, logger_vars, factory_names)):
        return _SINK_KIND_ADD_HANDLER
    return None
def _sink_kind_survives_filters(kind: str | None, node: ast.Call) -> str | None:
    if kind == _SINK_KIND_BASIC_CONFIG:
        filename = (node.args[0] if node.args else next(
            (kw.value for kw in node.keywords if kw.arg == "filename"), None))
        if filename is None:
            return None
        if isinstance(filename, ast.Constant) and filename.value is None:
            return None
        return kind
    if kind == _SINK_KIND_ADD_HANDLER:
        handlers = list(node.args)
        handlers.extend(
            kw.value for kw in node.keywords if kw.arg == "hdlr")
        if handlers and all(_is_null_handler_call(a) for a in handlers):
            return None
    return kind
def _sink_kind_of_call(
        node: ast.Call,
        refs: _SinkRefs,
        logger_vars: frozenset,
        factory_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES,
) -> str | None:
    func = node.func
    if isinstance(func, ast.Attribute):
        kind = _attr_sink_kind(func, refs, logger_vars, factory_names)
    else:
        kind = refs.direct_names.get(_reference_name(func))
    return _sink_kind_survives_filters(kind, node)
def _file_handler_base_kind(base: ast.expr, refs: _SinkRefs) -> str | None:
    if isinstance(base, ast.Name):
        kind = refs.direct_names.get(base.id)
    elif isinstance(base, ast.Attribute):
        if _resolve_logging_module(base.value, refs.module_refs) is None:
            return None
        kind = _MODULE_SINK_KINDS.get(base.attr)
    else:
        return None
    return kind if kind == _SINK_KIND_FILE_HANDLER else None
def _scan_sink_bypasses(
        tree: ast.AST,
        logger_vars: frozenset,
        factory_names: frozenset[str] = _EMPTY_LOGGER_FACTORY_NAMES,
) -> list[dict[str, Any]]:
    refs = _collect_logging_sink_aliases(tree)
    hits: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            kind = _sink_kind_of_call(
                node, refs, logger_vars, factory_names)
            if kind:
                hits.append({"kind": kind, "line": node.lineno})
        elif (isinstance(node, ast.ClassDef)
              and any(_file_handler_base_kind(base, refs) for base in node.bases)):
            hits.append({"kind": _SINK_KIND_FILE_HANDLER,
                         "line": node.lineno})
    hits.sort(key=lambda h: (h["line"], h["kind"]))
    return hits
def _dotted_module_name(rel_path: str) -> str:
    rel = rel_path.replace("\\", "/")
    rel = rel[:-len(".py")] if rel.lower().endswith(".py") else rel
    parts = [part for part in rel.split("/") if part not in ("", ".")]
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)
def _scan_key(scan: dict[str, Any]) -> str:
    key = scan.get("module_key")
    if isinstance(key, str) and key:
        return key
    return str(scan.get("module", ""))
def _without_source_layout_root(dotted: str) -> str:
    head, sep, tail = dotted.partition(".")
    if sep and head.lower() in _SOURCE_LAYOUT_ROOT_NAMES_LOWER:
        return tail
    return ""
def _module_path_map(
    scans: list[dict[str, Any]], target_dir: str,
) -> dict[str, str]:
    mapping: dict[str, str] = {}
    direct_names: set[str] = set()
    layout_alias_owners: dict[str, set[str]] = {}
    root_init_key = ""
    root_name = os.path.basename(os.path.normpath(target_dir))
    for scan in scans:
        rel = str(scan.get("rel_path") or "").replace("\\", "/")
        dotted = _dotted_module_name(rel)
        key = _scan_key(scan)
        if dotted:
            mapping[dotted] = key
            direct_names.add(dotted)
            if root_name:
                qualified = f"{root_name}.{dotted}"
                mapping[qualified] = key
                direct_names.add(qualified)
            layout_alias = _without_source_layout_root(dotted)
            if layout_alias:
                layout_alias_owners.setdefault(layout_alias, set()).add(key)
        if rel == "__init__.py":
            root_init_key = key
    if root_init_key and root_name:
        mapping[root_name] = root_init_key
        direct_names.add(root_name)
    for alias, owners in layout_alias_owners.items():
        if alias not in direct_names and len(owners) == 1:
            mapping[alias] = next(iter(owners))
    return mapping
def _scan_module(path: str, root: str) -> dict[str, Any]:
    rel_path = _relative_audit_path(path, root)
    result: dict[str, Any] = {
        "file": path,
        "rel_path": rel_path,
        "module": os.path.splitext(os.path.basename(path))[0],
        "module_key": (_dotted_module_name(rel_path) or
                       os.path.splitext(os.path.basename(path))[0]),
        "lines": 0,
        "has_getlogger": False,
        "log_calls": 0,
        "struct_event_calls": 0,
        "perf_calls": 0,
        "swallow_calls": 0,
        "silent_excepts": [],
        "silent_exempts": [],
        "is_pure_constants": False,
        "has_except_handlers": False,
        "has_load_event": False,
        "sink_bypasses": [],
    }
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError as e:
        log_swallowed(__name__, e,
                      context=f'_scan_module:read:{type(e).__name__}')
        result["error"] = f"read failed: {e}"
        return result
    src = decode_source_bytes(raw)
    result["lines"] = count_lines(src)
    try:
        tree = ast.parse(raw)
    except PARSE_DEGRADE_EXC as e:
        log_swallowed(__name__, e,
                      context=f'_scan_module:parse:{type(e).__name__}')
        result["parse_error"] = (
            f"line {getattr(e, 'lineno', 0)}: "
            f"{getattr(e, 'msg', None) or e}")
        return result
    result["is_pure_constants"] = not _has_exec_surface(tree)
    result["has_except_handlers"] = _has_except_handlers(tree)
    bindings, has_getlogger = _collect_logger_bindings(tree)
    result["has_getlogger"] = has_getlogger
    _collect_runtime_events(tree, bindings, result,
                            _marked_silent_lines(tree, src))
    result["has_load_event"] = _detect_load_event(tree, bindings)
    result["sink_bypasses"] = _scan_sink_bypasses(
        tree, bindings.logger_vars, bindings.logger_factory_names)
    return result
_SPECIAL_LOGGER_CHANNELS = frozenset({
    "audit", "perf", "bug_intercept", "unhandled",
    "detector_liveness", "defense_feedback",
    "warnings",
})
_PERF_LOGGER_CHANNEL = "perf"
_COVERAGE_GAP_HIGH_LINES = 800
_COVERAGE_GAP_MEDIUM_LINES = 300
_SILENT_HOTSPOT_THRESHOLD = 15
_SILENT_POSITION_SAMPLE = 5
_ZERO_INSTRUMENTATION_SAMPLE = 30
_SINK_SANCTIONED_MODULES = frozenset({"log_config"})
_PRODUCT_LOGGER_NAMESPACE = PACKAGE_NAME
_SOURCE_LAYOUT_ROOT_NAMES_LOWER = frozenset(
    name.lower() for name in SOURCE_LAYOUT_ROOT_NAMES)
_NON_PRODUCT_LOGGER_ROOTS = frozenset({"__main__"})
_SANCTIONED_FOREIGN_LOGGERS = frozenset({"py.warnings"})
_LOG_DIR_TRANSIENT_SUFFIXES = (".tmp",)
_PRUNE_TMP_MARKER = ".prune_tmp"
_PRUNE_TRANSIENT_GRACE_SECONDS = 300.0
_FOREIGN_NAMESPACE_SAMPLE = 10
_FILE_HANDLER_NAMES = frozenset({
    "FileHandler", "RotatingFileHandler", "TimedRotatingFileHandler",
    "WatchedFileHandler", "BaseRotatingHandler",
})
_LOGGING_NAMESPACE = "logging"
_LOGGING_HANDLERS_MODULE = "logging.handlers"
_LOG_PROXY_FUNCS = frozenset({"fail_cli", "_emit_cli_error"})
_SINK_KIND_FILE_HANDLER = "file_handler"
_SINK_KIND_BASIC_CONFIG = "basic_config_filename"
_SINK_KIND_ADD_HANDLER = "add_handler"
_MODULE_SINK_KINDS = {
    **dict.fromkeys(_FILE_HANDLER_NAMES, _SINK_KIND_FILE_HANDLER),
    "basicConfig": _SINK_KIND_BASIC_CONFIG,
}
_DIRECT_SINK_KINDS = dict(_MODULE_SINK_KINDS)
def _stable_id(finding_type: str, module: str) -> str:
    raw = f"{finding_type}|{module}"
    return "LCO-" + hashlib.md5(raw.encode("utf-8"), usedforsecurity=False).hexdigest()[:12]
def _scan_identity(scan: dict[str, Any]) -> str:
    rel_path = scan.get("rel_path")
    if isinstance(rel_path, str) and rel_path:
        return rel_path
    return str(scan.get("module", ""))
class _FindingSpec(NamedTuple):
    finding_type: str
    module: str
    severity: str
    title: str
    description: str
    suggested_action: str
    source: str
    pattern_data: dict[str, Any]
    log_evidence: list[dict[str, Any]] | None = None
    identity: str = ""
class _ExposureSignals(NamedTuple):
    exposed: set[str]
    total_log_lines: int
    perf_entries: int
class _LoadSignals(NamedTuple):
    loaded_modules: set[str]
    load_failure_entries: int
class _RuntimeSignals(NamedTuple):
    exposed: set[str]
    total_log_lines: int
    perf_entries: int
    loaded_modules: set[str]
    load_failure_entries: int
    log_read_error: str | None
class _AuditReportInputs(NamedTuple):
    target_dir: str
    static: dict[str, Any]
    runtime: _RuntimeSignals
    metrics: dict[str, Any]
    findings: list[dict[str, Any]]
    elapsed_s: float
    test_channel: dict[str, Any]
def _make_finding(spec: _FindingSpec) -> dict[str, Any]:
    return {
        "finding_id": _stable_id(
            spec.finding_type, spec.identity or spec.module),
        "finding_type": spec.finding_type,
        "severity": spec.severity,
        "title": spec.title,
        "description": spec.description,
        "suggested_action": spec.suggested_action,
        "source": spec.source,
        "log_evidence": (spec.log_evidence or [])[:5],
        "pattern_data": spec.pattern_data,
        "status": "open",
        "created_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "resolved_at": "",
        "resolution": "",
    }
def _ratio(part: int, whole: int) -> float:
    return (part / whole) if whole else 0.0
def _coverage_gap_severity(lines: int) -> str:
    if lines >= _COVERAGE_GAP_HIGH_LINES:
        return "high"
    if lines >= _COVERAGE_GAP_MEDIUM_LINES:
        return "medium"
    return "low"
def _is_tests_path(scan: dict[str, Any],
                   root: str | None = None) -> bool:
    rel = scan.get("rel_path")
    if not isinstance(rel, str) or not rel:
        if not root:
            return False
        rel = _relative_audit_path(str(scan.get("file", "")), root)
    if not rel:
        return False
    return is_test_file_path(rel)
def _is_coverage_gap(scan: dict[str, Any],
                     test_channel_active: bool) -> bool:
    if _scan_error(scan) or _has_instrumentation(scan) or scan.get("is_pure_constants"):
        return False
    if test_channel_active and _is_tests_path(scan):
        return False
    return bool(scan.get("has_except_handlers"))
def _find_coverage_gap_findings(scans: list[dict[str, Any]],
                                test_channel_active: bool
                                ) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for scan in scans:
        if not _is_coverage_gap(scan, test_channel_active):
            continue
        lines = scan["lines"]
        module = scan["module"]
        severity = _coverage_gap_severity(lines)
        findings.append(_make_finding(_FindingSpec(
            finding_type="log_coverage_gap",
            module=module,
            severity=severity,
            title=f"日志盲区: {module} 零埋点（{lines} 行）",
            description=f"模块 {module} 共 {lines} 行，logger 与统一日志结构化事件"
                         f"通道均零调用——其运行情况、缺陷与异常在统一日志中完全不可见",
            suggested_action=f"为 {module} 添加 logger 埋点（getLogger(__name__)）或接入 "
                              f"log_config/log_analysis 结构化事件（write_audit/perf_trace 等），"
                              f"关键路径与 except 块补充 warning/error 级日志",
            source="codebase_scan",
            pattern_data={"module": module, "lines": lines},
            identity=_scan_identity(scan),
        )))
    return findings
def _find_sink_bypass_findings(scans: list[dict[str, Any]],
                              test_channel_active: bool
                              ) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for scan in scans:
        if not _has_sink_bypass(scan, test_channel_active):
            continue
        hits = scan.get("sink_bypasses") or []
        module = scan["module"]
        kinds = sorted({h["kind"] for h in hits})
        positions = [h["line"] for h in hits]
        severity = ("high" if _SINK_KIND_FILE_HANDLER in kinds else "medium")
        findings.append(_make_finding(_FindingSpec(
            finding_type="log_sink_bypass",
            module=module,
            severity=severity,
            title=f"日志旁路: {module} 自建 logging 落点（{len(hits)} 处）",
            description=(
                f"模块 {module} 在行 {positions} 装配自有日志落点"
                f"（形态 {kinds}）——不经过统一栈，绕开 JSON schema 对齐、"
                f"敏感字段脱敏、20M 单文件截断、重复消息过滤与跨进程写锁，"
                f"其日志可能落出技能根 log/ 或与统一日志格式撕裂"),
            suggested_action=(
                "改为消费统一栈：初始化走 log_config.setup_logging()，"
                "文件通道用 log_config.TruncatingFileHandler + JsonFormatter；"
                "确需独立通道时在 cleanup_artifacts.FEEDBACK_ARTIFACTS "
                "登记落点与"
                "消费方，并复用 append_jsonl_locked 的行级写锁"),
            source="codebase_scan",
            pattern_data={"module": module, "kinds": kinds,
                          "positions": positions},
            identity=_scan_identity(scan),
        )))
    return findings
def _within_prune_grace(path: str) -> bool:
    if not path:
        return True
    try:
        age = time.time() - os.path.getmtime(path)
    except FileNotFoundError:
        return True
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'_within_prune_grace:{type(_e).__name__}')
        return False
    return age <= _PRUNE_TRANSIENT_GRACE_SECONDS
def _is_prune_transient(fname: str, log_dir: str,
                        registry: frozenset[str] | None) -> bool:
    if registry is None:
        return False
    head, sep, tail = fname.partition(_PRUNE_TMP_MARKER)
    if not sep or head not in registry:
        return False
    if tail:
        if not tail.startswith("."):
            return False
        if not all(part.isdecimal() for part in tail[1:].split(".")):
            return False
    return _within_prune_grace(
        os.path.join(log_dir, fname) if log_dir else "")
def _is_registered_log_artifact(
        fname: str, log_dir: str,
        registry: frozenset[str] | None) -> bool:
    if registry is None:
        return False
    if fname in registry:
        return True
    for suffix in _LOG_DIR_TRANSIENT_SUFFIXES:
        if fname.endswith(suffix) and fname[:-len(suffix)] in registry:
            return True
    if _is_prune_transient(fname, log_dir, registry):
        return True
    base, dot, suffix = fname.rpartition(".")
    return bool(dot) and suffix.isdecimal() and base in registry
def _scan_log_dir_hygiene(
        log_dir: str | None,
        registry: frozenset[str] | None) -> dict[str, Any]:
    result: dict[str, Any] = {
        "log_dir": log_dir or "",
        "registered_count": 0,
        "unregistered": [],
        "subdirectories": [],
        "total": 0,
        "error": None,
    }
    if registry is None or not log_dir or not os.path.isdir(log_dir):
        return result
    try:
        names = sorted(os.listdir(log_dir))
    except OSError as e:
        log_swallowed(__name__, e,
                      context=f'_scan_log_dir_hygiene:{type(e).__name__}')
        result["error"] = f"listdir failed: {type(e).__name__}: {e}"
        return result
    registered = 0
    unregistered: list[str] = []
    subdirectories: list[str] = []
    for name in names:
        if os.path.isdir(os.path.join(log_dir, name)):
            subdirectories.append(name)
            unregistered.append(name)
            continue
        if _is_registered_log_artifact(name, log_dir, registry):
            registered += 1
            continue
        unregistered.append(name)
    result["registered_count"] = registered
    result["unregistered"] = unregistered
    result["subdirectories"] = subdirectories
    result["total"] = registered + len(unregistered)
    return result
def _same_physical_path(left: str, right: str) -> bool:
    try:
        return (os.path.normcase(os.path.realpath(left))
                == os.path.normcase(os.path.realpath(right)))
    except OSError as e:
        log_swallowed(__name__, e,
                      context=f'_same_physical_path:{type(e).__name__}')
        return False
def _log_artifact_registry(
        log_dir: str | None,
        target_dir: str | None = None) -> frozenset[str] | None:
    if not log_dir:
        return None
    try:
        own_dir = get_log_dir()
    except (OSError, RuntimeError, ValueError) as e:
        log_swallowed(__name__, e,
                      context=f'_log_artifact_registry:{type(e).__name__}')
        own_dir = None
    if own_dir and _same_physical_path(log_dir, own_dir):
        return ACTIVE_FILES
    if target_dir and os.path.isfile(os.path.join(target_dir, "SKILL.md")):
        return ACTIVE_FILES
    return None
def _effective_product_roots(
        product_roots: frozenset[str] | None) -> frozenset[str]:
    return (product_roots if product_roots
            else frozenset({_PRODUCT_LOGGER_NAMESPACE}))
def _product_logger_roots(
    scans: list[dict[str, Any]],
    target_dir: str,
) -> frozenset[str]:
    roots: set[str] = set()
    for scan in scans:
        key = _scan_key(scan)
        if isinstance(key, str) and key:
            roots.add(key.split(".", 1)[0])
            layout_alias = _without_source_layout_root(key)
            if layout_alias:
                roots.add(layout_alias.split(".", 1)[0])
    if target_dir:
        roots.add(os.path.basename(os.path.normpath(target_dir)))
    return _effective_product_roots(
        frozenset(root for root in roots if root))
def _foreign_log_namespaces(
    entries: list[dict[str, Any]] | None,
    product_roots: frozenset[str] | None = None,
) -> list[dict[str, Any]]:
    roots = _effective_product_roots(product_roots)
    counts: dict[str, int] = {}
    for entry in entries or []:
        if not isinstance(entry, dict):
            continue
        logger_name = entry.get("logger")
        if not isinstance(logger_name, str) or not logger_name:
            continue
        root = logger_name.split(".", 1)[0]
        if root in roots and root not in _NON_PRODUCT_LOGGER_ROOTS:
            continue
        if logger_name in _SANCTIONED_FOREIGN_LOGGERS:
            continue
        counts[logger_name] = counts.get(logger_name, 0) + 1
    ordered = sorted(counts.items(), key=lambda item: (-item[1], item[0]))
    return [{"logger": name, "count": count}
            for name, count in ordered]
def _find_log_hygiene_findings(
    hygiene: dict[str, Any],
    foreign: list[dict[str, Any]],
    product_roots: frozenset[str] | None = None,
) -> list[dict[str, Any]]:
    roots_label = "、".join(sorted(product_roots or ())) or _PRODUCT_LOGGER_NAMESPACE
    findings: list[dict[str, Any]] = []
    error = hygiene.get("error")
    if error:
        module = hygiene.get("log_dir") or "log"
        findings.append(_make_finding(_FindingSpec(
            finding_type="log_dir_scan_error",
            module=module,
            severity="medium",
            title=f"日志目录扫描失败: {module} 未判定",
            description=(
                f"日志目录 {module} 枚举失败（{error}）——目录内已登记、"
                "未登记与轮转产物均未判定，不得按零缺陷处理"),
            suggested_action=(
                "修复日志目录读取权限或路径后重新运行日志覆盖度审计；"
                "扫描成功前不要将该目录计为已完成卫生检查"),
            source="log_dir_scan",
            pattern_data={"log_dir": hygiene.get("log_dir"),
                          "error": error},
            identity="log_dir_hygiene_error",
        )))
    unregistered = list(hygiene.get("unregistered") or [])
    if unregistered:
        findings.append(_make_finding(_FindingSpec(
            finding_type="unregistered_log_artifact",
            module=hygiene.get("log_dir") or "log",
            severity="medium",
            title=f"日志目录存在未登记产物: {', '.join(unregistered[:5])}",
            description=(
                "日志落点只允许 log_config.ACTIVE_FILES 登记的产物；"
                f"目录内未登记条目 {unregistered} 说明有写入方绕过统一栈，"
                "其内容不与 JSON schema 对齐、不参与滚动截断与消费游标"),
            suggested_action=(
                "确认写入方后二选一：改为经 log_config 统一栈落盘；"
                "确需独立通道时在 cleanup_artifacts.FEEDBACK_ARTIFACTS 与 "
                "log_config.ACTIVE_FILES 登记落点与消费方"),
            source="log_dir_scan",
            pattern_data={"log_dir": hygiene.get("log_dir"),
                          "unregistered": unregistered},
            identity="log_dir_hygiene",
        )))
    if foreign:
        foreign_sample = foreign[:_FOREIGN_NAMESPACE_SAMPLE]
        names = [item["logger"] for item in foreign_sample]
        findings.append(_make_finding(_FindingSpec(
            finding_type="foreign_log_namespace",
            module=hygiene.get("log_dir") or "log",
            severity="low",
            title=f"产品日志出现外部命名空间: {', '.join(names[:5])}",
            description=(
                f"主日志中存在不属于目标产品命名空间（{roots_label}）的 "
                f"logger {names}——外部进程（临时脚本/探针/生成器）正在写"
                "产品日志，按 logger 前缀的归因与告警路由会把它们误归给产品模块"),
            suggested_action=(
                "非产品运行（测试、探针、生成脚本）经 "
                f"{LOG_DIR_ENV_VAR} 指向独立日志目录；"
                f"测试辅助模块改用 {roots_label}.tests.* 命名空间"),
            source="runtime_log_scan",
            pattern_data={
                "foreign_loggers": foreign,
                "foreign_loggers_sample": foreign_sample,
                "foreign_log_namespace_total": len(foreign),
            },
            identity="foreign_log_namespace",
        )))
    return findings
def _find_silent_hotspot_findings(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for scan in scans:
        positions = scan.get("silent_excepts") or []
        if len(positions) < _SILENT_HOTSPOT_THRESHOLD:
            continue
        module = scan["module"]
        findings.append(_make_finding(_FindingSpec(
            finding_type="silent_except_hotspot",
            module=module,
            severity="medium",
            title=f"静默异常热点: {module} 有 {len(positions)} 处无日志无再抛的 except 块",
            description=f"模块 {module} 存在 {len(positions)} 处 except 块既无日志调用也无 "
                        f"raise 再抛——运行时被吞没的异常在日志中不可见，构成静默降级盲区",
            suggested_action=f"为 {module} 的静默 except 块补充日志（logger.warning 带 exc_info "
                              f"或 log_swallowed），关键路径改为显式处理或再抛",
            source="codebase_scan",
            pattern_data={"module": module, "silent_except_count": len(positions)},
            log_evidence=[
                {"file": scan["file"], "line": ln} for ln in positions[:_SILENT_POSITION_SAMPLE]
            ],
            identity=_scan_identity(scan),
        )))
    return findings
def _scans_project_label(scans: list[dict[str, Any]]) -> str:
    dirs = [os.path.dirname(str(scan.get("file", "")))
            for scan in scans if scan.get("file")]
    if not dirs:
        return "project"
    try:
        common = os.path.commonpath(dirs)
    except ValueError as e:
        log_swallowed(__name__, e,
                      context=f'_scans_project_label:{type(e).__name__}')
        return "project"
    return os.path.basename(os.path.normpath(common)) or "project"
def _find_swallow_idle_finding(
    scans: list[dict[str, Any]],
    swallow_producers: int,
    target_label: str | None = None,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    product_scans = [
        scan for scan in scans
        if (not scan.get("is_pure_constants")
            and scan.get("has_except_handlers")
            and not _is_tests_path(scan))
    ]
    if swallow_producers == 0 and product_scans:
        label = target_label or _scans_project_label(product_scans)
        findings.append(_make_finding(_FindingSpec(
            finding_type="swallow_channel_idle",
            module=label,
            severity="high",
            title=f"静默异常治理通道空转: {label} 的 log_swallowed 零生产者",
            description=f"{label} 的产品代码接入 log_swallowed 通道的调用点为零"
                        "——被吞异常永远不会出现在日志中，"
                        "静默异常分析恒消费空数据源",
            suggested_action=f"为 {label} 的典型吞异常路径（降级/兜底/兼容分支）"
                              "接入 log_swallowed 或 logger.warning 留痕，"
                              "使静默路径运行时可观测",
            source="codebase_scan",
            pattern_data={"module": label, "swallow_producers": 0},
        )))
    return findings
def _find_scan_error_findings(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for scan in scans:
        error = _scan_error(scan)
        if not error:
            continue
        module = scan["module"]
        identity = _scan_identity(scan)
        findings.append(_make_finding(_FindingSpec(
            finding_type="log_scan_error",
            module=module,
            severity="medium",
            title=f"日志扫描失败: {identity} 未判定",
            description=(
                f"模块 {identity} 读取或解析失败（{error}）——该文件未进入"
                "有效扫描面，其埋点、加载事件、静默 except 与日志旁路均未判定，"
                "不得按零缺陷处理"),
            suggested_action=(
                "修复文件读取、编码或语法错误后重新运行日志覆盖度审计；"
                "扫描成功前不要将该模块计为已覆盖"),
            source="codebase_scan",
            pattern_data={"module": module, "rel_path": identity,
                          "error": error},
            identity=identity,
        )))
    return findings
def _build_findings(scans: list[dict[str, Any]],
                    swallow_producers: int,
                    test_channel_active: bool,
                    target_label: str | None = None,
                    *,
                    hygiene: dict[str, Any] | None = None,
                    foreign_namespaces: list[dict[str, Any]] | None = None,
                    product_roots: frozenset[str] | None = None,
                    ) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    findings.extend(_find_scan_error_findings(scans))
    findings.extend(_find_coverage_gap_findings(scans, test_channel_active))
    findings.extend(_find_silent_hotspot_findings(scans))
    findings.extend(_find_swallow_idle_finding(
        scans, swallow_producers, target_label))
    findings.extend(_find_sink_bypass_findings(scans, test_channel_active))
    findings.extend(_find_log_hygiene_findings(
        hygiene or {}, list(foreign_namespaces or []), product_roots))
    return findings
def _module_from_logger(
    logger_name: str,
    module_paths: dict[str, str],
) -> str | None:
    if not logger_name:
        return None
    module = module_paths.get(logger_name)
    if module is not None:
        return module
    parent = logger_name
    while "." in parent:
        parent = parent.rsplit(".", 1)[0]
        module = module_paths.get(parent)
        if module is not None:
            return module
    return None
def _logger_in_channels(logger_name: str, channels: frozenset[str]) -> bool:
    return any(logger_name == channel or logger_name.startswith(channel + ".")
               for channel in channels)
def _special_loggers(
        product_roots: frozenset[str] | None = None,
) -> frozenset[str]:
    roots = _effective_product_roots(product_roots)
    names = {f"{root}.{channel}"
             for root in roots for channel in _SPECIAL_LOGGER_CHANNELS}
    names |= _SANCTIONED_FOREIGN_LOGGERS
    return frozenset(names)
def _perf_loggers(
        product_roots: frozenset[str] | None = None,
) -> frozenset[str]:
    roots = _effective_product_roots(product_roots)
    return frozenset(f"{root}.{_PERF_LOGGER_CHANNEL}" for root in roots)
def _runtime_exposure(
    entries: list[dict[str, Any]],
    module_paths: dict[str, str],
    product_roots: frozenset[str] | None = None,
) -> _ExposureSignals:
    special = _special_loggers(product_roots)
    perf_loggers = _perf_loggers(product_roots)
    exposed: set[str] = set()
    perf_count = 0
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        lg = entry.get("logger", "")
        if not isinstance(lg, str):
            continue
        event = entry.get("event")
        if event in ("module_load", "module_load_failure"):
            continue
        module = _module_from_logger(lg, module_paths)
        module_evidence = module is not None and (
            event is None or event in (
                "module_run", "module_run_repeat", "swallowed_exception"))
        if _logger_in_channels(lg, perf_loggers) and not module_evidence:
            perf_count += 1
        if _logger_in_channels(lg, special) and not module_evidence:
            continue
        if module is not None:
            exposed.add(module)
    return _ExposureSignals(exposed, len(entries), perf_count)
def _runtime_module_loads(
    entries: list[dict[str, Any]],
    module_paths: dict[str, str],
) -> _LoadSignals:
    loaded: set[str] = set()
    load_failures = 0
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        evt = entry.get("event")
        if evt not in ("module_load", "module_load_failure"):
            continue
        lg = entry.get("logger", "")
        if not isinstance(lg, str):
            continue
        module = _module_from_logger(lg, module_paths)
        if module is None:
            continue
        if evt == "module_load_failure":
            load_failures += 1
        else:
            loaded.add(module)
    return _LoadSignals(loaded, load_failures)
def _has_instrumentation(scan: dict[str, Any]) -> bool:
    return scan["log_calls"] > 0 or scan["struct_event_calls"] > 0
def _is_zero_instrumented(scan: dict[str, Any]) -> bool:
    return not _has_instrumentation(scan) and not scan.get("is_pure_constants")
def _is_struct_only(scan: dict[str, Any]) -> bool:
    return scan["log_calls"] == 0 and scan["struct_event_calls"] > 0
def _is_zombie_logger(scan: dict[str, Any],
                     test_channel_active: bool) -> bool:
    if test_channel_active and _is_tests_path(scan):
        return False
    return scan["has_getlogger"] and scan["log_calls"] == 0
def _lacks_load_event(scan: dict[str, Any]) -> bool:
    return (not scan.get("has_load_event")
            and (_has_instrumentation(scan) or bool(scan.get("has_getlogger")))
            and not scan.get("is_pure_constants"))
def _has_perf_calls(scan: dict[str, Any]) -> bool:
    return scan["perf_calls"] > 0
def _is_test_capture_probe(scan: dict[str, Any]) -> bool:
    hits = scan.get("sink_bypasses") or []
    return bool(hits) and all(h["kind"] == _SINK_KIND_ADD_HANDLER for h in hits)
def _is_sanctioned_sink_module(scan: dict[str, Any]) -> bool:
    if scan["module"] not in _SINK_SANCTIONED_MODULES:
        return False
    rel_path = scan.get("rel_path")
    module_key = scan.get("module_key")
    keys: set[str] = set()
    if isinstance(module_key, str) and module_key:
        keys.add(module_key)
    if isinstance(rel_path, str) and rel_path:
        keys.add(_dotted_module_name(rel_path))
    if not keys:
        return True
    sanctioned = {"log_config", f"{_PRODUCT_LOGGER_NAMESPACE}.log_config"}
    return any(
        key in sanctioned or _without_source_layout_root(key) in sanctioned
        for key in keys
    )
def _has_sink_bypass(scan: dict[str, Any],
                     test_channel_active: bool) -> bool:
    hits = scan.get("sink_bypasses") or []
    if not hits or _is_sanctioned_sink_module(scan):
        return False
    if test_channel_active and _is_tests_path(scan):
        return not _is_test_capture_probe(scan)
    return True
def _bin_instrumentation(bins: dict[str, list], scan: dict[str, Any]) -> None:
    module = scan["module"]
    if _has_instrumentation(scan):
        bins["instrumented"].append(scan)
    if scan.get("is_pure_constants"):
        bins["pure_constant_modules"].append(module)
    if _is_struct_only(scan):
        bins["struct_only"].append(
            {"module": module, "struct_event_calls": scan["struct_event_calls"]})
    if _has_perf_calls(scan):
        bins["perf_instrumented"].append(
            {"module": module, "perf_calls": scan["perf_calls"]})
def _bin_zero_instrumentation(bins: dict[str, list], scan: dict[str, Any],
                              test_channel_active: bool) -> None:
    if not _is_zero_instrumented(scan):
        return
    item = {"module": scan["module"], "module_key": _scan_key(scan),
            "lines": scan["lines"]}
    if test_channel_active and _is_tests_path(scan):
        bins["test_channel_modules"].append(item)
    else:
        bins["zero_inst"].append(item)
def _bin_logger_channel(bins: dict[str, list], scan: dict[str, Any],
                        test_channel_active: bool) -> None:
    item = {"module": scan["module"], "lines": scan["lines"]}
    if _is_zombie_logger(scan, test_channel_active):
        bins["zombie_loggers"].append(item)
    elif (test_channel_active and _is_tests_path(scan)
          and scan["has_getlogger"]):
        bins["test_channel_loggers"].append(item)
def _bin_sink_channel(bins: dict[str, list], scan: dict[str, Any],
                      test_channel_active: bool) -> None:
    if _has_sink_bypass(scan, test_channel_active):
        bins["sink_bypass"].append({
            "module": scan["module"],
            "kinds": [h["kind"] for h in scan["sink_bypasses"]],
            "positions": [h["line"] for h in scan["sink_bypasses"]],
        })
    elif (test_channel_active and _is_tests_path(scan)
          and _is_test_capture_probe(scan)):
        bins["test_capture_probes"].append({
            "module": scan["module"],
            "positions": [h["line"] for h in scan["sink_bypasses"]],
        })
def _bin_one_scan(bins: dict[str, list], scan: dict[str, Any],
                  test_channel_active: bool) -> None:
    _bin_instrumentation(bins, scan)
    _bin_zero_instrumentation(bins, scan, test_channel_active)
    _bin_logger_channel(bins, scan, test_channel_active)
    _bin_sink_channel(bins, scan, test_channel_active)
def _sort_classification_bins(bins: dict[str, list]) -> dict[str, list]:
    bins["pure_constant_modules"].sort()
    bins["test_channel_modules"].sort(key=lambda x: x["module"])
    bins["test_capture_probes"].sort(key=lambda x: x["module"])
    bins["test_channel_loggers"].sort(key=lambda x: x["module"])
    bins["sink_bypass"].sort(key=lambda x: x["module"])
    bins["perf_instrumented"].sort(key=lambda x: (-x["perf_calls"], x["module"]))
    bins["zero_inst"].sort(key=lambda x: (-x["lines"], x["module"]))
    bins["struct_only"].sort(
        key=lambda x: (-x["struct_event_calls"], x["module"]))
    bins["zombie_loggers"].sort(key=lambda x: (-x["lines"], x["module"]))
    return bins
def _classify_module_lists(valid_scans: list[dict[str, Any]],
                           test_channel_active: bool) -> dict[str, Any]:
    bins: dict[str, list] = {
        "instrumented": [],
        "zero_inst": [],
        "test_channel_modules": [],
        "pure_constant_modules": [],
        "struct_only": [],
        "perf_instrumented": [],
        "zombie_loggers": [],
        "sink_bypass": [],
        "test_capture_probes": [],
        "test_channel_loggers": [],
    }
    for scan in valid_scans:
        _bin_one_scan(bins, scan, test_channel_active)
    return _sort_classification_bins(bins)
def _summarize_silent_channel(valid_scans: list[dict[str, Any]]) -> dict[str, Any]:
    silent_total = sum(len(s["silent_excepts"]) for s in valid_scans)
    test_silent = sum(len(s["silent_excepts"]) for s in valid_scans
                      if _is_tests_path(s))
    silent_modules = sorted(
        (s for s in valid_scans if s["silent_excepts"]),
        key=lambda x: (-len(x["silent_excepts"]), x["module"]))
    hotspots = [
        {
            "module": s["module"],
            "count": len(s["silent_excepts"]),
            "positions": s["silent_excepts"][:_SILENT_POSITION_SAMPLE],
        }
        for s in silent_modules
    ]
    exempt_hotspots = [
        {
            "module": s["module"],
            "count": len(s["silent_exempts"]),
            "positions": s["silent_exempts"][:_SILENT_POSITION_SAMPLE],
        }
        for s in sorted(
            (s for s in valid_scans if s.get("silent_exempts")),
            key=lambda x: (-len(x["silent_exempts"]), x["module"]))
    ]
    return {
        "silent_total": silent_total,
        "silent_exempt_total": sum(len(s.get("silent_exempts") or [])
                                   for s in valid_scans),
        "exempt_hotspots": exempt_hotspots,
        "test_silent_total": test_silent,
        "product_silent_total": silent_total - test_silent,
        "silent_modules": silent_modules,
        "hotspots": hotspots,
    }
def _scan_error(scan: dict[str, Any]) -> str | None:
    return scan.get("parse_error") or scan.get("error")
def _split_scans(scans: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    parse_errors = [
        {"module": s["module"], "error": _scan_error(s)}
        for s in scans if _scan_error(s)
    ]
    valid_scans = [s for s in scans if not _scan_error(s)]
    return parse_errors, valid_scans
def _list_no_load_event(valid_scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    no_load_event = [
        {"module": s["module"], "lines": s["lines"]}
        for s in valid_scans if _lacks_load_event(s)
    ]
    no_load_event.sort(key=lambda x: (-x["lines"], x["module"]))
    return no_load_event
def _summarize_static_scans(scans: list[dict[str, Any]],
                           test_channel_active: bool) -> dict[str, Any]:
    parse_errors, valid_scans = _split_scans(scans)
    classified = _classify_module_lists(valid_scans, test_channel_active)
    test_swallow = sum(s["swallow_calls"] for s in valid_scans
                       if _is_tests_path(s))
    swallow_producers = sum(s["swallow_calls"] for s in valid_scans) - test_swallow
    no_load_event = _list_no_load_event(valid_scans)
    silent = _summarize_silent_channel(valid_scans)
    return {
        "parse_errors": parse_errors,
        "valid_scans": valid_scans,
        "total_modules": len(valid_scans),
        "instrumented": classified["instrumented"],
        "zero_inst": classified["zero_inst"],
        "test_channel_modules": classified["test_channel_modules"],
        "pure_constant_modules": classified["pure_constant_modules"],
        "struct_only": classified["struct_only"],
        "perf_instrumented": classified["perf_instrumented"],
        "zombie_loggers": classified["zombie_loggers"],
        "sink_bypass": classified["sink_bypass"],
        "test_capture_probes": classified["test_capture_probes"],
        "test_channel_loggers": classified["test_channel_loggers"],
        "swallow_producers": swallow_producers,
        "test_swallow_producers": test_swallow,
        "no_load_event": no_load_event,
        "silent_total": silent["silent_total"],
        "test_silent_total": silent["test_silent_total"],
        "product_silent_total": silent["product_silent_total"],
        "silent_modules": silent["silent_modules"],
        "hotspots": silent["hotspots"],
        "silent_exempt_total": silent["silent_exempt_total"],
        "exempt_hotspots": silent["exempt_hotspots"],
    }
def _load_runtime_signals(
    entries: list[dict[str, Any]],
    module_paths: dict[str, str],
    *,
    load_error: str | None = None,
    product_roots: frozenset[str] | None = None,
) -> _RuntimeSignals:
    try:
        exposure = _runtime_exposure(entries, module_paths, product_roots)
        loads = _runtime_module_loads(entries, module_paths)
    except Exception as e:
        log_swallowed(__name__, e,
                      context=f'_load_runtime_signals:{type(e).__name__}')
        return _RuntimeSignals(set(), 0, 0, set(), 0, str(e)[:200])
    return _RuntimeSignals(
        exposure.exposed,
        exposure.total_log_lines,
        exposure.perf_entries,
        loads.loaded_modules,
        loads.load_failure_entries,
        load_error,
    )
def _derive_coverage_metrics(
    static: dict[str, Any],
    exposed: set[str],
    loaded_modules: set[str],
    *, evidence_measured: bool = True,
) -> dict[str, Any]:
    valid_scans: list[dict[str, Any]] = static["valid_scans"]
    total_modules = static["total_modules"]
    if not evidence_measured:
        exposed = set()
        loaded_modules = set()
    blind_no_inst = sorted({
        _scan_key(z) for z in static["zero_inst"]
        if _scan_key(z) not in exposed
    }) if evidence_measured else []
    blind_not_executed = sorted({
        _scan_key(s) for s in static["instrumented"]
        if _scan_key(s) not in exposed
    }) if evidence_measured else []
    exposed_count = sum(
        1 for scan in valid_scans if _scan_key(scan) in exposed)
    loaded_count = sum(
        1 for scan in valid_scans if _scan_key(scan) in loaded_modules)
    return {
        "total_modules": total_modules,
        "runtime_evidence_measured": evidence_measured,
        "blind_no_instrumentation": blind_no_inst,
        "blind_not_executed": blind_not_executed,
        "exposed_count": exposed_count,
        "loaded_count": loaded_count,
        "coverage_rate": _ratio(exposed_count, total_modules),
        "load_coverage_rate": _ratio(loaded_count, total_modules),
    }
def _codebase_section(inputs: _AuditReportInputs) -> dict[str, Any]:
    static = inputs.static
    zero_inst = static["zero_inst"]
    return {
        "total_modules": inputs.metrics["total_modules"],
        "with_logger_calls": sum(
            1 for scan in static.get("valid_scans") or []
            if scan["log_calls"] > 0),
        "zero_instrumentation": zero_inst,
        "zero_instrumentation_sample": zero_inst[:_ZERO_INSTRUMENTATION_SAMPLE],
        "test_channel_modules": static.get("test_channel_modules", []),
        "pure_constant_modules": static["pure_constant_modules"],
        "struct_event_only_modules": static["struct_only"],
        "perf_instrumented_modules": static["perf_instrumented"],
        "zombie_loggers": static["zombie_loggers"],
        "without_load_event": static["no_load_event"],
        "parse_errors": static["parse_errors"],
    }
def _runtime_section(inputs: _AuditReportInputs) -> dict[str, Any]:
    runtime = inputs.runtime
    metrics = inputs.metrics
    return {
        "total_log_lines": runtime.total_log_lines,
        "evidence_measured": metrics["runtime_evidence_measured"],
        "exposed_modules": metrics["exposed_count"],
        "coverage_rate": round(metrics["coverage_rate"], 4),
        "loaded_modules": metrics["loaded_count"],
        "module_load_coverage_rate": round(metrics["load_coverage_rate"], 4),
        "module_load_failures": runtime.load_failure_entries,
        "blind_modules": {
            "no_instrumentation": metrics["blind_no_instrumentation"],
            "not_executed": metrics["blind_not_executed"],
        },
        "log_read_error": runtime.log_read_error,
    }
def _count_test_modules(target_dir: str) -> int:
    return sum(
        1 for path in _collect_py_files(target_dir, include_tests=True)
        if is_test_source_basename(os.path.basename(path))
    )
def _is_test_writer_module(module: str | None) -> bool:
    if not isinstance(module, str) or not module:
        return False
    return module.rsplit(".", 1)[-1] == _TEST_CHANNEL_WRITER
def _import_module_refs(node: ast.Import, module_refs: dict[str, str]) -> None:
    for alias in node.names:
        if not _is_test_writer_module(alias.name):
            continue
        bound = alias.asname or alias.name.split(".", 1)[0]
        module_refs[bound] = alias.name if alias.asname else bound
def _importfrom_direct_hooks(node: ast.ImportFrom,
                            direct_hooks: dict[str, str]) -> None:
    for alias in node.names:
        if alias.name in _TEST_HOOK_APIS:
            direct_hooks[alias.asname or alias.name] = alias.name
def _importfrom_module_refs(node: ast.ImportFrom,
                           module_refs: dict[str, str]) -> None:
    for alias in node.names:
        if alias.name != _TEST_CHANNEL_WRITER:
            continue
        prefix = f"{node.module}." if node.module else ""
        canonical = f"{prefix}{alias.name}"
        if _is_test_writer_module(canonical):
            module_refs[alias.asname or alias.name] = canonical
def _iter_live_conftest_nodes(tree: ast.Module):
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.If):
            branch = _runtime_branch_of_static_if(node)
            if branch is not None:
                stack.extend(reversed(branch))
                continue
            if _is_main_guard(node.test):
                stack.extend(reversed(node.orelse))
                continue
        yield node
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _test_hook_import_bindings(tree: ast.Module) -> tuple[dict[str, str], dict[str, str]]:
    module_refs: dict[str, str] = {}
    direct_hooks: dict[str, str] = {}
    for node in _iter_live_conftest_nodes(tree):
        if isinstance(node, ast.Import):
            _import_module_refs(node, module_refs)
        elif isinstance(node, ast.ImportFrom):
            if _is_test_writer_module(node.module):
                _importfrom_direct_hooks(node, direct_hooks)
            else:
                _importfrom_module_refs(node, module_refs)
    return module_refs, direct_hooks
def _called_test_hook(call: ast.Call, module_refs: dict[str, str],
                      direct_hooks: dict[str, str]) -> str:
    if isinstance(call.func, ast.Name):
        return direct_hooks.get(call.func.id, "")
    dotted = dotted_name(call.func)
    root, _sep, rest = dotted.partition(".")
    canonical = module_refs.get(root)
    if canonical is None or not rest:
        return ""
    module, sep, hook = f"{canonical}.{rest}".rpartition(".")
    if sep and _is_test_writer_module(module) and hook in _TEST_HOOK_APIS:
        return hook
    return ""
def _test_hooks_of_conftest(
    conftest: str, errors: list[dict[str, Any]] | None = None,
) -> list[str]:
    if not conftest or not os.path.isfile(conftest):
        return []
    try:
        with open(conftest, "rb") as f:
            tree = ast.parse(f.read())
    except (OSError, LookupError, *PARSE_DEGRADE_EXC) as e:
        log_swallowed(__name__, e,
                      context=f'_test_hooks_of_conftest:{type(e).__name__}')
        if errors is not None:
            errors.append({
                "file": conftest,
                "error": f"{type(e).__name__}: {e}",
            })
        return []
    module_refs, direct_hooks = _test_hook_import_bindings(tree)
    called = {
        hook
        for node in _iter_live_conftest_nodes(tree)
        if isinstance(node, ast.Call)
        if (hook := _called_test_hook(node, module_refs, direct_hooks))
    }
    return [name for name in _TEST_HOOK_APIS if name in called]
def _test_wiring(target_dir: str) -> dict[str, Any]:
    test_dirs = _test_dirs_of(target_dir)
    tests_dir = test_dirs[0] if test_dirs else ""
    candidate = os.path.join(tests_dir, "conftest.py") if tests_dir else ""
    root_candidate = os.path.join(target_dir, "conftest.py")
    conftest = next(
        (path for path in (candidate, root_candidate)
         if path and os.path.isfile(path)),
        "",
    )
    conftests = [
        path
        for directory in (target_dir, *test_dirs)
        if os.path.isfile(path := os.path.join(directory, "conftest.py"))
    ]
    for directory in test_dirs:
        conftests.extend(
            path for path in _collect_py_files(directory, include_tests=True)
            if os.path.basename(path) == "conftest.py"
            and path not in conftests)
    if not conftest and conftests:
        conftest = conftests[0]
    hook_errors: list[dict[str, Any]] = []
    hooks: set[str] = set()
    for path in conftests:
        hooks.update(_test_hooks_of_conftest(path, hook_errors))
    ordered_hooks = [name for name in _TEST_HOOK_APIS if name in hooks]
    return {
        "conftest": conftest,
        "conftests": conftests,
        "hooks": ordered_hooks,
        "errors": hook_errors,
        "wired": len(ordered_hooks) == len(_TEST_HOOK_APIS),
    }
def _target_log_dir(target_dir: str) -> str:
    candidate = os.path.join(target_dir, SKILL_LOG_DIR_NAME)
    return candidate if os.path.isdir(candidate) else ""
def _test_runs_evidence(log_dir: str | None) -> dict[str, Any]:
    _dir = log_dir or ""
    path = os.path.join(_dir, TEST_RUNS_FILE) if _dir else ""
    size_bytes = 0
    if path and os.path.isfile(path):
        try:
            size_bytes = os.path.getsize(path)
        except OSError as e:
            log_swallowed(__name__, e,
                          context=f'_test_runs_evidence:{type(e).__name__}')
    return {
        "runs_file": path,
        "runs_file_bytes": size_bytes,
        "summary": summarize_test_runs(load_test_runs(
            log_dir=_dir, propagate_io=True)),
    }
def _test_channel_probe(target_dir: str, include_tests: bool) -> dict[str, Any]:
    covered_modules = _count_test_modules(target_dir)
    root_conftest = os.path.join(target_dir, "conftest.py")
    section: dict[str, Any] = {
        "applicable": bool(
            covered_modules or _tests_dir_of(target_dir)
            or os.path.isfile(root_conftest)),
        "include_tests_scanned": include_tests,
        "writer": _TEST_CHANNEL_WRITER,
        "reader": _TEST_CHANNEL_READER,
        "active": False,
        "wiring": {},
        "runs_file": "",
        "runs_file_bytes": 0,
        "cases": 0,
        "by_outcome": {},
        "modules_with_evidence": 0,
        "covered_modules": covered_modules,
        "scanned_test_modules": 0,
        "evidence_window": "",
        "evidence_measured": False,
        "no_recent_evidence": [],
        "error": None,
    }
    if not section["applicable"]:
        return section
    try:
        wiring = _test_wiring(target_dir)
        section.update({"active": bool(wiring["wired"]), "wiring": wiring})
        if wiring["errors"]:
            section["error"] = "; ".join(
                f"{item['file']}: {item['error']}"
                for item in wiring["errors"])[:200]
        evidence = _test_runs_evidence(_target_log_dir(target_dir))
        summary = evidence["summary"]
    except Exception as e:
        log_swallowed(__name__, e,
                      context=f'_test_channel_probe:{type(e).__name__}')
        section["error"] = str(e)[:200]
        return section
    evidence_modules = _test_evidence_modules(summary["modules"], target_dir)
    section.update({
        "runs_file": evidence["runs_file"],
        "runs_file_bytes": evidence["runs_file_bytes"],
        "cases": summary["cases"],
        "by_outcome": summary["by_outcome"],
        "modules_with_evidence": len(evidence_modules),
        "evidence_modules": evidence_modules,
    })
    if section["runs_file_bytes"]:
        section["evidence_window"] = (
            f"last {_TEST_RUNS_WINDOW_MB}MB of test_runs.jsonl")
    return section
def _test_module_identity(path: Any) -> str:
    if not isinstance(path, str) or not path:
        return ""
    normalized = path.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized[:-3] if normalized.lower().endswith(".py") else normalized
def _test_evidence_modules(modules: list[str], target_dir: str) -> set[str]:
    identities: set[str] = set()
    target_root = os.path.abspath(target_dir)
    for path in modules:
        if not isinstance(path, str) or not path:
            continue
        absolute = os.path.abspath(
            path if os.path.isabs(path) else os.path.join(target_root, path))
        relative = _relative_audit_path(absolute, target_root)
        identity = _test_module_identity(relative)
        if identity:
            identities.add(identity)
    return identities
def _scanned_test_modules(static: dict[str, Any],
                          target_dir: str | None = None) -> set[str]:
    identities: set[str] = set()
    for scan in static.get("valid_scans") or []:
        if not _is_tests_path(scan, target_dir):
            continue
        path = scan.get("rel_path")
        if not path and target_dir:
            path = _relative_audit_path(str(scan.get("file", "")), target_dir)
        identity = _test_module_identity(path or scan.get("module", ""))
        basename = identity.rsplit("/", 1)[-1] + ".py"
        if identity and is_test_source_basename(basename):
            identities.add(identity)
    return identities
def _test_channel_section(probe: dict[str, Any],
                          static: dict[str, Any],
                          target_dir: str) -> dict[str, Any]:
    section = dict(probe)
    evidence = section.pop("evidence_modules", set())
    scanned = _scanned_test_modules(static, target_dir)
    section["scanned_test_modules"] = len(scanned)
    measured = (not section.get("error") and bool(scanned)
                and len(scanned) == section.get("covered_modules"))
    section["evidence_measured"] = measured
    section["no_recent_evidence"] = (
        sorted(scanned - evidence) if measured else [])
    return section
def _silent_paths_section(static: dict[str, Any]) -> dict[str, Any]:
    return {
        "silent_except_total": static["silent_total"],
        "product_silent_except_total": static.get("product_silent_total", 0),
        "test_silent_except_total": static.get("test_silent_total", 0),
        "silent_exempt_total": static.get("silent_exempt_total", 0),
        "modules_with_silent": len(static["silent_modules"]),
        "hotspots": static["hotspots"],
        "exempt_hotspots": static.get("exempt_hotspots") or [],
        "swallow_producers": static["swallow_producers"],
        "test_swallow_producers": static.get("test_swallow_producers", 0),
    }
def _sink_section(static: dict[str, Any],
                  target_dir: str) -> dict[str, Any]:
    log_dir = _target_log_dir(target_dir)
    expected = os.path.join(target_dir, SKILL_LOG_DIR_NAME)
    unified = bool(log_dir) and _same_physical_path(log_dir, expected)
    return {
        "sanctioned_modules": sorted(_SINK_SANCTIONED_MODULES),
        "log_dir": log_dir,
        "expected_log_dir": expected,
        "log_dir_unified": unified,
        "bypass_count": len(static["sink_bypass"]),
        "bypass_modules": static["sink_bypass"],
        "test_capture_probes": static.get("test_capture_probes", []),
    }
def _summary_section(inputs: _AuditReportInputs) -> dict[str, Any]:
    static = inputs.static
    metrics = inputs.metrics
    runtime = inputs.runtime
    total_modules = metrics["total_modules"]
    instrumented = static["instrumented"]
    return {
        "total_modules": total_modules,
        "scan_error_count": len(static["parse_errors"]),
        "instrumentation_rate": round(_ratio(len(instrumented), total_modules), 4),
        "runtime_coverage_rate": round(metrics["coverage_rate"], 4),
        "runtime_evidence_measured": metrics["runtime_evidence_measured"],
        "zero_instrumentation_count": len(static["zero_inst"]),
        "without_load_event_count": len(static["no_load_event"]),
        "struct_event_only_count": len(static["struct_only"]),
        "perf_instrumented_count": len(static["perf_instrumented"]),
        "blind_no_instrumentation_count": len(metrics["blind_no_instrumentation"]),
        "blind_not_executed_count": len(metrics["blind_not_executed"]),
        "loaded_modules_count": metrics["loaded_count"],
        "module_load_failures_count": runtime.load_failure_entries,
        "silent_except_total": static["silent_total"],
        "product_silent_except_total": static.get("product_silent_total", 0),
        "test_silent_except_total": static.get("test_silent_total", 0),
        "silent_exempt_total": static.get("silent_exempt_total", 0),
        "swallow_producers": static["swallow_producers"],
        "test_swallow_producers": static.get("test_swallow_producers", 0),
        "sink_bypass_count": len(static["sink_bypass"]),
        "test_channel_active": bool(inputs.test_channel.get("active")),
        "test_channel_evidence_measured": bool(
            inputs.test_channel.get("evidence_measured")),
        "test_channel_covered_modules": inputs.test_channel.get("covered_modules", 0),
        "test_channel_scanned_modules": inputs.test_channel.get(
            "scanned_test_modules", 0),
        "test_channel_modules_with_evidence": inputs.test_channel.get(
            "modules_with_evidence", 0),
        "test_channel_cases": inputs.test_channel.get("cases", 0),
        "test_channel_no_recent_evidence": len(
            inputs.test_channel.get("no_recent_evidence") or []),
        "finding_count": len(inputs.findings),
        "unregistered_log_artifact_count": sum(
            len(f.get("pattern_data", {}).get("unregistered") or [])
            for f in inputs.findings
            if f.get("finding_type") == "unregistered_log_artifact"),
        "foreign_log_namespace_count": sum(
            len(f.get("pattern_data", {}).get("foreign_loggers") or [])
            for f in inputs.findings
            if f.get("finding_type") == "foreign_log_namespace"),
        "elapsed_s": inputs.elapsed_s,
    }
def _test_channel_message(summary: dict[str, Any]) -> str:
    if not summary["test_channel_active"]:
        return ""
    text = (f"，测试面经 {_TEST_CHANNEL_WRITER} 写 / {_TEST_CHANNEL_READER} 读覆盖 "
            f"{summary['test_channel_modules_with_evidence']} 模块 / "
            f"{summary['test_channel_cases']} 用例")
    if not summary.get("test_channel_evidence_measured"):
        text += "（测试通道证据不完整，缺口未度量）"
    return text
def _report_message(summary: dict[str, Any]) -> str:
    runtime_coverage = (
        f"{summary['runtime_coverage_rate'] * 100:.0f}%"
        if summary.get("runtime_evidence_measured", True)
        else "未判定"
    )
    if not summary["total_modules"]:
        scan_errors = summary.get("scan_error_count", 0)
        if scan_errors:
            return (f"日志覆盖度审计完成: 无有效模块，扫描失败 {scan_errors} 个，"
                    f"发现 {summary['finding_count']} 条")
        return "日志覆盖度审计完成: 无有效模块"
    return (
        f"日志覆盖度审计完成: {summary['total_modules']} 模块，埋点率 "
        f"{summary['instrumentation_rate'] * 100:.0f}%，运行时覆盖率 "
        f"{runtime_coverage}，静默 except "
        f"{summary['silent_except_total']} 处，log_swallowed 生产者 "
        f"{summary['swallow_producers']}，perf 埋点模块 "
        f"{summary['perf_instrumented_count']}，日志旁路模块 "
        f"{summary['sink_bypass_count']}，未登记日志产物 "
        f"{summary['unregistered_log_artifact_count']}，外部命名空间 "
        f"{summary['foreign_log_namespace_count']}，发现 "
        f"{summary['finding_count']} 条"
        + _test_channel_message(summary)
    )
def _build_audit_report(
    inputs: _AuditReportInputs,
    *,
    hygiene: dict[str, Any],
) -> dict[str, Any]:
    summary = _summary_section(inputs)
    hygiene_section = dict(hygiene)
    hygiene_section["registry_available"] = (
        _log_artifact_registry(
            _target_log_dir(inputs.target_dir), inputs.target_dir)
        is not None)
    return {
        "status": "ok",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "target_dir": inputs.target_dir,
        "codebase": _codebase_section(inputs),
        "runtime": _runtime_section(inputs),
        "silent_paths": _silent_paths_section(inputs.static),
        "test_channel": inputs.test_channel,
        "sink_unification": _sink_section(inputs.static, inputs.target_dir),
        "log_dir_hygiene": hygiene_section,
        "perf": {"perf_entries": inputs.runtime.perf_entries},
        "findings": inputs.findings,
        "summary": summary,
        "message": _report_message(summary),
    }
class _RuntimeEvidence(NamedTuple):
    runtime: _RuntimeSignals
    evidence_dir: str
    target_label: str
    hygiene: dict[str, Any]
    foreign_namespaces: list[dict[str, Any]]
    product_roots: frozenset[str]
def _collect_runtime_evidence(
    target_dir: str,
    valid_scans: list[dict[str, Any]],
    max_log_entries: int,
) -> _RuntimeEvidence:
    evidence_dir = _target_log_dir(target_dir)
    module_paths = _module_path_map(valid_scans, target_dir)
    load_error: str | None = None
    try:
        runtime_entries = load_json_logs(
            max_entries=max_log_entries, log_dir=evidence_dir,
            propagate_io=True)
    except Exception as e:
        log_swallowed(__name__, e,
                      context=f'_collect_runtime_evidence:{type(e).__name__}')
        runtime_entries = []
        load_error = str(e)[:200]
    product_roots = _product_logger_roots(valid_scans, target_dir)
    runtime = _load_runtime_signals(
        runtime_entries, module_paths,
        load_error=load_error, product_roots=product_roots)
    return _RuntimeEvidence(
        runtime=runtime,
        evidence_dir=evidence_dir,
        target_label=(os.path.basename(os.path.normpath(target_dir))
                      or target_dir),
        hygiene=_scan_log_dir_hygiene(
            evidence_dir, _log_artifact_registry(evidence_dir, target_dir)),
        foreign_namespaces=_foreign_log_namespaces(
            runtime_entries, product_roots),
        product_roots=product_roots,
    )
def _log_audit_summary(
    static: dict[str, Any],
    metrics: dict[str, Any],
    findings: list[dict[str, Any]],
    evidence: _RuntimeEvidence,
    elapsed_s: float,
) -> None:
    total_modules = static["total_modules"]
    instrumented = static["instrumented"]
    coverage_text = (
        f"{metrics['coverage_rate'] * 100:.0f}%"
        if metrics.get("runtime_evidence_measured", True) else "未判定")
    _LOGGER.info(
        "audit_log_coverage: 完成 %d 模块 / 埋点率 %.0f%% / 运行时覆盖率 %s / "
        "静默 except %d / 生产者 %d / perf 埋点模块 %d / 发现 %d 条 / "
        "未登记日志产物 %d / 外部命名空间 %d (%.1fs)",
        total_modules, _ratio(len(instrumented), total_modules) * 100,
        coverage_text, static["silent_total"],
        static["swallow_producers"], len(static["perf_instrumented"]),
        len(findings), len(evidence.hygiene.get("unregistered") or []),
        len(evidence.foreign_namespaces), elapsed_s,
    )
def audit_log_coverage(
    target_dir: str | None = None,
    *,
    include_tests: bool = False,
    max_log_entries: int = DEFAULT_MAX_LOG_ENTRIES,
) -> dict[str, Any]:
    started = time.time()
    include_tests = signal_bool(include_tests)
    if target_dir is None:
        target_dir = os.path.dirname(os.path.realpath(__file__))
    else:
        target_dir = (os.fspath(target_dir)
                      if isinstance(target_dir, os.PathLike) else target_dir)
        if not isinstance(target_dir, str) or not target_dir.strip():
            return {
                "status": "error",
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
                "target_dir": target_dir if isinstance(target_dir, str) else "",
                "message": "目标目录参数非法或空白，拒绝以当前目录兜底",
            }
    target_dir = os.path.abspath(target_dir)
    try:
        setup_logging()
        if not os.path.isdir(target_dir):
            _LOGGER.warning(
                "audit_log_coverage: 目标目录不存在或不是目录: %s", target_dir)
            return {
                "status": "error",
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
                "target_dir": target_dir,
                "message": f"目标目录不存在或不是目录: {target_dir}",
            }
        _LOGGER.info("audit_log_coverage: 开始审计 target=%s", target_dir)
        walk_errors: list[dict[str, Any]] = []
        paths = _collect_py_files(
            target_dir, include_tests, walk_errors=walk_errors)
        scans: list[dict[str, Any]] = list(walk_errors)
        for path in paths:
            scans.append(_scan_module(path, root=target_dir))
        probe = _test_channel_probe(target_dir, include_tests)
        _static = _summarize_static_scans(
            scans, test_channel_active=bool(probe["active"]))
        test_channel = _test_channel_section(probe, _static, target_dir)
        runtime_entry_limit = max(
            0, int_or(max_log_entries, DEFAULT_MAX_LOG_ENTRIES))
        evidence = _collect_runtime_evidence(
            target_dir, _static["valid_scans"], runtime_entry_limit)
        findings = _build_findings(
            scans, _static["swallow_producers"],
            test_channel["active"], evidence.target_label,
            hygiene=evidence.hygiene,
            foreign_namespaces=evidence.foreign_namespaces,
            product_roots=evidence.product_roots)
        metrics = _derive_coverage_metrics(
            _static, evidence.runtime.exposed, evidence.runtime.loaded_modules,
            evidence_measured=(evidence.runtime.log_read_error is None
                               and runtime_entry_limit > 0))
        elapsed_s = round(time.time() - started, 2)
        _log_audit_summary(_static, metrics, findings, evidence, elapsed_s)
        return _build_audit_report(_AuditReportInputs(
            target_dir, _static, evidence.runtime, metrics, findings, elapsed_s,
            test_channel), hygiene=evidence.hygiene)
    except Exception as e:
        _LOGGER.warning("audit_log_coverage: 审计失败: %s", e, exc_info=True)
        return {
            "status": "error",
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "target_dir": target_dir,
            "message": f"日志覆盖度审计失败: {str(e)[:200]}",
        }

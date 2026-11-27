from __future__ import annotations

import ast
import builtins
import hashlib
import importlib.machinery as _ilm
import importlib.util as _ilu
import inspect
import os
import re as _re
import sys
import textwrap
import tokenize
import types as _types_mod
from typing import Any

from jwsgj.diag_blindspot_report import (
    BlindspotHub,
    confirm_dead_code_with_evidence,
)
from jwsgj.diag_callgraph_builder import (
    ensure_built_call_graph,
    prepare_instrumentation_paths,
)
from jwsgj.diag_callgraph_channels import merge_trace_edges
from jwsgj.diag_runtime_forensics import ensure_coverage_hook
from jwsgj.diag_shared_ast_nodes import (
    _prune_non_import_time_branches,
    _type_checking_guard_node_polarities,
    _type_checking_guard_polarity,
    is_main_check,
)
from jwsgj.diag_shared_source_core import parse_cached
from jwsgj.diag_shared_source_scan import comment_tokens
from jwsgj.diag_simulate_sandbox import (
    _MODULES_MISSING,
    _invoke_callable,
    _normalized_root_forms,
    _path_within_roots,
    _pop_sys_path,
    _push_sys_path,
    _relative_module_parts,
    _system_exit_label,
    _top_package_dir,
)
from jwsgj.diag_simulate_sandbox import (
    SIM_MODULE_FILE as _SANDBOX_MODULE_FILE,
)
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import is_path_within_skill

logger = get_module_logger(__name__, __file__)
SIM_MODULE_FILE: str = __file__
__all__ = [
    'empty_fuzz_result',
    'run_diagnosis',
    'run_dynamic_evidence_phase',
    'targeted_fuzz_orphans',
]
_DEFAULT_PROJECT_ROOT = ""
_FUZZ_REASON_LIMIT = 120
def _resume_coverage(coverage_hook) -> None:
    if not coverage_hook:
        return
    try:
        coverage_hook.resume()
    except (OSError, RuntimeError, AttributeError):
        logger.debug(
            "suppressed OSError/RuntimeError/AttributeError in _resume_coverage",
            exc_info=True)
def _scan_blindspots_for_diagnosis(project_root, coverage_hook, call_graph,
                                   ctx, reuse):
    if getattr(reuse, "skip_blindspot_scan", False):
        logger.info("  [Cache] 跳过盲点扫描（自诊断优化）")
        return None
    reused = getattr(reuse, "blindspot_report", None)
    if reused is not None:
        logger.info("  [Cache] 复用外部盲点报告，跳过重复扫描")
        return reused
    try:
        hub = BlindspotHub(project_root, ctx=ctx)
        return hub.scan_all(
            coverage_hook=coverage_hook,
            call_graph=call_graph,
            include_code_blindspots=True,
        )
    except Exception as e:  # noqa: BLE001 — 盲点扫描失败降级跳过
        logger.warning("[Simulate] 盲点扫描失败（降级跳过）: %s", e)
        return None
_TOKENIZER_NEWLINE_RE = _re.compile(rb'\r\n|\r|\n')
_MAX_FUZZ_ORPHANS = 50
_MAX_REQUIRED_COMPLEX_PARAMS = 3
_DANGEROUS_PATTERNS = frozenset({
    "open(", "write(", "writelines(", "os.remove(", "os.unlink(",
    "os.rmdir(", ".mkdir(", ".unlink(", ".rmdir(",
    "shutil.rmtree(", "os.rename(", "os.replace(",
    "shutil.copy(", "shutil.copy2(", "shutil.copyfile(",
    "shutil.move(", "shutil.copytree(",
    "os.chmod(", "os.truncate(", "os.symlink(", "os.link(",
    "os.utime(",
    "subprocess.", "os.system(", "os.popen(", "os.exec", "os.spawn",
    "exec(", "eval(", "compile(", "__import__(",
    "os.makedirs(", "os.mkdir(", "pathlib.Path(", ".write_text(",
    ".write_bytes(", "json.dump(", "pickle.dump(", "shelve.open(",
    "socket.", "urllib.request.", "requests.", "http.client.",
    "os.environ[", ".environ[", "globals()[", "setattr(", "delattr(",
    "ctypes.", "cffi.", "multiprocessing.", "threading.Thread(",
})
_DANGER_RES: tuple = tuple(
    (pattern,
     _re.compile((r"(?<![\w])" if (pattern[0].isalnum() or pattern[0] == "_")
                else "") + _re.escape(pattern)))
    for pattern in sorted(_DANGEROUS_PATTERNS)
)
_DANGEROUS_MODULE_CALLS = frozenset({
    "subprocess", "socket", "urllib.request", "requests",
    "http.client", "ctypes", "cffi", "multiprocessing",
})
_DANGEROUS_NAMED_CALLS = {
    "os": frozenset({
        "remove", "unlink", "rmdir", "rename", "replace", "chmod",
        "truncate", "symlink", "link", "utime", "makedirs", "mkdir",
        "system", "popen", "_exit", "abort", "chdir", "fchdir",
        "putenv", "unsetenv", "environ.clear", "environ.pop",
        "environ.popitem", "environ.setdefault", "environ.update",
    }),
    "shutil": frozenset({
        "rmtree", "copy", "copy2", "copyfile", "move", "copytree",
    }),
    "pathlib": frozenset({"Path"}),
    "threading": frozenset({"Thread"}),
    "json": frozenset({"dump"}),
    "pickle": frozenset({"dump"}),
    "shelve": frozenset({"open"}),
    "io": frozenset({"open"}),
    "builtins": frozenset({
        "open", "exec", "eval", "compile", "__import__",
        "setattr", "delattr",
    }),
}
_DANGEROUS_CALL_MODULES = frozenset(
    _DANGEROUS_MODULE_CALLS | _DANGEROUS_NAMED_CALLS.keys())
def _load_eval_net_spans(source: str, nodes: list,
                         scan_bodies: bool, *, tc_polarities=None
                         ) -> tuple[bytes, list, list]:
    src_bytes = source.encode("utf-8")
    line_starts = _line_byte_starts(src_bytes)
    exec_spans: list[tuple[int, int]] = []
    skip_spans: list[tuple[int, int]] = _comment_byte_spans(
        source, line_starts)
    for node in nodes:
        _collect_load_eval_spans(
            node, line_starts, exec_spans, skip_spans,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
    net = _subtract_byte_spans(exec_spans, skip_spans)
    return src_bytes, line_starts, net
def _eval_net_evidence(
        source: str, nodes: list, scan_bodies: bool, *, tree=None,
) -> tuple[list, str | None]:
    tc_polarities = (_type_checking_guard_node_polarities(tree)
                     if tree is not None else None)
    src_bytes, line_starts, net = _load_eval_net_spans(
        source, nodes, scan_bodies, tc_polarities=tc_polarities)
    calls: list = []
    for node in nodes:
        for candidate in walk_nodes(node):
            if not isinstance(candidate, ast.Call):
                continue
            span = _node_byte_span(candidate.func, line_starts)
            if span is None:
                continue
            if any(start < span[1] and span[0] < end
                   for start, end in net):
                calls.append(candidate)
    hit = _earliest_danger_pattern(
        b"\n".join(src_bytes[s:e] for s, e in net))
    return calls, hit
def _call_path(node) -> list[str]:
    parts = []
    current = node
    while isinstance(current, ast.Attribute):
        parts.append(current.attr)
        current = current.value
    if isinstance(current, ast.Call):
        constructor = _call_path(current.func)
        return [*constructor, *reversed(parts)] if constructor else []
    if not isinstance(current, ast.Name):
        return []
    parts.append(current.id)
    return list(reversed(parts))
def _local_class_bindings(nodes: list) -> dict[str, str]:
    bindings: dict[str, str] = {}
    def record(targets: list, value) -> None:
        constructor = _call_path(value.func) if isinstance(value, ast.Call) else []
        for target in targets:
            if not isinstance(target, ast.Name):
                continue
            if constructor:
                bindings[target.id] = ".".join(constructor)
            else:
                bindings.pop(target.id, None)
    def visit(node) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            return
        if isinstance(node, ast.Assign):
            record(node.targets, node.value)
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            record([node.target], node.value)
        for child in ast.iter_child_nodes(node):
            visit(child)
    for node in nodes:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for statement in node.body:
                visit(statement)
        elif not isinstance(node, (ast.Lambda, ast.ClassDef)):
            visit(node)
    return bindings
def _import_aliases(tree: ast.AST,
                    global_values: dict | None = None) -> dict[str, str]:
    aliases: dict[str, str] = {}
    def bind_alias(name: str, qualified: str) -> None:
        previous = aliases.get(name)
        if (previous and previous != qualified
                and (previous in _DANGEROUS_CALL_MODULES
                     or _dangerous_qualified_name(previous) is not None)):
            # 危险别名一旦绑定即保留：别名表按最终绑定解释全部调用点，
            # 允许后续安全赋值覆盖会把覆盖前的危险调用重新解释为安全
            # 调用（fail-open）。无法按调用时序回溯时只能保守保留。
            return
        aliases[name] = qualified
    if isinstance(global_values, dict):
        referenced = {
            node.id for node in walk_nodes(tree) if isinstance(node, ast.Name)
        }
        for name in referenced.intersection(global_values):
            value = global_values[name]
            if isinstance(value, _types_mod.ModuleType):
                module_name = getattr(value, "__name__", "")
                if isinstance(module_name, str) and module_name:
                    bind_alias(name, module_name)
                continue
            qualified = _dangerous_callable_object(value)
            if qualified is not None:
                bind_alias(name, qualified)
    def record_assignment(targets: list, value) -> None:
        if isinstance(value, ast.Call):
            path = _getattr_call_path(value, aliases)
        elif isinstance(value, (ast.Name, ast.Attribute)):
            path = _call_path(value)
        else:
            return
        if not path:
            return
        if path[0] in aliases:
            qualified = ".".join([aliases[path[0]], *path[1:]])
        elif len(path) == 1 and path[0] == "getattr":
            qualified = "builtins.getattr"
        elif (len(path) == 1 and _dangerous_qualified_name(
                f"builtins.{path[0]}") is not None):
            qualified = f"builtins.{path[0]}"
        else:
            return
        for target in targets:
            if isinstance(target, ast.Name):
                bind_alias(target.id, qualified)
    binding_nodes = [
        node for node in walk_nodes(tree)
        if isinstance(node, (ast.Import, ast.ImportFrom,
                             ast.Assign, ast.AnnAssign))
    ]
    for node in sorted(
            binding_nodes,
            key=lambda item: (getattr(item, "lineno", 0),
                              getattr(item, "col_offset", 0))):
        if isinstance(node, ast.Import):
            for alias in node.names:
                local = alias.asname or alias.name.split(".", 1)[0]
                canonical = alias.name if alias.asname else local
                bind_alias(local, canonical)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            for alias in node.names:
                if alias.name != "*":
                    bind_alias(
                        alias.asname or alias.name,
                        f"{node.module}.{alias.name}")
        elif isinstance(node, ast.Assign):
            record_assignment(node.targets, node.value)
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            record_assignment([node.target], node.value)
    return aliases
def _dangerous_module_attr(module_name: str, attr: str) -> bool:
    if attr == "<dynamic>" or attr.endswith(".<dynamic>"):
        return True
    if module_name in _DANGEROUS_MODULE_CALLS:
        return True
    if module_name == "os" and attr.startswith(("exec", "spawn")):
        return True
    return attr in _DANGEROUS_NAMED_CALLS.get(module_name, ())
def _dangerous_qualified_name(name: str) -> str | None:
    for module_name in sorted(
            _DANGEROUS_CALL_MODULES, key=len, reverse=True):
        prefix = module_name + "."
        if name.startswith(prefix) and _dangerous_module_attr(
                module_name, name[len(prefix):]):
            return name
    return None
def _getattr_call_path(call, aliases: dict[str, str]) -> list[str]:
    if not isinstance(call, ast.Call) or call.keywords:
        return []
    if not 2 <= len(call.args) <= 3:
        return []
    getter_path = _call_path(call.func)
    if getter_path and getter_path[0] in aliases:
        getter_path = [aliases[getter_path[0]], *getter_path[1:]]
    if ".".join(getter_path) not in ("getattr", "builtins.getattr"):
        return []
    owner_path = _call_path(call.args[0])
    if not owner_path:
        return []
    if owner_path[0] in aliases:
        owner_path = [aliases[owner_path[0]], *owner_path[1:]]
    attr_node = call.args[1]
    attr = (attr_node.value
            if isinstance(attr_node, ast.Constant)
            and isinstance(attr_node.value, str) else "<dynamic>")
    return [*owner_path, attr]
def _dynamic_getattr_danger(call, aliases: dict[str, str]) -> str | None:
    def resolve(node) -> list[str]:
        if isinstance(node, ast.Attribute):
            base = resolve(node.value)
            return [*base, node.attr] if base else []
        if isinstance(node, ast.Call):
            return _getattr_call_path(node, aliases)
        return []
    path = resolve(call.func)
    if not path:
        return None
    return _dangerous_qualified_name(".".join(path))
def _first_alias_danger(calls: list, aliases: dict[str, str]) -> str | None:
    for call in calls:
        hit = _dynamic_getattr_danger(call, aliases)
        if hit is not None:
            return hit
        path = _call_path(call.func)
        if not path:
            continue
        if path[0] in aliases:
            qualified = ".".join([aliases[path[0]], *path[1:]])
        elif len(path) == 1:
            qualified = f"builtins.{path[0]}"
        elif path[0] == "builtins":
            qualified = ".".join(path)
        else:
            continue
        hit = _dangerous_qualified_name(qualified)
        if hit is not None:
            return hit
    return None
def _local_function_definitions(tree: ast.AST) -> dict[str, list]:
    parents = {
        child: parent
        for parent in walk_nodes(tree)
        for child in ast.iter_child_nodes(parent)
    }
    definitions: dict[str, list] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        definitions.setdefault(node.name, []).append(node)
        parent = parents.get(node)
        if isinstance(parent, ast.ClassDef):
            definitions.setdefault(f"{parent.name}.{node.name}", []).append(node)
    for node in walk_nodes(tree):
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets, value = [node.target], node.value
        else:
            continue
        if isinstance(value, ast.Lambda):
            # 局部 lambda 赋值后调用（g = lambda: os.remove(...); g()）
            # 也是本地函数定义；不记录会在 _reachable_local_side_effect 中
            # 断链，漏判其函数体副作用。
            for target in targets:
                if not isinstance(target, ast.Name):
                    continue
                aliases = definitions.setdefault(target.id, [])
                if value not in aliases:
                    aliases.append(value)
            continue
        path = _call_path(value)
        resolved = definitions.get(".".join(path), []) if path else []
        if not resolved:
            continue
        for target in targets:
            if not isinstance(target, ast.Name):
                continue
            aliases = definitions.setdefault(target.id, [])
            aliases.extend(
                definition for definition in tuple(resolved)
                if definition not in aliases)
    return definitions
def _local_definition_owners(tree: ast.AST) -> dict[int, str]:
    return {
        id(node): class_node.name
        for class_node in walk_nodes(tree) if isinstance(class_node, ast.ClassDef)
        for node in class_node.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
def _reachable_local_side_effect(source: str, tree: ast.AST,
                                 initial_calls: list,
                                 aliases: dict[str, str]) -> str | None:
    definitions = _local_function_definitions(tree)
    owners = _local_definition_owners(tree)
    pending: list = []
    seen: set[int] = set()
    def enqueue(calls: list, caller=None,
                bindings: dict[str, str] | None = None) -> None:
        local_bindings = bindings or {}
        for call in calls:
            path = _call_path(call.func)
            if not path:
                continue
            keys = [".".join(path)]
            if path[0] in local_bindings:
                keys.append(".".join(
                    [local_bindings[path[0]], *path[1:]]))
            if len(path) == 1:
                keys.append(f"{path[0]}.__init__")
            owner = owners.get(id(caller)) if caller is not None else None
            if owner and len(path) == 2:
                args = (*caller.args.posonlyargs, *caller.args.args)
                if args and path[0] == args[0].arg:
                    keys.append(f"{owner}.{path[1]}")
            for key in dict.fromkeys(keys):
                for node in definitions.get(key, ()):
                    if id(node) not in seen:
                        pending.append(node)
    enqueue(initial_calls, bindings=_local_class_bindings(list(tree.body)))
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        calls, hit = _eval_net_evidence(source, [node], True, tree=tree)
        hit = _first_alias_danger(calls, aliases) or hit
        if hit is not None:
            return hit
        enqueue(calls, caller=node, bindings=_local_class_bindings([node]))
    return None
def _dangerous_callable_object(value) -> str | None:
    if not callable(value):
        return None
    for module_name in sorted(_DANGEROUS_CALL_MODULES):
        module = sys.modules.get(module_name)
        if not isinstance(module, _types_mod.ModuleType):
            continue
        if module_name in _DANGEROUS_MODULE_CALLS:
            attrs = [name for name in dir(module) if not name.startswith("_")]
        else:
            attrs = list(_DANGEROUS_NAMED_CALLS[module_name])
            if module_name == "os":
                attrs.extend(
                    name for name in dir(module)
                    if name.startswith(("exec", "spawn")))
        for attr in attrs:
            try:
                candidate = module
                for part in attr.split("."):
                    candidate = getattr(candidate, part, None)
            except Exception as exc:  # noqa: BLE001 — 病态模块不得击穿扫描
                logger.debug("危险调用身份读取失败 %s.%s: %s",
                             module_name, attr, exc)
                continue
            same_bound_method = (
                isinstance(candidate, _types_mod.MethodType)
                and isinstance(value, _types_mod.MethodType)
                and candidate.__self__ is value.__self__
                and candidate.__func__ is value.__func__
            )
            if candidate is value or same_bound_method:
                return f"{module_name}.{attr}"
    return None
def _resolve_call_path(func, path: list[str],
                       local_bindings: dict[str, str] | None = None):
    if not path:
        return _MODULES_MISSING
    binding = local_bindings.get(path[0]) if local_bindings else None
    if binding:
        value = _resolve_call_path(func, binding.split("."))
    else:
        receiver = getattr(func, "__self__", _MODULES_MISSING)
        code = getattr(getattr(func, "__func__", None), "__code__", None)
        if (receiver is not _MODULES_MISSING and code is not None
                and code.co_argcount >= 1
                and path[0] == code.co_varnames[0]):
            value = receiver
        else:
            globals_ = getattr(func, "__globals__", {})
            value = (globals_.get(path[0], _MODULES_MISSING)
                     if isinstance(globals_, dict) else _MODULES_MISSING)
            if value is _MODULES_MISSING and len(path) == 1:
                value = getattr(builtins, path[0], _MODULES_MISSING)
    if value is _MODULES_MISSING:
        return _MODULES_MISSING
    for attr in path[1:]:
        value = inspect.getattr_static(value, attr, _MODULES_MISSING)
        if value is _MODULES_MISSING:
            return _MODULES_MISSING
        if isinstance(value, (classmethod, staticmethod)):
            value = value.__func__
    return value
def _first_global_danger(func, calls: list,
                         local_bindings: dict[str, str] | None = None) -> str | None:
    for call in calls:
        value = _resolve_call_path(
            func, _call_path(call.func), local_bindings)
        if value is _MODULES_MISSING:
            continue
        hit = _dangerous_callable_object(value)
        if hit is not None:
            return hit
    return None
def _same_module_call_side_effect(
        func, calls: list, seen: set[int],
        local_bindings: dict[str, str] | None = None) -> bool:
    for call in calls:
        value = _resolve_call_path(
            func, _call_path(call.func), local_bindings)
        if value is _MODULES_MISSING:
            continue
        if inspect.isclass(value):
            value = inspect.getattr_static(value, "__init__", _MODULES_MISSING)
        if not (inspect.isfunction(value) or inspect.ismethod(value)):
            continue
        if _has_side_effects(value, _seen=seen):
            return True
    return False
def _definition_eval_nodes(node) -> list:
    nodes: list = []
    nodes.extend(getattr(node, "decorator_list", ()) or ())
    arguments = node.args
    for _arg in (*arguments.posonlyargs, *arguments.args,
                 *arguments.kwonlyargs):
        if _arg.annotation is not None:
            nodes.append(_arg.annotation)
    for _vararg in (arguments.vararg, arguments.kwarg):
        if _vararg is not None and _vararg.annotation is not None:
            nodes.append(_vararg.annotation)
    nodes.extend(arguments.defaults)
    nodes.extend(default for default in arguments.kw_defaults
                 if default is not None)
    if getattr(node, "returns", None) is not None:
        nodes.append(node.returns)
    nodes.extend(getattr(node, "type_params", ()) or ())
    return nodes
def _side_effect_scan_nodes(func, tree: ast.Module) -> list:
    function_node = next(
        (node for node in tree.body
         if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if function_node is not None:
        return [function_node]
    if getattr(func, "__name__", "") == "<lambda>":
        lambda_nodes = [
            node for node in walk_nodes(tree) if isinstance(node, ast.Lambda)]
        if lambda_nodes:
            return lambda_nodes
    return list(tree.body)
def _method_receiver_binding(func) -> tuple[str, str] | None:
    """返回方法首个参数到其所属类的绑定（self/cls -> Class）。

    ``_has_side_effects`` 只解析单个函数的源码，类体不在该源码树内；
    因此 ``self.helper()`` 这类同类别名调用无法由 ``_local_function_definitions``
    解析，会漏判 ``helper`` 内的文件/子进程等副作用，导致靶向模糊执行真的
    调用有副作用的入口。用 ``__qualname__`` 从 ``__globals__`` 还原所属类，
    让 ``_resolve_call_path`` 能把 ``self`` 解析到该类，后续
    ``_same_module_call_side_effect`` 即可递归检查兄弟方法。
    """
    code = getattr(func, "__code__", None)
    if code is None or getattr(code, "co_argcount", 0) < 1:
        return None
    qualname = getattr(func, "__qualname__", "")
    if not isinstance(qualname, str) or "." not in qualname:
        return None
    class_path = qualname.rsplit(".", 1)[0]
    if not class_path or "<locals>" in class_path:
        return None
    globals_ = getattr(func, "__globals__", {})
    if not isinstance(globals_, dict):
        return None
    owner = globals_.get(class_path.split(".", 1)[0], _MODULES_MISSING)
    if owner is _MODULES_MISSING:
        return None
    for part in class_path.split(".")[1:]:
        owner = inspect.getattr_static(owner, part, _MODULES_MISSING)
        if owner is _MODULES_MISSING:
            return None
    if not inspect.isclass(owner):
        return None
    return code.co_varnames[0], class_path
def _has_side_effects(func, _seen: set[int] | None = None):
    if _seen is None:
        _seen = set()
    identity = id(func)
    if identity in _seen:
        return False
    _seen.add(identity)
    try:
        src = textwrap.dedent(inspect.getsource(func))
        tree = parse_cached(src)
        nodes = _side_effect_scan_nodes(func, tree)
        calls, hit = _eval_net_evidence(src, nodes, True, tree=tree)
        aliases = _import_aliases(
            tree, getattr(func, "__globals__", {}))
        local_bindings = _local_class_bindings(nodes)
        _receiver_binding = _method_receiver_binding(func)
        if _receiver_binding is not None:
            local_bindings.setdefault(*_receiver_binding)
        if (_first_alias_danger(calls, aliases) is not None
                or _first_global_danger(func, calls, local_bindings) is not None
                or hit is not None):
            return True
        if _reachable_local_side_effect(src, tree, calls, aliases) is not None:
            return True
        return _same_module_call_side_effect(
            func, calls, _seen, local_bindings)
    except (OSError, TypeError, SyntaxError, ValueError, UnicodeError,
            RecursionError, MemoryError) as _e:
        logger.debug("函数源码副作用分析不可用（保守拒绝执行）: %s", _e)
        return True
def _merge_byte_spans(spans: list) -> list:
    merged: list = []
    for s, e in sorted(spans):
        if merged and s <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], e))
        else:
            merged.append((s, e))
    return merged
def _first_overlapping_skip(skip_m: list, start: int) -> int:
    si = 0
    while si < len(skip_m) and skip_m[si][1] <= start:
        si += 1
    return si
def _clip_span(s: int, e: int, skip_m: list, si: int) -> list:
    pieces: list = []
    cur = s
    j = si
    while j < len(skip_m) and skip_m[j][0] < e:
        ks, ke = skip_m[j]
        if ks > cur:
            pieces.append((cur, ks))
        cur = max(cur, ke)
        if cur >= e:
            break
        j += 1
    if cur < e:
        pieces.append((cur, e))
    return pieces
def _subtract_byte_spans(exec_spans: list, skip_spans: list) -> list:
    skip_m = _merge_byte_spans(skip_spans)
    out: list = []
    si = 0
    for s, e in _merge_byte_spans(exec_spans):
        si = _first_overlapping_skip(skip_m, s)
        out.extend(_clip_span(s, e, skip_m, si))
    return out
def _node_byte_span(node, line_byte_starts: list) -> tuple[int, int] | None:
    _lo = getattr(node, "lineno", None)
    _co = getattr(node, "col_offset", None)
    _el = getattr(node, "end_lineno", None)
    _ec = getattr(node, "end_col_offset", None)
    if (_lo is None or _co is None or _el is None or _ec is None
            or not (1 <= _lo < len(line_byte_starts)
                    and 1 <= _el < len(line_byte_starts))):
        return None
    return (line_byte_starts[_lo - 1] + _co,
            line_byte_starts[_el - 1] + _ec)
def _guard_execution_branches(
        node: ast.If, tc_polarities=None) -> tuple[list, list] | None:
    polarity = (tc_polarities.get(id(node))
                if tc_polarities is not None
                else _type_checking_guard_polarity(node.test))
    if polarity is not None:
        return ((node.body, node.orelse) if polarity
                else (node.orelse, node.body))
    if is_main_check(node.test):
        return node.orelse, node.body
    return None
def _collect_load_eval_spans(node, line_byte_starts: list,
                             exec_out: list, skip_out: list,
                             *, scan_bodies: bool, tc_polarities=None) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _collect_def_eval_spans(
            node, line_byte_starts, exec_out, skip_out,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
        return
    if isinstance(node, ast.Lambda):
        _collect_lambda_eval_spans(
            node, line_byte_starts, exec_out, skip_out,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
        return
    if isinstance(node, ast.ClassDef):
        _collect_class_eval_spans(
            node, line_byte_starts, exec_out, skip_out,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
        return
    _sp = _node_byte_span(node, line_byte_starts)
    if _sp is not None:
        exec_out.append(_sp)
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
        if _sp is not None:
            skip_out.append(_sp)
        return
    if isinstance(node, ast.If):
        branches = _guard_execution_branches(node, tc_polarities)
        if branches is not None:
            executing, non_executing = branches
            _collect_body_skip_span(non_executing, line_byte_starts, skip_out)
            for _child in executing:
                _collect_load_eval_spans(
                    _child, line_byte_starts, exec_out, skip_out,
                    scan_bodies=scan_bodies, tc_polarities=tc_polarities)
            return
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Lambda):
        _collect_lambda_eval_spans(
            node.func, line_byte_starts, exec_out, skip_out,
            scan_bodies=True, tc_polarities=tc_polarities)
        for _child in (*node.args, *(kw.value for kw in node.keywords)):
            _collect_load_eval_spans(
                _child, line_byte_starts, exec_out, skip_out,
                scan_bodies=scan_bodies, tc_polarities=tc_polarities)
        return
    for _child in ast.iter_child_nodes(node):
        _collect_load_eval_spans(
            _child, line_byte_starts, exec_out, skip_out,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
def _collect_body_skip_span(body: list, line_byte_starts: list,
                            skip_out: list) -> None:
    if not body:
        return
    _b_start = _node_byte_span(body[0], line_byte_starts)
    _b_end = _node_byte_span(body[-1], line_byte_starts)
    if _b_start is not None and _b_end is not None:
        skip_out.append((_b_start[0], _b_end[1]))
def _collect_class_eval_spans(node, line_byte_starts: list,
                             exec_out: list, skip_out: list,
                             *, scan_bodies: bool, tc_polarities=None) -> None:
    for _expr in (*(node.decorator_list or ()), *(node.bases or ()),
                  *(kw.value for kw in node.keywords or ()),
                  *(getattr(node, "type_params", ()) or ())):
        _collect_load_eval_spans(
            _expr, line_byte_starts, exec_out, skip_out,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
    for _stmt in node.body:
        _collect_load_eval_spans(
            _stmt, line_byte_starts, exec_out, skip_out,
            scan_bodies=scan_bodies, tc_polarities=tc_polarities)
def _collect_def_eval_spans(node, line_byte_starts: list,
                            exec_out: list, skip_out: list,
                            *, scan_bodies: bool, tc_polarities=None) -> None:
    for _expr in _definition_eval_nodes(node):
        _collect_load_eval_spans(
            _expr, line_byte_starts, exec_out, skip_out,
            scan_bodies=False, tc_polarities=tc_polarities)
    if scan_bodies:
        for _stmt in node.body:
            _collect_load_eval_spans(
                _stmt, line_byte_starts, exec_out, skip_out,
                scan_bodies=False, tc_polarities=tc_polarities)
        return
    _collect_body_skip_span(node.body, line_byte_starts, skip_out)
def _collect_lambda_eval_spans(node, line_byte_starts: list,
                               exec_out: list, skip_out: list,
                               *, scan_bodies: bool, tc_polarities=None) -> None:
    for _expr in _definition_eval_nodes(node):
        _collect_load_eval_spans(
            _expr, line_byte_starts, exec_out, skip_out,
            scan_bodies=False, tc_polarities=tc_polarities)
    _body_sp = _node_byte_span(node.body, line_byte_starts)
    if _body_sp is None:
        return
    if scan_bodies:
        _collect_load_eval_spans(
            node.body, line_byte_starts, exec_out, skip_out,
            scan_bodies=False, tc_polarities=tc_polarities)
    else:
        skip_out.append(_body_sp)
def _line_byte_starts(src_bytes: bytes) -> list[int]:
    starts = [0]
    starts.extend(m.end() for m in _TOKENIZER_NEWLINE_RE.finditer(src_bytes))
    if starts[-1] < len(src_bytes):
        starts.append(len(src_bytes))
    return starts
_LINE_TEXT_SPLIT_RE = _re.compile(r'\r\n|\r|\n')
def _comment_byte_spans(source: str, line_starts: list[int]) -> list:
    # 行切分必须与 _line_byte_starts / AST lineno / tokenize 行号同口径（仅
    # CR/LF/CRLF）。str.splitlines 还会在 U+2028/U+0085/\x0c 等处切分，导致
    # 注释行号相对 line_starts 整体错位：错位的跳过跨度会把真实代码从 exec
    # 跨度里剪掉，模块级危险模式（如 subprocess.）被漏检。
    lines = _LINE_TEXT_SPLIT_RE.split(source)
    spans = []
    for token in comment_tokens(source) or ():
        (row, col), (end_row, end_col) = token.start, token.end
        if row != end_row or not (0 < row <= len(lines)):
            continue
        line = lines[row - 1]
        start = line_starts[row - 1] + len(line[:col].encode("utf-8"))
        end = line_starts[row - 1] + len(line[:end_col].encode("utf-8"))
        if end > start:
            spans.append((start, end))
    return spans
def _earliest_danger_pattern(exec_bytes: bytes) -> str | None:
    _text = exec_bytes.decode("utf-8", "replace")
    hits = []
    for pattern, _rx in _DANGER_RES:
        _match = _rx.search(_text)
        if _match is not None:
            hits.append((_match.start(), pattern))
    return min(hits)[1] if hits else None
def _module_load_side_effect(source: str) -> tuple[bool, str | None]:
    try:
        tree = parse_cached(source)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(
            __name__, _e,
            context='_module_load_side_effect:SyntaxError,ValueError,RecursionError')
        return True, "unparseable source"
    nodes = list(tree.body)
    calls, hit = _eval_net_evidence(source, nodes, False, tree=tree)
    aliases = _import_aliases(tree)
    hit = _first_alias_danger(calls, aliases) or hit
    if hit is None:
        hit = _reachable_local_side_effect(source, tree, calls, aliases)
    return hit is not None, hit
def _static_attr(obj, name: str):
    try:
        return inspect.getattr_static(obj, name)
    except AttributeError:
        return _MODULES_MISSING
def _lookup_on_module(mod, simple_name: str, class_name):
    if isinstance(class_name, str) and class_name:
        _cls = _static_attr(mod, class_name)
        if _cls is _MODULES_MISSING:
            return None
        value = _static_attr(_cls, simple_name)
        if value is _MODULES_MISSING:
            return None
        if isinstance(value, staticmethod):
            return value.__func__
        if isinstance(value, classmethod):
            return value.__get__(None, _cls)
        return value
    value = _static_attr(mod, simple_name)
    return value if value is not _MODULES_MISSING else None
def _module_file_matches(mod_file: str, norm_orphan: str,
                         orphan_base: str, has_dir: bool) -> bool:
    _mf = os.path.normcase(os.path.normpath(mod_file))
    if has_dir:
        return _mf == norm_orphan or _mf.endswith(os.sep + norm_orphan)
    return orphan_base == os.path.basename(_mf)
def _normalized_orphan_path(orphan_fp) -> tuple[str, str, bool]:
    if isinstance(orphan_fp, (bytes, os.PathLike)):
        orphan_fp = os.fsdecode(orphan_fp)
    raw = orphan_fp if isinstance(orphan_fp, str) else str(orphan_fp or "")
    norm = os.path.normcase(os.path.normpath(raw.replace('/', os.sep)))
    return norm, os.path.normcase(os.path.basename(raw)), os.sep in norm
def _path_within_project_roots(path: str, roots: tuple[str, ...]) -> bool:
    return (
        _path_within_roots(path, roots)
        and _path_within_roots(os.path.realpath(path), roots)
    )
def _find_func_in_sys_modules(orphan_fp: str, simple_name: str,
                              class_name, project_root: str = _DEFAULT_PROJECT_ROOT):
    if not (orphan_fp and simple_name):
        return None
    norm_orphan, orphan_base, has_dir = _normalized_orphan_path(orphan_fp)
    roots = _normalized_root_forms(project_root)
    found = None
    found_identity = ""
    for _mod_key, _mod in list(sys.modules.items()):
        if _mod is None:
            continue
        _mod_file = getattr(_mod, "__file__", None)
        if not _mod_file or not isinstance(
                _mod_file, (str, bytes, os.PathLike)):
            continue
        _mod_file = os.fsdecode(_mod_file)
        if not _module_file_matches(
                _mod_file, norm_orphan, orphan_base, has_dir):
            continue
        if roots and not _path_within_project_roots(_mod_file, roots):
            continue
        func = _lookup_on_module(_mod, simple_name, class_name)
        if func is None:
            continue
        identity = os.path.normcase(os.path.realpath(os.path.abspath(_mod_file)))
        if found is not None:
            if identity != found_identity or func is not found:
                logger.debug(
                    "模糊执行模块匹配存在歧义（失败关闭）: %s:%s",
                    orphan_fp, simple_name)
                return None
            continue
        found = func
        found_identity = identity
    return found
def _iter_runtime_import_nodes(tree: ast.AST):
    pruned = _prune_non_import_time_branches(tree)
    stack = [pruned]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            yield node
            continue
        stack.extend(ast.iter_child_nodes(node))

def _import_module_candidates(node, module_name: str,
                              is_package: bool) -> list[str]:
    if isinstance(node, ast.Import):
        return [alias.name for alias in node.names]
    if not isinstance(node, ast.ImportFrom):
        return []
    if node.level:
        if not module_name:
            return []
        package_parts = module_name.split(".")
        if not is_package:
            package_parts = package_parts[:-1]
        ascent = node.level - 1
        if ascent >= len(package_parts):
            return []
        base = (package_parts[:len(package_parts) - ascent]
                if ascent else package_parts)
        root = ".".join([*base, node.module] if node.module else base)
    else:
        root = node.module or ""
    candidates = [root] if root else []
    prefix = root + "." if root else ""
    candidates.extend(
        prefix + alias.name for alias in node.names if alias.name != "*")
    return list(dict.fromkeys(name for name in candidates if name))

def _local_spec_files(dotted: str, search_paths: tuple[str, ...],
                      roots: tuple[str, ...]) -> list[str]:
    files: list[str] = []
    paths = list(search_paths)
    parts = dotted.split(".")
    for index, _part in enumerate(parts):
        fullname = ".".join(parts[:index + 1])
        spec = _ilm.PathFinder.find_spec(fullname, paths)
        if spec is None:
            break
        origin = getattr(spec, "origin", None)
        if origin and origin not in ("built-in", "frozen"):
            candidate = os.path.realpath(origin)
            if not _path_within_project_roots(candidate, roots):
                break
            files.append(candidate)
        paths = list(getattr(spec, "submodule_search_locations", None) or ())
        if not paths and index + 1 < len(parts):
            break
    return files

def _preflight_local_imports(source: str, abs_fp: str, project_root: str,
                             checked: dict, active: set[str]) -> bool:
    tree = parse_cached(source)
    module_name, search_root = _package_import_context(abs_fp, project_root)
    boundary = project_root or search_root
    roots = _normalized_root_forms(boundary)
    search_paths = tuple(dict.fromkeys(
        path for path in (search_root, boundary) if path))
    is_package = os.path.basename(abs_fp) == "__init__.py"
    for node in _iter_runtime_import_nodes(tree):
        candidates = _import_module_candidates(node, module_name, is_package)
        for dotted in candidates:
            for dependency in _local_spec_files(dotted, search_paths, roots):
                dependency_source = _read_loadable_source(
                    dependency, boundary, _checked=checked, _active=active)
                if dependency_source is None:
                    logger.debug(
                        "模糊执行加载拒绝: 项目内导入未通过副作用预检 %s -> %s",
                        abs_fp, dependency)
                    return False
    return True

def _read_loadable_source(abs_fp: str,
                          project_root: str = _DEFAULT_PROJECT_ROOT,
                          _checked: dict | None = None,
                          _active: set[str] | None = None) -> str | None:
    checked = {} if _checked is None else _checked
    active = set() if _active is None else _active
    identity = os.path.normcase(os.path.realpath(os.path.abspath(abs_fp)))
    if identity in checked:
        return checked[identity]
    if identity in active:
        return ""
    try:
        with tokenize.open(abs_fp) as _srcf:
            _mod_src = _srcf.read()
    except (OSError, UnicodeDecodeError, SyntaxError, LookupError) as _e:
        logger.debug("suppressed source read in _load_func_from_file: %s", _e)
        checked[identity] = None
        return None
    _danger, _hit = _module_load_side_effect(_mod_src)
    if _danger:
        logger.debug("模糊执行加载拒绝: 模块级危险语句 (%s): %s", _hit, abs_fp)
        checked[identity] = None
        return None
    active.add(identity)
    try:
        if not _preflight_local_imports(
                _mod_src, abs_fp, project_root, checked, active):
            checked[identity] = None
            return None
    except (ImportError, OSError, TypeError, ValueError) as _e:
        logger.debug("项目内导入预检不可用（保守拒绝）%s: %s", abs_fp, _e)
        checked[identity] = None
        return None
    finally:
        active.discard(identity)
    checked[identity] = _mod_src
    return _mod_src
def _drop_modules_under(root: str, before: set[str]) -> None:
    for key in set(sys.modules) - before:
        module = sys.modules.get(key)
        module_file = getattr(module, "__file__", None)
        if not module_file:
            continue
        if is_path_within_skill(module_file, root):
            sys.modules.pop(key, None)
def _module_spec_from_path(abs_fp: str, mod_name: str):
    spec = _ilu.spec_from_file_location(mod_name, abs_fp)
    if spec is not None and spec.loader is not None:
        return spec
    loader = _ilm.SourceFileLoader(mod_name, abs_fp)
    spec = _ilu.spec_from_loader(mod_name, loader, origin=abs_fp)
    if spec is not None:
        spec.has_location = True
    return spec
def _exec_module_from_path(abs_fp: str, mod_name: str, *,
                           search_root: str = "", source: str | None = None):
    previous = sys.modules.get(mod_name, _MODULES_MISSING)
    cleanup_root = os.path.abspath(search_root) if search_root else ""
    before_modules = set(sys.modules) if cleanup_root else None
    added_roots = _push_sys_path((cleanup_root,)) if cleanup_root else []
    try:
        spec = _module_spec_from_path(abs_fp, mod_name)
        if spec and spec.loader:
            tmp_mod = _ilu.module_from_spec(spec)
            sys.modules[mod_name] = tmp_mod
            if source is None:
                spec.loader.exec_module(tmp_mod)
            else:
                exec(compile(source, abs_fp, "exec", dont_inherit=True),  # noqa: S102
                     tmp_mod.__dict__)
            return tmp_mod
    except BaseException as exc:  # noqa: BLE001 — 隔离目标模块的全部退出异常
        logger.debug("模糊执行加载函数失败 (%s): %s", type(exc).__name__, exc)
    finally:
        if previous is _MODULES_MISSING:
            sys.modules.pop(mod_name, None)
        else:
            sys.modules[mod_name] = previous
        _pop_sys_path(added_roots)
        if cleanup_root and before_modules is not None:
            _drop_modules_under(cleanup_root, before_modules)
    return None
def _package_import_context(abs_fp: str,
                            project_root: str) -> tuple[str, str]:
    file_dir = os.path.dirname(abs_fp)
    fallback_root = file_dir
    stem = os.path.splitext(os.path.basename(abs_fp))[0]
    parts = [] if stem == "__init__" else [stem]
    boundary = (os.path.normcase(os.path.realpath(project_root))
                if project_root else "")
    current = file_dir
    if boundary and is_path_within_skill(current, project_root):
        if not os.path.isfile(os.path.join(project_root, "__init__.py")):
            top_package = _top_package_dir(abs_fp, project_root)
            if top_package is not None:
                import_root = os.path.dirname(top_package)
                package_parts = _relative_module_parts(abs_fp, import_root)
                if package_parts and package_parts[-1] == "__init__":
                    package_parts = package_parts[:-1]
                if package_parts and all(
                        part.isidentifier() for part in package_parts):
                    return ".".join(package_parts), import_root
        while True:
            parts.insert(0, os.path.basename(current))
            if os.path.normcase(os.path.realpath(current)) == boundary:
                if os.path.isfile(os.path.join(current, "__init__.py")):
                    current = os.path.dirname(current)
                else:
                    parts.pop(0)
                break
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent
    else:
        packaged = False
        while os.path.isfile(os.path.join(current, "__init__.py")):
            packaged = True
            parts.insert(0, os.path.basename(current))
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent
        if not packaged:
            return "", fallback_root
    if not parts or not all(part.isidentifier() for part in parts):
        return "", fallback_root
    return ".".join(parts), current
def _load_func_from_file(orphan_fp: str, simple_name: str, class_name, project_root):
    if not (orphan_fp and simple_name):
        return None
    _abs_fp = os.fsdecode(os.fspath(orphan_fp))
    if not os.path.isabs(_abs_fp) and project_root:
        _abs_fp = os.path.join(project_root, _abs_fp)
    roots = _normalized_root_forms(project_root)
    if roots and not _path_within_project_roots(_abs_fp, roots):
        logger.debug("模糊执行加载拒绝: 孤儿路径越出项目根: %s", _abs_fp)
        return None
    if not os.path.isfile(_abs_fp):
        return None
    _module_source = _read_loadable_source(_abs_fp, project_root)
    if _module_source is None:
        return None
    _path_key = os.path.normcase(os.path.abspath(_abs_fp))
    _path_digest = hashlib.sha256(
        _path_key.encode("utf-8", "surrogatepass")).hexdigest()[:16]
    _pkg_name, _search_root = _package_import_context(_abs_fp, project_root)
    _stem = os.path.splitext(os.path.basename(_abs_fp))[0]
    _mod_name = _pkg_name or (
        "_fuzz_tmp_" + _stem + "_" + _path_digest)
    _tmp_mod = _exec_module_from_path(
        _abs_fp, _mod_name, search_root=_search_root,
        source=_module_source)
    if _tmp_mod is None:
        return None
    return _lookup_on_module(_tmp_mod, simple_name, class_name)
def _orphan_name(orphan) -> str:
    if isinstance(orphan, str):
        return orphan
    if isinstance(orphan, dict):
        _name = orphan.get("name") or orphan.get("function") or ""
    else:
        _name = getattr(orphan, "name", "")
    return _name if isinstance(_name, str) else ""
def _load_func_by_orphan_fp(fp, name, class_name, project_root):
    simple = name.split(".")[-1] if name else ""
    found = _find_func_in_sys_modules(fp, simple, class_name, project_root)
    if found is None:
        found = _load_func_from_file(fp, simple, class_name, project_root)
    return found
def _resolve_dict_orphan(orphan: dict, func_name: str, project_root):
    ref = orphan.get("ref")
    if callable(ref):
        return ref
    fp = orphan.get("filepath")
    if not fp:
        return None
    return _load_func_by_orphan_fp(
        fp, func_name, orphan.get("class_name"), project_root)
def _resolve_object_orphan(orphan, func_name: str, project_root):
    if not (hasattr(orphan, "name") and hasattr(orphan, "filepath")):
        return None
    return _load_func_by_orphan_fp(
        getattr(orphan, "filepath", ""), func_name,
        getattr(orphan, "class_name", None), project_root)
def _evidence_function_name(func, orphan_name: str) -> str:
    if isinstance(orphan_name, str) and orphan_name:
        return orphan_name
    name = getattr(func, "__name__", "")
    return name if isinstance(name, str) else ""
def _resolve_orphan_func(orphan, project_root):
    func_name = _orphan_name(orphan)
    if callable(orphan):
        return orphan, _evidence_function_name(orphan, func_name)
    if isinstance(orphan, dict):
        func = _resolve_dict_orphan(orphan, func_name, project_root)
    else:
        func = _resolve_object_orphan(orphan, func_name, project_root)
    return func, _evidence_function_name(func, func_name)
def _scalar_candidate_rounds(safe_args, safe_kwargs, existing) -> list:
    rounds = []
    for round_name, val in (("zeros", 0), ("ones", 1), ("emptystr", "")):
        candidate_args = [val if a is None else a for a in safe_args]
        candidate_kwargs = {k: (val if v is None else v)
                            for k, v in safe_kwargs.items()}
        if (candidate_args, candidate_kwargs) not in existing:
            rounds.append((candidate_args, candidate_kwargs, round_name))
    return rounds
def _read_signature(func):
    try:
        return inspect.signature(func)
    except (OSError, ValueError, TypeError, KeyError, AttributeError,
            RecursionError) as _e:
        logger.debug("signature unavailable: %s", _e)
        return None
def _required_positional_count(func) -> int:
    sig = _read_signature(func)
    if sig is None:
        return 0
    return sum(
        1 for p in sig.parameters.values()
        if p.default is inspect.Parameter.empty
        and p.kind in (inspect.Parameter.POSITIONAL_ONLY,
                       inspect.Parameter.POSITIONAL_OR_KEYWORD)
    )
def _build_input_rounds(func, safe_args, safe_kwargs) -> list:
    input_rounds = [(safe_args, safe_kwargs, "safe_args")]
    if safe_args or safe_kwargs:
        input_rounds.append(([], {}, "no_args"))
    none_args = [None] * _required_positional_count(func)
    if none_args and none_args != safe_args:
        input_rounds.append((none_args, safe_kwargs, "none_args"))
    if any(value is None
           for value in (*safe_args, *safe_kwargs.values())):
        existing = [(r[0], r[1]) for r in input_rounds]
        input_rounds.extend(_scalar_candidate_rounds(safe_args, safe_kwargs, existing))
    return input_rounds
def _record_outcome(results: dict, func_name: str, status: str,
                    reason: str) -> None:
    results[status] += 1
    results["details"].append({
        "function": func_name,
        "status": status,
        "reason": reason,
    })
def _execute_fuzz_rounds(func, func_name, safe_args, safe_kwargs, results):
    input_rounds = _build_input_rounds(func, safe_args, safe_kwargs)
    resolved_this = False
    last_error = ""
    for args_try, kwargs_try, round_name in input_rounds:
        try:
            result = _invoke_callable(func, *args_try, **kwargs_try)
            has_return = result is not None
            _record_outcome(
                results, func_name, "resolved",
                f"executed with {round_name}"
                + (" (has return value)" if has_return else ""))
            resolved_this = True
            break
        except SystemExit as exc:
            label = _system_exit_label(exc)
            if label is None:
                _record_outcome(
                    results, func_name, "resolved",
                    f"executed with {round_name} (SystemExit(0))")
                resolved_this = True
                break
            logger.debug("suppressed SystemExit: %s", exc)
            last_error = f"{label} with {round_name}"
            continue
        except BaseException as exc:  # noqa: BLE001 — 隔离模糊目标的全部退出异常
            logger.debug("suppressed %s: %s", type(exc).__name__, exc)
            last_error = f"{type(exc).__name__} with {round_name}: {str(exc)[:80]}"
            continue
    return resolved_this, last_error
_IDENTITY_FACTORIES: tuple = (
    (int, lambda: 0), (float, lambda: 0), (str, lambda: ""),
    (bool, lambda: False), (list, list), (dict, dict),
    (set, set), (tuple, tuple),
)
_SIMPLE_TYPE_OBJECTS = tuple(_t for _t, _ in _IDENTITY_FACTORIES) + (type(None),)
_SIMPLE_TYPE_NAMES: dict = {_t.__name__: _f for _t, _f in _IDENTITY_FACTORIES}
def _annotation_to_safe_value(anno: Any) -> Any:
    if isinstance(anno, str):
        factory = _SIMPLE_TYPE_NAMES.get(anno.strip())
        return factory() if factory is not None else None
    for _type, _factory in _IDENTITY_FACTORIES:
        if anno is _type:
            return _factory()
    return None
def _annotation_is_simple(anno: Any) -> bool:
    if isinstance(anno, str):
        return anno.strip() in _SIMPLE_TYPE_NAMES
    return any(anno is _t for _t in _SIMPLE_TYPE_OBJECTS)
def _required_params(sig) -> list:
    return [
        param for param in sig.parameters.values()
        if param.kind not in (inspect.Parameter.VAR_POSITIONAL,
                              inspect.Parameter.VAR_KEYWORD)
        and param.default is inspect.Parameter.empty
    ]
def _slice_function_viability(func):
    sig = _read_signature(func)
    if sig is None:
        return True, "no signature available"
    required_complex = 0
    for param in _required_params(sig):
        anno = param.annotation
        if anno is not inspect.Parameter.empty and not _annotation_is_simple(anno):
            required_complex += 1
    if required_complex > _MAX_REQUIRED_COMPLEX_PARAMS:
        return False, f"{required_complex} required complex params — likely needs real context"
    return True, "viable for fuzzing"
def _make_safe_args(func):
    sig = _read_signature(func)
    if sig is None:
        return [], {}
    args = []
    kwargs = {}
    for param in _required_params(sig):
        if param.kind is inspect.Parameter.KEYWORD_ONLY:
            kwargs[param.name] = _annotation_to_safe_value(param.annotation)
        else:
            args.append(_annotation_to_safe_value(param.annotation))
    return args, kwargs
def _truncate_fuzz_orphans(orphans: list, results: dict) -> list:
    if len(orphans) <= _MAX_FUZZ_ORPHANS:
        return orphans
    results["truncated"] = {
        "total": len(orphans),
        "kept": _MAX_FUZZ_ORPHANS,
        "dropped": len(orphans) - _MAX_FUZZ_ORPHANS,
    }
    return orphans[:_MAX_FUZZ_ORPHANS]
def empty_fuzz_result(skipped: str | None = None) -> dict:
    _result = {"attempted": 0, "resolved": 0, "failed": 0,
               "sliced": 0, "details": []}
    if skipped is not None:
        _result["skipped"] = skipped
    return _result
def targeted_fuzz_orphans(orphans: list, project_root: str = _DEFAULT_PROJECT_ROOT) -> dict:
    if orphans is not None and not isinstance(orphans, (list, tuple)):
        logger.warning("targeted_fuzz_orphans 入参非列表形态: %r，按空载荷处理",
                       orphans)
        return empty_fuzz_result("orphans 入参非列表形态")
    results = empty_fuzz_result()
    if not orphans:
        return results
    orphans = _truncate_fuzz_orphans(list(orphans), results)
    for orphan in orphans:
        results["attempted"] += 1
        _fuzz_single_orphan(orphan, project_root, results)
    return results
def _fuzz_single_orphan(orphan, project_root: str, results: dict) -> None:
    func_name = ""
    try:
        func_name = _orphan_name(orphan)
        func, func_name = _resolve_orphan_func(orphan, project_root)
        if func is None:
            _record_outcome(results, func_name, "failed",
                            "function object not accessible")
            return
        if not callable(func):
            _record_outcome(results, func_name, "failed",
                            "resolved object is not callable")
            return
        safe_args, safe_kwargs = _make_safe_args(func)
        viable, slice_reason = _slice_function_viability(func)
        if not viable:
            _record_outcome(results, func_name, "sliced",
                            f"skipped: {slice_reason}")
            return
        if _has_side_effects(func):
            _record_outcome(
                results, func_name, "sliced",
                "skipped: side-effect risk (file I/O, subprocess, exec, etc.)")
            return
        resolved_this, last_error = _execute_fuzz_rounds(
            func, func_name, safe_args, safe_kwargs, results)
        if not resolved_this:
            _record_outcome(results, func_name, "failed",
                            last_error or "all input rounds failed")
    except BaseException as e:  # noqa: BLE001 — 隔离孤儿解析与执行的全部退出异常
        logger.debug("模糊执行函数 %s 失败: %s", func_name, e)
        _record_outcome(
            results, func_name, "failed", str(e)[:_FUZZ_REASON_LIMIT])
def _run_fuzz_phase(sim_report, call_graph, project_root: str) -> None:
    orphans = getattr(call_graph, 'orphans', None) or []
    if orphans:
        try:
            sim_report.fuzzy_execution = targeted_fuzz_orphans(
                orphans, project_root=project_root)
        except Exception as e:  # noqa: BLE001 — 模糊执行失败不阻断诊断链
            logger.warning("[FuzzOrphans] 靶向模糊执行失败（不阻塞）: %s", e)
            sim_report.fuzzy_execution = empty_fuzz_result(
                skipped=f"fuzz error: {e}")
    else:
        sim_report.fuzzy_execution = empty_fuzz_result()
def _run_confirm_phase(blindspot_report, sim_report) -> None:
    if blindspot_report is None:
        return
    try:
        _entries = getattr(blindspot_report, "entries", None)
        if _entries:
            _conf = confirm_dead_code_with_evidence(_entries, sim_report)
            _pc = _conf["phase_counts"]
            sim_report.dead_code_confirmation = _pc
            logger.info(
                "  [DeadCodeConfirm] 三阶段确认: 静态%d, 动态排除%d, "
                "确认%d, 缺测试%d",
                _pc["phase1"], _pc["phase2_rejected"], _pc["confirmed"],
                _pc.get("confirmed_untested", 0),
            )
    except Exception as e:  # noqa: BLE001 — 确认失败不阻塞诊断链
        logger.warning("[DeadCodeConfirm] 三阶段死代码确认失败（不阻塞）: %s", e)
def run_dynamic_evidence_phase(sim_report, call_graph,
                               project_root: str,
                               blindspot_report=None) -> None:
    try:
        _run_fuzz_phase(sim_report, call_graph, project_root)
    except Exception as e:  # noqa: BLE001 — 模糊执行是辅助证据
        logger.warning("[FuzzOrphans] 靶向模糊执行阶段失败（降级）: %s", e)
        sim_report.fuzzy_execution = empty_fuzz_result(
            skipped=f"fuzz error: {e}")
    try:
        _run_confirm_phase(blindspot_report, sim_report)
    except Exception as e:  # noqa: BLE001 — 死代码确认是辅助证据
        logger.warning("[DeadCodeConfirm] 死代码确认阶段失败（降级）: %s", e)
def run_diagnosis(existing_call_graph, trace_edges, sim_report,
                  coverage_hook, reuse=None, ctx=None):
    project_root = sim_report.project_root
    logger.info("\n[Simulate] 全量诊断...")
    if existing_call_graph is not None:
        call_graph = existing_call_graph
        logger.info("  [Cache] 复用外部调用图，跳过重复构建")
    else:
        call_graph = None
        logger.warning("[Simulate] 诊断侧无可用调用图，图依赖诊断降级跳过")
    blindspot_report = None
    try:
        try:
            merge_trace_edges(call_graph, trace_edges, sim_report)
        except Exception as _merge_e:  # noqa: BLE001 — 调用边合并是辅助证据
            logger.warning(
                "[Simulate] 运行时调用边合并失败（降级继续诊断）: %s", _merge_e)
        blindspot_report = _scan_blindspots_for_diagnosis(
            project_root, coverage_hook, call_graph, ctx, reuse)
        run_dynamic_evidence_phase(
            sim_report, call_graph, project_root, blindspot_report)
    finally:
        _resume_coverage(coverage_hook)
    return sim_report, blindspot_report
def simulate_engine_files(current_file: str) -> tuple[str, ...]:
    return (_SANDBOX_MODULE_FILE, current_file, SIM_MODULE_FILE)
def prepare_evidence_context(project_root: str, coverage_hook: Any,
                             reuse: Any) -> tuple[Any, Any]:
    call_graph = ensure_built_call_graph(
        project_root, getattr(reuse, "call_graph", None))
    source_paths = prepare_instrumentation_paths(project_root, call_graph)
    coverage_hook = ensure_coverage_hook(
        coverage_hook, source_paths, project_root)
    return call_graph, coverage_hook
